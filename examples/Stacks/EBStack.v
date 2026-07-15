Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulation.
Require Import RGILogic.
Require Import examples.Common.AtomicLTS.
Require Import examples.Stacks.StackSpec.
Require Import examples.Exchanger.ExchangerSpec.


Module EBStackImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS TryStackSpec ExchSpec StackSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.

  Definition ETryStackLayer : layer_interface :=
  {|
    li_sig := ETryStack A;
    li_lts := VTryStack;
    li_init := Idle nil;
  |}.

  Definition EExchangerLayer : layer_interface :=
  {|
    li_sig := EExch (option A);
    li_lts := VExch;
    li_init := ExSIdle;
  |}.

  Definition E : layer_interface := ETryStackLayer ⊗ₗ EExchangerLayer.
  
  Definition F : layer_interface :=
  {|
    li_sig := EStack A;
    li_lts := VStack;
    li_init := Idle nil
  |}.
  
  Definition push_impl (v : A) (_ : tid) : Prog (li_sig E) unit :=
    Do {
      inr (ExchSpec.exch (Some v)) >= other =>
      match other with
      | Some None => Ret (inr tt)
      | _ =>
        inl (TryStackSpec.push v) >= succ =>
        Ret (match succ with | FAIL => inl tt | _ => inr tt end)
      end
    } Loop.

  Definition pop_impl (_ : tid) : Prog (li_sig E) (option A) :=
    Do {
      inr (ExchSpec.exch None) >= other =>
      match other with
      | Some (Some v) => Ret (inr (Some v))
      | _ =>
        inl TryStackSpec.pop >= succ =>
        Ret (match succ with | FAIL => inl tt | OK v => inr v end)
      end
    } Loop.

  Definition assertion := @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.

  Definition stack_state (s : State (li_lts E)) : list A :=
    state (fst s).

  Definition exch_state (s : State (li_lts E)) : @EExchState (option A) :=
    snd s.

  Definition wait_lin (t : tid) (v : option A) (π : tmap Semantics.LinState) : Prop :=
    match v with
    | Some x => TMap.find t π = Some (Semantics.ls_inv (StackSpec.push x))
    | None => TMap.find t π = Some (Semantics.ls_inv StackSpec.pop)
    end.

  Definition done_lin
    (t : tid) (v other : option A) (π : tmap Semantics.LinState) : Prop :=
    match v, other with
    | Some x, None =>
        TMap.find t π = Some (Semantics.ls_linr (StackSpec.push x) tt)
    | None, Some x =>
        TMap.find t π = Some (Semantics.ls_linr StackSpec.pop (Some x))
    | _, _ => False
    end.

  Definition paired_lin
    (t1 : tid) (v1 : option A) (t2 : tid) (v2 : option A)
    (π : tmap Semantics.LinState) : Prop :=
    match v1, v2 with
    | Some _, None | None, Some _ =>
        done_lin t1 v1 v2 π /\ done_lin t2 v2 v1 π
    | Some _, Some _ | None, None =>
        wait_lin t1 v1 π /\ wait_lin t2 v2 π
    end.

  Definition accepted_lin
    (t1 : tid) (v1 : option A) (t2 : tid) (v2 : option A)
    (π : tmap Semantics.LinState) : Prop :=
    match v1, v2 with
    | Some _, None | None, Some _ => done_lin t2 v2 v1 π
    | Some _, Some _ | None, None => wait_lin t2 v2 π
    end.

  Definition exch_ok (xs : @EExchState (option A)) (π : tmap Semantics.LinState) : Prop :=
    match xs with
    | ExSIdle => True
    | ExSOffered t v => wait_lin t v π
    | ExSPaired t1 v1 t2 v2 => paired_lin t1 v1 t2 v2 π
    | ExSAccepted t1 v1 t2 v2 => accepted_lin t1 v1 t2 v2 π
    end.

  Definition exch_distinct (xs : @EExchState (option A)) : Prop :=
    match xs with
    | ExSPaired t1 _ t2 _ | ExSAccepted t1 _ t2 _ => t1 <> t2
    | _ => True
    end.

  Definition I : assertion :=
    fun s =>
      ρ s = Idle (stack_state (σ s)) /\
      exch_ok (exch_state (σ s)) (π s) /\
      exch_distinct (exch_state (σ s)).

  Definition no_exch_by (t : tid) (xs : @EExchState (option A)) : Prop :=
    match xs with
    | ExSIdle => True
    | ExSOffered t1 _ => t <> t1
    | ExSPaired t1 _ t2 _ => t <> t1 /\ t <> t2
    | ExSAccepted _ _ t2 _ => t <> t2
    end.

  Definition NoExchBy (t : tid) : assertion :=
    fun s => no_exch_by t (exch_state (σ s)).

  Definition Active (t : tid) (m : Sig.op (li_sig F)) : assertion :=
    ALin t (Semantics.ls_inv m) //\\ NoExchBy t.

  Definition Done (t : tid) (m : Sig.op (li_sig F)) : assertion :=
    ∃ ret, ALin t (Semantics.ls_linr m ret).

  Definition Live (t : tid) (m : Sig.op (li_sig F)) : assertion :=
    ALin t (Semantics.ls_inv m) \\// Done t m.

  Definition R_pres t : rg_relation :=
    fun s1 s2 =>
      (TMap.find t (π s1) = None <-> TMap.find t (π s2) = None) /\
      (forall m, Active t m s1 -> Active t m s2) /\
      (forall m ret, ALin t (Semantics.ls_linr m ret) s1 ->
        ALin t (Semantics.ls_linr m ret) s2) /\
      (forall m, Live t m s1 -> Live t m s2) /\
      (NoExchBy t s1 -> NoExchBy t s2).

  Definition G t : rg_relation :=
    fun s1 s2 =>
      I s2 /\
      (forall t', t <> t' -> R_pres t' s1 s2).

  Definition R t : rg_relation :=
    R_pres t.

  Lemma Istable {t} : Stable (R t) I I.
  Proof. unfold Stable. apply ConjRightImpl, ImplRefl. Qed.

  Lemma Activestable {t m}: Stable (R t) I (Active t m).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Hact [_ [Hpres _]]]] ?].
    eauto.
  Qed.

  Lemma Donestable {t m}: Stable (R t) I (Done t m).
  Proof.
    unfold Stable, R, R_pres, Done.
    intros ? [[? [[ret Hdone] [_ [_ [Hpres _]]]]] ?].
    exists ret. eauto.
  Qed.

  Lemma ALinRetstable {t m ret}: Stable (R t) I (ALin t (Semantics.ls_linr m ret)).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Hdone [_ [_ [Hpres _]]]]] ?].
    eauto.
  Qed.

  Lemma Livestable {t m}: Stable (R t) I (Live t m).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Hlive [_ [_ [_ [Hpres _]]]]]] ?].
    eauto.
  Qed.

  Lemma NoExchBystable {t}: Stable (R t) I (NoExchBy t).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Hno [_ [_ [_ [_ Hpres]]]]]] ?].
    eauto.
  Qed.

  Create HintDb stableDB.
  Hint Resolve Istable Activestable Donestable ALinRetstable Livestable NoExchBystable : stableDB.

  Lemma wait_lin_add_fresh t t' v f π :
    TMap.find t π = None ->
    wait_lin t' v π ->
    wait_lin t' v (TMap.add t (Semantics.ls_inv f) π).
  Proof.
    intros Hnone Hwait.
    destruct v; simpl in *;
    destruct (PositiveMap.E.eq_dec t t'); subst.
    - rewrite Hnone in Hwait. discriminate.
    - rewrite PositiveMap.gso by auto. exact Hwait.
    - rewrite Hnone in Hwait. discriminate.
    - rewrite PositiveMap.gso by auto. exact Hwait.
  Qed.

  Lemma done_lin_add_fresh t t' v other f π :
    TMap.find t π = None ->
    done_lin t' v other π ->
    done_lin t' v other (TMap.add t (Semantics.ls_inv f) π).
  Proof.
    intros Hnone Hdone.
    destruct v as [v|], other as [other|]; simpl in *; try contradiction;
    destruct (PositiveMap.E.eq_dec t t'); subst.
    - rewrite Hnone in Hdone. discriminate.
    - rewrite PositiveMap.gso by auto. exact Hdone.
    - rewrite Hnone in Hdone. discriminate.
    - rewrite PositiveMap.gso by auto. exact Hdone.
  Qed.

  Lemma paired_lin_add_fresh t t1 v1 t2 v2 f π :
    TMap.find t π = None ->
    paired_lin t1 v1 t2 v2 π ->
    paired_lin t1 v1 t2 v2 (TMap.add t (Semantics.ls_inv f) π).
  Proof.
    destruct v1 as [a|], v2 as [b|]; simpl in *; intros Hnone [H1 H2]; split.
    - change (wait_lin t1 (Some a) (TMap.add t (Semantics.ls_inv f) π)).
      eapply wait_lin_add_fresh; eauto.
    - change (wait_lin t2 (Some b) (TMap.add t (Semantics.ls_inv f) π)).
      eapply wait_lin_add_fresh; eauto.
    - change (done_lin t1 (Some a) None (TMap.add t (Semantics.ls_inv f) π)).
      eapply done_lin_add_fresh; eauto.
    - change (done_lin t2 None (Some a) (TMap.add t (Semantics.ls_inv f) π)).
      eapply done_lin_add_fresh; eauto.
    - change (done_lin t1 None (Some b) (TMap.add t (Semantics.ls_inv f) π)).
      eapply done_lin_add_fresh; eauto.
    - change (done_lin t2 (Some b) None (TMap.add t (Semantics.ls_inv f) π)).
      eapply done_lin_add_fresh; eauto.
    - change (wait_lin t1 None (TMap.add t (Semantics.ls_inv f) π)).
      eapply wait_lin_add_fresh; eauto.
    - change (wait_lin t2 None (TMap.add t (Semantics.ls_inv f) π)).
      eapply wait_lin_add_fresh; eauto.
  Qed.

  Lemma accepted_lin_add_fresh t t1 v1 t2 v2 f π :
    TMap.find t π = None ->
    accepted_lin t1 v1 t2 v2 π ->
    accepted_lin t1 v1 t2 v2 (TMap.add t (Semantics.ls_inv f) π).
  Proof.
    destruct v1 as [a|], v2 as [b|]; simpl in *; intros Hnone H.
    - change (wait_lin t2 (Some b) (TMap.add t (Semantics.ls_inv f) π)).
      eapply wait_lin_add_fresh; eauto.
    - change (done_lin t2 None (Some a) (TMap.add t (Semantics.ls_inv f) π)).
      eapply done_lin_add_fresh; eauto.
    - change (done_lin t2 (Some b) None (TMap.add t (Semantics.ls_inv f) π)).
      eapply done_lin_add_fresh; eauto.
    - change (wait_lin t2 None (TMap.add t (Semantics.ls_inv f) π)).
      eapply wait_lin_add_fresh; eauto.
  Qed.

  Lemma IGinv : forall t f, ⊨ Ginv t f ⊚ I ==>> I //\\ ALin t (Semantics.ls_inv f).
  Proof.
    unfold I, ALin, Ginv, LiftRelation_π.
    intros t f s [s' [HI [? [? [Hnone Hπ]]]]].
    destruct s, s'; simpl in *; subst.
    split.
    - destruct HI as [Hr [Hex Hdist]]. split; [exact Hr|].
      split.
      2:{ destruct σ0 as [ts xs]; simpl in *; exact Hdist. }
      destruct σ0 as [ts xs]; simpl in *.
      destruct xs as [ot ov|pt1 pv1 pt2 pv2|at1 av1 at2 av2|]; simpl in *; auto.
      + eapply wait_lin_add_fresh; eauto.
      + eapply paired_lin_add_fresh; eauto.
      + eapply accepted_lin_add_fresh; eauto.
    - simpl. rewrite PositiveMap.gss. auto.
  Qed.

  Lemma exch_ok_no_exch_add_fresh t xs π :
    TMap.find t π = None ->
    exch_ok xs π ->
    no_exch_by t xs.
  Proof.
    intros Hnone Hex.
    destruct xs as [t1 v1|t1 v1 t2 v2|t1 v1 t2 v2|]; simpl in *; auto.
    - destruct v1; simpl in *; intros Heq; subst; rewrite Hnone in Hex; discriminate.
    - destruct v1 as [a|], v2 as [b|]; simpl in *; destruct Hex as [H1 H2]; split;
      intros Heq; subst; rewrite Hnone in *; discriminate.
    - destruct v1 as [a|], v2 as [b|]; simpl in *;
      intros Heq; subst; rewrite Hnone in Hex; discriminate.
  Qed.

  Lemma IGinvActive : forall t f, ⊨ Ginv t f ⊚ I ==>> I //\\ Active t f.
  Proof.
    unfold I, Active, ALin, NoExchBy, Ginv, LiftRelation_π.
    intros t f s [s' [HI [? [? [Hnone Hπ]]]]].
    destruct s, s'; simpl in *; subst.
    destruct HI as [Hr [Hex Hdist]].
    split.
    - split; [exact Hr|].
      split.
      2:{ destruct σ0 as [ts xs]; simpl in *; exact Hdist. }
      destruct σ0 as [ts xs]; simpl in *.
      destruct xs as [ot ov|pt1 pv1 pt2 pv2|at1 av1 at2 av2|]; simpl in *; auto.
      + eapply wait_lin_add_fresh; eauto.
      + eapply paired_lin_add_fresh; eauto.
      + eapply accepted_lin_add_fresh; eauto.
    - split.
      + simpl. rewrite PositiveMap.gss. auto.
      + simpl. eapply exch_ok_no_exch_add_fresh; eauto.
  Qed.

  Lemma exch_ok_remove_no_exch t xs π :
    no_exch_by t xs ->
    exch_ok xs π ->
    exch_ok xs (TMap.remove t π).
  Proof.
    intros Hno Hex.
    destruct xs as [t1 v1|t1 v1 t2 v2|t1 v1 t2 v2|]; simpl in *; auto.
    - destruct v1; simpl in *; rewrite PositiveMap.gro by auto; exact Hex.
    - destruct v1 as [a|], v2 as [b|]; simpl in *; destruct Hex as [H1 H2]; destruct Hno as [Hn1 Hn2]; split;
      rewrite PositiveMap.gro by auto; assumption.
    - destruct v1 as [a|], v2 as [b|]; simpl in *;
      rewrite PositiveMap.gro by auto; assumption.
  Qed.

  Lemma exch_ok_add_add_no_exch t xs π ls1 ls2 :
    no_exch_by t xs ->
    exch_ok xs π ->
    exch_ok xs (TMap.add t ls2 (TMap.add t ls1 π)).
  Proof.
    intros Hno Hex.
    destruct xs as [t1 v1|t1 v1 t2 v2|t1 v1 t2 v2|]; simpl in *; auto.
    - destruct v1; simpl in *; repeat (rewrite PositiveMap.gso by auto); exact Hex.
    - destruct v1 as [a|], v2 as [b|]; simpl in *; destruct Hex as [H1 H2]; destruct Hno as [Hn1 Hn2]; split;
      repeat (rewrite PositiveMap.gso by auto); assumption.
    - destruct v1 as [a|], v2 as [b|]; simpl in *;
      repeat (rewrite PositiveMap.gso by auto); assumption.
  Qed.

  Lemma IGretNoExch : forall t f ret,
    ⊨ Gret t f ret ⊚ (I //\\ ALin t (Semantics.ls_linr f ret) //\\ NoExchBy t) ==>> I.
  Proof.
    unfold Gret, LiftRelation_π.
    intros t f ret s [s' [Hpre [? [? [Hfind Hπ]]]]].
    destruct Hpre as [HI [Hlin Hno]].
    unfold I, ALin, NoExchBy in *.
    destruct s, s'; simpl in *; subst.
    destruct HI as [Hr [Hex Hdist]]. split; [exact Hr|].
    destruct σ0 as [ts xs]; simpl in *.
    split.
    - eapply exch_ok_remove_no_exch; eauto.
    - exact Hdist.
  Qed.

  Lemma no_error t (m : Sig.op (li_sig E)) (P : assertion) :
    ⊨ P ==>> ANoError {| te_tid := t; te_ev := InvEv m |}.
  Proof.
    unfold ANoError.
    intros [σ0 ρ0 π0] _ Herr.
    destruct σ0 as [ts xs], m as [m|m]; simpl in *; contradiction.
  Qed.

  Lemma R_pres_ginv_other t t' f s1 s2 :
    t <> t' ->
    Ginv t f s1 s2 ->
    R_pres t' s1 s2.
  Proof.
    intros Hneq Hinv.
    assert (Hneq' : t' <> t) by congruence.
    unfold Ginv, LiftRelation_π in Hinv.
    destruct s1 as [σ1 ρ1 π1], s2 as [σ2 ρ2 π2]; simpl in *.
    destruct Hinv as [Hσ [Hρ [Hfind Hπ]]]. subst.
    unfold R_pres, Active, NoExchBy, Live, Done, ALin; simpl.
    split.
    - split; intro H.
      + rewrite (@PositiveMap.gso Semantics.LinState t' t (Semantics.ls_inv f) π1 Hneq'). exact H.
      + rewrite (@PositiveMap.gso Semantics.LinState t' t (Semantics.ls_inv f) π1 Hneq') in H. exact H.
    - split.
      + intros m [Hlin Hno]. simpl in *. split.
        * change (TMap.find t' (TMap.add t (Semantics.ls_inv f) π1) =
            Some (Semantics.ls_inv m)).
          rewrite (@PositiveMap.gso Semantics.LinState t' t (Semantics.ls_inv f) π1 Hneq').
          exact Hlin.
        * exact Hno.
      + split.
        * intros m ret H. simpl in *.
          change (TMap.find t' (TMap.add t (Semantics.ls_inv f) π1) =
            Some (Semantics.ls_linr m ret)).
          rewrite (@PositiveMap.gso Semantics.LinState t' t (Semantics.ls_inv f) π1 Hneq').
          exact H.
        * split.
          -- intros m [Hlin | [ret Hret]]; simpl in *; simpl.
             ++ left.
                change (TMap.find t' (TMap.add t (Semantics.ls_inv f) π1) =
                  Some (Semantics.ls_inv m)).
                rewrite (@PositiveMap.gso Semantics.LinState t' t (Semantics.ls_inv f) π1 Hneq').
                exact Hlin.
             ++ right. exists ret.
                change (TMap.find t' (TMap.add t (Semantics.ls_inv f) π1) =
                  Some (Semantics.ls_linr m ret)).
                rewrite (@PositiveMap.gso Semantics.LinState t' t (Semantics.ls_inv f) π1 Hneq').
                exact Hret.
          -- intros H. exact H.
  Qed.

  Lemma R_pres_gret_other t t' f ret s1 s2 :
    t <> t' ->
    Gret t f ret s1 s2 ->
    R_pres t' s1 s2.
  Proof.
    intros Hneq Hret.
    assert (Hneq' : t' <> t) by congruence.
    unfold Gret, LiftRelation_π in Hret.
    destruct s1 as [σ1 ρ1 π1], s2 as [σ2 ρ2 π2]; simpl in *.
    destruct Hret as [Hσ [Hρ [Hfind Hπ]]]. subst.
    unfold R_pres, Active, NoExchBy, Live, Done, ALin; simpl.
    split.
    - split; intro H.
      + rewrite (@PositiveMap.gro Semantics.LinState t' t π1 Hneq'). exact H.
      + rewrite (@PositiveMap.gro Semantics.LinState t' t π1 Hneq') in H. exact H.
    - split.
      + intros m [Hlin Hno]. simpl in *. split.
        * change (TMap.find t' (TMap.remove t π1) =
            Some (Semantics.ls_inv m)).
          rewrite (@PositiveMap.gro Semantics.LinState t' t π1 Hneq').
          exact Hlin.
        * exact Hno.
      + split.
        * intros m r H. simpl in *.
          change (TMap.find t' (TMap.remove t π1) =
            Some (Semantics.ls_linr m r)).
          rewrite (@PositiveMap.gro Semantics.LinState t' t π1 Hneq').
          exact H.
        * split.
          -- intros m [Hlin | [r Hr]]; simpl in *; simpl.
             ++ left.
                change (TMap.find t' (TMap.remove t π1) =
                  Some (Semantics.ls_inv m)).
                rewrite (@PositiveMap.gro Semantics.LinState t' t π1 Hneq').
                exact Hlin.
             ++ right. exists r.
                change (TMap.find t' (TMap.remove t π1) =
                  Some (Semantics.ls_linr m r)).
                rewrite (@PositiveMap.gro Semantics.LinState t' t π1 Hneq').
                exact Hr.
          -- intros H. exact H.
  Qed.

  Lemma R_pres_refl t s : R_pres t s s.
  Proof.
    unfold R_pres. firstorder.
  Qed.

  Lemma R_pres_same_π t' σ1 σ2 ρ0 π0 :
    (no_exch_by t' (exch_state σ1) -> no_exch_by t' (exch_state σ2)) ->
    R_pres t' (σ1, ρ0, π0) (σ2, ρ0, π0).
  Proof.
    unfold R_pres, Active, Live, Done, ALin, NoExchBy.
    simpl. intros Hno.
    split; [tauto|].
    split.
    - intros m [Hlin Hnx]. split; [exact Hlin|auto].
    - split.
      + intros m ret Hlin. exact Hlin.
      + split.
        * intros m Hlive. exact Hlive.
        * intros Hnx. auto.
  Qed.

  Lemma R_pres_add_add_other t t' ls1 ls2 σ1 σ2 ρ1 ρ2 π0 :
    t <> t' ->
    (no_exch_by t' (exch_state σ1) -> no_exch_by t' (exch_state σ2)) ->
    R_pres t' (σ1, ρ1, π0) (σ2, ρ2, TMap.add t ls2 (TMap.add t ls1 π0)).
  Proof.
    intros Hneq Hno.
    assert (Hneq' : t' <> t) by congruence.
    unfold R_pres, Active, Live, Done, ALin, NoExchBy.
    simpl.
    split.
    - split; intro Hnone.
      + rewrite PositiveMap.gso by exact Hneq'.
        rewrite PositiveMap.gso by exact Hneq'.
        exact Hnone.
      + rewrite PositiveMap.gso in Hnone by exact Hneq'.
        rewrite PositiveMap.gso in Hnone by exact Hneq'.
        exact Hnone.
    - split.
      + intros m [Hlin Hnx]. simpl in *. split.
        * simpl. rewrite PositiveMap.gso by exact Hneq'.
          rewrite PositiveMap.gso by exact Hneq'.
          exact Hlin.
        * auto.
      + split.
        * intros m ret Hlin. simpl in *.
          simpl. rewrite PositiveMap.gso by exact Hneq'.
          rewrite PositiveMap.gso by exact Hneq'.
          exact Hlin.
        * split.
          -- intros m [Hlin | [ret Hlin]]; simpl in *.
             ++ left. simpl.
                rewrite PositiveMap.gso by exact Hneq'.
                rewrite PositiveMap.gso by exact Hneq'.
                exact Hlin.
             ++ right. exists ret. simpl.
                rewrite PositiveMap.gso by exact Hneq'.
                rewrite PositiveMap.gso by exact Hneq'.
                exact Hlin.
          -- intros Hnx. auto.
  Qed.
    
  Program Definition Mebstack : layer_implementation E F := {|
    li_impl m :=
      match m with
      | push v => push_impl v
      | pop => pop_impl
      end
  |}.
  Next Obligation.
    eapply RGILogic.soundness with (R:=R) (G:=G) (I:=I).
	    {
	      constructor.
	      unfold R. intros s s' Hrel _.
	      exact (proj1 Hrel).
	    }
	    {
	      unfold G, R.
	      intros t1 t2 Hneq s1 s2 Hrel.
	      destruct Hrel as [HG | Hmeta].
	      - exact (proj2 HG t2 Hneq).
	      - unfold GINV, GRET, GId in Hmeta.
	        destruct Hmeta as [[Hinv | Hret] | Hid].
	        + destruct Hinv as [f Hinv].
	          eapply R_pres_ginv_other; eauto.
	        + destruct Hret as [f [ret Hret]].
	          eapply R_pres_gret_other; eauto.
	        + subst. apply R_pres_refl.
	    }
    intros t f. destruct f.
    - exists (I //\\ Active t (push v)).
      exists (fun _ => I //\\ ALin t (Semantics.ls_linr (push v) tt) //\\ NoExchBy t).
      constructor.
      + apply IGinvActive.
      + solve_conj_impl.
      + solve_conj_stable stableDB.
      + intros [].
        apply IGretNoExch.
      + unfold ALin. intros [] σ0 ρ0 π0 [HI [Hlin Hno]].
        exact Hlin.
      + simpl. unfold push_impl.
        eapply provable_doloop;
        try solve_conj_impl;
        try solve_conj_stable stableDB.
        eapply provable_vis_safe with
          (P' := I //\\ Live t (push v))
          (Q' := fun other =>
            match other with
            | Some None => I //\\ ALin t (Semantics.ls_linr (push v) tt) //\\ NoExchBy t
            | _ => I //\\ Active t (push v)
            end);
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        try (intro other; destruct other as [[ov|]|]; try destruct ov; solve_conj_stable stableDB);
        try solve [apply no_error].
        * intros [[ov|]|]; try destruct ov; solve_conj_impl.
        * pupdate_intros_atomic.
          {
            pupdate_finish; split.
            - destruct Hpre as [HI [Hlin Hno]].
              unfold I, Active, Live, Done, ALin, NoExchBy in *; simpl in *.
              split.
              + destruct HI as [Hr _]. split; [exact Hr|split; [exact Hlin|auto]].
              + left. exact Hlin.
            - unfold G, R_pres, Active, Live, Done, ALin, NoExchBy.
              split.
              + destruct Hpre as [HI [Hlin Hno]].
                unfold I in *; simpl in *.
                destruct HI as [Hr _]. split; [exact Hr|split; [exact Hlin|auto]].
              + intros t' Hneq; simpl.
                split.
                -- split; intro H; exact H.
                -- split.
                   ++ intros m [Hlin Hno]. split; [exact Hlin|congruence].
                   ++ split.
                      ** intros m ret Hlin. exact Hlin.
                      ** split.
                         --- intros m [Hlin | [ret Hlin]]; [left | right; exists ret]; exact Hlin.
                         --- intros _. congruence.
          }
          {
            destruct v1 as [w|].
            - pupdate_finish; split.
              + destruct Hpre as [HI [Hlin Hno]].
	                unfold I, Active, Live, Done, ALin, NoExchBy in *; simpl in *.
		                destruct HI as [Hr [Hex Hdist]].
		                split; [split; [exact Hr|split; [split; [exact Hex|exact Hlin]|congruence]]|left; exact Hlin].
              + unfold G, R_pres, Active, Live, Done, ALin, NoExchBy.
                split.
                * destruct Hpre as [HI [Hlin Hno]].
                  unfold I, Active, ALin in *; simpl in *.
		                  destruct HI as [Hr [Hex Hdist]].
		                  split; [exact Hr|split; [split; [exact Hex|exact Hlin]|congruence]].
	                * intros t' Hneq; simpl.
                  destruct (PositiveMap.E.eq_dec t' t1) as [Heq|Hne1]; subst.
                  -- split.
                     ++ split; intro Hnone.
                        ** destruct Hpre as [HI [Hlin Hno]].
                           unfold I in HI; simpl in HI.
	                           destruct HI as [_ [Hex _]].
                           rewrite Hex in Hnone. discriminate.
                        ** destruct Hpre as [HI [Hlin Hno]].
                           unfold I in HI; simpl in HI.
	                           destruct HI as [_ [Hex _]].
                           rewrite Hex in Hnone. discriminate.
                     ++ split.
                        ** intros m [Hlin Hno]. contradiction.
                        ** split.
                           --- intros m ret Hret.
                               destruct Hpre as [HI _].
                               unfold I in HI; simpl in HI.
	                               destruct HI as [_ [Hex _]].
                               rewrite Hex in Hret. discriminate.
                           --- split.
	                               +++ intros m [Hlin | [ret Hret]].
                                   { left; exact Hlin. }
                                   { destruct Hpre as [HI _].
                                     unfold I in HI; simpl in HI.
	                                     destruct HI as [_ [Hex _]].
                                     simpl in Hret.
                                     rewrite Hex in Hret. discriminate. }
                               +++ intros Hno. contradiction.
                  -- split.
                     ++ split; intro Hnone; exact Hnone.
                     ++ split.
                        ** intros m [Hlin Hno]. split; [exact Hlin|split; [exact Hno|congruence]].
                        ** split.
                           --- intros m ret Hret. exact Hret.
                           --- split.
                               +++ intros m [Hlin | [ret Hret]]; [left | right; exists ret]; exact Hlin || exact Hret.
                               +++ intros Hno. split; [exact Hno|congruence].
	            - destruct Hpre as [HI [Hlin Hno]].
                unfold I, Active, ALin, NoExchBy in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                pupdate_start.
                pupdate_forward t2 (InvEv (push v)).
                pupdate_forward t2 (ResEv (push v) tt).
                pupdate_forward t1 (@InvEv (EStack A) (@pop A));
                  try (rewrite PositiveMap.gso by congruence;
                       rewrite PositiveMap.gso by congruence;
                       exact Hex).
                pupdate_forward t1 (@ResEv (EStack A) (@pop A) (Some v)).
                pupdate_finish.
                split.
	                + split.
	                  * split; [reflexivity|].
	                    simpl. split.
	                    -- split.
                         ++ rewrite PositiveMap.gss. reflexivity.
                         ++ rewrite PositiveMap.gso by congruence.
                            rewrite PositiveMap.gso by congruence.
                            rewrite PositiveMap.gss. reflexivity.
	                    -- congruence.
	                  * right. exists tt.
	                    unfold ALin; simpl.
                    rewrite PositiveMap.gso by congruence.
                    rewrite PositiveMap.gso by congruence.
                    rewrite PositiveMap.gss. reflexivity.
                + unfold G, R_pres, Active, Live, Done, ALin, NoExchBy.
                  split.
	                  * split; [reflexivity|].
	                    simpl. split.
	                    -- split.
                         ++ rewrite PositiveMap.gss. reflexivity.
                         ++ rewrite PositiveMap.gso by congruence.
                            rewrite PositiveMap.gso by congruence.
                            rewrite PositiveMap.gss. reflexivity.
	                    -- congruence.
                  * intros t' Hneq.
                    simpl.
                    destruct (PositiveMap.E.eq_dec t' t1) as [Heq|Hne1]; subst.
                    -- split.
                       ++ split; intro Hnone.
                          ** rewrite Hex in Hnone. discriminate.
                          ** rewrite PositiveMap.gss in Hnone. discriminate.
                       ++ split.
                          ** intros m [Hinv Hno']. contradiction.
                          ** split.
                             --- intros m ret Hret.
                                 rewrite Hex in Hret. discriminate.
                             --- split.
	                                 +++ intros m [Hinv | [ret Hret]].
	                                     { destruct m as [x|].
                                         - simpl in Hinv. rewrite Hex in Hinv. discriminate.
                                         - right. exists (Some v).
                                           simpl. rewrite PositiveMap.gss. reflexivity. }
	                                     { simpl in Hret. rewrite Hex in Hret. discriminate. }
                                 +++ intros Hno'. contradiction.
	                    -- assert (Hne2 : t' <> t2) by congruence.
                       simpl in *.
	                       split.
                       ++ split; intro Hnone.
                          ** repeat (rewrite PositiveMap.gso by congruence). exact Hnone.
                          ** repeat (rewrite PositiveMap.gso in Hnone by congruence). exact Hnone.
                       ++ split.
	                          ** intros m [Hinv Hno']. simpl in Hinv. split.
	                             --- simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hinv.
                             --- split; [exact Hno'|exact Hne2].
                          ** split.
	                             --- intros m ret Hret. simpl in Hret.
	                                 simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hret.
                             --- split.
	                                 +++ intros m [Hinv | [ret Hret]].
	                                     { simpl in Hinv. left. simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hinv. }
	                                     { simpl in Hret. right. exists ret. simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hret. }
	                                 +++ intros Hno'. split; [exact Hno'|exact Hne2].
	          }
        * intros ret.
          pupdate_intros_atomic.
	          { inversion H0; subst; clear H0.
	            pupdate_finish; split.
            + destruct Hpre as [HI Hlive].
              unfold I, Live, Done, ALin in *; simpl in *.
              destruct HI as [Hr [Hex Hdist]]. subst ρ1.
              split; [split; [reflexivity|split; auto]|].
              split; [exact Hex|auto].
            + unfold G. split.
              * destruct Hpre as [HI Hlive].
                unfold I in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                split; [reflexivity|split; auto].
              * intros t' Hneq.
	                eapply R_pres_same_π. simpl. intros Hno'. constructor.
            }
	          { inversion H0; subst; clear H0.
	            destruct v2 as [rv|].
            + pupdate_finish; split.
              * destruct Hpre as [HI Hlive].
                unfold I, Live, Done, Active, ALin, NoExchBy in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                destruct Hex as [Hcur Hother].
                split.
                -- split; [reflexivity|split; [exact Hother|exact Hdist]].
	                -- split; [exact Hcur|exact Hdist].
              * unfold G. split.
                -- destruct Hpre as [HI Hlive].
                   unfold I in *; simpl in *.
                   destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                   destruct Hex as [Hcur Hother].
                   split; [reflexivity|split; [exact Hother|exact Hdist]].
                -- intros t' Hneq.
                   eapply R_pres_same_π. simpl.
                   intros Hno'. destruct Hno' as [_ Hneq2]. exact Hneq2.
            + pupdate_finish; split.
              * destruct Hpre as [HI Hlive].
                unfold I, Live, Done, ALin, NoExchBy in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                destruct Hex as [Hcur Hother].
                split.
                -- split; [reflexivity|split; [exact Hother|exact Hdist]].
                -- split; [exact Hcur|exact Hdist].
              * unfold G. split.
                -- destruct Hpre as [HI Hlive].
                   unfold I in *; simpl in *.
                   destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                   destruct Hex as [Hcur Hother].
                   split; [reflexivity|split; [exact Hother|exact Hdist]].
                -- intros t' Hneq.
                   eapply R_pres_same_π. simpl.
                   intros Hno'. destruct Hno' as [_ Hneq2]. exact Hneq2.
            }
	          { inversion H0; subst; clear H0.
	            destruct v1 as [rv|].
            + pupdate_finish; split.
              * destruct Hpre as [HI Hlive].
                unfold I, Live, Done, Active, ALin, NoExchBy in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                split.
	                -- split; [reflexivity|split; constructor].
		                -- split; [exact Hex|simpl; auto].
              * unfold G. split.
                -- destruct Hpre as [HI Hlive].
                   unfold I in *; simpl in *.
                   destruct HI as [Hr [Hex Hdist]]. subst ρ1.
	                   split; [reflexivity|split; constructor].
                -- intros t' Hneq.
	                   eapply R_pres_same_π. simpl. intros Hno'. constructor.
            + pupdate_finish; split.
              * destruct Hpre as [HI Hlive].
                unfold I, Live, Done, ALin, NoExchBy in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                split.
	                -- split; [reflexivity|split; constructor].
	                -- split; [exact Hex|simpl; auto].
              * unfold G. split.
                -- destruct Hpre as [HI Hlive].
                   unfold I in *; simpl in *.
                   destruct HI as [Hr [Hex Hdist]]. subst ρ1.
	                   split; [reflexivity|split; constructor].
                -- intros t' Hneq.
	                   eapply R_pres_same_π. simpl. intros Hno'. constructor.
            }
        * intros [[ov|]|].
          { eapply provable_vis_safe with
              (P' := I //\\ Active t (push v))
              (Q' := fun succ =>
                match succ with
                | OK _ => I //\\ ALin t (Semantics.ls_linr (push v) tt) //\\ NoExchBy t
                | FAIL => I //\\ Active t (push v)
                end);
            try solve_conj_impl;
            try solve_conj_stable stableDB;
            try (intro succ; destruct succ; solve_conj_stable stableDB);
            try solve [apply no_error].
            + intros succ; destruct succ; solve_conj_impl.
            + pupdate_intros_atomic.
              pupdate_finish; split.
              * destruct Hpre as [HI Hact].
                unfold I in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]].
                split; [split; [exact Hr|split; [exact Hex|exact Hdist]]|exact Hact].
              * unfold G. split.
	                -- destruct Hpre as [HI Hact].
	                   unfold I in *; simpl in *.
	                   destruct HI as [Hr [Hex Hdist]].
	                   split; [exact Hr|split; [exact Hex|exact Hdist]].
	                -- intros t' Hneq. eapply R_pres_same_π. simpl. auto.
	            + intros [[]|].
	              * pupdate_intros_atomic.
                  {
	                  destruct Hpre as [HI [Hlin Hno]].
                    unfold I, Active, ALin, NoExchBy in *; simpl in *.
                    destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                    pupdate_start.
                    pupdate_forward t0 (InvEv (push v0)).
                    pupdate_forward t0 (ResEv (push v0) tt).
                    pupdate_finish.
                    split.
                    - split.
	                      + split; [reflexivity|split; [eapply exch_ok_add_add_no_exch; eauto|exact Hdist]].
                      + split.
                        * unfold ALin; simpl. rewrite PositiveMap.gss. reflexivity.
                        * exact Hno.
                    - unfold G. split.
	                      + split; [reflexivity|split; [eapply exch_ok_add_add_no_exch; eauto|exact Hdist]].
                      + intros t' Hneq.
                        eapply R_pres_add_add_other; [exact Hneq|].
                        simpl. auto.
                  }
                * pupdate_intros_atomic.
                  {
                    pupdate_finish; split.
                    - destruct Hpre as [HI Hact].
                      unfold I in *; simpl in *.
                      destruct HI as [Hr [Hex Hdist]].
                      split; [split; [exact Hr|split; [exact Hex|exact Hdist]]|exact Hact].
                    - unfold G. split.
                      + destruct Hpre as [HI Hact].
                        unfold I in *; simpl in *.
                        destruct HI as [Hr [Hex Hdist]].
                        split; [exact Hr|split; [exact Hex|exact Hdist]].
                      + intros t' Hneq. eapply R_pres_same_π. simpl. auto.
                  }
	            + intros [[]|]; eapply provable_ret_safe;
                try solve_conj_impl;
                try solve_conj_stable stableDB.
          }
          { eapply provable_ret_safe;
            try solve_conj_impl;
            try solve_conj_stable stableDB.
          }
          { eapply provable_vis_safe with
              (P' := I //\\ Active t (push v))
              (Q' := fun succ =>
                match succ with
                | OK _ => I //\\ ALin t (Semantics.ls_linr (push v) tt) //\\ NoExchBy t
                | FAIL => I //\\ Active t (push v)
                end);
            try solve_conj_impl;
            try solve_conj_stable stableDB;
            try (intro succ; destruct succ; solve_conj_stable stableDB);
            try solve [apply no_error].
            + intros succ; destruct succ; solve_conj_impl.
            + pupdate_intros_atomic.
              pupdate_finish; split.
              * destruct Hpre as [HI Hact].
                unfold I in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]].
                split; [split; [exact Hr|split; [exact Hex|exact Hdist]]|exact Hact].
              * unfold G. split.
	                -- destruct Hpre as [HI Hact].
	                   unfold I in *; simpl in *.
	                   destruct HI as [Hr [Hex Hdist]].
	                   split; [exact Hr|split; [exact Hex|exact Hdist]].
	                -- intros t' Hneq. eapply R_pres_same_π. simpl. auto.
	            + intros [[]|].
                * pupdate_intros_atomic.
                  {
                    destruct Hpre as [HI [Hlin Hno]].
                    unfold I, Active, ALin, NoExchBy in *; simpl in *.
                    destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                    pupdate_start.
                    pupdate_forward t0 (InvEv (push v0)).
                    pupdate_forward t0 (ResEv (push v0) tt).
                    pupdate_finish.
                    split.
                    - split.
                      + split; [reflexivity|split; [eapply exch_ok_add_add_no_exch; eauto|exact Hdist]].
                      + split.
                        * unfold ALin; simpl. rewrite PositiveMap.gss. reflexivity.
                        * exact Hno.
                    - unfold G. split.
                      + split; [reflexivity|split; [eapply exch_ok_add_add_no_exch; eauto|exact Hdist]].
                      + intros t' Hneq.
                        eapply R_pres_add_add_other; [exact Hneq|].
                        simpl. auto.
                  }
                * pupdate_intros_atomic.
                  {
                    pupdate_finish; split.
                    - destruct Hpre as [HI Hact].
                      unfold I in *; simpl in *.
                      destruct HI as [Hr [Hex Hdist]].
                      split; [split; [exact Hr|split; [exact Hex|exact Hdist]]|exact Hact].
                    - unfold G. split.
                      + destruct Hpre as [HI Hact].
                        unfold I in *; simpl in *.
                        destruct HI as [Hr [Hex Hdist]].
                        split; [exact Hr|split; [exact Hex|exact Hdist]].
                      + intros t' Hneq. eapply R_pres_same_π. simpl. auto.
                  }
	            + intros [[]|]; eapply provable_ret_safe;
                try solve_conj_impl;
                try solve_conj_stable stableDB.
          }
    - exists (I //\\ Active t pop).
      exists (fun ret => I //\\ ALin t (Semantics.ls_linr pop ret) //\\ NoExchBy t).
      constructor.
      + apply IGinvActive.
      + solve_conj_impl.
      + solve_conj_stable stableDB.
      + intros ret. apply IGretNoExch.
      + unfold ALin. intros ret σ0 ρ0 π0 [HI [Hlin Hno]].
        exact Hlin.
      + simpl. unfold pop_impl.
        eapply provable_doloop;
        try solve_conj_impl;
        try solve_conj_stable stableDB.
        eapply provable_vis_safe with
          (P' := I //\\ Live t pop)
          (Q' := fun other =>
            match other with
            | Some (Some x) => I //\\ ALin t (Semantics.ls_linr pop (Some x)) //\\ NoExchBy t
            | _ => I //\\ Active t pop
            end);
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        try (intro other; destruct other as [[ov|]|]; try destruct ov; solve_conj_stable stableDB);
        try solve [apply no_error].
        * intros [[ov|]|]; try destruct ov; solve_conj_impl.
        * pupdate_intros_atomic.
          {
            pupdate_finish; split.
            - destruct Hpre as [HI [Hlin Hno]].
              unfold I, Active, Live, Done, ALin, NoExchBy in *; simpl in *.
              split.
              + destruct HI as [Hr _]. split; [exact Hr|split; [exact Hlin|auto]].
              + left. exact Hlin.
            - unfold G, R_pres, Active, Live, Done, ALin, NoExchBy.
              split.
              + destruct Hpre as [HI [Hlin Hno]].
                unfold I in *; simpl in *.
                destruct HI as [Hr _]. split; [exact Hr|split; [exact Hlin|auto]].
              + intros t' Hneq; simpl.
                split.
                -- split; intro H; exact H.
                -- split.
                   ++ intros m [Hlin Hno]. split; [exact Hlin|congruence].
                   ++ split.
                      ** intros m ret Hlin. exact Hlin.
                      ** split.
                         --- intros m [Hlin | [ret Hlin]]; [left | right; exists ret]; exact Hlin.
                         --- intros _. congruence.
          }
          {
            destruct v1 as [w|].
            - destruct Hpre as [HI [Hlin Hno]].
              unfold I, Active, ALin, NoExchBy in *; simpl in *.
              destruct HI as [Hr [Hex Hdist]]. subst ρ1.
              pupdate_start.
              pupdate_forward t1 (InvEv (push w)).
              pupdate_forward t1 (ResEv (push w) tt).
              pupdate_forward t2 (@InvEv (EStack A) (@pop A));
                try (rewrite PositiveMap.gso by congruence;
                     rewrite PositiveMap.gso by congruence;
                     exact Hlin).
              pupdate_forward t2 (@ResEv (EStack A) (@pop A) (Some w)).
              pupdate_finish.
              split.
              + split.
                * split; [reflexivity|].
                  simpl. split.
                  -- split.
                     ++ rewrite PositiveMap.gso by congruence.
                        rewrite PositiveMap.gso by congruence.
                        rewrite PositiveMap.gss. reflexivity.
                     ++ rewrite PositiveMap.gss. reflexivity.
                  -- congruence.
                * right. exists (Some w).
                  unfold ALin; simpl. rewrite PositiveMap.gss. reflexivity.
              + unfold G, R_pres, Active, Live, Done, ALin, NoExchBy.
                split.
                * split; [reflexivity|].
                  simpl. split.
                  -- split.
                     ++ rewrite PositiveMap.gso by congruence.
                        rewrite PositiveMap.gso by congruence.
                        rewrite PositiveMap.gss. reflexivity.
                     ++ rewrite PositiveMap.gss. reflexivity.
                  -- congruence.
                * intros t' Hneq.
                  simpl.
                  destruct (PositiveMap.E.eq_dec t' t1) as [Heq|Hne1]; subst.
                  -- split.
                     ++ split; intro Hnone.
                        ** rewrite Hex in Hnone. discriminate.
                        ** simpl in Hnone.
                           rewrite PositiveMap.gso in Hnone by congruence.
                           rewrite PositiveMap.gso in Hnone by congruence.
                           rewrite PositiveMap.gss in Hnone. discriminate.
                     ++ split.
                        ** intros m [Hinv Hno']. contradiction.
                        ** split.
                           --- intros m ret Hret.
                               simpl in Hret. rewrite Hex in Hret. discriminate.
                           --- split.
                               +++ intros m [Hinv | [ret Hret]].
	                                   { destruct m as [x|].
	                                     - right. exists tt. simpl.
                                       simpl in Hinv. rewrite Hex in Hinv.
                                       inversion Hinv; subst.
	                                       rewrite PositiveMap.gso by congruence.
	                                       rewrite PositiveMap.gso by congruence.
	                                       rewrite PositiveMap.gss. reflexivity.
                                     - simpl in Hinv. rewrite Hex in Hinv. discriminate. }
                                   { simpl in Hret. rewrite Hex in Hret. discriminate. }
                               +++ intros Hno'. contradiction.
                  -- assert (Hne2 : t' <> t2) by congruence.
                     simpl in *.
                     split.
                     ++ split; intro Hnone.
                        ** repeat (rewrite PositiveMap.gso by congruence). exact Hnone.
                        ** repeat (rewrite PositiveMap.gso in Hnone by congruence). exact Hnone.
                     ++ split.
                        ** intros m [Hinv Hno']. simpl in Hinv. split.
                           --- simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hinv.
                           --- split; [exact Hno'|exact Hne2].
                        ** split.
                           --- intros m ret Hret. simpl in Hret.
                               simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hret.
                           --- split.
                               +++ intros m [Hinv | [ret Hret]].
                                   { simpl in Hinv. left. simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hinv. }
                                   { simpl in Hret. right. exists ret. simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hret. }
                               +++ intros Hno'. split; [exact Hno'|exact Hne2].
            - pupdate_finish; split.
              + destruct Hpre as [HI [Hlin Hno]].
                unfold I, Active, Live, Done, ALin, NoExchBy in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]].
                split; [split; [exact Hr|split; [split; [exact Hex|exact Hlin]|congruence]]|left; exact Hlin].
              + unfold G, R_pres, Active, Live, Done, ALin, NoExchBy.
                split.
                * destruct Hpre as [HI [Hlin Hno]].
                  unfold I, Active, ALin in *; simpl in *.
                  destruct HI as [Hr [Hex Hdist]].
                  split; [exact Hr|split; [split; [exact Hex|exact Hlin]|congruence]].
                * intros t' Hneq; simpl.
                  destruct (PositiveMap.E.eq_dec t' t1) as [Heq|Hne1]; subst.
                  -- split.
                     ++ split; intro Hnone.
                        ** destruct Hpre as [HI [Hlin Hno]].
                           unfold I in HI; simpl in HI.
                           destruct HI as [_ [Hex _]].
                           rewrite Hex in Hnone. discriminate.
                        ** destruct Hpre as [HI [Hlin Hno]].
                           unfold I in HI; simpl in HI.
                           destruct HI as [_ [Hex _]].
                           rewrite Hex in Hnone. discriminate.
                     ++ split.
                        ** intros m [Hlin Hno]. contradiction.
                        ** split.
                           --- intros m ret Hret.
                               destruct Hpre as [HI _].
                               unfold I in HI; simpl in HI.
                               destruct HI as [_ [Hex _]].
                               simpl in Hret. rewrite Hex in Hret. discriminate.
                           --- split.
                               +++ intros m [Hlin | [ret Hret]].
                                   { left; exact Hlin. }
                                   { destruct Hpre as [HI _].
                                     unfold I in HI; simpl in HI.
                                     destruct HI as [_ [Hex _]].
                                     simpl in Hret.
                                     rewrite Hex in Hret. discriminate. }
                               +++ intros Hno. contradiction.
                  -- split.
                     ++ split; intro Hnone; exact Hnone.
                     ++ split.
                        ** intros m [Hlin Hno]. split; [exact Hlin|split; [exact Hno|congruence]].
                        ** split.
                           --- intros m ret Hret. exact Hret.
                           --- split.
                               +++ intros m [Hlin | [ret Hret]]; [left | right; exists ret]; exact Hlin || exact Hret.
                               +++ intros Hno. split; [exact Hno|congruence].
          }
        * intros ret.
          pupdate_intros_atomic.
          {
            inversion H0; subst; clear H0.
            pupdate_finish; split.
            - destruct Hpre as [HI Hlive].
              unfold I, Live, Done, ALin in *; simpl in *.
              destruct HI as [Hr [Hex Hdist]]. subst ρ1.
              split; [split; [reflexivity|split; constructor]|].
              split; [exact Hex|simpl; auto].
            - unfold G. split.
              + destruct Hpre as [HI Hlive].
                unfold I in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                split; [reflexivity|split; constructor].
              + intros t' Hneq.
                eapply R_pres_same_π. simpl. intros Hno'. constructor.
          }
          {
            inversion H0; subst; clear H0.
            destruct v2 as [w|].
            - pupdate_finish; split.
              + destruct Hpre as [HI Hlive].
                unfold I, Live, Done, ALin, NoExchBy in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                destruct Hex as [Hcur Hother].
                split.
                * split; [reflexivity|split; [exact Hother|exact Hdist]].
                * split; [exact Hcur|exact Hdist].
              + unfold G. split.
                * destruct Hpre as [HI Hlive].
                  unfold I in *; simpl in *.
                  destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                  destruct Hex as [Hcur Hother].
                  split; [reflexivity|split; [exact Hother|exact Hdist]].
                * intros t' Hneq.
                  eapply R_pres_same_π. simpl.
                  intros Hno'. destruct Hno' as [_ Hneq2]. exact Hneq2.
            - pupdate_finish; split.
              + destruct Hpre as [HI Hlive].
                unfold I, Live, Done, Active, ALin, NoExchBy in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                destruct Hex as [Hcur Hother].
                split.
                * split; [reflexivity|split; [exact Hother|exact Hdist]].
                * split; [exact Hcur|exact Hdist].
              + unfold G. split.
                * destruct Hpre as [HI Hlive].
                  unfold I in *; simpl in *.
                  destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                  destruct Hex as [Hcur Hother].
                  split; [reflexivity|split; [exact Hother|exact Hdist]].
                * intros t' Hneq.
                  eapply R_pres_same_π. simpl.
                  intros Hno'. destruct Hno' as [_ Hneq2]. exact Hneq2.
          }
          {
            inversion H0; subst; clear H0.
            destruct v1 as [w|].
            - pupdate_finish; split.
              + destruct Hpre as [HI Hlive].
                unfold I, Live, Done, ALin, NoExchBy in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                split.
                * split; [reflexivity|split; constructor].
                * split; [exact Hex|simpl; auto].
              + unfold G. split.
                * destruct Hpre as [HI Hlive].
                  unfold I in *; simpl in *.
                  destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                  split; [reflexivity|split; constructor].
                * intros t' Hneq.
                  eapply R_pres_same_π. simpl. intros Hno'. constructor.
            - pupdate_finish; split.
              + destruct Hpre as [HI Hlive].
                unfold I, Live, Done, Active, ALin, NoExchBy in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                split.
                * split; [reflexivity|split; constructor].
                * split; [exact Hex|simpl; auto].
              + unfold G. split.
                * destruct Hpre as [HI Hlive].
                  unfold I in *; simpl in *.
                  destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                  split; [reflexivity|split; constructor].
	                * intros t' Hneq.
	                  eapply R_pres_same_π. simpl. intros Hno'. constructor.
	          }
        * intros [[ov|]|].
          { eapply provable_ret_safe;
            try solve_conj_impl;
            try solve_conj_stable stableDB.
          }
          { eapply provable_vis_safe with
              (P' := I //\\ Active t pop)
              (Q' := fun succ =>
                match succ with
                | OK v => I //\\ ALin t (Semantics.ls_linr pop v) //\\ NoExchBy t
                | FAIL => I //\\ Active t pop
                end);
            try solve_conj_impl;
            try solve_conj_stable stableDB;
            try (intro succ; destruct succ; solve_conj_stable stableDB);
            try solve [apply no_error].
            + intros succ; destruct succ; solve_conj_impl.
            + pupdate_intros_atomic.
              pupdate_finish; split.
              * destruct Hpre as [HI Hact].
                unfold I in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]].
                split; [split; [exact Hr|split; [exact Hex|exact Hdist]]|exact Hact].
              * unfold G. split.
                -- destruct Hpre as [HI Hact].
                   unfold I in *; simpl in *.
                   destruct HI as [Hr [Hex Hdist]].
                   split; [exact Hr|split; [exact Hex|exact Hdist]].
                -- intros t' Hneq. eapply R_pres_same_π. simpl. auto.
	            + intros [retv|].
	              * pupdate_intros_atomic.
                {
                  destruct Hpre as [HI [Hlin Hno]].
                  unfold I, Active, ALin, NoExchBy in *; simpl in *.
                  destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                  pupdate_start.
                  pupdate_forward t0 (@InvEv (EStack A) (@pop A)).
		                  pupdate_forward t0 (@ResEv (EStack A) (@pop A) None);
                    try rewrite PositiveMap.gss; auto.
                  pupdate_finish.
                  split.
                  - split.
                    + split; [reflexivity|split; [eapply exch_ok_add_add_no_exch; eauto|exact Hdist]].
                    + split.
                      * unfold ALin; simpl. rewrite PositiveMap.gss. reflexivity.
                      * exact Hno.
                  - unfold G. split.
                    + split; [reflexivity|split; [eapply exch_ok_add_add_no_exch; eauto|exact Hdist]].
                    + intros t' Hneq.
                      eapply R_pres_add_add_other; [exact Hneq|].
                      simpl. auto.
                }
              {
                  destruct Hpre as [HI [Hlin Hno]].
                  unfold I, Active, ALin, NoExchBy in *; simpl in *.
                  destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                  pupdate_start.
                  pupdate_forward t0 (@InvEv (EStack A) (@pop A)).
	                  pupdate_forward t0 (@ResEv (EStack A) (@pop A) (Some v));
                    try rewrite PositiveMap.gss; auto.
                  pupdate_finish.
                  split.
                  - split.
                    + split; [reflexivity|split; [eapply exch_ok_add_add_no_exch; eauto|exact Hdist]].
                    + split.
                      * unfold ALin; simpl. rewrite PositiveMap.gss. reflexivity.
                      * exact Hno.
                  - unfold G. split.
                    + split; [reflexivity|split; [eapply exch_ok_add_add_no_exch; eauto|exact Hdist]].
                    + intros t' Hneq.
                      eapply R_pres_add_add_other; [exact Hneq|].
                      simpl. auto.
	                }
	              * pupdate_intros_atomic.
                {
	                  pupdate_finish; split.
                  - destruct Hpre as [HI Hact].
                    unfold I in *; simpl in *.
                    destruct HI as [Hr [Hex Hdist]].
                    split; [split; [exact Hr|split; [exact Hex|exact Hdist]]|exact Hact].
                  - unfold G. split.
                    + destruct Hpre as [HI Hact].
                      unfold I in *; simpl in *.
                      destruct HI as [Hr [Hex Hdist]].
                      split; [exact Hr|split; [exact Hex|exact Hdist]].
                    + intros t' Hneq. eapply R_pres_same_π. simpl. auto.
                }
            + intros [retv|]; eapply provable_ret_safe;
              try solve_conj_impl;
              try solve_conj_stable stableDB.
          }
          { eapply provable_vis_safe with
              (P' := I //\\ Active t pop)
              (Q' := fun succ =>
                match succ with
                | OK v => I //\\ ALin t (Semantics.ls_linr pop v) //\\ NoExchBy t
                | FAIL => I //\\ Active t pop
                end);
            try solve_conj_impl;
            try solve_conj_stable stableDB;
            try (intro succ; destruct succ; solve_conj_stable stableDB);
            try solve [apply no_error].
            + intros succ; destruct succ; solve_conj_impl.
            + pupdate_intros_atomic.
              pupdate_finish; split.
              * destruct Hpre as [HI Hact].
                unfold I in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]].
                split; [split; [exact Hr|split; [exact Hex|exact Hdist]]|exact Hact].
              * unfold G. split.
                -- destruct Hpre as [HI Hact].
                   unfold I in *; simpl in *.
                   destruct HI as [Hr [Hex Hdist]].
                   split; [exact Hr|split; [exact Hex|exact Hdist]].
                -- intros t' Hneq. eapply R_pres_same_π. simpl. auto.
            + intros [retv|].
              * pupdate_intros_atomic.
                {
                  destruct Hpre as [HI [Hlin Hno]].
                  unfold I, Active, ALin, NoExchBy in *; simpl in *.
                  destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                  pupdate_start.
                  pupdate_forward t0 (@InvEv (EStack A) (@pop A)).
	                  pupdate_forward t0 (@ResEv (EStack A) (@pop A) None);
                    try rewrite PositiveMap.gss; auto.
                  pupdate_finish.
                  split.
                  - split.
                    + split; [reflexivity|split; [eapply exch_ok_add_add_no_exch; eauto|exact Hdist]].
                    + split.
                      * unfold ALin; simpl. rewrite PositiveMap.gss. reflexivity.
                      * exact Hno.
                  - unfold G. split.
                    + split; [reflexivity|split; [eapply exch_ok_add_add_no_exch; eauto|exact Hdist]].
                    + intros t' Hneq.
                      eapply R_pres_add_add_other; [exact Hneq|].
                      simpl. auto.
	                }
	              {
	                  destruct Hpre as [HI [Hlin Hno]].
                  unfold I, Active, ALin, NoExchBy in *; simpl in *.
                  destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                  pupdate_start.
                  pupdate_forward t0 (@InvEv (EStack A) (@pop A)).
	                  pupdate_forward t0 (@ResEv (EStack A) (@pop A) (Some v));
                    try rewrite PositiveMap.gss; auto.
                  pupdate_finish.
                  split.
                  - split.
                    + split; [reflexivity|split; [eapply exch_ok_add_add_no_exch; eauto|exact Hdist]].
                    + split.
                      * unfold ALin; simpl. rewrite PositiveMap.gss. reflexivity.
                      * exact Hno.
                  - unfold G. split.
                    + split; [reflexivity|split; [eapply exch_ok_add_add_no_exch; eauto|exact Hdist]].
                    + intros t' Hneq.
                      eapply R_pres_add_add_other; [exact Hneq|].
                      simpl. auto.
                }
              * pupdate_intros_atomic.
                {
                  pupdate_finish; split.
                  - destruct Hpre as [HI Hact].
                    unfold I in *; simpl in *.
                    destruct HI as [Hr [Hex Hdist]].
                    split; [split; [exact Hr|split; [exact Hex|exact Hdist]]|exact Hact].
                  - unfold G. split.
                    + destruct Hpre as [HI Hact].
                      unfold I in *; simpl in *.
                      destruct HI as [Hr [Hex Hdist]].
                      split; [exact Hr|split; [exact Hex|exact Hdist]].
                    + intros t' Hneq. eapply R_pres_same_π. simpl. auto.
                }
            + intros [retv|]; eapply provable_ret_safe;
              try solve_conj_impl;
              try solve_conj_stable stableDB.
          }
    - unfold I. simpl. split; [reflexivity|split; constructor].
  Defined.
  End Impl.
End EBStackImpl.
