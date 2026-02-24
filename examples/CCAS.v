Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import PeanoNat.
Require Import Classical.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulationSet.
Require Import RGILogicSet.
Require Import Specs.
Require Import SeparationAlgebra.

Class HasBeq (t : Type) := {
  beq : t -> t -> bool;
  beq_refl : forall x, beq x x = true;
  beq_true : forall x y, beq x y = true -> x = y;
  beq_false : forall x y, beq x y = false -> x <> y;
}.

Module CASTaskImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.
  Import AssertionsSet.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS CAS'Spec FAISpec CASTaskSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.
  Open Scope prog_scope.
  Open Scope rg_relation_scope.

  Context (Val : Type).
  Context (vInit : Val).

  Definition E : layer_interface :=
  {|
    li_sig := Sig.Plus.omap (ECAS' ((CASTask Val) + Val)) EFAI;
    li_lts := tens_lts VCAS' VFAI;
    li_init := pair (Idle (inr vInit)) (Idle O);
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := ECASTask Val;
    li_lts := VCASTask;
    li_init := Idle (cts (inr vInit) O nil);
  |}.

  Definition allocTask_impl (_ : tid) : Prog (li_sig E) nat :=
    inr fai >= i => Ret i.
  
  Definition tryPlaceTask_impl o n i (cid : tid) : Prog (li_sig E) ((CASTask Val) + Val) :=
    inl (cas (inr o) (inl (CTask cid o n i))) >= r => Ret r.
  
  Definition tryResolveTask_impl tsk v (_ : tid) : Prog (li_sig E) unit :=
    inl (cas (inl tsk) (inr v)) >= _ => Ret tt.
End CASTaskImpl.


Module CCASImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.
  Import AssertionsSet.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS Reg'Spec CASTaskSpec CCASSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.
  Open Scope prog_scope.
  Open Scope rg_relation_scope.

  Context (Val : Type).
  Context (vInit : Val).
  Context `{HasBeq Val}.

  Definition E : layer_interface :=
  {|
    li_sig := Sig.Plus.omap (ECASTask Val) (EReg bool);
    li_lts := tens_lts VCASTask VReg;
    li_init := pair (Idle (cts (inr vInit) O nil)) (Idle true);
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := ECCAS Val;
    li_lts := VCCAS;
    li_init := Idle (pair vInit false);
  |}.

  Definition assertion := @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.

  Definition ALinEx t ls : assertion := fun s => exists ρ π, Δ s ρ π /\ TMap.find t π = ls.
  Definition ALinIdle t : assertion := ALinEx t None.

  Definition Flag b : assertion := fun s => state (snd (σ s)) = b.
  Definition Expired i : assertion := fun s => List.In i (expired (state (fst (σ s)))).
  Definition CurrentTask t o n i : assertion := fun s => (current (state (fst (σ s)))) = inl (CTask t o n i).
  Definition CurrentVal v : assertion := fun s => (current (state (fst (σ s)))) = inr v.
  
  Definition castask_val (c : @CASTaskState Val) : Val :=
    match (current c) with
    | inl (CTask _ o _ _) => o
    | inr v => v
    end.

  Definition I_val : assertion :=
    fun s => 
      forall v, CurrentVal v s ->
      forall ρ π, Δ s ρ π -> fst (state ρ) = v.

  Definition NotDone t o n : assertion :=
    fun s =>
      exists ρ π, Δ s ρ π /\
      TMap.find t π = Some (ls_inv (cas o n)) /\
      fst (state ρ) = o.

  Definition I_task : assertion :=
    ∀ t o n i , CurrentTask t o n i ==>>
      (
        !! Expired i //\\
        !! ALinIdle t //\\
        NotDone t o n
      ).
  
  Definition I_flag : assertion :=
    fun s => forall ρ π, Δ s ρ π ->
      snd (state ρ) = state (snd (σ s)).

  Definition I_ρ_atomic : assertion :=
    fun s => forall ρ π, Δ s ρ π ->
      exists s, ρ = Idle s.

  Definition ticket_not_expired : assertion :=
    fun s => forall t, (ticket (state (fst (σ s)))) <= t ->
      ~ List.In t (expired (state (fst (σ s)))).

  Definition I : assertion :=
    I_ρ_atomic //\\ I_flag //\\
    I_val //\\ I_task //\\
    ticket_not_expired.


  Definition G_trylin : rg_relation :=
    fun s1 s2 => exists t o n i,
      CurrentTask t o n i s1 /\
      CurrentTask t o n i s2 /\
      (* non-decr when there is task *)
      (Δ s1 ⊆ Δ s2)%AbstractConfig.

  Definition G_resolve : rg_relation :=
    fun s1 s2 => exists t o n i,
      CurrentTask t o n i s1 /\
      Expired i s2 /\
      (* resolve to single poss with linr *)
      exists ρ π,
        (Δ s2 ≡ [( ρ, π )])%AbstractConfig /\
        ([( ρ, π )] ⊆ Δ s1)%AbstractConfig /\
        TMap.find t π = Some (ls_linr (cas o n) o).

  Definition G_id : rg_relation :=
    fun s1 s2 =>
      state (fst (σ s1)) = state (fst (σ s2)) /\
      state (snd (σ s1)) = state (snd (σ s2)) /\
      Δ s1 ≡ Δ s2.

  Definition G_task t : rg_relation :=
    fun s1 s2 => exists o n i,
      CurrentVal o s1 /\
      CurrentTask t o n i s2 /\
      Δ s1 ≡ Δ s2.

  Definition G t : rg_relation :=
    G_id ∪ G_task t ∪ G_trylin ∪ G_resolve.

  (* only the owner can place the task *)
  Definition R_task t : rg_relation :=
    fun s1 s2 => exists t' o n i,
      t <> t' /\
      CurrentVal o s1 /\
      CurrentTask t' o n i s2 /\
      Δ s1 ≡ Δ s2.

  Definition R_id t : rg_relation :=
    fun s1 s2 => 
      state (fst (σ s1)) = state (fst (σ s2)) /\
      state (snd (σ s1)) = state (snd (σ s2)) /\
      forall ls, ALinEx t ls s1 <-> ALinEx t ls s2.

  Definition R t : rg_relation :=
    R_id t ∪ R_task t ∪ G_trylin ∪ G_resolve.

  Lemma RG_compatible : forall t1 t2, t1 <> t2 -> (G t1 ⊆ R t2).
  Proof.
    intros. intros s1 s2 ?.
    destruct H1 as [[[? | ?] | ?] | ?].
    - do 3 left.
      destruct H1 as [? [? ?]].
      unfold R_id, ALinEx, ALinIdle; intros.
      do 2 (split; auto).
      split; intros [ρ [π [? ?]]];
      apply H3 in H4; eauto.
    - do 2 left; right.
      destruct H1 as (o & n & i & [? ?]).
      do 4 eexists; split; eauto.
    - left; right. auto.
    - right. auto.
  Qed.

  Lemma R_domexact : forall t0 s1 s2, R t0 s1 s2 -> I s2 ->
    (forall (ρ1 : State (li_lts F)) (π1 : tmap LinState), Δ s1 ρ1 π1 -> TMap.find t0 π1 = None) <->
    (forall (ρ2 : State (li_lts F)) (π2 : tmap LinState), Δ s2 ρ2 π2 -> TMap.find t0 π2 = None).
  Proof.
    destruct 1 as [[[? | ?] | ?] | ?]; intros.
    - destruct H0 as [_ [_ ?]].
      split; intros.
      + pose proof ac_nonempty (Δ s1) as [ρ1 [π1 ?]].
        specialize (H2 _ _ H4).
        assert (ALinEx t0 None s1); unfold ALinEx; eauto.
        apply H0 in H5 as [? [? [? ?]]].
        eapply ac_domexact; eauto.
      + pose proof ac_nonempty (Δ s2) as [ρ2 [π2 ?]].
        specialize (H2 _ _ H4).
        assert (ALinEx t0 None s2); unfold ALinEx; eauto.
        apply H0 in H5 as [? [? [? ?]]].
        eapply ac_domexact; eauto.
    - destruct H0 as (t & o & n & i & [_ [_ [_ ?]]]).
      split; intros; apply H0 in H3; eapply H2; eauto.
    - destruct H0 as (t & o & n & i & _ & _ & ?).
      split; intros.
      + epose proof ac_nonempty (Δ s1) as [ρ1 [π1 ?]].
        pose proof (H0 _ _ H4).
        apply H2 in H4.
        eapply ac_domexact; eauto.
      + apply H0 in H3.
        apply H2 in H3; auto.
    - destruct H0 as (t & o & n & i & _ & _ & [ρ [π [? [? ?]]]]).
      split; intros.
      + epose proof ACSingle.
        apply H2, H4 in H6.
        apply H0 in H5.
        inversion H5; subst; auto.
      + do 2 epose proof ACSingle.
        apply H2 in H6.
        apply H0, H4 in H7.
        eapply ac_domexact; eauto.
  Qed.  
  
  (*
  
  I :=
      (* current ticket not expired *)
      ~ In ticket expired //\\
      (* current task not expired *)
      (* so that we can easily deduce that the complete method always fail if the task is expired *)
      forall i, In i expire -> current <> CTask _ _ _ i

      //\\

      (* idle thread should not have pending task *)
      ALinIdle t -> current <> CTask t _ _ _

  *)
  

  (* 
    G_trylin  : current' = CTask t _ _ _ /\ forall π ∈ Δ, π ∈ Δ'
    G_resolve : current = CTask t o _ i /\ expired'(i)
  *)

  (* cid_not_idle := (cid = t //\\ ~ ALinIdle t) \\// cid <> t *)

  Definition complete t o n i : Prog (li_sig E) unit :=
    (*
      cid_not_idle //\\
      task_placed t o n i
    *)
    inr Reg'Spec.get >= b =>
    (*
      cid_not_idle //\\
      ((expired(i) //\\ (ALinIdle t \\// ALin t linr o)) \\//
        (current = CTask t o n i //\\ (exists π ∈ Δ, π ⊨ ALin t linr o)))
    *)
    inl (tryResolveTask (CTask t o n i)
                        (match b with
                          | true => n
                          | false => o end)) >= _ =>
    (* (cid = t //\\ ALin t linr o) \\// cid <> t *)
    Ret tt.
  

  (* task_placed t o n i :=
        cid_not_idle //\\
        ((expired(i) //\\ (ALinIdle t \\// ALin t linr o)) \\//
        (current = CTask t o n i //\\ (exists π ∈ Δ, π ⊨ ALin t inv)))
  *)

  Definition ccas_impl o n (cid : tid) : Prog (li_sig E) Val :=
    (* I:= ... //\\ ALin t None -> current <> CTask t _ _ _ //\\ ... *)
    (* 
      ALin t inv //\\ current <> CTask t _ _ _
    *)
    inl (allocTask o n) >= i =>
    (* ILoop :=
      ALin t inv //\\ 
      (* stable because current <> CTask t _ _ i *)
      ~ expired(i) //\\
      (* stable because only t can set current to CTask t _ _ _ *)
      current <> CTask t _ _ i
    *)
    Do {
      inl (tryPlaceTask o n i) >= r =>
      (* 
        (* other task *)
        (ILoop //\\
          r <> o //\\ r = task t' o' n' i' //\\ task_placed t' o' n' i' //\\ t' <> t)
        (* the following cases will break the loop *)
        (* failed *)
        (r <> o //\\ isVal r //\\ alin t (linr ccas r))
        (* my task *)
        (r = o //\\ task_placed t o n i //\\ ~ ALinIdle t)
      *)
      match r with
      (*
        (ILoop //\\
          r <> o //\\ r = task t' o' n' i' //\\ task_placed t' o' n' i')
      *)
      | inl (CTask t o n i) =>
          (complete t o n i) ;;
          (* ILoop *)
          Ret r
      (* 
        (* failed *)
        (r <> o //\\ isVal r //\\ Alin t (linr ccas r))
        (* my task *)
        (r = o //\\ task_placed t o n //\\ ~ ALinIdle t)
      *)
      | _ => Ret r
      end
    } Loop >= r =>
    (if beq r o then
      (*
        r = o //\\ task_placed t o n //\\ ~ ALinIdle t
      *)
      complete cid o n i
      (*
        ALin t linr r
      *)
    else
      (*
        Alin t (linr ccas r)
      *)
      Ret tt) ;;
    Ret r.

  Definition setFlag_impl b (_ : tid) : Prog (li_sig E) unit :=
    inr (set b) >= _ => Ret tt.

  Program Definition MCCAS : layer_implementation E F := {|
    li_impl m :=
      match m with
    | setFlag b => setFlag_impl b
    | cas o n => ccas_impl o n
      end
  |}.
  Next Obligation.
    eapply RGILogic.soundness with (R:=R) (G:=G) (I:=I).
    (* valid RG *)
    {
      constructor.
      apply R_domexact.
    }
    {
      intros. intros s1 s2 [? | ?]; [eapply RG_compatible; eauto |].
      destruct H1 as [[? | ?] | ?].
      - do 3 left.
        unfold GINV, Ginv, LiftRelation_Δ in *.
        destruct H1 as [? [? [? ?]]].
        unfold R_id. rewrite H1.
        do 2 (split; auto).
        intros. unfold ALinEx.
    }




(* ************ Outdate ************* *)

  Definition ccas_impl o n (cid : tid) : Prog (li_sig E) Val :=
    inl (allocTask o n) >= i =>
    Do {
      (*
        I //\\ alin t (inv ccas) 
        (* my ticket is not expired *)
        (* other wise it breaks the invariant *)
        //\\ ~ In i expired
      *)
      inl (tryPlaceTask o n i) >= r =>
      (* I //\\ 
            (* failed *)
            (r <> o //\\ isVal r //\\ alin t (linr ccas r))
            (* other task *)
            (r <> o //\\ alin t (inv ccas) //\\ r = task t' o' n' i' //\\ 
                (task_placed t' o' n' i' \\// task_resolved t t' o' n' i'))
            (* my task *)
            (r = o //\\ task_placed t o n i)
      *)
      match r with
      (* I //\\
            (r <> o //\\ alin t (inv ccas) //\\ r = task t' o' n' i' //\\ 
                (task_placed t' o' n' i' \\// task_resolved t t' o' n' i'))
      *)
      | inl (CTask t o n i) =>
          (complete t o n i) ;;
          (* I //\\ r = task t' o' n' i' //\\ alin t (inv ccas) *)
          Ret r
      (* I //\\ 
            (* failed *)
            (r <> o //\\ isVal r //\\ alin t (linr ccas r))
            (* my task *)
            (r = o //\\ task_placed t o n)
      *)
      | _ => Ret r
      end
    } Loop >= r =>
    (if beq r o then
      (* I //\\ 
            (r = o //\\ task_placed t o n)
      *)
      complete cid o n i
      (* I //\\ 
            (r = o //\\ alin t (linr ccas r))
      *)
    else
      (* I //\\
            (r <> o //\\ isVal r //\\ alin t (linr ccas r))
      *)
      Ret tt) ;;
    Ret r.
  
  Definition setFlag_impl b (_ : tid) : Prog (li_sig E) unit :=
    inr (set b) >= _ => Ret tt.

  Instance PSS_Join_equiv : Join (@ProofState _ _ (li_lts E) (li_lts F)) :=
    (@PSS_Join _ _ _ _ equiv_Join equiv_Join).

  (* Task placed but not executed *)
  Definition notDone t (o n : Val) : assertion :=
    ALin' t (ls_inv (cas o n)) * (∃ b, (@Aρ _ _ _ (li_lts F) (Idle (pair o b)))).
  
  (* Task executed and succeeded *)
  Definition endSucc t o n : assertion :=
    ALin' t (ls_linr (cas o n) o) * (∃ b, @Aρ _ _ _ (li_lts F) (Idle (pair n b))).

  (* Task executed but failed *)
  Definition endFail t o n : assertion :=
    ALin' t (ls_linr (cas o n) o) * (∃ b, @Aρ _ _ _ (li_lts F) (Idle (pair o b))).

  Definition trySucc t o n : assertion :=
    notDone t o n ⨁ endSucc t o n.
  Definition tryFail t o n : assertion :=
    notDone t o n ⨁ endFail t o n.
  Definition tryBoth t o n : assertion :=
    notDone t o n ⨁ endSucc t o n ⨁ endFail t o n.

  Definition ACAS P : assertion := fun s => P (fst (σ s)).
  Notation "'cas' ↦ v" :=
    (ACAS (fun c => state c = v))
    (at level 30, no associativity).
  
  Definition CTask t o n : assertion :=
    cas ↦ inl (task t o n) //\\
    (notDone t o n \\// trySucc t o n \\// tryFail t o n \\// tryBoth t o n).
  Definition CVal : assertion :=
    ∃ v : Val, cas ↦ inr v //\\ ∃ b, @Aρ _ _ _ (li_lts F) (Idle (pair v b)).
  
  Definition ICAS : assertion :=
    CVal \\// ∃ t, ∃ o, ∃ n, CTask t o n.

  Definition AFlag P : assertion := fun s => P (snd (σ s)).
  Notation "'flag' ↦ v" :=
    (AFlag (fun b => state b = v))
    (at level 30, no associativity).
  
  Definition IFlag : assertion :=
    ∃ b, flag ↦ b //\\ (fun s => forall ρ π, Δ s ρ π -> snd (state ρ) = b).
    (* FIXME: the assertion below cannot handle the case with multiple possibilities *)
    (* separation of v and b is necessary *)
    (* ∃ v, @Aρ _ _ _ (li_lts F) (Idle (pair v b)). *)

  (* MARK: for the sake of simplicity, use race-free register *)
  (* Definition IRacy : assertion :=
    ∀ t, ∀ b', ∀ s, AFlag (fun b => b = Pending s t (set b'))
      ==>> (ALin' t (ls_inv (setFlag b'))). *)

  Definition I : assertion := Inv.

    (fun s => state (σ s) )
            ((state (σ s) = None /\
              exists ρt ρf, (Aρ ρt ⊕ Aρ ρf) s /\ state ρt = true /\ state ρf = false)
            \/ (exists b, state (σ s) = Some b /\
              exists ρ, Aρ ρ s /\ state ρ = b))
        /\  (forall v t w, σ s = Pending v t (set w) ->
              exists b : bool, @Aρ _ _ _ (li_lts F) (Pending b t flip) s)
        /\  ((forall v w t, σ s <> Pending v t (set w)) -> exists b, @Aρ _ _ _ (li_lts F) (Idle b) s).
    
  
  (* Definition I : assertion :=
    fun s =>
            (* state correspondence *)
            ((state (σ s) = None /\ forall b, exists ρ π, Δ s ρ π /\ state ρ = b) \/
            (exists b, state (σ s) = Some b /\ exists ρ π, Δ s ρ π /\ state ρ = b))
            (* racy set implies racy flip *)
        /\  (forall v t w, σ s = Pending v t (set w) ->
              exists ρ π, Δ s ρ π /\ exists b, ρ = Pending b t flip)
        /\  ((forall v w t, σ s <> Pending v t (set w)) -> forall ρ π, Δ s ρ π -> exists b, ρ = Idle b)
        . *)
  
  Lemma idle_not_pending : forall (u v w : option bool) t, Idle u <> Pending v t (set w).
  Proof. inversion 1. Qed.

  Definition π_independent (P : assertion) := forall s1 s2,
    σ s1 = σ s2 ->
    (forall ρ1 π1, Δ s1 ρ1 π1 -> exists ρ2 π2, Δ s2 ρ2 π2 /\ ρ1 = ρ2) ->
    (forall ρ2 π2, Δ s2 ρ2 π2 -> exists ρ1 π1, Δ s1 ρ1 π1 /\ ρ1 = ρ2) ->
    P s1 -> P s2.

  (* Lemma I_π_independent: π_independent I.
  Proof.
    unfold π_independent; intros.
    unfold I in *. rewrite H in *.
    destruct H2 as [? ?].
    split; [|split].
    - destruct H2.
      + left.
        destruct H2.
        split; auto.
        intros. specialize (H4 b) as [? [? [? ?]]].
        specialize (H0 _ _ H4) as [? [? [? ?]]]; subst.
        eauto.
      + right.
        destruct H2 as [b [? [? [? [? ?]]]]].
        specialize (H0 _ _ H4) as [? [? [? ?]]]; subst.
        eexists; eauto.
    - intros.
      eapply H3 in H4 as [? [? [? ?]]].
      specialize (H0 _ _ H4) as [? [? [? ?]]]; subst.
      eauto.
    - destruct H3. intros.
      apply H1 in H6 as [? [? [? ?]]]; subst.
      eapply H4; eauto.
  Qed. *)
  

  Definition domexact_G t : rg_relation := 
    fun s1 s2 => forall t', t <> t' ->
        forall ρ1 π1 ρ2 π2, Δ s1 ρ1 π1 -> Δ s2 ρ2 π2 -> TMap.find t' π1 = None <-> TMap.find t' π2 = None.
  
  Definition domexact_R t : rg_relation :=
    fun s1 s2 =>
      forall ρ1 π1 ρ2 π2, Δ s1 ρ1 π1 -> Δ s2 ρ2 π2 -> TMap.find t π1 = None <-> TMap.find t π2 = None.
  
  Lemma domexact_RG_compatible : forall t1 t2, t1 <> t2 -> (domexact_G t1 ⊆ domexact_R t2)%RGRelation.
  Proof.
    intros. intros ? ?.
    unfold domexact_R, domexact_G.
    intros. eapply H0; eauto.
  Qed.

  Lemma GINV_domexact : forall t1 t2, t1 <> t2 -> (GINV t1 ⊆ domexact_R t2)%RGRelation.
  Proof.
    intros. intros ? ?.
    unfold domexact_R, GINV, Ginv, LiftRelation_Δ.
    intros.
    destruct H0 as [? [? [? ?]]].
    apply H4 in H2.
    inversion H2; subst.
    rewrite PositiveMap.gso; auto.
    eapply (ac_domexact (Δ x)); eauto.
  Qed.

  Lemma GRET_domexact : forall t1 t2, t1 <> t2 -> (GRET t1 ⊆ domexact_R t2)%RGRelation.
  Proof.
    intros. intros ? ?.
    unfold domexact_R, GRET, Gret, LiftRelation_Δ.
    intros.
    destruct H0 as [? [? [? [? ?]]]].
    apply H4 in H2.
    inversion H2; subst.
    rewrite PositiveMap.gro; auto.
    eapply (ac_domexact (Δ x)); eauto.
  Qed.

  Lemma domexact_R_refl : forall t s, domexact_R t s s.
  Proof.
    intros. intros ? ?.
    unfold domexact_R, GId.
    intros; subst.
    eapply (ac_domexact (Δ s)); eauto.
  Qed.

  Definition G t : rg_relation := domexact_G t ∩
    fun s1 s2 => forall t' ls, t <> t' -> ALin t' ls s1 -> ALin t' ls s2.

  Definition R t : rg_relation := domexact_R t ∩
    fun s1 s2 => forall ls, ALin t ls s1 -> ALin t ls s2.

  Lemma Istable {t} : Stable (R t) I I.
  Proof. unfold Stable. apply ConjRightImpl, ImplRefl. Qed.

  Lemma ALinstable {t ls}: Stable (R t) I (ALin t ls).
  Proof.
    unfold Stable, R.
    intros ? [[? [? [? ?]]] ?] ? ? ?.
    apply H1 in H. apply H in H3. auto.
  Qed.

  Lemma ALin'stable {t ls}: Stable (R t) I (ALin' t ls).
  Proof.
    unfold Stable, R.
    intros ? [[? [? [? ?]]] ?] ? ? ?.
    apply H1 in H. apply H in H3. auto.
  Qed.

  Create HintDb stableDB.
  Hint Resolve Istable ALinstable : stableDB.



End CCASImpl.

Print Assumptions OneShotLazyCoinImpl.Mcoin.