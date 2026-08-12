Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.

Require Import models.EffectSignatures.
Require Import models.LinCCAL.
Require Import models.logics.Logics.
Require Import models.logics.SeparationAlgebra.
Require Import models.simlin.LTS.
Require Import models.simlin.Lang.
Require Import models.simlin.Semantics.
Require Import models.simlin.Assertion.
Require Import models.simlin.TensorSeparation.
Require Import models.simlin.TPSimulation.
Require Import examples.Common.AtomicLTS.
Require Import examples.Stacks.StackSpec.
Require Import examples.Exchanger.ExchangerSpec.

(** A self-contained separation-logic presentation of EBStack.  The
    try-stack and exchanger components are owned separately, and the
    linearization map is an ordinary disjoint-map resource. *)
Module EBStackSep.
  Import Reg LinCCALBase LTSSpec Semantics TPSimulation.
  Import Lang AtomicLTS TryStackSpec ExchSpec StackSpec.
  Import AssertionsSingle.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.

  Open Scope prog_scope.
  Open Scope assertion_scope.

  Section Proof.
    Context {A : Type}.

    Definition ETryStackLayer : layer_interface :=
    {| li_sig := ETryStack A; li_lts := VTryStack; li_init := Idle nil |}.

    Definition EExchangerLayer : layer_interface :=
    {| li_sig := EExch (option A); li_lts := VExch; li_init := ExSIdle |}.

    Definition E : layer_interface := ETryStackLayer ⊗ₗ EExchangerLayer.

    Definition F : layer_interface :=
    {| li_sig := EStack A; li_lts := VStack; li_init := Idle nil |}.

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

    Definition assertion :=
      @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).
    Definition lin_state := @LinState (li_sig F).

    (** Exclusive ownership with a distinguished empty state. *)
    Inductive pointed_join {X : Type} (empty : X) : X -> X -> X -> Prop :=
    | pj_owned x : pointed_join empty x empty x
    | pj_frame x : pointed_join empty empty x x.

    Arguments pj_owned {X empty} x.
    Arguments pj_frame {X empty} x.

    Definition pointed_Join {X : Type} (empty : X) : Join X :=
      pointed_join empty.

    Lemma pointed_join_comm {X} (empty : X) x y z :
      pointed_join empty x y z -> pointed_join empty y x z.
    Proof. inversion 1; subst; constructor. Qed.

    Lemma pointed_join_assoc {X} (empty : X) mx my mz mxy mxyz :
      pointed_join empty mx my mxy ->
      pointed_join empty mxy mz mxyz ->
      exists myz,
        pointed_join empty my mz myz /\
        pointed_join empty mx myz mxyz.
    Proof.
      intros Hxy Hyz. inversion Hxy; subst; inversion Hyz; subst;
        eexists; split; constructor.
    Qed.

    Definition pointed_SA {X : Type} (empty : X) :
      @SeparationAlgebra X (pointed_Join empty).
    Proof.
      constructor.
      - exact (pointed_join_comm empty).
      - exact (pointed_join_assoc empty).
    Defined.

    Program Definition pointed_unit {X : Type} (empty : X) :
      @SeparationAlgebraUnit X (pointed_Join empty) (pointed_SA empty) :=
      {| ue := empty |}.
    Next Obligation. constructor. Qed.
    Next Obligation. intros n n' Hj. inversion Hj; reflexivity. Qed.

    Definition try_empty : State (@TryStackSpec.VTryStack A) := Idle nil.
    Definition exch_empty : State (@ExchSpec.VExch (option A)) := ExSIdle.
    Definition stack_empty : State (@StackSpec.VStack A) := Idle nil.

    Definition try_Join : Join (State (@TryStackSpec.VTryStack A)) :=
      pointed_Join try_empty.
    Definition try_SA : @SeparationAlgebra _ try_Join :=
      pointed_SA try_empty.
    Definition try_unit : @SeparationAlgebraUnit _ try_Join try_SA :=
      pointed_unit try_empty.

    Definition exch_Join : Join (State (@ExchSpec.VExch (option A))) :=
      pointed_Join exch_empty.
    Definition exch_SA : @SeparationAlgebra _ exch_Join :=
      pointed_SA exch_empty.
    Definition exch_unit : @SeparationAlgebraUnit _ exch_Join exch_SA :=
      pointed_unit exch_empty.

    Definition stack_Join : Join (State (@StackSpec.VStack A)) :=
      pointed_Join stack_empty.
    Definition stack_SA : @SeparationAlgebra _ stack_Join :=
      pointed_SA stack_empty.
    Definition stack_unit : @SeparationAlgebraUnit _ stack_Join stack_SA :=
      pointed_unit stack_empty.

    Definition underlay_Join : Join (State (li_lts E)) :=
      @prod_Join _ _ try_Join exch_Join.
    Definition underlay_SA : @SeparationAlgebra _ underlay_Join :=
      @prod_SA _ _ try_Join exch_Join try_SA exch_SA.
    Definition underlay_unit :
      @SeparationAlgebraUnit _ underlay_Join underlay_SA :=
      @prod_unit _ _ try_Join exch_Join try_SA exch_SA try_unit exch_unit.

    Definition proof_Join : Join (@ProofState _ _ (li_lts E) (li_lts F)) :=
      fun s1 s2 s =>
        @join _ underlay_Join (σ s1) (σ s2) (σ s) /\
        @join _ stack_Join (ρ s1) (ρ s2) (ρ s) /\
        @join _ tmap_Join (π s1) (π s2) (π s).

    Definition proof_SA : @SeparationAlgebra _ proof_Join.
    Proof.
      constructor.
      - intros x y z [Hσ [Hρ Hπ]].
        split.
        + exact (@join_comm _ underlay_Join underlay_SA _ _ _ Hσ).
        + split.
          * exact (@join_comm _ stack_Join stack_SA _ _ _ Hρ).
          * exact (@join_comm _ tmap_Join tmap_SA _ _ _ Hπ).
      - intros mx my mz mxy mxyz [Hσxy [Hρxy Hπxy]]
          [Hσxyz [Hρxyz Hπxyz]].
        destruct (@join_assoc _ underlay_Join underlay_SA
          _ _ _ _ _ Hσxy Hσxyz)
          as [uσ [Huσ Hσ]].
        destruct (@join_assoc _ stack_Join stack_SA
          _ _ _ _ _ Hρxy Hρxyz)
          as [uρ [Huρ Hρ]].
        destruct (@join_assoc _ _ tmap_SA _ _ _ _ _ Hπxy Hπxyz)
          as [uπ [Huπ Hπ]].
        exists (uσ, uρ, uπ). split; unfold proof_Join; simpl.
        + exact (conj Huσ (conj Huρ Huπ)).
        + exact (conj Hσ (conj Hρ Hπ)).
    Defined.

    Definition proof_unit :
      @SeparationAlgebraUnit _ proof_Join proof_SA.
    Proof.
      refine {| ue :=
        (@ue _ underlay_Join underlay_SA underlay_unit,
         @ue _ stack_Join stack_SA stack_unit,
         @ue _ tmap_Join tmap_SA tmap_unit) |}.
      - intros [us or lm]. repeat split; apply unit_join.
      - intros [us or lm] [us' or' lm'] [Hus [Hor Hlm]].
        simpl in *.
        pose proof (@unit_spec _ underlay_Join underlay_SA underlay_unit
          _ _ Hus) as Eus.
        pose proof (@unit_spec _ stack_Join stack_SA stack_unit
          _ _ Hor) as Eor.
        pose proof (@unit_spec _ tmap_Join tmap_SA tmap_unit
          _ _ Hlm) as Elm.
        subst. reflexivity.
    Defined.

    Local Existing Instance proof_Join.
    Local Existing Instance proof_SA.
    Local Existing Instance proof_unit.

    (** Concrete component ownership.  Each assertion owns one underlay
        component, the unit of the other component, and its indicated
        overlay/linearization resources. *)
    Definition TryOwn
        (ts : State (@TryStackSpec.VTryStack A)) : assertion :=
      fun s =>
        σ s = pair ts exch_empty /\
        ρ s = Idle (state ts) /\
        π s = @TMap.empty lin_state.

    Definition ExchOwn
        (xs : @EExchState (option A))
        (lm : tmap lin_state) : assertion :=
      fun s =>
        σ s = pair try_empty xs /\
        ρ s = stack_empty /\
        π s = lm.

    (** A single linearization-state cell, useful in method assertions.
        The concrete and overlay components are empty, so this assertion
        composes with either underlay component. *)
    Definition lin_equiv (lm1 lm2 : tmap lin_state) : Prop :=
      forall q, TMap.find q lm1 = TMap.find q lm2.

    Lemma lin_equiv_refl lm : lin_equiv lm lm.
    Proof. intros q; reflexivity. Qed.

    Lemma lin_equiv_sym lm1 lm2 :
      lin_equiv lm1 lm2 -> lin_equiv lm2 lm1.
    Proof. intros H q; symmetry; apply H. Qed.

    Lemma lin_equiv_trans lm1 lm2 lm3 :
      lin_equiv lm1 lm2 -> lin_equiv lm2 lm3 -> lin_equiv lm1 lm3.
    Proof. intros H12 H23 q; rewrite H12, H23; reflexivity. Qed.

    Lemma lin_equiv_remove_add t ls lm :
      TMap.find t lm = None ->
      lin_equiv lm (TMap.remove t (TMap.add t ls lm)).
    Proof.
      intros Hnone q. destruct (Pos.eq_dec q t); subst.
      - rewrite TMap.grs. exact Hnone.
      - rewrite TMap.gro, TMap.gso; auto.
    Qed.

    Definition LinMapsto (t : tid) (ls : lin_state) : assertion :=
      fun s =>
        σ s = pair try_empty exch_empty /\
        ρ s = stack_empty /\
        lin_equiv (TMap.add t ls (@TMap.empty lin_state)) (π s).

    (** Granular resources used by the framed proof.  In contrast to
        [TryOwn]/[ExchOwn], each assertion below owns exactly one physical
        or ghost component.  This permits the proof to regroup ownership
        according to the next operation. *)
    Definition TryStateOwn
        (ts : State (@TryStackSpec.VTryStack A)) : assertion :=
      fun s =>
        σ s = pair ts exch_empty /\
        ρ s = stack_empty /\
        π s = @TMap.empty lin_state.

    Definition ExchStateOwn
        (xs : @EExchState (option A)) : assertion :=
      fun s =>
        σ s = pair try_empty xs /\
        ρ s = stack_empty /\
        π s = @TMap.empty lin_state.

    Definition StackOwn (stk : list A) : assertion :=
      fun s =>
        σ s = pair try_empty exch_empty /\
        ρ s = Idle stk /\
        π s = @TMap.empty lin_state.

    Definition LinOwn (lm : tmap lin_state) : assertion :=
      fun s =>
        σ s = pair try_empty exch_empty /\
        ρ s = stack_empty /\
        lin_equiv lm (π s).

    (** Representation-preserving removal of one map cell.  The standard
        [PositiveMap.remove] normalizes empty nodes, whereas [tree_join]
        records the original tree shape. *)
    Fixpoint lin_residual (t : tid) (lm : tmap lin_state) : tmap lin_state :=
      match t, lm with
      | xH, TMap.Leaf _ => TMap.Leaf _
      | xH, TMap.Node l _ r => TMap.Node l None r
      | xO t', TMap.Leaf _ => TMap.Leaf _
      | xO t', TMap.Node l o r => TMap.Node (lin_residual t' l) o r
      | xI t', TMap.Leaf _ => TMap.Leaf _
      | xI t', TMap.Node l o r => TMap.Node l o (lin_residual t' r)
      end.

    Lemma lin_residual_find_none t lm :
      TMap.find t (lin_residual t lm) = None.
    Proof.
      revert lm. induction t; intros [|l o r]; simpl; auto.
    Qed.

    Lemma lin_residual_find_other t q lm :
      t <> q -> TMap.find q (lin_residual t lm) = TMap.find q lm.
    Proof.
      revert q lm. induction t; intros q [|l o r] Hneq; destruct q;
        simpl; auto; try contradiction; try (apply IHt; congruence).
    Qed.

    Lemma lin_cell_join_residual t lm ls :
      TMap.find t lm = Some ls ->
      @join _ tmap_Join
        (TMap.add t ls (@TMap.empty lin_state))
        (lin_residual t lm) lm.
    Proof.
      revert lm. induction t; intros [|l o r] Hfind; simpl in *;
        try discriminate.
      - constructor; [constructor|apply IHt; exact Hfind|destruct o; constructor].
      - constructor; [apply IHt; exact Hfind|constructor|destruct o; constructor].
      - subst o. constructor; constructor.
    Qed.

    (** A value offered to the exchanger denotes the pending abstract
        stack operation of that thread. *)
    Definition op_of (v : option A) : Sig.op (li_sig F) :=
      match v with
      | Some a => StackSpec.push a
      | None => StackSpec.pop
      end.

    Definition complementary (v1 v2 : option A) : Prop :=
      match v1, v2 with
      | Some _, None | None, Some _ => True
      | _, _ => False
      end.

    Definition offered_token (v : option A) : lin_state :=
      ls_inv (op_of v).

    Definition done_token (v1 v2 : option A) : lin_state :=
      match v1, v2 with
      | Some a, None => ls_linr (StackSpec.push a) tt
      | None, Some a => ls_linr StackSpec.pop (Some a)
      | _, _ => ls_inv (op_of v1)
      end.

    (** [Required] is the Coq case form of the guarded wands in the paper.
        A pair always retains the offering party's token: complementary
        pairs own its completed token, while conflicting pairs keep its
        pending token.  The accepting party's token remains local. *)
    Definition Required (xs : @EExchState (option A)) : assertion :=
      match xs with
      | ExSOffered t v => LinMapsto t (offered_token v)
      | ExSPaired t1 (Some a1) _ (Some _) =>
          LinMapsto t1 (offered_token (Some a1))
      | ExSPaired t1 None _ None =>
          LinMapsto t1 (offered_token None)
      | ExSPaired t1 (Some a) _ None =>
          LinMapsto t1 (done_token (Some a) None)
      | ExSPaired t1 None _ (Some a) =>
          LinMapsto t1 (done_token None (Some a))
      | _ => emp
      end.

    Definition IStack : assertion :=
      ∃ ts, TryOwn ts.

    Definition IExch : assertion :=
      ∃ xs, (ExchStateOwn xs * Required xs)%Assertion.

    (** This top is deliberately map-sorted.  It cannot hide physical
        underlay state or abstract-stack state. *)
    Definition True_pi : assertion :=
      ∃ lm, LinOwn lm.

    (** A convenient exact layout used only by the small algebraic transfer
        lemmas below.  It remains a separating conjunction of the three
        disjoint resource sorts. *)
    Definition WholeOwn
        (ts : State (@TryStackSpec.VTryStack A))
        (xs : @EExchState (option A))
        (lm : tmap lin_state) : assertion :=
      (TryOwn ts * (ExchStateOwn xs * LinOwn lm))%Assertion.

    Lemma WholeOwn_exact ts xs lm s :
      WholeOwn ts xs lm s <->
      σ s = pair ts xs /\ ρ s = Idle (state ts) /\ lin_equiv lm (π s).
    Proof.
      split.
      - intros [st [sr [Hj [Ht [se [sl [Hjr [Hx Hl]]]]]]]].
        destruct st as [[tst xst] ost lmt],
          se as [[tse xse] ose lme], sl as [[tsl xsl] osl lml],
          sr as [[tsr xsr] osr lmr], s as [[tsw xsw] osw lmw].
        unfold TryOwn, ExchStateOwn, LinOwn in *; simpl in *.
        destruct Ht as [Et [Eot Elt]], Hx as [Ex [Eox Elx]],
          Hl as [El [Eol Ell]].
        inversion Et; inversion Ex; inversion El; subst.
        destruct Hjr as [[Hte Hxe] [Hoe Hle]],
          Hj as [[Htw Hxw] [How Hlw]]. simpl in *.
        pose proof (@join_unit_right_inv _ try_Join try_SA try_unit
          try_empty tsr Hte) as Etr.
        pose proof (@join_unit_right_inv _ exch_Join exch_SA exch_unit
          xs xsr Hxe) as Exr.
        pose proof (@join_unit_left_inv _ stack_Join stack_SA stack_unit
          stack_empty osr Hoe) as Eor.
        pose proof (@join_unit_left_inv _ tmap_Join tmap_SA tmap_unit
          lml lmr Hle) as Elr.
        rewrite <- Etr in Htw.
        rewrite <- Exr in Hxw.
        rewrite <- Eor in How.
        rewrite <- Elr in Hlw.
        pose proof (@join_unit_right_inv _ try_Join try_SA try_unit
          ts tsw Htw) as Etw.
        pose proof (@join_unit_left_inv _ exch_Join exch_SA exch_unit
          xs xsw Hxw) as Exw.
        pose proof (@join_unit_right_inv _ stack_Join stack_SA stack_unit
          (Idle (state ts)) osw How) as Eow.
        pose proof (@join_unit_left_inv _ tmap_Join tmap_SA tmap_unit
          lml lmw Hlw) as Elw.
        subst tsw xsw osw lmw; auto.
      - destruct s as [[tsw xsw] osw lmw]. simpl.
        intros [Eσ [Eρ Eπ]]. inversion Eσ; subst.
        set (et := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair ts exch_empty) (Idle (state ts)) (@TMap.empty lin_state)).
        set (exr := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair try_empty xs) stack_empty (@TMap.empty lin_state)).
        set (el := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair try_empty exch_empty) stack_empty lmw).
        set (er := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair try_empty xs) stack_empty lmw).
        exists et, er. split.
        + repeat split; simpl; constructor.
        + split.
          * unfold TryOwn; simpl; auto.
          * exists exr, el. split.
            -- repeat split; simpl; constructor.
            -- split; [unfold ExchStateOwn|unfold LinOwn]; simpl; auto.
    Qed.

    (** The invariant has exactly the three separating conjuncts stated in
        the proof document. *)
    Definition I : assertion :=
      ((IStack * IExch) * True_pi)%Assertion.

    Definition Exposed (t : tid) (ls : lin_state) : assertion :=
      (((IStack * IExch) * LinMapsto t ls) * True_pi)%Assertion.

    Definition Active (t : tid) (m : Sig.op (li_sig F)) : assertion :=
      Exposed t (ls_inv m).

    Definition Completed
        (t : tid) (m : Sig.op (li_sig F)) (ret : Sig.ar m) : assertion :=
      Exposed t (ls_linr m ret).

    Definition DoneCell (t : tid) (m : Sig.op (li_sig F)) : assertion :=
      ∃ ret, LinMapsto t (ls_linr m ret).

    Definition LocalLive (t : tid) (m : Sig.op (li_sig F)) : assertion :=
      (LinMapsto t (ls_inv m) \\// DoneCell t m)%Assertion.

    Definition in_exchanger_fact
        (t : tid) (m : Sig.op (li_sig F))
        (xs : @EExchState (option A)) : Prop :=
      match xs with
        | ExSOffered t' v => t = t' /\ m = op_of v
        | ExSPaired t' (Some a) _ (Some _) =>
            t = t' /\ m = StackSpec.push a
        | ExSPaired t' None _ None =>
            t = t' /\ m = StackSpec.pop
        | ExSPaired t' (Some a) _ None =>
            t = t' /\ m = StackSpec.push a
        | ExSPaired t' None _ (Some _) =>
            t = t' /\ m = StackSpec.pop
        | _ => False
      end.

    Definition InExchanger
        (t : tid) (m : Sig.op (li_sig F)) : assertion :=
      fun s => exists xs,
        (ExchStateOwn xs * Required xs)%Assertion s /\
        in_exchanger_fact t m xs.

    Definition Pending (t : tid) (m : Sig.op (li_sig F)) : assertion :=
      ((IStack * InExchanger t m * True_pi) \\//
       (((IStack * IExch) * LocalLive t m) * True_pi))%Assertion.

    (** Tactic-facing ownership state for an exchanger call.  Unlike the
        deliberately broad [Pending], this assertion remembers how the
        concrete exchanger state determines the location and phase of this
        particular thread's token.  Every constructor remains spatial: its
        payload is either [I] (the token is in [Required]) or one exact
        [Exposed] cell. *)
    Inductive ExchangeReady (t : tid) (v : option A) : assertion :=
    | ready_offered s :
        I s -> snd (σ s) = ExSOffered t v -> ExchangeReady t v s
    | ready_pair_offerer_comp t2 v2 s :
        t <> t2 -> complementary v v2 -> I s ->
        snd (σ s) = ExSPaired t v t2 v2 -> ExchangeReady t v s
    | ready_pair_offerer_same t2 v2 s :
        t <> t2 -> ~ complementary v v2 ->
        I s ->
        snd (σ s) = ExSPaired t v t2 v2 -> ExchangeReady t v s
    | ready_pair_accepter_comp t1 v1 s :
        t1 <> t -> complementary v1 v ->
        Exposed t (done_token v v1) s ->
        snd (σ s) = ExSPaired t1 v1 t v -> ExchangeReady t v s
    | ready_pair_accepter_same t1 v1 s :
        t1 <> t -> ~ complementary v1 v ->
        Exposed t (ls_inv (op_of v)) s ->
        snd (σ s) = ExSPaired t1 v1 t v -> ExchangeReady t v s
    | ready_accepted_accepter_comp t1 v1 s :
        t1 <> t -> complementary v1 v ->
        Exposed t (done_token v v1) s ->
        snd (σ s) = ExSAccepted t1 v1 t v -> ExchangeReady t v s
    | ready_accepted_accepter_same t1 v1 s :
        t1 <> t -> ~ complementary v1 v ->
        Exposed t (ls_inv (op_of v)) s ->
        snd (σ s) = ExSAccepted t1 v1 t v -> ExchangeReady t v s.

    (** Invocation adds the fresh method cell to the map-only residual and
        then exposes it.  The shared spatial resources are not unfolded. *)
    Lemma ginv_exposes_active t m s s' :
      I s -> Ginv t m s s' -> Active t m s'.
    Proof.
      intros [shared [top [Hwhole [Hshared [lm Htop]]]]] Hginv.
      unfold Ginv, LiftRelation_π in Hginv.
      destruct Hginv as [Hσ [Hρ [Hfresh Hmap]]].
      destruct s as [us os pi], s' as [us' os' pi']; simpl in *.
      subst us' os' pi'.
      destruct shared as [ush osh pish], top as [ust ost pist].
      destruct Hwhole as [Hus [Hos Hpi]]. simpl in *.
      pose proof (tree_join_none _ _ _ Hpi t) as Hnone.
      rewrite Hfresh in Hnone.
      destruct (proj1 Hnone eq_refl) as [Hnone_sh Hnone_top].
      set (cell := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair try_empty exch_empty) stack_empty
        (TMap.add t (ls_inv m) (@TMap.empty lin_state))).
      set (newtop := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        ust ost (TMap.add t (ls_inv m) pist)).
      set (oldtop := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        ust ost pist).
      set (oldshared := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        ush osh pish).
      set (poststate := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        us os (TMap.add t (ls_inv m) pi)).
      assert ((LinMapsto t (ls_inv m) * True_pi)%Assertion newtop)
        as Hlocal.
      {
        exists cell, oldtop. split.
        - destruct Htop as [Hu_top [Ho_top Hlm_top]].
          unfold cell, oldtop, newtop; simpl in *.
          inversion Hu_top; subst.
          repeat split; simpl.
          + constructor.
          + constructor.
          + constructor.
          + apply tree_join_add_empty_left; exact Hnone_top.
        - split.
          + unfold cell, LinMapsto, lin_equiv; simpl; auto.
          + exists lm. exact Htop.
      }
      assert (((IStack * IExch) *
        (LinMapsto t (ls_inv m) * True_pi))%Assertion
        poststate) as Hnested.
      {
        exists oldshared, newtop. split.
        - unfold newtop, oldshared, poststate; simpl.
          split; [exact Hus|]. split; [exact Hos|].
          eapply linmap_join_add_right; eauto.
        - auto.
      }
      unfold Active, poststate in *.
      apply sepcon_assoc1 in Hnested. exact Hnested.
    Qed.

    Lemma Required_idle :
      ⊨ Required ExSIdle <<==>> emp.
    Proof. split; apply ImplRefl. Qed.

    Lemma Required_offered t v :
      ⊨ Required (ExSOffered t v) <<==>>
        LinMapsto t (ls_inv (op_of v)).
    Proof. split; apply ImplRefl. Qed.

    Lemma Required_paired_push_pop t1 a t2 :
      ⊨ Required (ExSPaired t1 (Some a) t2 None) <<==>>
        LinMapsto t1 (ls_linr (StackSpec.push a) tt).
    Proof. split; apply ImplRefl. Qed.

    Lemma Required_paired_pop_push t1 t2 a :
      ⊨ Required (ExSPaired t1 None t2 (Some a)) <<==>>
        LinMapsto t1 (ls_linr StackSpec.pop (Some a)).
    Proof. split; apply ImplRefl. Qed.

    Lemma Required_paired_push_push t1 a1 t2 a2 :
      ⊨ Required (ExSPaired t1 (Some a1) t2 (Some a2)) <<==>>
        LinMapsto t1 (ls_inv (StackSpec.push a1)).
    Proof. split; apply ImplRefl. Qed.

    Lemma Required_paired_pop_pop t1 t2 :
      ⊨ Required (ExSPaired t1 None t2 None) <<==>>
        LinMapsto t1 (ls_inv StackSpec.pop).
    Proof. split; apply ImplRefl. Qed.

    Lemma Required_accepted t1 v1 t2 v2 :
      ⊨ Required (ExSAccepted t1 v1 t2 v2) <<==>> emp.
    Proof. split; apply ImplRefl. Qed.

    Definition required_ok
        (xs : @EExchState (option A)) (pi : tmap lin_state) : Prop :=
      match xs with
      | ExSOffered t v => TMap.find t pi = Some (offered_token v)
      | ExSPaired t1 (Some a) _ None =>
          TMap.find t1 pi = Some (done_token (Some a) None)
      | ExSPaired t1 None _ (Some a) =>
          TMap.find t1 pi = Some (done_token None (Some a))
      | ExSPaired t1 v1 _ _ =>
          TMap.find t1 pi = Some (offered_token v1)
      | _ => True
      end.

    Definition required_owner
        (xs : @EExchState (option A)) : option tid :=
      match xs with
      | ExSOffered t _ => Some t
      | ExSPaired t1 (Some _) _ None => Some t1
      | ExSPaired t1 None _ (Some _) => Some t1
      | ExSPaired t1 _ _ _ => Some t1
      | _ => None
      end.

    Lemma required_ok_remove_other xs pi t :
      required_ok xs pi -> required_owner xs <> Some t ->
      required_ok xs (TMap.remove t pi).
    Proof.
      destruct xs as [tr v|t1 v1 t2 v2|t1 v1 t2 v2|];
        try destruct v1; try destruct v2; simpl; auto;
        intros Hfind Hneq; rewrite TMap.gro; auto; congruence.
    Qed.

    Lemma required_ok_add_other xs pi t ls :
      required_ok xs pi -> required_owner xs <> Some t ->
      required_ok xs (TMap.add t ls pi).
    Proof.
      destruct xs as [tr v|t1 v1 t2 v2|t1 v1 t2 v2|];
        try destruct v1; try destruct v2; simpl; auto;
        intros Hfind Hneq; rewrite TMap.gso; auto; congruence.
    Qed.

    Lemma Required_unit_components xs s :
      Required xs s ->
      σ s = pair try_empty exch_empty /\ ρ s = stack_empty.
    Proof.
      destruct xs as [t v|t1 v1 t2 v2|t1 v1 t2 v2|];
        try destruct v1; try destruct v2; simpl; intros H.
      all: try solve [destruct H as [Hσ [Hρ _]]; auto].
      all: pose proof (@unit_element_eq _ proof_Join proof_SA proof_unit s H)
        as ->; simpl; auto.
    Qed.

    Lemma Required_ok_local xs s :
      Required xs s -> required_ok xs (π s).
    Proof.
      destruct xs as [t v|t1 v1 t2 v2|t1 v1 t2 v2|].
      - simpl. intros [_ [_ Hmap]]. specialize (Hmap t).
        rewrite TMap.gss in Hmap. symmetry; exact Hmap.
      - destruct v1, v2; simpl; auto; intros [_ [_ Hmap]];
          specialize (Hmap t1); rewrite TMap.gss in Hmap;
          symmetry; exact Hmap.
      - destruct v1, v2; simpl; auto.
      - simpl; auto.
    Qed.

    Lemma Required_find_none_other xs s t :
      Required xs s -> required_owner xs <> Some t ->
      TMap.find t (π s) = None.
    Proof.
      destruct xs as [tr v|t1 v1 t2 v2|t1 v1 t2 v2|];
        try destruct v1; try destruct v2; simpl; intros H Hneq.
      all: try solve
        [ unfold LinMapsto, lin_equiv in H;
          destruct H as [_ [_ Hmap]]; rewrite <- Hmap;
          rewrite TMap.gso, TMap.gleaf; auto; congruence ].
      all: pose proof (@unit_element_eq _ proof_Join proof_SA proof_unit s H)
        as ->; simpl; apply TMap.gleaf.
    Qed.

    Lemma IExch_observe s :
      IExch s -> exists xs,
        snd (σ s) = xs /\
        (ExchStateOwn xs * Required xs)%Assertion s.
    Proof.
      intros [xs Hres]. exists xs. split; [|exact Hres].
      destruct Hres as [sx [sr [J [Hex Hreq]]]].
      destruct s as [[tsw xsw] osw piw], sx as [[tsx xsx] osx pix],
        sr as [[tsr xsr] osr pir].
      destruct J as [[Jt Jx] [Jo Jpi]]. simpl in *.
      unfold ExchStateOwn in Hex; simpl in Hex.
      destruct Hex as [Ex [_ _]].
      pose proof (Required_unit_components xs
        (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair tsr xsr) osr pir) Hreq) as [Er _].
      inversion Ex; inversion Er; subst.
      pose proof (@join_unit_right_inv _ exch_Join exch_SA exch_unit
        xs xsw Jx) as E. symmetry; exact E.
    Qed.

    Lemma ExchResource_observe xs s :
      (ExchStateOwn xs * Required xs)%Assertion s -> snd (σ s) = xs.
    Proof.
      intros [sx [sr [J [Hex Hreq]]]].
      destruct s as [[tsw xsw] osw piw], sx as [[tsx xsx] osx pix],
        sr as [[tsr xsr] osr pir].
      destruct J as [[Jt Jx] [Jo Jpi]]. simpl in *.
      unfold ExchStateOwn in Hex; simpl in Hex.
      destruct Hex as [Ex [_ _]].
      pose proof (Required_unit_components xs
        (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair tsr xsr) osr pir) Hreq) as [Er _].
      inversion Ex; inversion Er; subst.
      pose proof (@join_unit_right_inv _ exch_Join exch_SA exch_unit
        xs xsw Jx) as E. symmetry; exact E.
    Qed.

    Lemma InExchanger_observe t m s :
      InExchanger t m s -> in_exchanger_fact t m (snd (σ s)).
    Proof.
      intros [xs [Hres Hfact]].
      pose proof (ExchResource_observe xs s Hres) as E.
      rewrite E. exact Hfact.
    Qed.

    Lemma InExchanger_entails_IExch t m :
      ⊨ InExchanger t m ==>> IExch.
    Proof.
      intros s [xs [Hres _]]. exists xs; exact Hres.
    Qed.

    Lemma Pending_shared_observe t m s :
      ((IStack * InExchanger t m) * True_pi)%Assertion s ->
      I s /\ in_exchanger_fact t m (snd (σ s)).
    Proof.
      intros Hpending. split.
      - unfold I. eapply sepcon_mono; [|apply ImplRefl|exact Hpending].
        eapply sepcon_mono; [apply ImplRefl|].
        apply InExchanger_entails_IExch.
      - destruct Hpending as [shared [top [J0
          [[stack [iex [J1 [Hstack Hin]]]] [lm Htop]]]]].
        pose proof (InExchanger_observe t m iex Hin) as Hfact.
        destruct Hstack as [ts Hstack].
        destruct s as [[tsw xsw] osw piw],
          shared as [[tsh xsh] osh pish], top as [[tst xst] ost pit],
          stack as [[tss xss] oss pis], iex as [[tsi xsi] osi pii].
        destruct J0 as [[Jt0 Jx0] _], J1 as [[Jt1 Jx1] _].
        simpl in *.
        unfold TryOwn in Hstack; simpl in Hstack.
        unfold LinOwn in Htop; simpl in Htop.
        destruct Hstack as [Est [_ _]], Htop as [Etop [_ _]].
        inversion Est; inversion Etop; subst.
        pose proof (@join_unit_left_inv _ exch_Join exch_SA exch_unit
          xsi xsh Jx1) as Exsh.
        rewrite <- Exsh in Jx0.
        pose proof (@join_unit_right_inv _ exch_Join exch_SA exch_unit
          xsi xsw Jx0) as Exw.
        rewrite <- Exw. exact Hfact.
    Qed.

    Lemma Pending_local_cases t m s :
      (((IStack * IExch) * LocalLive t m) * True_pi)%Assertion s ->
      Exposed t (ls_inv m) s \/
      exists ret, Exposed t (ls_linr m ret) s.
    Proof.
      intros [owned [top [J0
        [[shared [local [J1 [Hshared Hlive]]]] Htop]]]].
      destruct Hlive as [Hinv | [ret Hdone]].
      - left. exists owned, top. split; [exact J0|]. split; [|exact Htop].
        exists shared, local. auto.
      - right. exists ret. exists owned, top.
        split; [exact J0|]. split; [|exact Htop].
        exists shared, local. auto.
    Qed.

    Lemma Pending_cases t m s :
      Pending t m s ->
      (I s /\ in_exchanger_fact t m (snd (σ s))) \/
      Exposed t (ls_inv m) s \/
      exists ret, Exposed t (ls_linr m ret) s.
    Proof.
      intros [Hshared | Hlocal].
      - left. eapply Pending_shared_observe; exact Hshared.
      - right. eapply Pending_local_cases; exact Hlocal.
    Qed.


    Lemma I_inexchanger_pending t m s :
      I s -> in_exchanger_fact t m (snd (σ s)) -> Pending t m s.
    Proof.
      intros [shared [top [J0
        [[stack [exch [J1 [Hstack HIExch]]]] Htop]]]] Hfact.
      destruct (IExch_observe exch HIExch) as [xs [Eex Hres]].
      destruct Hstack as [ts Hstack], Htop as [lm Htop].
      destruct s as [[tsw xsw] osw piw], shared as [[tsh xsh] osh pish],
        top as [[tst xst] ost pit], stack as [[tss xss] oss pis],
        exch as [[tse xse] ose pie].
      destruct J0 as [[Jt0 Jx0] [Jo0 Jp0]],
        J1 as [[Jt1 Jx1] [Jo1 Jp1]]. simpl in *.
      unfold TryOwn in Hstack; simpl in Hstack.
      unfold LinOwn in Htop; simpl in Htop.
      destruct Hstack as [Est [Eost Epist]],
        Htop as [Etop [Eotop Htopmap]].
      inversion Est; inversion Etop; subst.
      pose proof (@join_unit_left_inv _ exch_Join exch_SA exch_unit
        xs xsh Jx1) as Exsh.
      rewrite <- Exsh in Jx0.
      pose proof (@join_unit_right_inv _ exch_Join exch_SA exch_unit
        xs xsw Jx0) as Exw.
      left. exists (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair tsh xsh) osh pish),
        (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair try_empty exch_empty) stack_empty pit).
      split.
      - split.
        + split; [exact Jt0|]. rewrite <- Exsh. exact Jx0.
        + split; [exact Jo0|exact Jp0].
      - split.
        + exists (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair ts exch_empty) (Idle (state ts))
            (@TMap.empty lin_state)),
            (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair tse xs) ose pie).
          split.
          * split.
            -- split; [exact Jt1|exact Jx1].
            -- split; [exact Jo1|exact Jp1].
          * split.
            -- exists ts. unfold TryOwn; simpl; auto.
            -- exists xs. split; [exact Hres|].
               rewrite <- Exw in Hfact. exact Hfact.
        + exists lm. unfold LinOwn, lin_equiv; simpl; auto.
    Qed.

    Lemma Active_entails_Pending t m :
      ⊨ Active t m ==>> Pending t m.
    Proof.
      unfold Active, Exposed, Pending. intros s H. right.
      eapply sepcon_mono; [|apply ImplRefl|exact H].
      eapply sepcon_mono; [apply ImplRefl|].
      intros cell Hcell. left; exact Hcell.
    Qed.

    Lemma Completed_entails_Pending t m ret :
      ⊨ Completed t m ret ==>> Pending t m.
    Proof.
      unfold Completed, Exposed, Pending. intros s H. right.
      eapply sepcon_mono; [|apply ImplRefl|exact H].
      eapply sepcon_mono; [apply ImplRefl|].
      intros cell Hcell. right. exists ret; exact Hcell.
    Qed.

    Lemma preserve_pending (t : tid) (m : Sig.op (li_sig F))
        (s s' : @ProofStateSingle _ _ (li_lts E) (li_lts F)) :
      I s' -> snd (σ s) = snd (σ s') ->
      (forall ls, Exposed t ls s -> Exposed t ls s') ->
      Pending t m s -> Pending t m s'.
    Proof.
      intros HI Hσ Hpres Hpending.
      destruct (Pending_cases t m s Hpending)
        as [[_ Hfact] | [Hinv | [ret Hdone]]].
      - eapply I_inexchanger_pending; [exact HI|].
        rewrite <- Hσ. exact Hfact.
      - eapply Active_entails_Pending. eapply Hpres; exact Hinv.
      - eapply Completed_entails_Pending. eapply Hpres; exact Hdone.
    Qed.

    Lemma preserve_exchange_ready (t : tid) (v : option A)
        (s s' : @ProofStateSingle _ _ (li_lts E) (li_lts F)) :
      I s' -> snd (σ s) = snd (σ s') ->
      (forall ls, Exposed t ls s -> Exposed t ls s') ->
      ExchangeReady t v s -> ExchangeReady t v s'.
    Proof.
      intros HI Hexch Hexp Hready.
      destruct Hready as
        [s0 HI0 E0
        |t2 v2 s0 Hneq Hcomp HI0 E0
        |t2 v2 s0 Hneq Hsame Hlocal E0
        |t1 v1 s0 Hneq Hcomp Hlocal E0
        |t1 v1 s0 Hneq Hsame Hlocal E0
        |t1 v1 s0 Hneq Hcomp Hlocal E0
        |t1 v1 s0 Hneq Hsame Hlocal E0].
      - eapply ready_offered; [exact HI|]. rewrite <- Hexch; exact E0.
      - eapply ready_pair_offerer_comp; [exact Hneq|exact Hcomp|exact HI|].
        rewrite <- Hexch; exact E0.
      - eapply ready_pair_offerer_same;
          [exact Hneq|exact Hsame|exact HI|].
        rewrite <- Hexch; exact E0.
      - eapply ready_pair_accepter_comp;
          [exact Hneq|exact Hcomp|eapply Hexp; exact Hlocal|].
        rewrite <- Hexch; exact E0.
      - eapply ready_pair_accepter_same;
          [exact Hneq|exact Hsame|eapply Hexp; exact Hlocal|].
        rewrite <- Hexch; exact E0.
      - eapply ready_accepted_accepter_comp;
          [exact Hneq|exact Hcomp|eapply Hexp; exact Hlocal|].
        rewrite <- Hexch; exact E0.
      - eapply ready_accepted_accepter_same;
          [exact Hneq|exact Hsame|eapply Hexp; exact Hlocal|].
        rewrite <- Hexch; exact E0.
    Qed.

    Lemma required_ok_join_left xs pi1 pi2 pi :
      @join _ tmap_Join pi1 pi2 pi ->
      required_ok xs pi1 -> required_ok xs pi.
    Proof.
      intros Hj. destruct xs as [t v|t1 v1 t2 v2|t1 v1 t2 v2|];
        try destruct v1; try destruct v2; simpl; auto;
        intros Hfind; eapply linmap_join_find_left; eauto.
    Qed.

    Lemma required_ok_join_right xs pi1 pi2 pi :
      @join _ tmap_Join pi1 pi2 pi ->
      required_ok xs pi2 -> required_ok xs pi.
    Proof.
      intros Hj. destruct xs as [t v|t1 v1 t2 v2|t1 v1 t2 v2|];
        try destruct v1; try destruct v2; simpl; auto;
        intros Hfind; eapply linmap_join_find_right; eauto.
    Qed.

    Lemma Shared_find_none t s :
      (IStack * IExch)%Assertion s ->
      required_owner (snd (σ s)) <> Some t ->
      TMap.find t (π s) = None.
    Proof.
      intros [ss [se [J [HIStack HIExch]]]] Hother.
      destruct HIStack as [ts Htry].
      destruct HIExch as [xs [sx [sr [Jx [Hex Hreq]]]]].
      destruct s as [[tsw xsw] osw piw], ss as [[tss xss] oss pis],
        se as [[tse xse] ose pie], sx as [[tsx xsx] osx pix],
        sr as [[tsr xsr] osr pir].
      destruct J as [[Jt Jex] [Jo Jpi]], Jx as [[Jtx Jxx] [Jox Jpix]].
      simpl in *.
      unfold TryOwn in Htry; simpl in Htry.
      unfold ExchStateOwn in Hex; simpl in Hex.
      destruct Htry as [Etry [_ Epi_try]], Hex as [Eex [_ Epi_ex]].
      pose proof (Required_unit_components xs
        (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair tsr xsr) osr pir) Hreq) as [Ereq _].
      inversion Etry; inversion Eex; inversion Ereq; subst.
      pose proof (@join_unit_right_inv _ exch_Join exch_SA exch_unit
        xs xse Jxx) as Exse.
      rewrite <- Exse in Jex.
      pose proof (@join_unit_left_inv _ exch_Join exch_SA exch_unit
        xs xsw Jex) as Exsw.
      rewrite <- Exsw in Hother.
      apply (proj2 (tree_join_none _ _ _ Jpi t)). split.
      - apply TMap.gleaf.
      - apply (proj2 (tree_join_none _ _ _ Jpix t)). split.
        + apply TMap.gleaf.
        + exact (Required_find_none_other xs
            (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
              (pair try_empty exch_empty) osr pir) t Hreq Hother).
    Qed.

    Lemma I_ALin_exposes t ls s :
      I s -> ALin t ls s ->
      required_owner (snd (σ s)) <> Some t ->
      Exposed t ls s.
    Proof.
      intros [shared [top [J [Hshared [lm Htop]]]]] Halin Hother.
      pose proof (Shared_find_none t shared Hshared) as Hnone_shared.
      destruct s as [us os pi], shared as [uss oss pis],
        top as [ust ost pit].
      destruct J as [Ju [Jo Jpi]]. simpl in *.
      destruct Htop as [Eut [Eot Htopmap]].
      change (ust = pair try_empty exch_empty) in Eut.
      change (ost = stack_empty) in Eot.
      rewrite Eut in Ju. rewrite Eot in Jo.
      assert (required_owner (snd uss) <> Some t) as Hother_shared.
      {
        destruct Ju as [Jt Jx]. simpl in *.
        pose proof (@join_unit_right_inv _ exch_Join exch_SA exch_unit
          (snd uss) (snd us) Jx) as Ex.
        rewrite Ex. exact Hother.
      }
      specialize (Hnone_shared Hother_shared).
      assert (TMap.find t pit = Some ls) as Hfind_top.
      {
        pose proof (linmap_join_lookup _ _ _ Jpi t) as Hlookup.
        rewrite Hnone_shared, Halin in Hlookup. inversion Hlookup; auto.
      }
      set (cell := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair try_empty exch_empty) stack_empty
        (TMap.add t ls (@TMap.empty lin_state))).
      set (rest := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair try_empty exch_empty) stack_empty (lin_residual t pit)).
      assert ((LinMapsto t ls * True_pi)%Assertion
        (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair try_empty exch_empty) stack_empty pit)) as Hlocal.
      {
        exists cell, rest. split.
        - unfold cell, rest; simpl. repeat split; try constructor.
          apply lin_cell_join_residual; exact Hfind_top.
        - split.
          + unfold cell, LinMapsto, lin_equiv; simpl; auto.
          + exists (lin_residual t pit).
            unfold rest, LinOwn, lin_equiv; simpl; auto.
      }
      assert (((IStack * IExch) *
        (LinMapsto t ls * True_pi))%Assertion
        (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F) us os pi))
        as Hnested.
      {
        exists (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          uss oss pis),
          (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (pair try_empty exch_empty) stack_empty pit).
        split; [split; [exact Ju|split; assumption]|]. auto.
      }
      unfold Exposed. apply sepcon_assoc1 in Hnested. exact Hnested.
    Qed.

    Lemma I_observe s :
      I s -> exists ts xs,
        σ s = pair ts xs /\
        ρ s = Idle (state ts) /\
        required_ok xs (π s).
    Proof.
      intros [sh [top [J0
        [[st [ex [J1 [[ts Htry]
          [xs [sx [req [J2 [Hex Hreq]]]]]]]]]
         [lm Htop]]]]].
      pose proof (Required_unit_components xs req Hreq) as Hrequnit.
      pose proof (Required_ok_local xs req Hreq) as Hreqok.
      destruct s as [[tw xw] os pi], sh as [[tsh xsh] osh pish],
        top as [[ttop xtop] ot pit], st as [[tst xst] ost pist],
        ex as [[tex xex] oex piex], sx as [[tsx xsx] osx pix],
        req as [[tr xr] or pir].
      destruct J0 as [Ju0 [Jo0 Jp0]], J1 as [Ju1 [Jo1 Jp1]],
        J2 as [Ju2 [Jo2 Jp2]]. simpl in *.
      unfold TryOwn in Htry; simpl in Htry.
      unfold ExchStateOwn in Hex; simpl in Hex.
      unfold LinOwn in Htop; simpl in Htop.
      destruct Htry as [Et [Eot Ept]], Hex as [Ex [Eox Epx]],
        Htop as [Etop [Eotop _]], Hrequnit as [Ereq Eoreq].
      inversion Et; inversion Ex; inversion Etop; inversion Ereq; subst.
      destruct Ju2 as [Jt2 Jx2]. simpl in *.
      pose proof (@join_unit_right_inv _ try_Join try_SA try_unit
        try_empty tex Jt2) as Et2.
      pose proof (@join_unit_right_inv _ exch_Join exch_SA exch_unit
        xs xex Jx2) as Ex2.
      pose proof (@join_unit_right_inv _ stack_Join stack_SA stack_unit
        stack_empty oex Jo2) as Eo2.
      rewrite <- Et2, <- Ex2 in Ju1. rewrite <- Eo2 in Jo1.
      destruct Ju1 as [Jt1 Jx1]. simpl in *.
      pose proof (@join_unit_right_inv _ try_Join try_SA try_unit
        ts tsh Jt1) as Et1.
      pose proof (@join_unit_left_inv _ exch_Join exch_SA exch_unit
        xs xsh Jx1) as Ex1.
      pose proof (@join_unit_right_inv _ stack_Join stack_SA stack_unit
        (Idle (state ts)) osh Jo1) as Eo1.
      rewrite <- Et1, <- Ex1 in Ju0. rewrite <- Eo1 in Jo0.
      destruct Ju0 as [Jt0 Jx0]. simpl in *.
      pose proof (@join_unit_right_inv _ try_Join try_SA try_unit
        ts tw Jt0) as Et0.
      pose proof (@join_unit_right_inv _ exch_Join exch_SA exch_unit
        xs xw Jx0) as Ex0.
      pose proof (@join_unit_right_inv _ stack_Join stack_SA stack_unit
        (Idle (state ts)) os Jo0) as Eo0.
      exists ts, xs. repeat split.
      - simpl in *; subst; reflexivity.
      - exact (eq_sym Eo0).
      - eapply required_ok_join_left; [exact Jp0|].
        eapply required_ok_join_right; [exact Jp1|].
        eapply required_ok_join_right; [exact Jp2|exact Hreqok].
    Qed.

    Lemma IExch_local_owner_distinct t ls s :
      (IExch * LinMapsto t ls)%Assertion s ->
      exists xs, snd (σ s) = xs /\ required_owner xs <> Some t.
    Proof.
      intros [iex [local [Jout
        [[xs [sx [req [Jin [Hex Hreq]]]]] Hlocal]]]].
      destruct s as [[tsw xsw] osw piw], iex as [[tsi xsi] osi pii],
        local as [[tsl xsl] osl pil], sx as [[tsx xsx] osx pix],
        req as [[tsr xsr] osr pir].
      destruct Jout as [[Jto Jxo] [Joo Jpo]],
        Jin as [[Jti Jxi] [Joi Jpi]]. simpl in *.
      unfold ExchStateOwn in Hex; simpl in Hex.
      unfold LinMapsto, lin_equiv in Hlocal; simpl in Hlocal.
      destruct Hex as [Exs [Eos Eps]], Hlocal as [El [Eol Hlm]].
      pose proof (Required_unit_components xs
        (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair tsr xsr) osr pir) Hreq) as [Er Eor].
      pose proof (Required_ok_local xs
        (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair tsr xsr) osr pir) Hreq) as Hreqfind.
      inversion Exs; inversion El; inversion Er; subst.
      pose proof (@join_unit_right_inv _ exch_Join exch_SA exch_unit
        xs xsi Jxi) as Exi.
      rewrite <- Exi in Jxo.
      pose proof (@join_unit_right_inv _ exch_Join exch_SA exch_unit
        xs xsw Jxo) as Exw.
      exists xs. split; [symmetry; exact Exw|].
      destruct xs as [tr v|t1 v1 t2 v2|t1 v1 t2 v2|];
        try destruct v1; try destruct v2; simpl in *; try congruence.
      all: intro Heq; inversion Heq; subst;
        eapply (linmap_join_exclusive _ _ _ Jpo t);
        [ eapply linmap_join_find_right; [exact Jpi|]; exact Hreqfind
        | specialize (Hlm t); rewrite TMap.gss in Hlm;
          symmetry; exact Hlm ].
    Qed.

    Lemma Exposed_owner_distinct t ls s :
      Exposed t ls s ->
      required_owner (snd (σ s)) <> Some t.
    Proof.
      intros [owned [top [J0
        [[shared [cell [J1
          [[stack [exch [J2 [Hstack Hexch]]]] Hcell]]]] Htop]]]].
      destruct (@join_assoc _ proof_Join proof_SA
        stack exch cell shared owned J2 J1)
        as [excell [Jec Jstack]].
      assert ((IExch * LinMapsto t ls)%Assertion excell)
        as Hec.
      { exists exch, cell. auto. }
      destruct (IExch_local_owner_distinct t ls excell Hec)
        as [xs [Hexs Hneq]].
      destruct Hstack as [ts Hstack], Htop as [lm Htop].
      destruct s as [[tsw xsw] osw piw], owned as [[tso xso] oso pio],
        top as [[tst xst] ost pit], stack as [[tss xss] oss pis],
        excell as [[tse xse] ose pie].
      destruct J0 as [[Jt0 Jx0] _],
        Jstack as [[Jts Jxs] _]. simpl in *.
      unfold TryOwn in Hstack; simpl in Hstack.
      unfold LinOwn in Htop; simpl in Htop.
      destruct Hstack as [Est [_ _]], Htop as [Etop [_ _]].
      inversion Est; inversion Etop; subst.
      pose proof (@join_unit_left_inv _ exch_Join exch_SA exch_unit
        xs xso Jxs) as Exo.
      rewrite <- Exo in Jx0.
      pose proof (@join_unit_right_inv _ exch_Join exch_SA exch_unit
        xs xsw Jx0) as Exw.
      rewrite <- Exw. exact Hneq.
    Qed.

    Lemma Active_owner_distinct t m s :
      Active t m s -> required_owner (snd (σ s)) <> Some t.
    Proof. apply Exposed_owner_distinct. Qed.

    Lemma Completed_owner_distinct t m ret s :
      Completed t m ret s -> required_owner (snd (σ s)) <> Some t.
    Proof. apply Exposed_owner_distinct. Qed.

    Lemma I_intro_no_required ts xs pi
        (Hreq : ⊨ Required xs <<==>> emp) :
      I (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair ts xs) (Idle (state ts)) pi).
    Proof.
      set (e := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair try_empty exch_empty) stack_empty (@TMap.empty lin_state)).
      set (st := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair ts exch_empty) (Idle (state ts)) (@TMap.empty lin_state)).

      set (sx := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair try_empty xs) stack_empty (@TMap.empty lin_state)).
      set (shared := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair ts xs) (Idle (state ts)) (@TMap.empty lin_state)).
      set (top := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair try_empty exch_empty) stack_empty pi).
      exists shared, top. split.
      - unfold shared, top; simpl. repeat split; constructor.
      - split.
        + exists st, sx. split.
          * unfold st, sx, shared; simpl. repeat split; constructor.
          * split.
            -- exists ts. unfold st, TryOwn; simpl; auto.
            -- exists xs. exists sx, e. split.
               ++ unfold sx, e; simpl.
                  exact (@unit_join _ proof_Join proof_SA proof_unit sx).
               ++ split.
                  { unfold sx, ExchStateOwn; simpl; auto. }
                  { apply (proj2 (Hreq e)).
                    exact (@unit_spec _ proof_Join proof_SA proof_unit). }
        + exists pi. unfold top, LinOwn, lin_equiv; simpl; auto.
    Qed.

    Lemma I_intro_required_cell ts xs pi tr ls
        (Hreq : ⊨ Required xs <<==>> LinMapsto tr ls)
        (Hfind : TMap.find tr pi = Some ls) :
      I (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair ts xs) (Idle (state ts)) pi).
    Proof.
      set (st := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair ts exch_empty) (Idle (state ts)) (@TMap.empty lin_state)).
      set (sx := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair try_empty xs) stack_empty (@TMap.empty lin_state)).
      set (cell := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair try_empty exch_empty) stack_empty
        (TMap.add tr ls (@TMap.empty lin_state))).
      set (exreq := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair try_empty xs) stack_empty
        (TMap.add tr ls (@TMap.empty lin_state))).
      set (shared := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair ts xs) (Idle (state ts))
        (TMap.add tr ls (@TMap.empty lin_state))).
      set (top := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair try_empty exch_empty) stack_empty (lin_residual tr pi)).
      exists shared, top. split.
      - unfold shared, top; simpl. repeat split; try constructor.
        apply lin_cell_join_residual; exact Hfind.
      - split.
        + exists st, exreq. split.
          * unfold st, exreq, shared; simpl. repeat split; constructor.
          * split.
            -- exists ts. unfold st, TryOwn; simpl; auto.
            -- exists xs. exists sx, cell. split.
               ++ unfold sx, cell, exreq; simpl. repeat split; constructor.
               ++ split.
                  { unfold sx, ExchStateOwn; simpl; auto. }
                  { apply (proj2 (Hreq cell)).
                    unfold cell, LinMapsto, lin_equiv; simpl; auto. }
        + exists (lin_residual tr pi).
          unfold top, LinOwn, lin_equiv; simpl; auto.
    Qed.

    (** Reassemble the three spatial resources after an atomic transition.
        The premise records only the cell demanded by [Required xs]; the
        proof below chooses the appropriate spatial constructor for the
        actual exchanger state. *)
    Lemma I_intro_observed ts xs pi :
      required_ok xs pi ->
      I (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair ts xs) (Idle (state ts)) pi).
    Proof.
      destruct xs as [tr v|t1 v1 t2 v2|t1 v1 t2 v2|]; simpl.
      - intro Hfind. eapply I_intro_required_cell with
          (tr := tr) (ls := offered_token v);
          [apply Required_offered|exact Hfind].
      - destruct v1 as [a1|], v2 as [a2|]; simpl; intro Hreq.
        + eapply I_intro_required_cell with
            (tr := t1) (ls := offered_token (Some a1));
            [apply Required_paired_push_push|exact Hreq].
        + eapply I_intro_required_cell with
            (tr := t1) (ls := done_token (Some a1) None);
            [apply Required_paired_push_pop|exact Hreq].
        + eapply I_intro_required_cell with
            (tr := t1) (ls := done_token None (Some a2));
            [apply Required_paired_pop_push|exact Hreq].
        + eapply I_intro_required_cell with
            (tr := t1) (ls := offered_token None);
            [apply Required_paired_pop_pop|exact Hreq].
      - intro Hreq. eapply I_intro_no_required; apply Required_accepted.
      - intro Hreq. eapply I_intro_no_required; apply Required_idle.
    Qed.

    Lemma Exposed_intro_observed ts xs pi t ls :
      required_ok xs pi -> TMap.find t pi = Some ls ->
      required_owner xs <> Some t ->
      Exposed t ls
        (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair ts xs) (Idle (state ts)) pi).
    Proof.
      intros Hreq Hfind Howner. eapply I_ALin_exposes.
      - apply I_intro_observed; exact Hreq.
      - exact Hfind.
      - exact Howner.
    Qed.

    (** Direct spatial transfer for a try-stack transition.  The exchanger
        ownership is unchanged; the old exposed cell proves that the
        state-dependent exchanger cell has a different owner. *)
    Lemma Exposed_rebuild_try t oldls newls ts ts' xs rho rho' pi pi' :
      Exposed t oldls
        (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair ts xs) rho pi) ->
      rho' = Idle (state ts') ->
      required_ok xs pi' -> TMap.find t pi' = Some newls ->
      Exposed t newls
        (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair ts' xs) rho' pi').
    Proof.
      intros Hold Erho Hreq Hfind.
      subst rho'.
      apply Exposed_intro_observed; [exact Hreq|exact Hfind|].
      pose proof (Exposed_owner_distinct t oldls _ Hold) as Howner.
      simpl in Howner. exact Howner.
    Qed.

    Lemma LinMapsto_exclusive t ls1 ls2 :
      forall s, ~ (LinMapsto t ls1 * LinMapsto t ls2)%Assertion s.
    Proof.
      intros s [s1 [s2 [Hjoin [H1 H2]]]].
      destruct s1 as [us1 os1 lm1], s2 as [us2 os2 lm2],
        s as [us os lm].
      unfold LinMapsto in H1, H2.
      destruct H1 as [_ [_ Hπ1]], H2 as [_ [_ Hπ2]].
      destruct Hjoin as [_ [_ Hπ]]. simpl in *. subst.
      eapply (linmap_join_exclusive lm1 lm2 lm Hπ t ls1 ls2).
      - specialize (Hπ1 t). rewrite PositiveMap.gss in Hπ1.
        symmetry; exact Hπ1.
      - specialize (Hπ2 t). rewrite PositiveMap.gss in Hπ2.
        symmetry; exact Hπ2.
    Qed.

    Lemma offered_cell_excludes_local t v ls :
      ⊨ (Required (ExSOffered t v) * LinMapsto t ls) ==>> FF.
    Proof.
      intros s H.
      exfalso. eapply LinMapsto_exclusive. exact H.
    Qed.

    Lemma paired_offerer_cell_excludes_local_push_pop t a t2 ls :
      ⊨ (Required (ExSPaired t (Some a) t2 None) *
          LinMapsto t ls) ==>> FF.
    Proof.
      intros s H.
      exfalso. eapply LinMapsto_exclusive. exact H.
    Qed.

    Lemma paired_offerer_cell_excludes_local_pop_push t t2 a ls :
      ⊨ (Required (ExSPaired t None t2 (Some a)) *
          LinMapsto t ls) ==>> FF.
    Proof.
      intros s H.
      exfalso. eapply LinMapsto_exclusive. exact H.
    Qed.

    (** Absorbing an explicit local cell changes only the residual map. *)
    Lemma LinOwn_absorb lm :
      ⊨ (LinOwn lm * True_pi) ==>> True_pi.
    Proof.
      intros s [s1 [s2 [Hjoin [Hlm [lm2 Hlm2]]]]].
      exists (π s).
      destruct s1 as [[ts1 xs1] os1 pi1],
        s2 as [[ts2 xs2] os2 pi2],
        s as [[ts xs] os pi].
      unfold LinOwn in Hlm, Hlm2. simpl in *.
      destruct Hlm as [Hσ1 [Hρ1 Hπ1]],
        Hlm2 as [Hσ2 [Hρ2 Hπ2]].
      inversion Hσ1; inversion Hσ2; subst.
      subst.
      destruct Hjoin as [[Ht Hx] [Hρ Hπ]]. simpl in *.
      pose proof (@join_unit_left_inv _ try_Join try_SA try_unit
        try_empty ts Ht) as Et.
      pose proof (@join_unit_left_inv _ exch_Join exch_SA exch_unit
        exch_empty xs Hx) as Ex.
      pose proof (@join_unit_left_inv _ stack_Join stack_SA stack_unit
        stack_empty os Hρ) as Eρ.
      subst. unfold LinOwn, lin_equiv; simpl; auto.
    Qed.

    Lemma LinMapsto_absorb t ls :
      ⊨ (LinMapsto t ls * True_pi) ==>> True_pi.
    Proof.
      eapply ImplTrans; [|apply LinOwn_absorb].
      eapply sepcon_mono; [|apply ImplRefl].
      intros s H; exact H.
    Qed.

    Lemma Active_entails_I t m :
      ⊨ Active t m ==>> I.
    Proof.
      unfold Active, I.
      intros s H.
      apply sepcon_assoc2 in H.
      eapply sepcon_mono; [apply ImplRefl| |exact H].
      apply LinMapsto_absorb.
    Qed.

    Lemma Exposed_entails_I t ls :
      ⊨ Exposed t ls ==>> I.
    Proof.
      unfold Exposed, I. intros s H. apply sepcon_assoc2 in H.
      eapply sepcon_mono; [apply ImplRefl| |exact H].
      apply LinMapsto_absorb.
    Qed.

    Lemma ExchangeReady_entails_I t v :
      ⊨ ExchangeReady t v ==>> I.
    Proof.
      intros s Hready. destruct Hready as
        [s0 HI E0
        |t2 v2 s0 Hneq Hcomp HI E0
        |t2 v2 s0 Hneq Hsame Hlocal E0
        |t1 v1 s0 Hneq Hcomp Hlocal E0
        |t1 v1 s0 Hneq Hsame Hlocal E0
        |t1 v1 s0 Hneq Hcomp Hlocal E0
        |t1 v1 s0 Hneq Hsame Hlocal E0].
      - exact HI.
      - exact HI.
      - exact Hlocal.
      - eapply Exposed_entails_I; exact Hlocal.
      - eapply Exposed_entails_I; exact Hlocal.
      - eapply Exposed_entails_I; exact Hlocal.
      - eapply Exposed_entails_I; exact Hlocal.
    Qed.

    Lemma Completed_entails_I t m ret :
      ⊨ Completed t m ret ==>> I.
    Proof.
      unfold Completed, I.
      intros s H.
      apply sepcon_assoc2 in H.
      eapply sepcon_mono; [apply ImplRefl| |exact H].
      apply LinMapsto_absorb.
    Qed.

    Lemma exposed_cell_ALin P t ls s :
      (((P * LinMapsto t ls) * True_pi)%Assertion s) ->
      ALin t ls s.
    Proof.
      intros [owned [frame [Hwhole [[shared [cell [Howned [_ Hcell]]]] _]]]].
      destruct s as [us os pi], owned as [uso oso pio],
        shared as [uss oss pis], cell as [usc osc pic].
      destruct Hwhole as [_ [_ Hpi_whole]], Howned as [_ [_ Hpi_owned]].
      unfold LinMapsto, lin_equiv in Hcell; simpl in Hcell.
      destruct Hcell as [_ [_ Hcell]].
      assert (TMap.find t pic = Some ls) as Hfind_cell.
      { specialize (Hcell t). rewrite TMap.gss in Hcell. symmetry; exact Hcell. }
      pose proof (linmap_join_find_right _ _ _ Hpi_owned t ls Hfind_cell)
        as Hfind_owned.
      exact (linmap_join_find_left _ _ _ Hpi_whole t ls Hfind_owned).
    Qed.

    Lemma Active_ALin t m :
      ⊨ Active t m ==>> ALin t (ls_inv m).
    Proof. intros s H; eapply exposed_cell_ALin; exact H. Qed.

    Lemma Completed_ALin t m ret :
      ⊨ Completed t m ret ==>> ALin t (ls_linr m ret).
    Proof. intros s H; eapply exposed_cell_ALin; exact H. Qed.

    Lemma Exposed_ALin t ls :
      ⊨ Exposed t ls ==>> ALin t ls.
    Proof. intros s H; eapply exposed_cell_ALin; exact H. Qed.

    Lemma preserve_exposed (t : tid) (ls : lin_state)
        (s s' : @ProofStateSingle _ _ (li_lts E) (li_lts F)) :
      I s' -> snd (σ s) = snd (σ s') ->
      TMap.find t (π s) = TMap.find t (π s') ->
      Exposed t ls s -> Exposed t ls s'.
    Proof.
      intros HI Hσ Hfind Hexp.
      eapply I_ALin_exposes.
      - exact HI.
      - unfold ALin. rewrite <- Hfind. eapply Exposed_ALin; exact Hexp.
      - rewrite <- Hσ. eapply Exposed_owner_distinct; exact Hexp.
    Qed.

    (** Returning a completed method removes only its exposed local cell.
        The state-dependent cell in [IExch], if present, has a different
        owner and is reconstructed spatially. *)
    Lemma gret_closes_completed t m ret s s' :
      Completed t m ret s -> Gret t m ret s s' -> I s'.
    Proof.
      intros Hcompleted Hgret.
      pose proof (Completed_entails_I t m ret s Hcompleted) as HI.
      destruct (I_observe s HI) as [ts [xs [Eσ [Eρ Hreq]]]].
      pose proof (Completed_owner_distinct t m ret s Hcompleted) as Hother.
      unfold Gret, LiftRelation_π in Hgret.
      destruct Hgret as [Hσ [Hρ [Hfind Hremove]]].
      destruct s as [us os pi], s' as [us' os' pi']; simpl in *.
      subst us' os' pi'. inversion Eσ; subst.
      assert (required_ok xs (TMap.remove t pi)) as Hreq'.
      { eapply required_ok_remove_other; eauto. }
      destruct xs as [tr v|t1 v1 t2 v2|t1 v1 t2 v2|].
      - eapply I_intro_required_cell with
          (tr := tr) (ls := offered_token v).
        + apply Required_offered.
        + exact Hreq'.
      - destruct v1 as [a1|], v2 as [a2|].
        + eapply I_intro_required_cell with
            (tr := t1) (ls := offered_token (Some a1)).
          * apply Required_paired_push_push.
          * exact Hreq'.
        + eapply I_intro_required_cell with
            (tr := t1) (ls := done_token (Some a1) None).
          * apply Required_paired_push_pop.
          * exact Hreq'.
        + eapply I_intro_required_cell with
            (tr := t1) (ls := done_token None (Some a2)).
          * apply Required_paired_pop_push.
          * exact Hreq'.
        + eapply I_intro_required_cell with
            (tr := t1) (ls := offered_token None).
          * apply Required_paired_pop_pop.
          * exact Hreq'.
      - eapply I_intro_no_required; apply Required_accepted.
      - eapply I_intro_no_required; apply Required_idle.
    Qed.

    Lemma I_has_exact_shape :
      ⊨ I <<==>> ((IStack * IExch) * True_pi).
    Proof. split; apply ImplRefl. Qed.


    Lemma initial_I :
      I (@Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair try_empty exch_empty) stack_empty (@TMap.empty lin_state)).
    Proof.
      set (e := @Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        (pair try_empty exch_empty) stack_empty (@TMap.empty lin_state)).
      change (((IStack * IExch) * True_pi)%Assertion e).
      exists e, e. split.
      - exact (@unit_join _ proof_Join proof_SA proof_unit e).
      - split.
        + exists e, e. split.
          * exact (@unit_join _ proof_Join proof_SA proof_unit e).
          * split.
            -- exists try_empty. unfold TryOwn; simpl. auto.
            -- exists ExSIdle.
               change ((ExchStateOwn ExSIdle * Required ExSIdle)%Assertion e).
               exists e, e. split.
               ++ exact (@unit_join _ proof_Join proof_SA proof_unit e).
               ++ split.
                  { unfold ExchStateOwn; simpl. auto. }
                  { exact (@unit_spec _ proof_Join proof_SA proof_unit). }
        + exists (@TMap.empty lin_state).
          unfold LinOwn, lin_equiv; simpl; auto.
    Qed.

    (** Tensor steps provide the operational frame facts used by the
        direct visible-call proofs. *)
    Lemma try_step_frames_exchanger t op u1 x1 u2 x2 :
      Step (li_lts E)
        (Build_ThreadEvent t (@InvEv (li_sig E) (inl op)))
        (pair u1 x1) (pair u2 x2) -> x1 = x2.
    Proof. eapply TensorSeparation.tensor_left_inv_preserves_right. Qed.

    Lemma exchanger_step_frames_try t op u1 x1 u2 x2 :
      Step (li_lts E)
        (Build_ThreadEvent t (@InvEv (li_sig E) (inr op)))
        (pair u1 x1) (pair u2 x2) -> u1 = u2.
    Proof. eapply TensorSeparation.tensor_right_inv_preserves_left. Qed.

    Lemma try_response_frames_exchanger t op ret u1 x1 u2 x2 :
      Step (li_lts E)
        (Build_ThreadEvent t (@ResEv (li_sig E) (inl op) ret))
        (pair u1 x1) (pair u2 x2) -> x1 = x2.
    Proof. eapply TensorSeparation.tensor_left_res_preserves_right. Qed.

    Lemma exchanger_response_frames_try t op ret u1 x1 u2 x2 :
      Step (li_lts E)
        (Build_ThreadEvent t (@ResEv (li_sig E) (inr op) ret))
        (pair u1 x1) (pair u2 x2) -> u1 = u2.
    Proof. eapply TensorSeparation.tensor_right_res_preserves_left. Qed.

  End Proof.
End EBStackSep.
