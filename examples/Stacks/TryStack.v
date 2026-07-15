Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import PeanoNat.
Require Import List.

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
Require Import examples.Common.Heap.
Require Import examples.Common.MemSpec.
Require Import examples.Common.OwnedMemSpec.
Require Import examples.CAS.CASRegSpec.
Require Import examples.Stacks.StackSpec.


Module TryStackImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS TryStackSpec MemSpec OwnedMemSpec OwnedMemSpec.WriteOwnedMem CASRegSpec.
  Import ListNotations.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.

  Definition ECASLayer : layer_interface :=
  {|
    li_sig := ECASReg (option Addr);
    li_lts := VCASReg;
    li_init := Idle None;
  |}.

  Definition EMemLayer : layer_interface :=
    @OwnedMemSpec.WriteOwnedMemLayer.F (A * option Addr).

  Definition E : layer_interface := ECASLayer ⊗ₗ EMemLayer.
  
  Definition F : layer_interface :=
  {|
    li_sig := ETryStack A;
    li_lts := VTryStack;
    li_init := Idle nil
  |}.

  Definition cas_op := Sig.op (ECASReg (option Addr)).
  Definition mem_op := Sig.op (EMem (A * option Addr)).
  Definition in_cas := @inl cas_op mem_op.
  Definition in_mem := @inr cas_op mem_op.
  
  Definition push_impl (v : A) (_ : tid) : Prog (li_sig E) (TryResult unit) :=
    in_cas get >= oldPtr =>
    in_mem malloc >= newLoc =>
    in_mem (mwrite newLoc (v, oldPtr)) >= _ =>
    in_cas (cas oldPtr (Some newLoc)) >= succ =>
    Ret (if succ then (OK tt) else FAIL).

  Definition pop_impl (_ : tid) : Prog (li_sig E) (TryResult (option A)) :=
    in_cas get >= oldPtr =>
    match oldPtr with
    | Some oldLoc =>
        in_mem (mread oldLoc) >= head =>
        in_cas (cas oldPtr (snd head)) >= succ =>
        Ret (if succ then (OK (Some (fst head))) else FAIL)
    | None => Ret (OK None)
    end.

  Inductive listseg (h : @Heap ((A * option Addr)%type)) : option Addr -> list A -> Prop :=
  | listseg_nil :
      listseg h None nil
  | listseg_cons l v nxt vs :
      h l = Some (v, nxt) ->
      listseg h nxt vs ->
      listseg h (Some l) (v :: vs).

  Inductive listseg_loc
    (h : @Heap ((A * option Addr)%type)) (loc : @Heap LocStat) :
    option Addr -> list A -> Prop :=
  | listseg_loc_nil :
      listseg_loc h loc None nil
  | listseg_loc_cons l v nxt vs :
      h l = Some (v, nxt) ->
      loc l = Some LWritten ->
      listseg_loc h loc nxt vs ->
      listseg_loc h loc (Some l) (v :: vs).

  Lemma listseg_defined h l vs :
    listseg h (Some l) vs -> exists v nxt vs', vs = v :: vs' /\ h l = Some (v, nxt) /\ listseg h nxt vs'.
  Proof.
    remember (Some l) as top eqn:Heq.
    intros Hls. revert l Heq.
    induction Hls; intros; inversion Heq; subst.
    exists v, nxt, vs. auto.
  Qed.

  Lemma listseg_update_fresh h top vs l v nxt :
    listseg h top vs ->
    h l = None ->
    listseg (heap_update l (v, nxt) h) top vs.
  Proof.
    intros Hls Hfresh.
    induction Hls.
    - econstructor.
    - econstructor.
      {
        unfold heap_update.
        destruct (Nat.eqb l l0) eqn:Heq.
        - apply Nat.eqb_eq in Heq. subst. congruence.
        - exact H.
      }
      { apply IHHls. }
  Qed.

  Lemma listseg_preserved h h' top vs :
    (forall l v, h l = Some v -> h' l = Some v) ->
    listseg h top vs ->
    listseg h' top vs.
  Proof.
    intros Hpres Hls.
    induction Hls.
    - constructor.
    - econstructor; eauto.
  Qed.

	  Lemma listseg_loc_defined h loc l vs :
	    listseg_loc h loc (Some l) vs ->
	    exists v nxt vs',
	      vs = v :: vs' /\
	      h l = Some (v, nxt) /\
	      loc l = Some LWritten /\
	      listseg_loc h loc nxt vs'.
  Proof.
    remember (Some l) as top eqn:Heq.
    intros Hls. revert l Heq.
    induction Hls; intros; inversion Heq; subst.
	    exists v, nxt, vs. auto.
	  Qed.

	  Lemma listseg_loc_none h loc vs :
	    listseg_loc h loc None vs -> vs = nil.
	  Proof.
	    intros Hls. inversion Hls; auto.
	  Qed.

  Lemma listseg_loc_update_alloc h loc top vs l p t :
    listseg_loc h loc top vs ->
    h l = None ->
    listseg_loc
      (heap_update l p h)
      (heap_update l (LAlloc t) loc)
      top vs.
  Proof.
    intros Hls Hfresh.
    induction Hls.
    - constructor.
    - econstructor.
      + unfold heap_update.
        destruct (Nat.eqb l l0) eqn:Heq.
        * apply Nat.eqb_eq in Heq. subst. congruence.
        * exact H.
      + unfold heap_update.
        destruct (Nat.eqb l l0) eqn:Heq.
        * apply Nat.eqb_eq in Heq. subst. congruence.
        * exact H0.
      + apply IHHls.
  Qed.

  Lemma listseg_loc_update_unlinked h loc top vs l p t :
    listseg_loc h loc top vs ->
    loc l = Some (LAlloc t) ->
    listseg_loc
      (heap_update l p h)
      (heap_update l LWritten loc)
      top vs.
  Proof.
    intros Hls Hown.
    induction Hls.
    - constructor.
    - econstructor.
      + unfold heap_update.
        destruct (Nat.eqb l l0) eqn:Heq.
        * apply Nat.eqb_eq in Heq. subst.
          rewrite H0 in Hown. discriminate.
        * exact H.
      + unfold heap_update.
        destruct (Nat.eqb l l0) eqn:Heq.
        * apply Nat.eqb_eq in Heq. subst.
          rewrite H0 in Hown. discriminate.
        * exact H0.
      + apply IHHls.
  Qed.

  Definition assertion := @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.

  Definition cas_state (s : State (li_lts E)) : option Addr :=
    state (fst s).

  Definition mem_state (s : State (li_lts E)) : @Heap ((A * option Addr)%type) :=
    om_heap (state (snd s)).

  Definition loc_state (s : State (li_lts E)) : @Heap LocStat :=
    om_loc (state (snd s)).

  Definition pending_write_owned (s : State (li_lts E)) : Prop :=
    match snd s with
    | Pending mem t (mwrite l _) => om_loc mem l = Some (LAlloc t)
    | _ => True
    end.

  Definition loc_defined (s : State (li_lts E)) : Prop :=
    forall l st, loc_state s l = Some st -> exists p, mem_state s l = Some p.

  Definition written_heap_preserved (s1 s2 : State (li_lts E)) : Prop :=
    forall l v,
      loc_state s1 l = Some LWritten ->
      mem_state s1 l = Some v ->
      loc_state s2 l = Some LWritten /\
      mem_state s2 l = Some v.

  Definition owned_preserved_for (t : tid) (s1 s2 : State (li_lts E)) : Prop :=
    forall l v,
      loc_state s1 l = Some (LAlloc t) ->
      mem_state s1 l = Some v ->
      loc_state s2 l = Some (LAlloc t) /\
      mem_state s2 l = Some v.

  Definition I : assertion :=
    fun s => exists stk,
      ρ s = Idle stk /\
      listseg_loc (mem_state (σ s)) (loc_state (σ s)) (cas_state (σ s)) stk /\
      pending_write_owned (σ s) /\
      loc_defined (σ s).

	  Definition HCell l p : assertion :=
	    fun s =>
	      mem_state (σ s) l = Some p /\
	      loc_state (σ s) l = Some LWritten.

	  Definition HWritten l : assertion :=
	    fun s => exists p, HCell l p s.

  Definition HAlloc l : assertion :=
    fun s => exists p, mem_state (σ s) l = Some p.

  Definition HOwned t l : assertion :=
    fun s => exists p,
      mem_state (σ s) l = Some p /\
      loc_state (σ s) l = Some (LAlloc t).

  Definition TopIs top : assertion :=
    fun s => cas_state (σ s) = top.

  Definition G t : rg_relation :=
    fun s1 s2 =>
      I s2 /\
      written_heap_preserved (σ s1) (σ s2) /\
      (forall t', t <> t' -> owned_preserved_for t' (σ s1) (σ s2)) /\
      (forall t', t <> t' -> TMap.find t' (π s1) = TMap.find t' (π s2)).

  Definition R t : rg_relation :=
    fun s1 s2 =>
      written_heap_preserved (σ s1) (σ s2) /\
      owned_preserved_for t (σ s1) (σ s2) /\
      TMap.find t (π s1) = TMap.find t (π s2).

  Lemma Istable {t} : Stable (R t) I I.
  Proof.
    unfold Stable. apply ConjRightImpl, ImplRefl.
  Qed.

  Lemma ALinstable {t ls}: Stable (R t) I (ALin t ls).
  Proof.
    unfold Stable, ALin, R.
    intros ? [[? [? [? [? ?]]]] ?].
    rewrite <- H2. auto.
  Qed.

  Lemma HCellStable {t l p}: Stable (R t) I (HCell l p).
  Proof.
    unfold Stable, R, HCell, written_heap_preserved.
    intros s Hstable.
    destruct Hstable as [[x [[Hmem Hloc] [Hwritten [Howned Hpi]]]] HI].
    specialize (Hwritten l p Hloc Hmem) as [Hloc' Hmem'].
    split; auto.
  Qed.

	  Lemma HOwnedStable {t l}: Stable (R t) I (HOwned t l).
	  Proof.
	    unfold Stable, R, HOwned, owned_preserved_for.
	    intros s Hstable.
	    destruct Hstable as [[x [[p [Hmem Hloc]] [Hwritten [Howned Hpi]]]] HI].
	    specialize (Howned l p Hloc Hmem) as [Hloc' Hmem'].
	    exists p. auto.
	  Qed.

	  Lemma HWrittenStable {t l}: Stable (R t) I (HWritten l).
	  Proof.
	    unfold Stable, HWritten.
	    intros s [[x [[p Hcell] Hrel]] HI].
	    exists p.
	    eapply HCellStable.
	    split; [exists x; split; eauto|auto].
	  Qed.

	  Create HintDb stableDB.
	  Hint Resolve Istable ALinstable HCellStable HOwnedStable HWrittenStable : stableDB.

  Ltac pupdate_intros_atomic' :=
    red;
    intros σ1 ρ1 π1 Hpre σ2 Hstep;
    try destruct σ1, σ2;
    try inversion_step;
    try (inversion Hstep; subst);
    try inversion_thread_event_eq;
    repeat match goal with
    | H : existT _ _ _ = existT _ _ _ |- _ =>
      dependent destruction H
    end.

  Lemma IGinv : forall t f, ⊨ Ginv t f ⊚ I ==>> I //\\ ALin t (Semantics.ls_inv f).
  Proof.
    unfold I, ALin.
    intros ? ? [? ?] [[? ?] [? [? [? [? ?]]]]]; simpl in *; subst.
    split; auto; simpl in *.
    rewrite PositiveMap.gss; auto.
  Qed.

  Lemma IGret : forall t f ret,
    ⊨ Gret t f ret ⊚ (I //\\ ALin t (Semantics.ls_linr f ret)) ==>> I.
  Proof.
    unfold I, ALin, Gret, LiftRelation_π.
    intros. intros [? [[? ?] ?]].
    destruct H1 as [? [? [? ?]]].
    destruct s, x; simpl in *; subst. auto.
  Qed.

  Lemma pupdate_cas_get_inv_push t v :
    PUpdate (G t) {| te_tid := t; te_ev := InvEv (in_cas get) |}
      (I //\\ ALin t (Semantics.ls_inv (push v)))
      (I //\\ ALin t (Semantics.ls_inv (push v))).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hcas Hmem]; subst.
    inversion Hcas; subst.
    dependent destruction Hstep.
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    { unfold Conj, I, ALin in *; simpl in *.
      firstorder eauto. }
    { unfold G, written_heap_preserved, owned_preserved_for, Conj, I, ALin in *; simpl in *.
      firstorder eauto. }
  Qed.

  Lemma pupdate_cas_get_res_push t v ret :
    PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_cas get) ret |}
      (I //\\ ALin t (Semantics.ls_inv (push v)))
      (I //\\ ALin t (Semantics.ls_inv (push v))).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hcas Hmem]; subst.
    inversion Hcas; subst.
    dependent destruction Hstep.
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    { unfold Conj, I, ALin in *; simpl in *.
      firstorder eauto. }
    { unfold G, written_heap_preserved, owned_preserved_for, Conj, I, ALin in *; simpl in *.
      firstorder eauto. }
  Qed.

  Lemma pupdate_malloc_inv_push t v :
    PUpdate (G t) {| te_tid := t; te_ev := InvEv (in_mem malloc) |}
      (I //\\ ALin t (Semantics.ls_inv (push v)))
      (I //\\ ALin t (Semantics.ls_inv (push v))).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hmem Hcas]; subst.
    inversion Hmem; subst.
    dependent destruction Hstep.
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    { unfold Conj, I, ALin in *; simpl in *.
      firstorder eauto. }
    { unfold G, written_heap_preserved, owned_preserved_for, Conj, I, ALin in *; simpl in *.
      firstorder eauto. }
  Qed.

  Lemma malloc_res_step t (h h' : OwnedMemState ((A * option Addr)%type)) ret :
    StepMem {| te_tid := t; te_ev := ResEv malloc ret |} h h' ->
    exists init : (A * option Addr)%type,
      om_heap h ret = None /\
      h' = {| om_heap := heap_update ret init (om_heap h);
              om_loc := heap_update ret (LAlloc t) (om_loc h) |}.
  Proof.
    intros Hstep.
    inversion Hstep; subst; try inversion_thread_event_eq.
    dependent destruction H3.
    eexists; split; eauto.
  Qed.

  Lemma pupdate_malloc_res_push t v newLoc :
    PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_mem malloc) newLoc |}
      (I //\\ ALin t (Semantics.ls_inv (push v)))
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HOwned t newLoc).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hmem Hcas]; subst.
    inversion Hmem; subst.
    dependent destruction H2.
    eapply malloc_res_step in Hstep as [[av an] [Hfresh Hupd]]; subst.
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    {
      unfold Conj, I, ALin, HOwned in *; simpl in *.
      destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] Hlin].
      split.
      - exists stk. repeat split; auto.
        + eapply listseg_loc_update_alloc; eauto.
        + unfold loc_defined in *; simpl in *.
          intros l st Hloc.
          unfold heap_update in *.
          destruct (Nat.eqb newLoc l) eqn:Heq.
          * exists (av, an). unfold mem_state; simpl. rewrite Heq. reflexivity.
          * assert (Holdloc : loc_state (cas', Pending s1 t malloc) l = Some st).
            { unfold loc_state in *; simpl in *. rewrite Heq in Hloc. exact Hloc. }
            destruct (Hdef l st Holdloc) as [p Hp].
            exists p. unfold mem_state in *; simpl in *. rewrite Heq. exact Hp.
      - split; auto.
        exists (av, an). split; apply HeapUpdateSelf.
    }
    {
      unfold G, written_heap_preserved, owned_preserved_for, Conj, I, ALin, HOwned in *; simpl in *.
      destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] Hlin].
      split.
      - exists stk. repeat split; auto.
        + eapply listseg_loc_update_alloc; eauto.
        + unfold loc_defined in *; simpl in *.
          intros l st Hloc.
          unfold heap_update in *.
          destruct (Nat.eqb newLoc l) eqn:Heq.
          * exists (av, an). unfold mem_state; simpl. rewrite Heq. reflexivity.
          * assert (Holdloc : loc_state (cas', Pending s1 t malloc) l = Some st).
            { unfold loc_state in *; simpl in *. rewrite Heq in Hloc. exact Hloc. }
            destruct (Hdef l st Holdloc) as [p Hp].
            exists p. unfold mem_state in *; simpl in *. rewrite Heq. exact Hp.
      - split.
        + intros l0 p HlocW Hsome.
          unfold heap_update.
          destruct (Nat.eqb newLoc l0) eqn:Heq.
          * apply Nat.eqb_eq in Heq. subst.
            specialize (Hdef l0 LWritten HlocW) as [pold Hpold].
            unfold mem_state in Hpold; simpl in Hpold.
            rewrite Hfresh in Hpold. discriminate.
          * unfold loc_state, mem_state in *. simpl in *.
            rewrite Heq. split; auto.
        + split.
          * unfold owned_preserved_for, loc_state, mem_state, loc_defined in *; simpl in *.
            intros t' Hneq l0 p0 Hloc Hheap0.
            unfold heap_update in *.
            destruct (Nat.eqb newLoc l0) eqn:Heq.
            -- apply Nat.eqb_eq in Heq. subst.
               specialize (Hdef l0 (LAlloc t') Hloc) as [p Hp].
               unfold mem_state in Hp; simpl in Hp.
               rewrite Hfresh in Hp. discriminate.
            -- split; auto.
          * intros; auto.
    }
  Qed.

  Lemma pupdate_mwrite_inv_push t v oldPtr newLoc :
    PUpdate (G t) {| te_tid := t; te_ev := InvEv (in_mem (mwrite newLoc (v, oldPtr))) |}
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HOwned t newLoc)
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HOwned t newLoc).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hmem Hcas]; subst.
    inversion Hmem; subst.
    dependent destruction Hstep.
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    {
      unfold Conj, I, ALin, HOwned, mem_state, loc_state in *; simpl in *.
      destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] [Hlin [p [Hheap Hloc]]]].
      split.
      - exists stk. repeat split; auto.
      - split; auto. exists p. auto.
    }
    {
      unfold G, written_heap_preserved, owned_preserved_for, Conj, I, ALin, HOwned,
        mem_state, loc_state in *; simpl in *.
      destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] [Hlin [p [Hheap Hloc]]]].
      repeat split; auto.
      exists stk. repeat split; auto.
    }
  Qed.

  Lemma pupdate_mwrite_res_push t v oldPtr newLoc :
    PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_mem (mwrite newLoc (v, oldPtr))) tt |}
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HOwned t newLoc)
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HCell newLoc (v, oldPtr)).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hmem Hcas]; subst.
    inversion Hmem; subst.
    dependent destruction Hstep.
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    {
      unfold Conj, I, ALin, HOwned, HCell, mem_state, loc_state in *; simpl in *.
      destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] [Hlin [p [Hheap Hloc]]]].
      repeat split; auto.
      - exists stk. repeat split; auto.
        + eapply listseg_loc_update_unlinked; eauto.
        + unfold loc_defined in *; simpl in *.
          intros l0 st Hloc'.
          unfold heap_update in *.
          destruct (Nat.eqb newLoc l0) eqn:Heq.
          * exists (v, oldPtr). unfold mem_state; simpl. rewrite Heq. reflexivity.
          * unfold loc_state in *; simpl in *.
            rewrite Heq in Hloc'.
            destruct (Hdef l0 st Hloc') as [p' Hp].
            exists p'. unfold mem_state in *; simpl in *. rewrite Heq. exact Hp.
      - unfold heap_update. rewrite Nat.eqb_refl. reflexivity.
      - unfold heap_update. rewrite Nat.eqb_refl. reflexivity.
    }
    {
      unfold G, written_heap_preserved, owned_preserved_for, Conj, I, ALin, HOwned, HCell,
        mem_state, loc_state in *; simpl in *.
      destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] [Hlin [p [Hheap Hloc]]]].
      split.
      - exists stk. repeat split; auto.
        + eapply listseg_loc_update_unlinked; eauto.
        + unfold loc_defined in *; simpl in *.
          intros l0 st Hloc'.
          unfold heap_update in *.
          destruct (Nat.eqb newLoc l0) eqn:Heq.
          * exists (v, oldPtr). unfold mem_state; simpl. rewrite Heq. reflexivity.
          * unfold loc_state in *; simpl in *.
            rewrite Heq in Hloc'.
            destruct (Hdef l0 st Hloc') as [p' Hp].
            exists p'. unfold mem_state in *; simpl in *. rewrite Heq. exact Hp.
      - split.
        + intros l1 p' HlocW Hsome.
          unfold heap_update in *.
          destruct (Nat.eqb newLoc l1) eqn:Heq.
          * apply Nat.eqb_eq in Heq. subst.
            rewrite Hloc in HlocW. discriminate.
          * split; auto.
        + split.
          * intros t' Hneq l1 p' Hloc' Hsome.
            unfold heap_update in *.
            destruct (Nat.eqb newLoc l1) eqn:Heq.
            -- apply Nat.eqb_eq in Heq. subst.
               rewrite Hloc in Hloc'. inversion Hloc'. tauto.
            -- split; auto.
          * intros; auto.
    }
  Qed.

  Lemma pupdate_cas_push_inv t v oldPtr newLoc :
    PUpdate (G t) {| te_tid := t; te_ev := InvEv (in_cas (cas oldPtr (Some newLoc))) |}
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HCell newLoc (v, oldPtr))
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HCell newLoc (v, oldPtr)).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hcas Hmem]; subst.
    inversion Hcas; subst.
    inversion Hstep; subst; try inversion_thread_event_eq.
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    {
      unfold Conj, I, ALin, HCell in *; simpl in *.
      destruct Hpre as [HI [Hlin Hcell]].
      split; [exact HI|split; auto].
    }
    {
      unfold G, written_heap_preserved, owned_preserved_for, Conj, I, ALin, HCell in *; simpl in *.
      destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] [Hlin Hcell]].
      repeat split; auto.
      exists stk. repeat split; auto.
    }
  Qed.

  Lemma pupdate_cas_push_res t v oldPtr newLoc succ :
    PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_cas (cas oldPtr (Some newLoc))) succ |}
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HCell newLoc (v, oldPtr))
	      (I //\\
	        match succ with
	        | true => ALin t (Semantics.ls_linr (push v) (OK tt))
	        | false => ALin t (Semantics.ls_linr (push v) FAIL)
	        end).
  Proof.
    destruct succ.
    - unfold PUpdate.
      intros σ0 ρ0 π0 Hpre σ' Hstep.
      destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
      destruct Hstep as [Hcas Hmem]; subst.
      inversion Hcas; subst; try inversion_thread_event_eq.
      dependent destruction Hstep; try inversion_thread_event_eq.
      unfold Conj, I, ALin, HCell in Hpre; simpl in *.
      destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] [Hlin [Hcell Hwritten]]].
      subst ρ0.
      exists (Idle (v :: stk)),
        (TMap.add t0 (Semantics.ls_linr (push v) (OK tt))
          (TMap.add t0 (Semantics.ls_lini (push v)) π0)).
      split.
      {
        eapply rt_trans.
        - eapply rt_step. eapply Semantics.ps_inv.
          + constructor. econstructor. reflexivity.
          + exact Hlin.
        - eapply rt_step. eapply Semantics.ps_ret.
          + constructor. econstructor. reflexivity.
          + rewrite PositiveMap.gss. auto.
      }
      split.
      + unfold I, ALin; simpl.
        split.
        * exists (v :: stk). split; auto.
          split.
          -- econstructor; eauto.
          -- split; auto.
        * cbn. rewrite PositiveMap.gss. auto.
      + unfold G, written_heap_preserved, owned_preserved_for, I; simpl.
        split.
        * exists (v :: stk). split; auto.
          split.
          -- econstructor; eauto.
          -- split; auto.
        * split.
          -- intros l0 p HlocW Hmem0. split; auto.
          -- split.
             ++ intros t' Hneq l0 p HlocO Hmem0. split; auto.
             ++ intros t' Hneq.
                do 2 (rewrite PositiveMap.gso by congruence).
                reflexivity.
      + dependent destruction H2.
    - unfold PUpdate.
      intros σ0 ρ0 π0 Hpre σ' Hstep.
      destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
      destruct Hstep as [Hcas Hmem]; subst.
      inversion Hcas; subst; try inversion_thread_event_eq.
      dependent destruction Hstep.
      + dependent destruction H2.
      + unfold Conj, I, ALin, HCell in Hpre; simpl in *.
        destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] [Hlin Hcell]].
        subst ρ0.
        exists (Idle stk),
          (TMap.add t0 (Semantics.ls_linr (push v) FAIL)
            (TMap.add t0 (Semantics.ls_lini (push v)) π0)).
        split.
        {
          eapply rt_trans.
          - eapply rt_step. eapply Semantics.ps_inv.
            + constructor. econstructor. reflexivity.
            + exact Hlin.
          - eapply rt_step. eapply Semantics.ps_ret.
            + constructor. eapply step_push_fail. reflexivity.
            + rewrite PositiveMap.gss. auto.
        }
        split.
        * unfold I, ALin; simpl.
          split.
          -- exists stk. repeat split; auto.
          -- cbn. rewrite PositiveMap.gss. auto.
        * unfold G, written_heap_preserved, owned_preserved_for, I; simpl.
          split.
          -- exists stk. repeat split; auto.
          -- split.
             ++ intros l0 p HlocW Hmem0. split; auto.
             ++ split.
                ** intros t' Hneq l0 p HlocO Hmem0. split; auto.
                ** intros t' Hneq.
                   do 2 (rewrite PositiveMap.gso by congruence).
                   reflexivity.
  Qed.

  Lemma mwrite_racy_error t t' c h l l' v v' :
    t <> t' ->
    l = l' ->
    Error (li_lts E)
      {| te_tid := t; te_ev := InvEv (in_mem (mwrite l v)) |}
      (c, Pending h t' (mwrite l' v')).
  Proof.
    intros Hneq Heq. simpl.
    eapply error_write_racy; eauto.
  Qed.

	  Lemma mwrite_owned_no_error t l v :
	    ⊨ I //\\ HOwned t l ==>>
	      ANoError {| te_tid := t; te_ev := InvEv (in_mem (mwrite l v)) |}.
  Proof.
    unfold I, HOwned, ANoError.
    intros [σ0 ρ0 π0] [[stk [Hr [Hls [Hpend Hdef]]]] [p [Hheap Hloc]]] Herror.
    destruct σ0 as [cas mem]; simpl in *.
    inversion Herror; subst;
      repeat match goal with
      | H : {| te_tid := _; te_ev := _ |} = {| te_tid := _; te_ev := _ |} |- _ =>
          inversion H; subst; clear H
      | H : InvEv _ = InvEv _ |- _ =>
          inversion H; subst; clear H
      end;
      unfold mem_state, loc_state in *; simpl in *;
	      try solve [congruence].
	  Qed.

	  Lemma mread_written_no_error t l :
	    ⊨ HWritten l ==>>
	      ANoError {| te_tid := t; te_ev := InvEv (in_mem (mread l)) |}.
	  Proof.
	    unfold HWritten, HCell, ANoError.
	    intros [σ0 ρ0 π0] [p [Hheap Hloc]] Herror.
	    destruct σ0 as [cas mem]; simpl in *.
	    inversion Herror; subst;
	      repeat match goal with
	      | H : {| te_tid := _; te_ev := _ |} = {| te_tid := _; te_ev := _ |} |- _ =>
	          inversion H; subst; clear H
	      | H : InvEv _ = InvEv _ |- _ =>
	          inversion H; subst; clear H
	      end;
	      unfold mem_state in *; simpl in *;
	      try solve [congruence].
	  Qed.

	  Lemma cas_get_no_error t (P : assertion) :
	    ⊨ P ==>>
	      ANoError {| te_tid := t; te_ev := InvEv (in_cas get) |}.
	  Proof.
	    unfold ANoError.
	    intros [σ0 ρ0 π0] _ Herror.
	    destruct σ0 as [cas mem]; simpl in *.
	    inversion Herror; subst; inversion_thread_event_eq.
	  Qed.

	  Lemma cas_cas_no_error t old new (P : assertion) :
	    ⊨ P ==>>
	      ANoError {| te_tid := t; te_ev := InvEv (in_cas (cas old new)) |}.
	  Proof.
	    unfold ANoError.
	    intros [σ0 ρ0 π0] _ Herror.
	    destruct σ0 as [cas0 mem]; simpl in *.
	    inversion Herror; subst; inversion_thread_event_eq.
	  Qed.

	  Lemma malloc_no_error t (P : assertion) :
	    ⊨ P ==>>
	      ANoError {| te_tid := t; te_ev := InvEv (in_mem malloc) |}.
	  Proof.
	    unfold ANoError.
	    intros [σ0 ρ0 π0] _ Herror.
	    destruct σ0 as [cas mem]; simpl in *.
	    inversion Herror; subst; inversion_thread_event_eq.
	  Qed.

	  Lemma pupdate_cas_get_inv_pop t :
	    PUpdate (G t) {| te_tid := t; te_ev := InvEv (in_cas get) |}
	      (I //\\ ALin t (Semantics.ls_inv pop))
	      (I //\\ ALin t (Semantics.ls_inv pop)).
	  Proof.
	    unfold PUpdate.
	    intros σ0 ρ0 π0 Hpre σ' Hstep.
	    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
	    destruct Hstep as [Hcas Hmem]; subst.
	    inversion Hcas; subst.
	    dependent destruction Hstep.
	    exists ρ0, π0. split; [apply rt_refl|].
	    split.
	    { unfold Conj, I, ALin in *; simpl in *.
	      firstorder eauto. }
	    { unfold G, written_heap_preserved, owned_preserved_for, Conj, I, ALin in *; simpl in *.
	      firstorder eauto. }
	  Qed.

	  Lemma pupdate_cas_get_res_pop t ret :
	    PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_cas get) ret |}
	      (I //\\ ALin t (Semantics.ls_inv pop))
	      (I //\\
	        match ret with
	        | None => ALin t (Semantics.ls_linr pop (OK None))
	        | Some oldLoc => ALin t (Semantics.ls_inv pop) //\\ HWritten oldLoc
	        end).
	  Proof.
	    destruct ret as [oldLoc|].
	    - unfold PUpdate.
	      intros σ0 ρ0 π0 Hpre σ' Hstep.
	      destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
	      destruct Hstep as [Hcas Hmem]; subst.
	      inversion Hcas; subst.
	      dependent destruction Hstep.
	      dependent destruction H2.
	      unfold Conj, I, ALin in Hpre; simpl in *.
	      destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] Hlin].
	      subst ρ0.
	      exists (Idle stk), π0. split; [apply rt_refl|].
	      split.
	      + unfold I, ALin, HWritten, HCell; simpl.
	        split.
	        * exists stk. repeat split; auto.
	        * split; auto.
	          apply listseg_loc_defined in Hls as [v [nxt [vs [Hstk [Hheap [Hloc Htail]]]]]].
	          exists (v, nxt). split; auto.
	      + unfold G, written_heap_preserved, owned_preserved_for, I; simpl.
	        split.
	        * exists stk. repeat split; auto.
	        * firstorder eauto.
	    - unfold PUpdate.
	      intros σ0 ρ0 π0 Hpre σ' Hstep.
	      destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
	      destruct Hstep as [Hcas Hmem]; subst.
	      inversion Hcas; subst.
	      dependent destruction Hstep.
	      dependent destruction H2.
	      unfold Conj, I, ALin in Hpre; simpl in *.
	      destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] Hlin].
	      apply listseg_loc_none in Hls. subst stk.
	      subst ρ0.
	      exists (Idle nil),
	        (TMap.add t (Semantics.ls_linr pop (OK None))
	          (TMap.add t (Semantics.ls_lini pop) π0)).
	      split.
	      {
	        eapply rt_trans.
	        - eapply rt_step. eapply Semantics.ps_inv.
	          + constructor. eapply step_pop_inv. reflexivity.
	          + exact Hlin.
	        - eapply rt_step. eapply Semantics.ps_ret.
	          + constructor. eapply step_pop_emp. reflexivity.
	          + rewrite PositiveMap.gss. auto.
	      }
	      split.
	      + unfold I, ALin; simpl.
	        split.
	        * exists nil. repeat split; auto. constructor.
	        * cbn. rewrite PositiveMap.gss. auto.
	      + unfold G, written_heap_preserved, owned_preserved_for, I; simpl.
	        split.
	        * exists nil. repeat split; auto. constructor.
	        * split.
	          -- intros l0 p HlocW Hmem0. split; auto.
	          -- split.
	             ++ intros t' Hneq l0 p HlocO Hmem0. split; auto.
	             ++ intros t' Hneq.
	                do 2 (rewrite PositiveMap.gso by congruence).
	                reflexivity.
	  Qed.

	  Lemma pupdate_mread_inv_pop t oldLoc :
	    PUpdate (G t) {| te_tid := t; te_ev := InvEv (in_mem (mread oldLoc)) |}
	      (I //\\ ALin t (Semantics.ls_inv pop) //\\ HWritten oldLoc)
	      (I //\\ ALin t (Semantics.ls_inv pop) //\\ HWritten oldLoc).
	  Proof.
	    unfold PUpdate.
	    intros σ0 ρ0 π0 Hpre σ' Hstep.
	    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
	    destruct Hstep as [Hmem Hcas]; subst.
	    inversion Hmem; subst.
	    dependent destruction Hstep.
	    exists ρ0, π0. split; [apply rt_refl|].
	    split.
	    {
	      unfold Conj, I, ALin, HWritten, HCell in *; simpl in *.
	      destruct Hpre as [HI [Hlin Hwritten]].
	      split; [exact HI|split; auto].
	    }
	    {
	      unfold G, written_heap_preserved, owned_preserved_for, Conj, I, ALin, HWritten, HCell in *; simpl in *.
	      destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] [Hlin Hwritten]].
	      repeat split; auto.
	      exists stk. repeat split; auto.
	    }
	  Qed.

	  Lemma pupdate_mread_res_pop t oldLoc head :
	    PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_mem (mread oldLoc)) head |}
	      (I //\\ ALin t (Semantics.ls_inv pop) //\\ HWritten oldLoc)
	      (I //\\ ALin t (Semantics.ls_inv pop) //\\ HCell oldLoc head).
	  Proof.
	    unfold PUpdate.
	    intros σ0 ρ0 π0 Hpre σ' Hstep.
	    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
	    destruct Hstep as [Hmem Hcas]; subst.
	    inversion Hmem; subst.
	    dependent destruction Hstep.
	    dependent destruction H2.
	    exists ρ0, π0. split; [apply rt_refl|].
	    split.
	    {
	      unfold Conj, I, ALin, HWritten, HCell, mem_state, loc_state in *; simpl in *.
	      destruct Hpre as [HI [Hlin [p [Hheap Hloc]]]].
	      split; [exact HI|].
	      split; auto.
	    }
	    {
	      unfold G, written_heap_preserved, owned_preserved_for, Conj, I, ALin, HWritten, HCell in *; simpl in *.
	      destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] [Hlin Hwritten]].
	      repeat split; auto.
	      exists stk. repeat split; auto.
	    }
	  Qed.

	  Lemma pupdate_cas_pop_inv t oldLoc head :
	    PUpdate (G t) {| te_tid := t; te_ev := InvEv (in_cas (cas (Some oldLoc) (snd head))) |}
	      (I //\\ ALin t (Semantics.ls_inv pop) //\\ HCell oldLoc head)
	      (I //\\ ALin t (Semantics.ls_inv pop) //\\ HCell oldLoc head).
	  Proof.
	    unfold PUpdate.
	    intros σ0 ρ0 π0 Hpre σ' Hstep.
	    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
	    destruct Hstep as [Hcas Hmem]; subst.
	    inversion Hcas; subst.
	    inversion Hstep; subst; try inversion_thread_event_eq.
	    exists ρ0, π0. split; [apply rt_refl|].
	    split.
	    {
	      unfold Conj, I, ALin, HCell in *; simpl in *.
	      destruct Hpre as [HI [Hlin Hcell]].
	      split; [exact HI|split; auto].
	    }
	    {
	      unfold G, written_heap_preserved, owned_preserved_for, Conj, I, ALin, HCell in *; simpl in *.
	      destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] [Hlin Hcell]].
	      repeat split; auto.
	      exists stk. repeat split; auto.
	    }
	  Qed.

	  Lemma pupdate_cas_pop_res t oldLoc v nxt succ :
	    PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_cas (cas (Some oldLoc) nxt)) succ |}
	      (I //\\ ALin t (Semantics.ls_inv pop) //\\ HCell oldLoc (v, nxt))
	      (I //\\
	        match succ with
	        | true => ALin t (Semantics.ls_linr pop (OK (Some v)))
	        | false => ALin t (Semantics.ls_linr pop FAIL)
	        end).
	  Proof.
	    destruct succ.
	    - unfold PUpdate.
	      intros σ0 ρ0 π0 Hpre σ' Hstep.
	      destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
	      destruct Hstep as [Hcas Hmem]; subst.
	      inversion Hcas; subst; try inversion_thread_event_eq.
	      dependent destruction Hstep; try inversion_thread_event_eq.
	      unfold Conj, I, ALin, HCell in Hpre; simpl in *.
	      destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] [Hlin [Hcell Hwritten]]].
	      apply listseg_loc_defined in Hls as [v' [nxt' [vs [Hstk [Hheap [Hloc Htail]]]]]].
	      rewrite Hcell in Hheap. inversion Hheap; subst v' nxt'. clear Hheap.
	      subst stk ρ0.
	      exists (Idle vs),
	        (TMap.add t0 (Semantics.ls_linr pop (OK (Some v)))
	          (TMap.add t0 (Semantics.ls_lini pop) π0)).
	      split.
	      {
	        eapply rt_trans.
	        - eapply rt_step. eapply Semantics.ps_inv.
	          + constructor. eapply step_pop_inv. reflexivity.
	          + exact Hlin.
	        - eapply rt_step. eapply Semantics.ps_ret.
	          + constructor. eapply step_pop_ok. reflexivity.
	          + rewrite PositiveMap.gss. auto.
	      }
	      split.
	      + unfold I, ALin; simpl.
	        split.
	        * exists vs. repeat split; auto.
	        * cbn. rewrite PositiveMap.gss. auto.
	      + unfold G, written_heap_preserved, owned_preserved_for, I; simpl.
	        split.
	        * exists vs. repeat split; auto.
	        * split.
	          -- intros l0 p HlocW Hmem0. split; auto.
	          -- split.
	             ++ intros t' Hneq l0 p HlocO Hmem0. split; auto.
	             ++ intros t' Hneq.
	                do 2 (rewrite PositiveMap.gso by congruence).
	                reflexivity.
	      + dependent destruction H2.
	    - unfold PUpdate.
	      intros σ0 ρ0 π0 Hpre σ' Hstep.
	      destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
	      destruct Hstep as [Hcas Hmem]; subst.
	      inversion Hcas; subst; try inversion_thread_event_eq.
	      dependent destruction Hstep.
	      + dependent destruction H2.
	      + unfold Conj, I, ALin, HCell in Hpre; simpl in *.
	        destruct Hpre as [[stk [Hr [Hls [Hpend Hdef]]]] [Hlin Hcell]].
	        subst ρ0.
	        exists (Idle stk),
	          (TMap.add t0 (Semantics.ls_linr pop FAIL)
	            (TMap.add t0 (Semantics.ls_lini pop) π0)).
	        split.
	        {
	          eapply rt_trans.
	          - eapply rt_step. eapply Semantics.ps_inv.
	            + constructor. eapply step_pop_inv. reflexivity.
	            + exact Hlin.
	          - eapply rt_step. eapply Semantics.ps_ret.
	            + constructor. eapply step_pop_fail. reflexivity.
	            + rewrite PositiveMap.gss. auto.
	        }
	        split.
	        * unfold I, ALin; simpl.
	          split.
	          -- exists stk. repeat split; auto.
	          -- cbn. rewrite PositiveMap.gss. auto.
	        * unfold G, written_heap_preserved, owned_preserved_for, I; simpl.
	          split.
	          -- exists stk. repeat split; auto.
	          -- split.
	             ++ intros l0 p HlocW Hmem0. split; auto.
	             ++ split.
	                ** intros t' Hneq l0 p HlocO Hmem0. split; auto.
	                ** intros t' Hneq.
	                   do 2 (rewrite PositiveMap.gso by congruence).
	                   reflexivity.
	  Qed.
	    
	  Program Definition Mtrystack : layer_implementation E F := {|
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
	      unfold R. intros s s' [_ [_ Hpi]] _.
	      rewrite Hpi. tauto.
	    }
	    {
	      unfold G, R, written_heap_preserved, owned_preserved_for.
	      intros t1 t2 Hneq s1 s2 Hrel.
	      destruct Hrel as [HG | Hmeta].
	      - destruct HG as [_ [Hwritten [Howned Hpi]]].
	        split; [exact Hwritten|].
	        split; [apply Howned; auto|apply Hpi; auto].
	      - unfold GINV, Ginv, GRET, Gret, GId, LiftRelation_π in Hmeta.
	        destruct Hmeta as [[Hinv | Hret] | Hid].
	        + destruct Hinv as [f [Hσ [Hρ [Hfind Hπ]]]].
	          split.
	          * intros l v Hloc Hmem. rewrite <- Hσ. split; auto.
	          * split.
	            -- intros l v Hloc Hmem. rewrite <- Hσ. split; auto.
	            -- rewrite Hπ. rewrite PositiveMap.gso; auto.
	        + destruct Hret as [f [ret [Hσ [Hρ [Hfind Hπ]]]]].
	          split.
	          * intros l v Hloc Hmem. rewrite <- Hσ. split; auto.
	          * split.
	            -- intros l v Hloc Hmem. rewrite <- Hσ. split; auto.
	            -- rewrite Hπ. rewrite PositiveMap.gro; auto.
	        + subst. repeat split; intros; auto.
	    }
	    intros t f. destruct f.
	    (* push *)
	    {
	      exists (I //\\ ALin t (Semantics.ls_inv (push v))).
	      exists (fun ret => I //\\ ALin t (Semantics.ls_linr (push v) ret)).
	      constructor;
	      try solve_conj_impl;
	      try solve_conj_stable stableDB;
	      try apply IGinv; try apply IGret.
	      {
	        unfold ALin. intros.
	        destruct H; auto.
	      }
	      simpl. unfold push_impl.
	      eapply provable_vis_safe with
	        (P' := I //\\ ALin t (Semantics.ls_inv (push v)))
	        (Q' := fun oldPtr => I //\\ ALin t (Semantics.ls_inv (push v)));
	      try solve_conj_impl;
	      try solve_conj_stable stableDB;
	      try (let ret := fresh "ret" in intro ret; destruct ret; solve_conj_stable stableDB);
	      try apply cas_get_no_error;
	      try solve_no_error;
	      try apply pupdate_cas_get_inv_push;
	      try apply pupdate_cas_get_res_push.
	      intros oldPtr.
	      eapply provable_vis_safe with
	        (P' := I //\\ ALin t (Semantics.ls_inv (push v)))
	        (Q' := fun newLoc => I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HOwned t newLoc);
	      try solve_conj_impl;
	      try solve_conj_stable stableDB;
	      try (let ret := fresh "ret" in intro ret; destruct ret; solve_conj_stable stableDB);
	      try apply malloc_no_error;
	      try solve_no_error;
	      try apply pupdate_malloc_inv_push;
	      try apply pupdate_malloc_res_push.
	      intros newLoc.
	      eapply provable_vis_safe with
	        (P' := I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HOwned t newLoc)
	        (Q' := fun _ => I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HCell newLoc (v, oldPtr));
	      try solve_conj_impl;
	      try solve_conj_stable stableDB;
	      try (let ret := fresh "ret" in intro ret; destruct ret; solve_conj_stable stableDB);
	      try apply pupdate_mwrite_inv_push;
	      try apply pupdate_mwrite_res_push.
	      - eapply ImplTrans; [|apply mwrite_owned_no_error].
	        solve_conj_impl.
	      - intros [].
	        apply pupdate_mwrite_res_push.
	      - intros [].
	        eapply provable_vis_safe with
	          (P' := I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HCell newLoc (v, oldPtr))
	          (Q' := fun succ =>
	            I //\\ match succ with
	                   | true => ALin t (Semantics.ls_linr (push v) (OK tt))
	                   | false => ALin t (Semantics.ls_linr (push v) FAIL)
	                   end);
	        try solve_conj_impl;
	        try solve_conj_stable stableDB;
	        try (let ret := fresh "ret" in intro ret; destruct ret; solve_conj_stable stableDB);
	        try apply cas_cas_no_error;
	        try solve_no_error;
	        try apply pupdate_cas_push_inv;
	        try apply pupdate_cas_push_res.
	        intros succ.
	        eapply provable_ret_safe; destruct succ;
	        try solve_conj_impl;
	        try solve_conj_stable stableDB;
	        try apply ImplRefl.
	    }
	    (* pop *)
	    {
	      exists (I //\\ ALin t (Semantics.ls_inv pop)).
	      exists (fun ret => I //\\ ALin t (Semantics.ls_linr pop ret)).
	      constructor;
	      try solve_conj_impl;
	      try solve_conj_stable stableDB;
	      try apply IGinv; try apply IGret.
	      {
	        unfold ALin. intros.
	        destruct H; auto.
	      }
	      simpl. unfold pop_impl.
	      eapply provable_vis_safe with
	        (P' := I //\\ ALin t (Semantics.ls_inv pop))
	        (Q' := fun oldPtr =>
	          I //\\ match oldPtr with
	                 | None => ALin t (Semantics.ls_linr pop (OK None))
	                 | Some oldLoc => ALin t (Semantics.ls_inv pop) //\\ HWritten oldLoc
	                 end);
	      try solve_conj_impl;
	      try solve_conj_stable stableDB;
	      try (let ret := fresh "ret" in intro ret; destruct ret; solve_conj_stable stableDB);
	      try apply cas_get_no_error;
	      try solve_no_error;
	      try apply pupdate_cas_get_inv_pop;
	      try apply pupdate_cas_get_res_pop.
	      intros oldPtr. destruct oldPtr as [oldLoc|].
	      - eapply provable_vis_safe with
	          (P' := I //\\ ALin t (Semantics.ls_inv pop) //\\ HWritten oldLoc)
	          (Q' := fun head => I //\\ ALin t (Semantics.ls_inv pop) //\\ HCell oldLoc head);
	        try solve_conj_impl;
	        try solve_conj_stable stableDB;
	        try (let ret := fresh "ret" in intro ret; destruct ret; solve_conj_stable stableDB);
	        try apply pupdate_mread_inv_pop;
	        try apply pupdate_mread_res_pop.
	        + eapply ImplTrans; [|apply mread_written_no_error].
	          solve_conj_impl.
	        + intros [pv nxt].
	          eapply provable_vis_safe with
	            (P' := I //\\ ALin t (Semantics.ls_inv pop) //\\ HCell oldLoc (pv, nxt))
	            (Q' := fun succ =>
	              I //\\ match succ with
	                     | true => ALin t (Semantics.ls_linr pop (OK (Some pv)))
	                     | false => ALin t (Semantics.ls_linr pop FAIL)
	                     end);
	          try solve_conj_impl;
	          try solve_conj_stable stableDB;
	          try (let ret := fresh "ret" in intro ret; destruct ret; solve_conj_stable stableDB);
	          try apply cas_cas_no_error;
	          try solve_no_error;
	          try apply pupdate_cas_pop_inv;
	          try apply pupdate_cas_pop_res.
	          intros succ.
	          eapply provable_ret_safe; destruct succ;
	          try solve_conj_impl;
	          try solve_conj_stable stableDB;
	          try apply ImplRefl.
	      - eapply provable_ret_safe;
	        try solve_conj_impl;
	        try solve_conj_stable stableDB;
	        try apply ImplRefl.
	    }
	    (* initial *)
	    {
	      unfold I, loc_defined, pending_write_owned. simpl.
	      exists nil. split; [reflexivity|].
	      split; [constructor|].
	      split; [auto|].
	      intros l st Hloc. discriminate.
	    }
	  Defined.
  End Impl.
End TryStackImpl.
