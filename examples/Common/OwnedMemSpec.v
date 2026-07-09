Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Classical.
Require Import PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.AtomicLTS.
Require Import examples.Common.MemSpec.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulation.
Require Import RGILogic.


Module OwnedMemSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  Import MemSpec.

  Module WriteOwnedMem.
    Variant LocStat :=
    | LAlloc (t : tid)
    | LWritten.

    Record OwnedMemState (A : Type) := {
      om_heap : @Heap A;
      om_loc : @Heap LocStat;
    }.
    Arguments om_heap {A} _.
    Arguments om_loc {A} _.

    Definition empty_owned_mem {A} : OwnedMemState A :=
      {| om_heap := empty_heap; om_loc := empty_heap |}.

    Variant StepMem {A} : @ThreadEvent (EMem A) -> OwnedMemState A -> OwnedMemState A -> Prop :=
    (* alloc steps *)
    | step_alloc_inv t s e:
      e = {| te_tid := t; te_ev := InvEv malloc |} ->
      StepMem e s s
    | step_alloc_res t s l e (v : A):
      e = {| te_tid := t; te_ev := ResEv malloc l |} ->
      om_heap s l = None ->
      StepMem e s
        {| om_heap := heap_update l v (om_heap s);
           om_loc := heap_update l (LAlloc t) (om_loc s) |}
    (* read steps *)
    | step_read_inv t l s e:
      e = {| te_tid := t; te_ev := InvEv (mread l) |} ->
      om_heap s l <> None ->
      StepMem e s s
    | step_read_res t l s v e:
      e = {| te_tid := t; te_ev := ResEv (mread l) v |} ->
      om_heap s l = Some v ->
      StepMem e s s
    (* write steps *)
	    | step_write_inv t l v s e:
	      e = {| te_tid := t; te_ev := InvEv (mwrite l v) |} ->
	      om_heap s l <> None ->
	      StepMem e s s
	    | step_write_res t l v s e:
	      e = {| te_tid := t; te_ev := ResEv (mwrite l v) tt |} ->
	      om_heap s l <> None ->
	      StepMem e s
	        {| om_heap := heap_update l v (om_heap s);
	           om_loc := heap_update l LWritten (om_loc s) |}.

    Variant ErrorMem {A} : @ThreadEvent (EMem A) -> (@AState (EMem A) (OwnedMemState A)) -> Prop :=
    | error_read_undefined t s l e:
      e = {| te_tid := t; te_ev := InvEv (mread l) |} ->
      om_heap s l = None ->
      ErrorMem e (Idle s)
    | error_write_undefined t s l v e:
      e = {| te_tid := t; te_ev := InvEv (mwrite l v) |} ->
      om_heap s l = None ->
      ErrorMem e (Idle s)
	    | error_write_racy t t' s l l' v v' e:
      t <> t' ->
      l = l' ->
      e = {| te_tid := t; te_ev := InvEv (mwrite l v) |} ->
      ErrorMem e (Pending s t' (mwrite l' v')).

    Definition VMem {A} : @LTS (EMem A) := VAE StepMem ErrorMem.
  End WriteOwnedMem.

  Module WriteOwnedMemLayer.
    Import Lang.
    Import AssertionsSingle.
    Import RGILogic.
    Import TPSimulation.
    Import MemSpec.WriteRacyMem.
    Import WriteOwnedMem.
    Import (coercions, canonicals, notations) Sig.
    Import (notations) LinCCAL.

    Open Scope prog_scope.

    Context {A : Type}.

    Definition E : layer_interface :=
    {|
      li_sig := EMem A;
      li_lts := MemSpec.WriteRacyMem.VMem;
      li_init := Idle empty_heap;
    |}.

    Definition F : layer_interface :=
    {|
      li_sig := EMem A;
      li_lts := WriteOwnedMem.VMem;
      li_init := Idle empty_owned_mem;
    |}.

	    Definition owned_mem_id_impl (m : Sig.op (EMem A)) (_ : tid) :
	      Prog (EMem A) (Sig.ar m) :=
	      m >= ret => Ret ret.

    Definition assertion := @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).
    Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

    Open Scope assertion_scope.
    Open Scope rg_relation_scope.

    Definition same_pending (p q : Sig.op (EMem A)) : Prop := p = q.

    Definition state_rel (σ : State (li_lts E)) (ρ : State (li_lts F)) : Prop :=
      match σ, ρ with
      | Idle h, Idle om => om_heap om = h
      | Pending h t p, Pending om t' q =>
          t = t' /\ same_pending p q /\ om_heap om = h
      | _, _ => False
      end.

    Definition I : assertion :=
      fun s => state_rel (σ s) (ρ s).

    Definition G t : rg_relation :=
      fun s1 s2 =>
        I s2 /\
        forall t', t <> t' -> TMap.find t' (π s1) = TMap.find t' (π s2).

    Definition R t : rg_relation :=
      fun s1 s2 => TMap.find t (π s1) = TMap.find t (π s2).

    Lemma Istable {t} : Stable (R t) I I.
    Proof.
      unfold Stable. apply ConjRightImpl, ImplRefl.
    Qed.

    Lemma ALinstable {t ls}: Stable (R t) I (ALin t ls).
    Proof.
      unfold Stable, R, ALin.
      intros ? [[? [Hlin Hrel]] _]. rewrite <- Hrel. exact Hlin.
    Qed.

    Create HintDb stableDB.
    Hint Resolve Istable ALinstable : stableDB.

    Lemma IGinv : forall t f, ⊨ Ginv t f ⊚ I ==>> I //\\ ALin t (Semantics.ls_inv f).
    Proof.
      unfold Ginv, LiftRelation_π, I, ALin.
      intros t f s [s' [HI [? [? [Hnone Hπ]]]]].
      destruct s as [σ0 ρ0 π0], s' as [σ1 ρ1 π1]; simpl in *; subst σ0 ρ0.
      split.
      - exact HI.
      - subst π0. cbn. rewrite PositiveMap.gss. reflexivity.
    Qed.

    Lemma IGret : forall t f ret,
      ⊨ Gret t f ret ⊚ (I //\\ ALin t (Semantics.ls_linr f ret)) ==>> I.
    Proof.
      unfold Gret, LiftRelation_π, I.
      intros t f ret s [s' [[HI Hlin] [? [? [? Hπ]]]]].
      destruct s, s'; simpl in *; subst. exact HI.
    Qed.

    Lemma concrete_error_refines t (m : Sig.op (EMem A)) σ0 ρ0 :
      I (σ0, ρ0, TMap.empty _) ->
      Error (li_lts E) {| te_tid := t; te_ev := InvEv m |} σ0 ->
      Error (li_lts F) {| te_tid := t; te_ev := InvEv m |} ρ0.
    Proof.
      unfold I, state_rel.
      destruct σ0 as [h | h tp p], ρ0 as [om | om tq q]; simpl; try contradiction.
      - intros Hheap Herr. symmetry in Hheap. subst h.
        inversion Herr; subst; clear Herr;
          repeat match goal with
          | H : {| te_tid := _; te_ev := _ |} =
                {| te_tid := _; te_ev := _ |} |- _ =>
              inversion H; subst; clear H
          | H : InvEv _ = InvEv _ |- _ =>
              inversion H; subst; clear H
          end;
          simpl in *.
        + eapply error_read_undefined; eauto.
        + eapply error_write_undefined; eauto.
      - intros [Ht [Hop Hheap]] Herr.
        unfold same_pending in Hop. symmetry in Hheap. subst tq q h.
        inversion Herr; subst; clear Herr;
          repeat match goal with
          | H : {| te_tid := _; te_ev := _ |} =
                {| te_tid := _; te_ev := _ |} |- _ =>
              inversion H; subst; clear H
          | H : InvEv _ = InvEv _ |- _ =>
              inversion H; subst; clear H
          end;
          simpl in *.
        eapply error_write_racy; eauto.
    Qed.

    Lemma no_error_or_abstract_error t (m : Sig.op (EMem A)) :
      ⊨ I //\\ ALin t (Semantics.ls_inv m) ==>>
        (I //\\ ALin t (Semantics.ls_inv m) //\\
           ANoError {| te_tid := t; te_ev := InvEv m |}) \\// APError.
    Proof.
      unfold ANoError, APError.
      intros [σ0 ρ0 π0] [HI Hlin].
      destruct (classic (Error (li_lts E) {| te_tid := t; te_ev := InvEv m |} σ0)) as [Herr|Hno].
      - right.
        eapply rt_step.
        eapply Semantics.ps_error; eauto.
        eapply concrete_error_refines with (σ0:=σ0); eauto.
      - left. repeat split; auto.
    Qed.

    Lemma pupdate_owned_inv th (m : Sig.op (EMem A)) :
      PUpdate (G th) {| te_tid := th; te_ev := InvEv m |}
        (I //\\ ALin th (Semantics.ls_inv m) //\\
           ANoError {| te_tid := th; te_ev := InvEv m |})
        (I //\\ ALin th (Semantics.ls_lini m)).
    Proof.
      unfold PUpdate.
      intros σ0 ρ0 π0 [HI [Hlin Hno]] σ' Hstep.
      unfold I, state_rel in HI.
      unfold ALin in Hlin. simpl in Hlin.
      destruct σ0 as [h | h tp p]; simpl in *.
      - destruct ρ0 as [om | om tq q]; simpl in HI; try contradiction.
        symmetry in HI. subst h.
        inversion Hstep; subst; clear Hstep.
        dependent destruction Hstep0.
        all:
          match goal with
          | |- exists ρ' π',
              _ /\ (I //\\ ALin ?tid (Semantics.ls_lini ?op))
                (Pending _ ?tid ?op, ρ', π') /\ _ =>
              exists (Pending om tid op), (TMap.add tid (Semantics.ls_lini op) π0)
          end;
          split;
          [ eapply rt_step;
            eapply Semantics.ps_inv;
            [ eapply step_inv;
              match goal with
              | |- StepMem {| te_tid := ?tid; te_ev := InvEv ?op |} _ _ =>
                  destruct op as [|addr w|addr];
                  [ eapply WriteOwnedMem.step_alloc_inv; reflexivity
                  | eapply WriteOwnedMem.step_write_inv;
                    [ reflexivity
                    | intro Hnone; apply Hno; simpl;
                      eapply MemSpec.WriteRacyMem.error_write_undefined; eauto ]
                  | eapply WriteOwnedMem.step_read_inv;
                    [ reflexivity
                    | intro Hnone; apply Hno; simpl;
                      eapply MemSpec.WriteRacyMem.error_read_undefined; eauto ] ]
              end
            | exact Hlin ]
          | split;
            [ split;
              [ unfold I, state_rel, same_pending; simpl; repeat split; auto
              | unfold ALin; cbn; rewrite PositiveMap.gss; reflexivity ]
            | split;
              [ unfold I, state_rel, same_pending; simpl; repeat split; auto
              | intros t' Hneq; cbn; rewrite PositiveMap.gso by congruence; reflexivity ] ] ].
      - dependent destruction Hstep.
    Qed.

    Lemma pupdate_owned_res th (m : Sig.op (EMem A)) ret :
      PUpdate (G th) {| te_tid := th; te_ev := ResEv m ret |}
        (I //\\ ALin th (Semantics.ls_lini m))
        (I //\\ ALin th (Semantics.ls_linr m ret)).
    Proof.
      unfold PUpdate.
      intros σ0 ρ0 π0 [HI Hlin] σ' Hstep.
      unfold I, state_rel in HI.
      unfold ALin in Hlin. simpl in Hlin.
      destruct σ0 as [h | h tp p]; simpl in *.
      - inversion Hstep.
      - destruct ρ0 as [om | om tq q]; cbn in HI; try contradiction.
      destruct HI as [Ht [Hop Hheap]].
      unfold same_pending in Hop. symmetry in Hheap. subst tq q h.
      inversion Hstep; subst; clear Hstep.
      dependent destruction Hstep0.
      + match goal with
        | |- exists ρ' π',
            _ /\ (I //\\ ALin ?tid (Semantics.ls_linr malloc l)) _ /\ _ =>
            exists (Idle {| om_heap := heap_update l v (om_heap om);
                            om_loc := heap_update l (LAlloc tid) (om_loc om) |}),
              (TMap.add tid (Semantics.ls_linr malloc l) π0)
        end.
        split.
        { eapply rt_step. eapply Semantics.ps_ret.
          - eapply step_res. eapply WriteOwnedMem.step_alloc_res; eauto.
          - exact Hlin. }
        split.
        { split.
          - unfold I, state_rel. simpl. reflexivity.
          - unfold ALin. cbn. rewrite PositiveMap.gss. reflexivity. }
        { split.
          - unfold I, state_rel. simpl. reflexivity.
          - intros t' Hneq. cbn. rewrite PositiveMap.gso by congruence. reflexivity. }
      + match goal with
        | |- exists ρ' π',
            _ /\ (I //\\ ALin ?tid (Semantics.ls_linr (mread l) v)) _ /\ _ =>
            exists (Idle om), (TMap.add tid (Semantics.ls_linr (mread l) v) π0)
        end.
        split.
        { eapply rt_step. eapply Semantics.ps_ret.
          - eapply step_res. eapply WriteOwnedMem.step_read_res; eauto.
          - exact Hlin. }
        split.
        { split.
          - unfold I, state_rel. simpl. reflexivity.
          - unfold ALin. cbn. rewrite PositiveMap.gss. reflexivity. }
        { split.
          - unfold I, state_rel. simpl. reflexivity.
          - intros t' Hneq. cbn. rewrite PositiveMap.gso by congruence. reflexivity. }
      + match goal with
        | |- exists ρ' π',
            _ /\ (I //\\ ALin ?tid (Semantics.ls_linr (mwrite l v) tt)) _ /\ _ =>
            exists (Idle {| om_heap := heap_update l v (om_heap om);
                            om_loc := heap_update l LWritten (om_loc om) |}),
              (TMap.add tid (Semantics.ls_linr (mwrite l v) tt) π0)
        end.
        split.
        { eapply rt_step. eapply Semantics.ps_ret.
          - eapply step_res. eapply WriteOwnedMem.step_write_res; eauto.
          - exact Hlin. }
        split.
        { split.
          - unfold I, state_rel. simpl. reflexivity.
          - unfold ALin. cbn. rewrite PositiveMap.gss. reflexivity. }
        { split.
          - unfold I, state_rel. simpl. reflexivity.
          - intros t' Hneq. cbn. rewrite PositiveMap.gso by congruence. reflexivity. }
    Qed.

    Program Definition Mowned_mem : layer_implementation E F := {|
      li_impl := owned_mem_id_impl
    |}.
    Next Obligation.
      eapply RGILogic.soundness with (R:=R) (G:=G) (I:=I).
      {
        constructor.
        unfold R. intros. rewrite H. tauto.
      }
      {
        unfold G, R.
        intros t1 t2 Hneq s1 s2 Hrel.
        destruct s1 as [σ1 ρ1 π1], s2 as [σ2 ρ2 π2]; simpl in *.
        destruct Hrel as [HG | [[Hinv | Hret] | Hid]].
        - destruct HG as [_ Hπ]. apply Hπ. congruence.
        - unfold GINV, Ginv, LiftRelation_π in Hinv.
          destruct Hinv as [f [? [? [_ Hπ]]]]. subst.
          cbn in Hπ. subst π2.
          rewrite PositiveMap.gso by congruence. reflexivity.
        - unfold GRET, Gret, LiftRelation_π in Hret.
          destruct Hret as [f [ret [? [? [_ Hπ]]]]]. subst.
          cbn in Hπ. subst π2.
          rewrite PositiveMap.gro by congruence. reflexivity.
        - unfold GId in Hid. inversion Hid; subst. reflexivity.
      }
      intros t m.
      exists (I //\\ ALin t (Semantics.ls_inv m)).
      exists (fun ret => I //\\ ALin t (Semantics.ls_linr m ret)).
      constructor;
        try solve [apply IGinv | apply IGret | solve_conj_impl | solve_conj_stable stableDB].
      {
        intros ret σ0 ρ0 π0 Hq. exact (proj2 Hq).
      }
      simpl. unfold owned_mem_id_impl.
      eapply provable_vis with
        (P := I //\\ ALin t (Semantics.ls_inv m) //\\
          ANoError {| te_tid := t; te_ev := InvEv m |})
        (P' := I //\\ ALin t (Semantics.ls_lini m))
        (Q' := fun ret => I //\\ ALin t (Semantics.ls_linr m ret));
        try solve [apply no_error_or_abstract_error
                  | solve_conj_impl
                  | solve_conj_stable stableDB
                  | apply pupdate_owned_inv
                  | intros; apply pupdate_owned_res].
      intros ret.
      eapply provable_ret_safe;
        try solve [solve_conj_impl | solve_conj_stable stableDB].
      unfold I, state_rel. simpl. reflexivity.
    Defined.
	  End WriteOwnedMemLayer.
	End OwnedMemSpec.
