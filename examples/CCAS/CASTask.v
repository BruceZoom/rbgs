Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.Logic.Classical_Prop.
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
Require Import examples.Common.AtomicLTS.
Require Import examples.CAS.CASRegSpec.
Require Import examples.FAI.FAISpec.
Require Import examples.CCAS.CASTaskSpec.
Require Import SeparationAlgebra.


  Lemma conj_from_imp : forall (P Q : Prop), P -> (P -> Q) -> P /\ Q.
  Proof. eauto. Qed.
  
  Lemma conj_right_imp {P Q R : Prop} :
    (Q -> R) -> (P /\ Q) -> (P /\ R).
  Proof. tauto. Qed.

  Ltac split_right :=
    try (split; [| split_right]).

  Ltac extract n H :=
    (* let Hneed := fresh "H" in *)
    lazymatch n with
      | O => idtac
      | S ?n' =>
          destruct H as [_ H];
          extract n' H
    end;
    simpl in H;
    match H with
    | exists _, _ => idtac
    | _ => try destruct H as [H _]
    end.

  Open Scope nat_scope.

Class HasBeq (t : Type) := {
  beq : t -> t -> bool;
  beq_refl : forall x, beq x x = true;
  beq_true : forall x y, beq x y = true -> x = y;
  beq_false : forall x y, beq x y = false -> x <> y;
}.

Require Import examples.CCAS.CCASCommon.
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
    li_init := Idle (cts (inr vInit) O (fun _ => Inactive));
  |}.

  Definition allocTask_impl (_ : tid) : Prog (li_sig E) nat :=
    inr fai >= i => Ret i.
  
  Definition tryPlaceTask_impl o n i (cid : tid) : Prog (li_sig E) ((CASTask Val) + Val) :=
    inl (cas (inr o) (inl (CTask cid o n i))) >= r => Ret r.
  
  Definition tryResolveTask_impl tsk v (_ : tid) : Prog (li_sig E) unit :=
    inl (cas (inl tsk) (inr v)) >= _ => Ret tt.
  
  Definition assertion := @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.
  
  Definition ALinEx t ls : assertion := fun s => exists ρ π, Δ s ρ π /\ TMap.find t π = ls.

  Definition SafeTicket i : assertion :=
    fun s => forall ρ π, Δ s ρ π -> owner (state ρ) i <> Inactive.

  Definition I_cas : assertion := fun s =>
    forall ρ π, Δ s ρ π ->
      state (fst (σ s)) = current (state ρ).

  Definition I_ticket : assertion := fun s =>
    forall ρ π, Δ s ρ π ->
      state (snd (σ s)) = ticket (state ρ) /\
      forall i, ticket (state ρ) <= i -> owner (state ρ) i = Inactive.

  Definition I_atomic : assertion := fun s =>
    exists ρ π c, Δ s ≡ [(ρ , π)] /\ ρ = Idle c.
    
  Definition I : assertion :=
    I_atomic //\\ I_cas //\\ I_ticket.
  
  Definition R t : rg_relation :=
    fun s1 s2 =>
      (forall ls, ALinEx t ls s1 <-> ALinEx t ls s2)
      /\ (forall i, SafeTicket i s1 -> SafeTicket i s2).
  
  Definition G_id : rg_relation :=
    fun s1 s2 =>
      state (fst (σ s1)) = state (fst (σ s2)) /\
      state (snd (σ s1)) = state (snd (σ s2)) /\
      Δ s1 ≡ Δ s2.

  Definition G_other t : rg_relation :=
    fun s1 s2 => forall t', t <> t' -> R t' s1 s2.
  
  Definition G t := G_id ∪ G_other t.

  Ltac simpl_all :=
    unfold R, G, G_id, G_other, I, I_atomic, I_ticket, I_cas, SafeTicket, owner_upd,
          Conj, Disj, Imply in *; simpl in *.

  Lemma RG_compatible : forall t1 t2, t1 <> t2 -> (I ⊓ G t1 ⊆ R t2).
  Proof.
    intros. intros ? ? [? ?].
    destruct H0.
    - unfold G_id, R, ALinEx, SafeTicket in *.
      split.
      + split; intros [? [? [HΔ ?]]];
        apply H0 in HΔ; do 2 eexists; eauto.
      + intros. apply H0 in H3. eauto.
    - apply H0; eauto.
  Qed.

  Lemma R_domexact : forall t0 s1 s2, R t0 s1 s2 -> I s2 ->
    (forall (ρ1 : State (li_lts F)) (π1 : tmap LinState), Δ s1 ρ1 π1 -> TMap.find t0 π1 = None) <->
    (forall (ρ2 : State (li_lts F)) (π2 : tmap LinState), Δ s2 ρ2 π2 -> TMap.find t0 π2 = None).
  Proof.
    intros.
    split; intros.
    - pose proof ac_nonempty (Δ s1) as [? [? ?]].
      apply H1 in H3 as ?.
      assert (ALinEx t0 None s1) by (do 2 eexists; eauto).
      apply H in H5 as [? [? [? ?]]].
      eapply (ac_domexact (Δ s2)) in H6; eauto.
    - pose proof ac_nonempty (Δ s2) as [? [? ?]].
      apply H1 in H3 as ?.
      assert (ALinEx t0 None s2) by (do 2 eexists; eauto).
      apply H in H5 as [? [? [? ?]]].
      eapply (ac_domexact (Δ s1)) in H6; eauto.
  Qed.

  Lemma ALinLinExI : forall t ls s,
    I s -> (ALinEx t (Some ls) s <-> ALin t ls s).
  Proof.
    intros. destruct H as [[? [? [? [? ?]]]]].
    split; intros.
    - intros ? ? ?. apply H in H3; inversion H3; subst.
      destruct H2 as [? [? [? ?]]].
      apply H in H0; inversion H0; subst. auto.
    - exists x, x0. split; [apply H; constructor|].
      pose proof ac_nonempty (Δ s) as [? [? ?]].
      apply H in H3; inversion H3; subst.
      eapply H2. apply H; eauto.
  Qed.

  Lemma ALinLinEx : forall t ls s,
    ALin t ls s -> ALinEx t (Some ls) s.
  Proof.
    intros.
    pose proof ac_nonempty (Δ s) as [? [? ?]].
    apply H in H0 as ?. do 2 eexists; eauto.
  Qed.

  Lemma stable_ALin : forall t ls, Stable (R t) I (ALin t ls).
  Proof.
    intros. intros ? [[? [? ?]] ?].
    rewrite <- ALinLinExI; eauto. apply H0.
    apply ALinLinEx; auto.
  Qed.

  Lemma stable_I : forall t, Stable (R t) I I.
  Proof. intros. intros ? [[? [? ?]] ?]; auto. Qed.

  Lemma stable_SafeTicket : forall t i, Stable (R t) I (SafeTicket i).
  Proof.
    intros. intros ? [[? [? ?]] ?].
    apply H0. auto.
  Qed.

  Lemma G_id_I : ⊨ G_id ⊚ I ==>> I.
  Proof.
    intros ? [? [? [? [? ?]]]].
    destruct H as [[? [? [? [? ?]]]] [? ?]]; subst.
    simpl_all. rewrite H0 in *. rewrite H1 in *.
    split; [|split]; eauto.
    - exists (Idle x2), x1, x2.
      split; auto. etransitivity; eauto. symmetry; auto.
    - intros. apply H2 in H3; eauto.
    - intros. apply H2 in H3; eauto.
  Qed.

  Create HintDb stableDB.
  Hint Resolve stable_I stable_ALin stable_SafeTicket
  : stableDB.

  Lemma G_id_G : forall s1 s2 t, G_id s1 s2 -> G t s1 s2.
  Proof. left; auto. Qed.
  
  Ltac post_pupdate_id :=
            eapply conj_right_imp; [apply G_id_G |];
                    apply and_comm, conj_from_imp; intros.

  Program Definition MCASTask : layer_implementation_simulation E F := {|
    li_impl m :=
      match m with
      | allocTask _ _ => allocTask_impl
      | tryPlaceTask o n i => tryPlaceTask_impl o n i
      | tryResolveTask tsk v => tryResolveTask_impl tsk v
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
      intros. intros s1 s2 [[? | ?] HI];
      [eapply RG_compatible; eauto; try (split; auto)|].
      destruct H0 as [[? | ?] | ?].
      - unfold GINV, Ginv, LiftRelation_Δ in *.
        destruct H0 as [? [? [? ?]]].
        split.
        * split; intros [? [? [? ?]]].
          + exists x0, (TMap.add t1 (ls_inv x) x1).
            split; [|rewrite TMap.gso;auto].
            apply H2. constructor; auto.
          + apply H2 in H3. inversion H3; subst.
            do 2 eexists; split; eauto.
            rewrite TMap.gso; auto.
        * unfold SafeTicket. intros.
          apply H2 in H4. inversion H4; subst. eauto.
      - unfold GRET, Gret, LiftRelation_Δ in *.
        destruct H0 as [? [? [? [? ?]]]].
        split.
        * split; intros [? [? [? ?]]].
          + exists x1, (TMap.remove t1 x2).
            split; [|rewrite TMap.gro;auto].
            apply H2. constructor; auto.
          + apply H2 in H3. inversion H3; subst.
            do 2 eexists; split; eauto.
            rewrite TMap.gro; auto.
        * unfold SafeTicket. intros.
          apply H2 in H4. inversion H4; subst. eauto.
      - unfold GId in *; subst. unfold R. tauto.
    }
    (* method provable *)
    {
      intros t f.
      exists (I //\\ ALin t (ls_inv f)).
      exists (fun r => I //\\ ALin t (ls_linr f r)).
      constructor;
      try solve_conj_impl;
      try solve_stable stableDB.
      (* invocation *)
      {
        intros ? [s' [? [? [? ?]]]]. simpl_all.
        rewrite H0 in *.
        destruct H as [[? [? [? [? ?]]]] [? ?]]; subst.
        split;[split;[|split]|].
        - exists (Idle x1), (TMap.add t (ls_inv f) x0).
          exists x1; split; auto.
          etransitivity; eauto.
          split; inversion 1; subst; try constructor; eauto.
          + apply H in Hposs; inversion Hposs; subst; auto.
            constructor.
          + apply H. constructor.
        - intros. apply H2 in H3; inversion H3; subst. eauto.
        - intros. apply H2 in H3. inversion H3; subst. eauto.
        - intros ? ? ?. apply H2 in H3; inversion H3; subst.
          rewrite TMap.gss; eauto.
      }
      (* response *)
      {
        intros ? ? [? [[? ?] [? [? ?]]]]. simpl_all.
        rewrite H1 in *.
        destruct H as [[? [? [? [? ?]]]] [? ?]]; subst.
        split;[|split].
        - exists (Idle x2), (TMap.remove t x1).
          exists x2; split; auto.
          etransitivity; eauto.
          split; inversion 1; subst; try constructor; eauto.
          + apply H in Hposs; inversion Hposs; subst; auto.
            constructor.
          + apply H. constructor.
        - intros. apply H3 in H4; inversion H4; subst. eauto.
        - intros. apply H3 in H4; inversion H4; subst. eauto.
      }
      {
        intros. destruct H as [_ ?]. eauto.
      }
      (* method body *)
      {
        destruct f.
        (* alloc *)
        {
          simpl.
          eapply provable_vis_safe with
            (P' := I //\\ ALin t (ls_inv (allocTask o n)))
            (Q' := fun r : nat => I //\\ ALin t (ls_linr (allocTask o n) r));
          try solve_no_error;
          try solve_conj_impl;
          try solve_stable stableDB.
          (* inv *)
          {
            pupdate_intros_atomic.
            dependent destruction Hstep.
            pupdate_start. eapply ac_steps_refl.
            
            post_pupdate_id.
            { unfold G_id; simpl; do 2 (split; auto); reflexivity. }
            destruct Hpre as [? ?].
            split; [apply G_id_I; eexists; eauto|].
            intros ? ? ?.
            apply H1 in H2. auto.
          }
          (* res *)
          {
            pupdate_intros_atomic.
            dependent destruction Hstep.
            destruct Hpre as [? ?].
            pose proof ac_nonempty (Δ1) as [? [? ?]].
            apply H0 in H1 as ?.
            destruct H as [[? [? [? [? ?]]]] ?].
            apply H in H1 as HΔ; inversion HΔ; subst. simpl in *.
            destruct x3.

            pupdate_start.
            pupdate_trylin_from H1.
            pupdate_forward t (InvEv (allocTask o n)).
            pupdate_forward t (ResEv (allocTask o n) ticket0).
            pupdate_finish.
            eapply ACTrylinFinish.

            repeat split; simpl_all.
            - exists (Idle {| current := current0; ticket := S ticket0; owner := owner_upd owner0 ticket0 (Owned t) |}).
              exists (TMap.add t (ls_linr (allocTask o n) ticket0) (TMap.add t (ls_lini (allocTask o n)) x0)).
              eexists; split; [|split;eauto].
              constructor; inversion 1; subst; try constructor; eauto.
              pupdate_forward t (InvEv (allocTask o n)).
              pupdate_forward t (ResEv (allocTask o n) ticket0).
              pupdate_finish.
            - inversion 1; subst. simpl in *.
              destruct H4.
              apply H4 in H1. eauto.
            - inversion H3; subst. simpl. apply f_equal.
              apply H4 in H1 as [? ?]. eauto.
            - inversion H3; subst. simpl.
              apply H4 in H1 as [? ?]. simpl in *.
              intros. unfold owner_upd.
              destruct (Nat.eqb_spec ticket0 i); subst; eauto; try lia.
              eapply H5. lia.
            - inversion 1; subst. simpl_all.
              rewrite TMap.gss; eauto.
              apply H4 in Hposs as [? ?]; simpl in *. subst. eauto.
            - right. intros. simpl_all.
              split.
              * split; intros [? [? [? ?]]]; [|inversion H5;subst].
                + exists (Idle {| current := current0; ticket := S ticket0; owner := owner_upd owner0 ticket0 (Owned t) |}),
                  (TMap.add t (ls_linr (allocTask o n) ticket0) (TMap.add t (ls_lini (allocTask o n)) x0)).
                  apply H in H5 as HΔ'; inversion HΔ'; simpl in *; subst.
                  simpl. split; [constructor|do 2 (rewrite TMap.gso; eauto) ]; eauto.
                  pupdate_forward t (InvEv (allocTask o n)).
                  pupdate_forward t (ResEv (allocTask o n) ticket0).
                  pupdate_finish.
                + exists (Idle {| current := current0; ticket := ticket0; owner := owner0 |}), x0. split; eauto.
                  do 2 (rewrite TMap.gso; eauto).
              * intros. inversion H6; subst. simpl in *.
                apply H5 in Hposs. simpl in *.
                destruct (Nat.eqb_spec ticket0 i); subst; eauto.
                congruence.
          }
          intros.
          eapply provable_ret;
          try solve_conj_impl;
          try solve_stable stableDB.
          left; auto.
        }
        (* place *)
        {
          simpl.
          eapply provable_vis_safe with
            (P' := I //\\ ALin t (ls_inv (tryPlaceTask o n i)))
            (Q' := fun r => I //\\ ALin t (ls_linr (tryPlaceTask o n i) r));
          try solve_no_error;
          try solve_conj_impl;
          try solve_stable stableDB.
          (* inv *)
          {
            pupdate_intros_atomic.
            dependent destruction Hstep.
            pupdate_start. eapply ac_steps_refl.
            
            post_pupdate_id.
            { unfold G_id; simpl; do 2 (split; auto); reflexivity. }
            destruct Hpre as [? ?].
            split; [apply G_id_I; eexists; eauto|].
            intros ? ? ?.
            apply H1 in H2. auto.
          }
          (* res *)
          {
            pupdate_intros_atomic;
            dependent destruction Hstep.
            (* succeed *)
            {
              destruct Hpre as [? ?].
              pose proof ac_nonempty (Δ1) as [? [? ?]].
              apply H0 in H1 as ?.
              destruct H as [[? [? [? [? ?]]]] ?].
              apply H in H1 as HΔ; inversion HΔ; subst. simpl in *.
              destruct x3.
              pose proof H4 as [? _]. apply H3 in H1 as ?; simpl in *. subst.

              pupdate_start.
              pupdate_trylin_from H1.
              eapply rt_trans.
              eapply rt_step, ps_inv; eauto.
              do 2 constructor.
              eapply rt_step, ps_ret; eauto.
              constructor. eapply step_tryPlaceTask_succ; eauto.
              rewrite TMap.gss; auto.
              eapply ACTrylinFinish.

              repeat split; simpl_all.
              - exists (Idle {| current := inl (CTask t0 o n i); ticket := ticket0; owner := owner0 |}),
                (TMap.add t0 (ls_linr (tryPlaceTask o n i) (inr o)) (TMap.add t0 (ls_lini (tryPlaceTask o n i)) x0)).
                eexists; split; [|split;eauto].
                constructor; inversion 1; subst; try constructor; eauto.
                eapply rt_trans.
                eapply rt_step, ps_inv; eauto.
                do 2 constructor.
                eapply rt_step, ps_ret; eauto.
                constructor. eapply step_tryPlaceTask_succ; eauto.
                rewrite TMap.gss; auto.
              - inversion 1; subst. simpl in *.
                destruct H4.
                apply H4 in H1. eauto.
              - inversion H5; subst. simpl.
                apply H4 in H1 as [? ?]. eauto.
              - inversion H5; subst. simpl.
                apply H4 in H1 as [? ?]. simpl in *.
                intros. unfold owner_upd.
                destruct (Nat.eqb_spec ticket0 i); subst; eauto; try lia.
              - inversion 1; subst. simpl_all.
                rewrite TMap.gss; eauto.
              - right. intros. simpl_all.
                split.
                * split; intros [? [? [? ?]]]; [|inversion H6;subst].
                  + exists (Idle {| current := inl (CTask t0 o n i); ticket := ticket0; owner := owner0 |}),
                      (TMap.add t0 (ls_linr (tryPlaceTask o n i) (inr o)) (TMap.add t0 (ls_lini (tryPlaceTask o n i)) x0)).
                    apply H in H6 as HΔ'; inversion HΔ'; simpl in *; subst.
                    simpl. split; [constructor|do 2 (rewrite TMap.gso; eauto) ]; eauto.
                    eapply rt_trans.
                    eapply rt_step, ps_inv; eauto.
                    do 2 constructor.
                    eapply rt_step, ps_ret; eauto.
                    constructor. eapply step_tryPlaceTask_succ; eauto.
                    rewrite TMap.gss; auto.
                  + do 2 eexists; split; eauto.
                    do 2 (rewrite TMap.gso; eauto).
              * intros. inversion H7; subst. simpl in *.
                apply H6 in Hposs. simpl in *.
                destruct (Nat.eqb_spec ticket0 i); subst; eauto.
            }
            (* fail *)
            {
              clear H0. rename H1 into Hneq.
              destruct Hpre as [? ?].
              pose proof ac_nonempty (Δ1) as [? [? ?]].
              apply H0 in H1 as ?.
              destruct H as [[? [? [? [? ?]]]] ?]. subst.
              apply H in H1 as HΔ; inversion HΔ; subst. simpl in *.
              destruct x3.
              pose proof H4 as [? _]. apply H3 in H1 as ?; simpl in *. subst.
              destruct current0.
              (* fail *)
              {
                pupdate_start.
                pupdate_trylin_from H1.
                eapply rt_trans.
                eapply rt_step, ps_inv; eauto.
                do 2 constructor.
                eapply rt_step, ps_ret; eauto.
                constructor. eapply step_tryPlaceTask_block; eauto.
                rewrite TMap.gss; auto.
                eapply ACTrylinFinish.

                repeat split; simpl_all.
                - exists (Idle {| current := inl c; ticket := ticket0; owner := owner0 |}),
    (TMap.add t0 (ls_linr (tryPlaceTask o n i) (inl c)) (TMap.add t0 (ls_lini (tryPlaceTask o n i)) x0)).
                  eexists; split; [|split;eauto].
                  constructor; inversion 1; subst; try constructor; eauto.
                  eapply rt_trans.
                  eapply rt_step, ps_inv; eauto.
                  do 2 constructor.
                  eapply rt_step, ps_ret; eauto.
                  constructor. eapply step_tryPlaceTask_block; eauto.
                  rewrite TMap.gss; auto.
                - inversion 1; subst. simpl in *.
                  destruct H4.
                  apply H4 in H1. eauto.
                - inversion H5; subst. simpl.
                  apply H4 in H1 as [? ?]. eauto.
                - inversion H5; subst. simpl.
                  apply H4 in H1 as [? ?]. simpl in *.
                  intros. unfold owner_upd.
                  destruct (Nat.eqb_spec ticket0 i); subst; eauto; try lia.
                - inversion 1; subst. simpl_all.
                  rewrite TMap.gss; eauto.
                - right. intros. simpl_all.
                  split.
                  * split; intros [? [? [? ?]]]; [|inversion H6;subst].
                    + exists (Idle {| current := inl c; ticket := ticket0; owner := owner0 |}),
      (TMap.add t0 (ls_linr (tryPlaceTask o n i) (inl c)) (TMap.add t0 (ls_lini (tryPlaceTask o n i)) x0)).
                      apply H in H6 as HΔ'; inversion HΔ'; simpl in *; subst.
                      simpl. split; [constructor|do 2 (rewrite TMap.gso; eauto) ]; eauto.
                      eapply rt_trans.
                      eapply rt_step, ps_inv; eauto.
                      do 2 constructor.
                      eapply rt_step, ps_ret; eauto.
                      constructor. eapply step_tryPlaceTask_block; eauto.
                      rewrite TMap.gss; auto.
                    + do 2 eexists; split; eauto.
                      do 2 (rewrite TMap.gso; eauto).
                  * intros. inversion H7; subst. simpl in *.
                    apply H6 in Hposs. simpl in *.
                    destruct (Nat.eqb_spec ticket0 i); subst; eauto.
              }
              (* fail *)
              {
                assert (Hneq' : v <> o) by congruence.
                pupdate_start.
                pupdate_trylin_from H1.
                eapply rt_trans.
                eapply rt_step, ps_inv; eauto.
                do 2 constructor.
                eapply rt_step, ps_ret; eauto.
                constructor. eapply step_tryPlaceTask_fail; eauto.
                rewrite TMap.gss; auto.
                eapply ACTrylinFinish.

                repeat split; simpl_all.
                - exists (Idle {| current := inr v; ticket := ticket0; owner := owner0 |}),
    (TMap.add t0 (ls_linr (tryPlaceTask o n i) (inr v)) (TMap.add t0 (ls_lini (tryPlaceTask o n i)) x0)).
                  eexists; split; [|split;eauto].
                  constructor; inversion 1; subst; try constructor; eauto.
                  eapply rt_trans.
                  eapply rt_step, ps_inv; eauto.
                  do 2 constructor.
                  eapply rt_step, ps_ret; eauto.
                  constructor. eapply step_tryPlaceTask_fail; eauto.
                  rewrite TMap.gss; auto.
                - inversion 1; subst. simpl in *.
                  destruct H4.
                  apply H4 in H1. eauto.
                - inversion H5; subst. simpl.
                  apply H4 in H1 as [? ?]. eauto.
                - inversion H5; subst. simpl.
                  apply H4 in H1 as [? ?]. simpl in *.
                  intros. unfold owner_upd.
                  destruct (Nat.eqb_spec ticket0 i); subst; eauto; try lia.
                - inversion 1; subst. simpl_all.
                  rewrite TMap.gss; eauto.
                - right. intros. simpl_all.
                  split.
                  * split; intros [? [? [? ?]]]; [|inversion H6;subst].
                    + exists (Idle {| current := inr v; ticket := ticket0; owner := owner0 |}),
      (TMap.add t0 (ls_linr (tryPlaceTask o n i) (inr v)) (TMap.add t0 (ls_lini (tryPlaceTask o n i)) x0)).
                      apply H in H6 as HΔ'; inversion HΔ'; simpl in *; subst.
                      simpl. split; [constructor|do 2 (rewrite TMap.gso; eauto) ]; eauto.
                      eapply rt_trans.
                      eapply rt_step, ps_inv; eauto.
                      do 2 constructor.
                      eapply rt_step, ps_ret; eauto.
                      constructor. eapply step_tryPlaceTask_fail; eauto.
                      rewrite TMap.gss; auto.
                    + do 2 eexists; split; eauto.
                      do 2 (rewrite TMap.gso; eauto).
                  * intros. inversion H7; subst. simpl in *.
                    apply H6 in Hposs. simpl in *.
                    destruct (Nat.eqb_spec ticket0 i); subst; eauto.
              }
            }
          }
          intros.
          eapply provable_ret;
          try solve_conj_impl;
          try solve_stable stableDB.
          left; auto.
        }
        (* resolve *)
        {
          simpl.
          destruct tsk.
          eapply provable_perror with
            (P' := I //\\ ALin t (ls_inv (tryResolveTask (CTask t0 o n i) v))
                    //\\ SafeTicket i).
          {
            intros ? [? ?].
            assert (SafeTicket i s \/ ~ SafeTicket i s) by apply classic.
            destruct H1; [left; do 2 (split; auto)|right].
            assert ((exists ρ π, Δ s ρ π /\ owner (state ρ) i = Inactive) \/ ~ (exists ρ π, Δ s ρ π /\ owner (state ρ) i = Inactive)) by apply classic.
            destruct H2.
            2:{
              exfalso. apply H1.
              intros ? ? ? ?.
              apply H2. eauto.
            }
            clear H1. destruct H2 as [? [? [? ?]]].
            econstructor; [exact H1|].
            apply rt_step.
            apply H0 in H1 as ?.
            econstructor; eauto.
            destruct H as [[? [? [? [? ?]]]] _].
            apply H in H1. inversion H1; subst.
            constructor. destruct x3.
            econstructor; eauto.
          }

          eapply provable_vis_safe with
            (P' := I //\\ ALin t (ls_inv (tryResolveTask (CTask t0 o n i) v)) //\\ SafeTicket i)
            (Q' := fun _ => I //\\ ALin t (ls_linr (tryResolveTask (CTask t0 o n i) v) tt));
          try solve_no_error;
          try solve_conj_impl;
          try solve_stable stableDB.
          (* inv *)
          {
            pupdate_intros_atomic.
            dependent destruction Hstep.
            pupdate_start. eapply ac_steps_refl.
            
            post_pupdate_id.
            { unfold G_id; simpl; do 2 (split; auto); reflexivity. }
            destruct Hpre as [? [? ?]].
            split; [apply G_id_I; eexists; eauto|].
            split.
            + intros ? ? ?.
              apply H1 in H3. auto.
            + intros ? ? ?. apply H in H3.
              apply H2 in H3. eauto.
          }
          (* res *)
          {
            pupdate_intros_atomic;
            dependent destruction Hstep.
            (* has task placed *)
            {
              destruct Hpre as [? [? Hticket]].
              pose proof ac_nonempty (Δ1) as [? [? ?]].
              apply H0 in H1 as ?.
              destruct H as [[? [? [? [? ?]]]] ?].
              apply H in H1 as HΔ; inversion HΔ; subst. clear HΔ. simpl in *.
              destruct x3.
              assert (current0 = inl (CTask t0 o n i) \/ current0 <> inl (CTask t0 o n i)) by apply classic.
              destruct H3 as [? | Hneq]; subst.
              (* succeed *)
              {
                pupdate_start.
                pupdate_trylin_from H1.
                eapply rt_trans.
                eapply rt_step, ps_inv; eauto.
                do 2 constructor.
                eapply rt_step, ps_ret; eauto; [|rewrite TMap.gss; auto].
                constructor. eapply step_tryResolveTask_succ; eauto.
                eapply ACTrylinFinish.

                  (* * intros. inversion H7; subst. simpl in *.
                    apply H6 in Hposs. simpl in *.
                    destruct (Nat.eqb_spec ticket0 i); subst; eauto. *)

                repeat split; simpl_all.
                - exists(Idle
                    {|
                      current := inr v;
                      ticket := ticket0;
                      owner := fun i' : nat => if i =? i' then Expired else owner0 i'
                    |}),
                  (TMap.add t1 (ls_linr (tryResolveTask (CTask t0 o n i) v) tt)
                    (TMap.add t1 (ls_lini (tryResolveTask (CTask t0 o n i) v)) x0)).
                  eexists; split; [|split;eauto].
                  constructor; inversion 1; subst; try constructor; eauto.
                  eapply rt_trans.
                  eapply rt_step, ps_inv; eauto.
                  do 2 constructor.
                  eapply rt_step, ps_ret; eauto; [|rewrite TMap.gss; auto].
                  constructor. eapply step_tryResolveTask_succ; eauto.
                - inversion 1; subst. simpl in *.
                  destruct H4.
                  apply H4 in H1. eauto.
                - inversion H3; subst. simpl.
                  apply H4 in H1 as [? ?]. eauto.
                - inversion H3; subst. simpl.
                  apply H4 in H1 as [? ?]. simpl in *.
                  intros. unfold owner_upd.
                  destruct (Nat.eqb_spec i i0); subst; eauto; try lia.
                  simpl_all.
                  apply Hticket in Hposs as ?. simpl in *.
                  apply H5 in H6. congruence.
                - inversion 1; subst. simpl_all.
                  rewrite TMap.gss; eauto.
                - right. intros. simpl_all.
                  split.
                  * split; intros [? [? [? ?]]]; [|inversion H6;subst].
                    + exists (Idle
                    {|
                      current := inr v;
                      ticket := ticket0;
                      owner := fun i' : nat => if i =? i' then Expired else owner0 i'
                    |}),
                  (TMap.add t1 (ls_linr (tryResolveTask (CTask t0 o n i) v) tt)
                    (TMap.add t1 (ls_lini (tryResolveTask (CTask t0 o n i) v)) x0)). simpl.
                      apply H in H5 as HΔ'; inversion HΔ'; simpl in *; subst.
                      simpl. split; [constructor|do 2 (rewrite TMap.gso; eauto) ]; eauto.
                      eapply rt_trans.
                      eapply rt_step, ps_inv; eauto.
                      do 2 constructor.
                      eapply rt_step, ps_ret; eauto.
                      constructor. eapply step_tryResolveTask_succ; eauto.
                      rewrite TMap.gss; auto.
                    + simpl_all. inversion H5; subst.
                      do 2 eexists; split; eauto.
                      do 2 (rewrite TMap.gso; eauto).
                  * intros. inversion H6; subst. simpl in *.
                    apply H5 in Hposs as ?. simpl in *. 
                    destruct (Nat.eqb_spec i i0); subst; eauto. congruence.
              }
              (* fail *)
              {
                pupdate_start.
                pupdate_trylin_from H1.
                eapply rt_trans.
                eapply rt_step, ps_inv; eauto.
                do 2 constructor.
                eapply rt_step, ps_ret; eauto; [|rewrite TMap.gss; auto].
                constructor. eapply step_tryResolveTask_fail; eauto.
                eapply ACTrylinFinish.

                  (* * intros. inversion H7; subst. simpl in *.
                    apply H6 in Hposs. simpl in *.
                    destruct (Nat.eqb_spec ticket0 i); subst; eauto. *)

                repeat split; simpl_all.
                - exists (Idle {| current := current0; ticket := ticket0; owner := owner0 |}),
                (TMap.add t1 (ls_linr (tryResolveTask (CTask t0 o n i) v) tt)
                  (TMap.add t1 (ls_lini (tryResolveTask (CTask t0 o n i) v)) x0)).
                  eexists; split; [|split;eauto].
                  constructor; inversion 1; subst; try constructor; eauto.
                  eapply rt_trans.
                  eapply rt_step, ps_inv; eauto.
                  do 2 constructor.
                  eapply rt_step, ps_ret; eauto; [|rewrite TMap.gss; auto].
                  constructor. eapply step_tryResolveTask_fail; eauto.
                - destruct H4. apply H3 in H1. simpl in *. congruence.
                - inversion H3; subst. simpl.
                  apply H4 in H1 as [? ?]. eauto.
                - inversion H3; subst. simpl.
                  apply H4 in H1 as [? ?]. simpl in *.
                  intros. unfold owner_upd.
                  destruct (Nat.eqb_spec i i0); subst; eauto; try lia.
                - inversion 1; subst. simpl_all.
                  rewrite TMap.gss; eauto.
                - right. intros. simpl_all.
                  split.
                  * split; intros [? [? [? ?]]]; [|inversion H6;subst].
                    + exists (Idle {| current := current0; ticket := ticket0; owner := owner0 |}),
                      (TMap.add t1 (ls_linr (tryResolveTask (CTask t0 o n i) v) tt)
                        (TMap.add t1 (ls_lini (tryResolveTask (CTask t0 o n i) v)) x0)). simpl.
                      apply H in H5 as HΔ'; inversion HΔ'; simpl in *; subst.
                      simpl. split; [constructor|do 2 (rewrite TMap.gso; eauto) ]; eauto.
                      eapply rt_trans.
                      eapply rt_step, ps_inv; eauto.
                      do 2 constructor.
                      eapply rt_step, ps_ret; eauto.
                      constructor. eapply step_tryResolveTask_fail; eauto.
                      rewrite TMap.gss; auto.
                    + simpl_all. inversion H5; subst.
                      do 2 eexists; split; eauto.
                      do 2 (rewrite TMap.gso; eauto).
                  * intros. inversion H6; subst. simpl in *.
                    apply H5 in Hposs as ?. simpl in *. 
                    destruct (Nat.eqb_spec i i0); subst; eauto.
              }
            }
            (* fail *)
            {
              clear H0. rename H1 into Hneq.
              destruct Hpre as [? [? Hticket]].
              pose proof ac_nonempty (Δ1) as [? [? ?]].
              apply H0 in H1 as ?.
              destruct H as [[? [? [? [? ?]]]] ?].
              apply H in H1 as HΔ; inversion HΔ; subst. clear HΔ. simpl in *.
              destruct x3.
              pose proof H4 as [Hcas _].
              apply Hcas in H1 as ?. simpl in *; subst ret. clear Hcas.

              pupdate_start.
              pupdate_trylin_from H1.
              eapply rt_trans.
              eapply rt_step, ps_inv; eauto.
              do 2 constructor.
              eapply rt_step, ps_ret; eauto; [|rewrite TMap.gss; auto].
              constructor. eapply step_tryResolveTask_fail; eauto.
              eapply ACTrylinFinish.

                (* * intros. inversion H7; subst. simpl in *.
                  apply H6 in Hposs. simpl in *.
                  destruct (Nat.eqb_spec ticket0 i); subst; eauto. *)

              repeat split; simpl_all.
              - exists (Idle {| current := current0; ticket := ticket0; owner := owner0 |}),
              (TMap.add t1 (ls_linr (tryResolveTask (CTask t0 o n i) v) tt)
                (TMap.add t1 (ls_lini (tryResolveTask (CTask t0 o n i) v)) x0)).
                eexists; split; [|split;eauto].
                constructor; inversion 1; subst; try constructor; eauto.
                eapply rt_trans.
                eapply rt_step, ps_inv; eauto.
                do 2 constructor.
                eapply rt_step, ps_ret; eauto; [|rewrite TMap.gss; auto].
                constructor. eapply step_tryResolveTask_fail; eauto.
              - inversion 1; subst. auto.
              - inversion H3; subst. simpl.
                apply H4 in H1 as [? ?]. eauto.
              - inversion H3; subst. simpl.
                apply H4 in H1 as [? ?]. simpl in *.
                intros. unfold owner_upd.
                destruct (Nat.eqb_spec i i0); subst; eauto; try lia.
              - inversion 1; subst. simpl_all.
                rewrite TMap.gss; eauto.
              - right. intros. simpl_all.
                split.
                * split; intros [? [? [? ?]]]; [|inversion H6;subst].
                  + exists (Idle {| current := current0; ticket := ticket0; owner := owner0 |}),
                    (TMap.add t1 (ls_linr (tryResolveTask (CTask t0 o n i) v) tt)
                      (TMap.add t1 (ls_lini (tryResolveTask (CTask t0 o n i) v)) x0)). simpl.
                    apply H in H5 as HΔ'; inversion HΔ'; simpl in *; subst.
                    simpl. split; [constructor|do 2 (rewrite TMap.gso; eauto) ]; eauto.
                    eapply rt_trans.
                    eapply rt_step, ps_inv; eauto.
                    do 2 constructor.
                    eapply rt_step, ps_ret; eauto.
                    constructor. eapply step_tryResolveTask_fail; eauto.
                    rewrite TMap.gss; auto.
                  + simpl_all. inversion H5; subst.
                    do 2 eexists; split; eauto.
                    do 2 (rewrite TMap.gso; eauto).
                * intros. inversion H6; subst. simpl in *.
                  apply H5 in Hposs as ?. simpl in *. 
                  destruct (Nat.eqb_spec i i0); subst; eauto.
            }
          }
          intros.
          eapply provable_ret;
          try solve_conj_impl;
          try solve_stable stableDB.
          left; auto.
        }
      }
    }
    {
      simpl_all.
      repeat split.
      - exists (Idle {| current := inr vInit; ticket := 0; owner := fun _ : nat => Inactive |}), (TMap.empty LinState); eexists; split; eauto.
        reflexivity.
      - inversion 1; subst. simpl. auto.
      - inversion H; subst; auto.
      - inversion H; subst; auto.
    }
  Qed.
End CASTaskImpl.
