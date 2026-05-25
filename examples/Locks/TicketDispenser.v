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
Require Import examples.FAI.FAISpec.
Require Import examples.Registers.RegSpec.
Require Import examples.Locks.TicketSpec.


Module TicketDispenserImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS FAISpec RegSpec TicketSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.
  Open Scope prog_scope.
  
  Definition E : layer_interface :=
  {|
    li_sig := Sig.Plus.omap EFAI (EReg nat);
    li_lts := tens_lts VFAI VReg;
    li_init := (Idle O, Idle O);
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := ETicket;
    li_lts := VTicket;
    li_init := Idle (TKS O nil O)
  |}.

  Definition acq_ticket_impl (_ : tid) : Prog (li_sig E) nat :=
    inl fai >= t => Ret t.
  
  Definition cmp_ticket_impl t (_ : tid) : Prog (li_sig E) bool :=
    inr get >= cur => Ret (t =? cur).

  Definition rel_ticket_impl (_ : tid) : Prog (li_sig E) unit :=
    inr get >= cur =>
    inr (set (S cur)) >= _ =>
    Ret tt.

  Definition assertion := @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Definition TicketOwnedBy t : assertion :=
    fun s => exists q, ts_q (state (ρ s)) = t :: q.
  
  Lemma TicketOwnedExclusive {t t' s}:
    t <> t' -> TicketOwnedBy t s -> TicketOwnedBy t' s -> False.
  Proof.
    unfold TicketOwnedBy.
    intros ? [? ?] [? ?].
    rewrite H0 in H1. congruence.
  Qed.

  Definition RegVal v : assertion :=
    fun s => state (snd (σ s)) = v.

  Definition I : assertion :=
    fun s =>
          (* fai matches tail *)
          state (fst (σ s)) = ts_tl (state (ρ s))
          (* reg matches head *)
      /\  state (snd (σ s)) = ts_hd (state (ρ s))
          (* only owner can set tail *)
      /\  (forall t v w, snd (σ s) = Pending v t (set w) -> TicketOwnedBy t s)
      /\  exists tks, ρ s = Idle tks
    .
  
  Definition G t : rg_relation := 
      (* (G_lock t ∪ G_unlock t ∪ G_id t) ∩ *)
      fun s1 s2 => forall t', t <> t'
        -> TMap.find t' (π s1) = TMap.find t' (π s2)
          /\  (TicketOwnedBy t' s1 -> TicketOwnedBy t' s2 /\ state (snd (σ s1)) = state (snd (σ s2))).

  Definition R t : rg_relation :=
    fun s1 s2 =>
      (TicketOwnedBy t s1 -> TicketOwnedBy t s2 /\ state (snd (σ s1)) = state (snd (σ s2))) /\
      (TMap.find t (π s1) = TMap.find t (π s2)).

  Lemma Istable {t} : Stable (R t) I I.
  Proof. unfold Stable. apply ConjRightImpl, ImplRefl. Qed.
  
  Lemma ALinstable {t ls}: Stable (R t) I (ALin t ls).
  Proof.
    unfold Stable, ALin, R.
    intros ? [[? [? [? ?]]] ?].
    rewrite <- H1. auto.
  Qed.

  Lemma OwnedBystable {t} : Stable (R t) I (TicketOwnedBy t).
  Proof.
    unfold Stable, ALin, R.
    intros ? [[? [? [? ?]]] ?].
    destruct (H0 H). auto.
  Qed.

  Lemma OwnedRegValstable {t v} : Stable (R t) I (TicketOwnedBy t //\\ RegVal v).
  Proof.
    unfold Stable, ALin, R.
    intros ? [[? [[? ?] [? ?]]] ?].
    destruct (H1 H). split; auto.
    unfold RegVal in *; rewrite <- H5; auto.
  Qed.

  Create HintDb stableDB.
  Hint Resolve
    Istable
    ALinstable
    OwnedBystable
    OwnedRegValstable
  : stableDB.

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

  Program Definition Mticket : layer_implementation E F := {|
    li_impl m :=
      match m with
      | acq_ticket => acq_ticket_impl
      | cmp_ticket t => cmp_ticket_impl t
      | rel_ticket => rel_ticket_impl
      end
  |}.
  Next Obligation.
    eapply RGILogic.soundness with (R:=R) (G:=G) (I:=I).
    (* valid RG *)
    {
      constructor.
      unfold R. intros.
      destruct H.
      rewrite H1. tauto.
    }
    (* G ⊆ R *)
    {
      unfold G, R.
      intros. intros ? ? ?.
      destruct H0; [specialize (H0 _ H) as [? ?]; split; intros; auto|].
      unfold GINV, Ginv, GRET, Gret, GId, LiftRelation_π in H0;
      destruct H0 as [[? | ?] | ?]; eauto.
      - destruct H0 as (? & ? & ? & ? & ?).
        unfold TicketOwnedBy.
        split; [rewrite H0, H1|]; auto.
        rewrite H3. rewrite PositiveMap.gso; try tauto; auto.
      - destruct H0 as (? & ? & ? & ? & ? & ?).
        unfold TicketOwnedBy.
        split; [rewrite H0, H1|]; auto.
        rewrite H3. rewrite PositiveMap.gro; try tauto; auto.
      - subst; auto.
    }
    intros t; destruct f; simpl.
    (* acq *)
    {
      (* pre-condition *)
      exists (I //\\ ALin t (Semantics.ls_inv acq_ticket)).
      (* post-condition *)
      exists (fun ret => I //\\ ALin t (Semantics.ls_linr acq_ticket ret)).
      constructor;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply IGinv; try apply IGret.
      {
        unfold ALin. intros.
        destruct H; auto.
      }
      simpl. unfold acq_ticket_impl.
      (* fai *)
      eapply provable_vis_safe with
        (P':=I //\\ ALin t (Semantics.ls_inv acq_ticket))
        (Q':=fun ret => I //\\ ALin t (Semantics.ls_linr acq_ticket ret));
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      [solve_no_error| | | ].
      (* inv *)
      {
        pupdate_intros_atomic.
        pupdate_finish.
        split; auto. unfold G; intros; simpl; auto.
      }
      (* res *)
      {
        pupdate_intros_atomic.
        destruct Hpre as [[? [? [? [tks ?]]]] ?]; simpl in *; subst.
        destruct tks as [hd q tl]; simpl in *.
        pupdate_start.
        pupdate_forward t (InvEv acq_ticket).
        pupdate_forward t (ResEv acq_ticket tl).
        pupdate_finish.
        split.
        + unfold Semantics.linstate_atomic_step, ALin, I in *.
          split; simpl in *; [|apply PositiveMap.gss; auto].
          do 2 split; auto. split; eauto.
          intros; subst.
          specialize (H1 _ _ _ eq_refl) as [? ?].
          unfold TicketOwnedBy in *; simpl in *; subst.
          exists (x ++ t :: nil). auto.
        + unfold G. simpl. intros.
          do 2 (rewrite PositiveMap.gso; auto).
          split; auto. unfold TicketOwnedBy. simpl.
          intros [? ?]. split; auto.
          exists (x ++ t :: nil). subst; auto.
      }
      (* return *)
      intros.
      eapply provable_ret_safe; destruct ret;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply ImplRefl.
    }
    (* cmp *)
    {
      rename t0 into tk. 
      (* pre-condition *)
      exists (I //\\ ALin t (Semantics.ls_inv (cmp_ticket tk))).
      (* post-condition *)
      exists (fun ret => I //\\ ALin t (Semantics.ls_linr (cmp_ticket tk) ret)).
      constructor;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply IGinv; try apply IGret.
      {
        unfold ALin. intros.
        destruct H; auto.
      }
      simpl. unfold cmp_ticket_impl.
      (* get *)
      eapply provable_vis_safe with
        (P':=I //\\ ALin t (Semantics.ls_inv (cmp_ticket tk)))
        (Q':=fun ret => I //\\ ALin t (Semantics.ls_linr (cmp_ticket tk) (tk =? ret)));
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      [solve_no_error| | | ].
      (* inv *)
      {
        pupdate_intros_atomic.
        pupdate_finish.
        do 2 split; destruct Hpre; auto.
        unfold I in *; simpl in *; subst; do 3 (split; try tauto).
        inversion 1.
      }
      (* res *)
      {
        pupdate_intros_atomic.
        destruct Hpre as [[? [? [? [tks ?]]]] ?]; simpl in *; subst.
        destruct tks as [hd q tl]; simpl in *.

        pupdate_start.
        pupdate_forward t (InvEv (cmp_ticket tk)).
        pupdate_forward t (ResEv (cmp_ticket tk) (tk =? hd)).
        pupdate_finish.

        split.
        + unfold Semantics.linstate_atomic_step, ALin, I in *.
          split; simpl in *; [|apply PositiveMap.gss; auto].
          do 2 (split; auto). split; eauto.
          inversion 1.
        + unfold G. simpl. intros.
          do 2 (rewrite PositiveMap.gso; auto).
      }
      (* return *)
      intros.
      eapply provable_ret_safe; destruct ret;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply ImplRefl.
    }
    (* rel *)
    {
      (* pre-condition *)
      exists (I //\\ ALin t (Semantics.ls_inv rel_ticket)).
      (* post-condition *)
      exists (fun ret => I //\\ ALin t (Semantics.ls_linr rel_ticket ret)).
      constructor;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply IGinv; try apply IGret.
      {
        unfold ALin. intros.
        destruct H; auto.
      }
      simpl. unfold rel_ticket_impl.
      (* perror *)
      eapply provable_perror with (P':=I //\\ ALin t (Semantics.ls_inv rel_ticket) //\\ TicketOwnedBy t).
      {
        unfold ALin, I. intros ? ?.
        destruct H as [[? [? [? [? ?]]]] ?].
        destruct s, ρ0; simpl in *; try congruence.
        inversion H2; subst.
        destruct x as [hd q tl]; simpl in *.
        destruct q as [| t' q];
        [ right; do 2 econstructor; simpl; eauto;
          constructor; eapply error_empty_queue; eauto |].
        destruct (Pos.eq_dec t t'); subst; simpl in *.
        - unfold TicketOwnedBy. left.
          do 2 (split; simpl; eauto).
        - right; do 2 econstructor; simpl; eauto;
          constructor; eapply error_jump_queue; eauto.
      }
      (* get *)
      eapply provable_vis_safe with
        (P':=I //\\ ALin t (Semantics.ls_inv rel_ticket) //\\ TicketOwnedBy t)
        (Q':=fun ret => I //\\ ALin t (Semantics.ls_inv rel_ticket) //\\ (TicketOwnedBy t //\\ RegVal ret));
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      [solve_no_error| | | ].
      (* inv *)
      {
        pupdate_intros_atomic.
        pupdate_finish.
        
        do 2 split; destruct Hpre as [[? ?] ?]; auto.
        unfold I in *; simpl in *; subst; do 3 (split; try tauto).
        inversion 1.
      }
      (* res *)
      {
        pupdate_intros_atomic.
        destruct Hpre as [[? [? [? [tks ?]]]] [? ?]]; simpl in *; subst.
        destruct tks as [hd q tl]; simpl in *.
        pupdate_finish.

        unfold I, TicketOwnedBy, RegVal.
        do 3 split; simpl; eauto.
        - split; auto. split; eauto. inversion 1.
        - split; simpl; eauto.
      }
      intros v.
      (* set *)
      eapply provable_vis_safe with
        (P':=I //\\ ALin t (Semantics.ls_inv rel_ticket) //\\ (TicketOwnedBy t //\\ RegVal v))
        (Q':=fun ret => I //\\ ALin t (Semantics.ls_linr rel_ticket tt));
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      [ | | | ].
      (* safe *)
      {
        intros ? ([? ?] & ? & ?) ?.
        destruct s, σ0; simpl in *.
        inversion H3; subst.
        destruct H2.
        destruct H0 as (_ & ? & _).
        specialize (H0 _ _ _ eq_refl).
        eapply TicketOwnedExclusive; eauto.
      }
      (* inv *)
      {
        pupdate_intros_atomic.
        pupdate_finish.

        do 2 split; destruct Hpre as [[? ?] ?]; auto.
        unfold I in *; simpl in *; subst; do 3 (split; try tauto).
        inversion 1; subst.
        destruct H1 as (_ & ? & _). auto.
      }
      (* res *)
      {
        pupdate_intros_atomic.
        destruct Hpre as [[? [? [? [tks ?]]]] [? [[q' ?] ?]]]; simpl in *; subst.
        destruct tks as [hd q tl]; subst; simpl in *.
        inversion Hstep; subst.

        pupdate_start.
        pupdate_forward t (InvEv rel_ticket).
        pupdate_forward t (ResEv rel_ticket tt).
        pupdate_finish.

        split.
        + unfold Semantics.linstate_atomic_step, ALin, I in *.
          split; simpl in *; [|apply PositiveMap.gss; auto].
          do 2 split; auto. split; eauto. inversion 1.
        + unfold G. simpl. intros.
          do 2 (rewrite PositiveMap.gso; auto).
          split; auto. unfold TicketOwnedBy. simpl.
          intros [? ?]. congruence.
      }

      (* return *)
      intros.
      eapply provable_ret_safe; destruct ret;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply ImplRefl.
    }
    {
      unfold I; simpl.
      do 3 (split; eauto).
      inversion 1.
    }
  Defined.

  Print Assumptions Mticket.

End TicketDispenserImpl.
