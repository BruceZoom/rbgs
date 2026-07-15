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
Require Import examples.CAS.CASRegSpec.
Require Import examples.Exchanger.ExchangerSpec.


Module ExchangerImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS CASRegSpec ExchSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.

  Variant Offer :=
  | Offered (t1 : tid) (v1 : A)
  | Accepted (t1 t2 : tid) (v1 v2 : A)
  | Empty.
  Arguments Offer : clear implicits.

  Definition E : layer_interface :=
  {|
    li_sig := ECASReg Offer;
    li_lts := VCASReg;
    li_init := Idle Empty;
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := EExch A;
    li_lts := VExch;
    li_init := ExSIdle
  |}.
  
  Definition exch_impl (v : A) (t:tid) : Prog (li_sig E) (option A) :=
    cas Empty (Offered t v) >= offered =>
    (* successfully proposed an offer *)
    if offered then
      cas (Offered t v) Empty >= revoked =>
      (* revoked *)
      if revoked then
        Ret None
      (* accepted *)
      else
        get >= w =>
        match w with
        | Accepted _ _ _ v' =>
           (* clean up *)
            cas w Empty >= _ =>
            Ret (Some v')
        (* impossible *)
        | _ => Ret None
        end
    (* already exists an offer *)
    else
      get >= w =>
      match w with
      (* attempt exchange *)
      | Offered t' v' =>
          cas w (Accepted t' t v' v) >= accepted =>
          Ret (if accepted then (Some v') else None)
      (* failed *)
      | _ => Ret None
      end
  .

  Definition assertion := @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.

  Definition ExchRel (o : Offer) (es : @EExchState A) (π : tmap Semantics.LinState) : Prop :=
    match o, es with
    | Empty, ExSIdle => True
    | Offered t v, ExSIdle =>
        TMap.find t π = Some (Semantics.ls_inv (exch v))
    | Accepted _ _ _ _, ExSIdle => True
    | _, _ => False
    end.

  Definition I : assertion :=
    fun s => ExchRel (state (σ s)) (ρ s) (π s).

  Definition OfferedBy (t : tid) (v : A) : assertion :=
    fun s => state (σ s) = Offered t v /\
      ρ s = ExSIdle /\
      ALin t (Semantics.ls_inv (exch v)) s.

  Definition AcceptedByFirst (t : tid) (v : A) (other : A) : assertion :=
    fun s => exists t2, state (σ s) = Accepted t t2 v other /\
      ρ s = ExSIdle /\
      ALin t (Semantics.ls_linr (exch v) (Some other)) s.

  Definition AcceptedBySecond (t : tid) (v : A) (other : A) : assertion :=
    fun s => exists t1, state (σ s) = Accepted t1 t other v /\
      ρ s = ExSIdle /\
      ALin t (Semantics.ls_linr (exch v) (Some other)) s.

  Definition NoOfferBy (t : tid) : assertion :=
    fun s => forall v, state (σ s) <> Offered t v.

  Definition FirstLive (t : tid) (v : A) : assertion :=
    (OfferedBy t v //\\ ALin t (Semantics.ls_inv (exch v))) \\//
    (∃ other, AcceptedByFirst t v other //\\
      ALin t (Semantics.ls_linr (exch v) (Some other))).

  Definition R_pres (t : tid) : rg_relation :=
    fun s1 s2 =>
      (TMap.find t (π s1) = None <-> TMap.find t (π s2) = None) /\
      (forall v, (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t) s1 ->
        (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t) s2) /\
      (forall v ret, ALin t (Semantics.ls_linr (exch v) ret) s1 ->
        ALin t (Semantics.ls_linr (exch v) ret) s2) /\
      (NoOfferBy t s1 -> NoOfferBy t s2) /\
      (forall v other, AcceptedByFirst t v other s1 ->
        AcceptedByFirst t v other s2) /\
      (forall v, FirstLive t v s1 -> FirstLive t v s2).

  Definition G t : rg_relation :=
    fun s1 s2 => forall t', t <> t' -> R_pres t' s1 s2.

  Definition R t : rg_relation :=
    R_pres t.

  Lemma Istable {t} : Stable (R t) I I.
  Proof. unfold Stable. apply ConjRightImpl, ImplRefl. Qed.

  Lemma ActiveInvstable {t v}: Stable (R t) I
    (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Halin [_ [Hinv _]]]] HI].
    eauto.
  Qed.

  Lemma ALinRetstable {t v ret}: Stable (R t) I (ALin t (Semantics.ls_linr (exch v) ret)).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Halin [_ [_ [Hret _]]]]] HI].
    eauto.
  Qed.

  Lemma AcceptedByFirststable {t v other}: Stable (R t) I (AcceptedByFirst t v other).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Hacc [_ [_ [_ [_ [Hpres _]]]]]]] HI].
    eauto.
  Qed.

  Lemma IAcceptedByFirstStable {t v}: Stable (R t) I (I //\\ ∃ other, AcceptedByFirst t v other).
  Proof.
    unfold Stable.
    intros s [[s' [[HI [other Hacc]] HR]] HI2].
    split.
    - apply (Istable (t:=t)); split; [exists s'; split; [exact HI|exact HR]|exact HI2].
    - exists other.
      apply (AcceptedByFirststable (t:=t) (v:=v) (other:=other)); split;
        [exists s'; split; [exact Hacc|exact HR]|exact HI2].
  Qed.

  Lemma IAcceptedByFirstPureStable {t v} (P : A -> Prop):
    Stable (R t) I (I //\\ ∃ other, AcceptedByFirst t v other //\\ ⌜P other⌝).
  Proof.
    unfold Stable.
    intros s [[s' [[HI [other [Hacc Hpure]]] HR]] HI2].
    split.
    - apply (Istable (t:=t)); split; [exists s'; split; [exact HI|exact HR]|exact HI2].
    - exists other; split.
      + apply (AcceptedByFirststable (t:=t) (v:=v) (other:=other)); split;
        [exists s'; split; [exact Hacc|exact HR]|exact HI2].
      + exact Hpure.
  Qed.

  Lemma FirstLivestable {t v}: Stable (R t) I (FirstLive t v).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Hfl [_ [_ [_ [_ [_ Hlive]]]]]]] HI].
    eauto.
  Qed.

  Lemma NoOfferBystable {t}: Stable (R t) I (NoOfferBy t).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Hno [_ [_ [_ [Hpres _]]]]]] HI].
    eauto.
  Qed.

  Lemma R_pres_unchanged t (s1 s2 : @ProofState _ _ (li_lts E) (li_lts F)) :
    σ s1 = σ s2 ->
    ρ s1 = ρ s2 ->
    TMap.find t (π s1) = TMap.find t (π s2) ->
    R_pres t s1 s2.
  Proof.
    intros Hσ Hρ Hπ.
    destruct s1 as [σ1 ρ1 π1], s2 as [σ2 ρ2 π2]; simpl in *; subst.
	    unfold R_pres, ALin; simpl.
	    repeat split; intros; simpl in *.
	    - rewrite <- Hπ. auto.
	    - rewrite Hπ. auto.
	    - destruct H as [Hlin Hno].
	      unfold ALin in *; simpl in *.
	      change (TMap.find t π2 = Some (Semantics.ls_inv (exch v))).
	      rewrite <- Hπ.
	      change (TMap.find t π1 = Some (Semantics.ls_inv (exch v))) in Hlin.
	      exact Hlin.
	    - destruct H as [_ Hno]. exact Hno.
	    - rewrite <- Hπ. auto.
	    - unfold NoOfferBy in *; auto.
	    - unfold AcceptedByFirst in *.
      destruct H as [t2 [? [? ?]]].
      exists t2. repeat split; auto.
      unfold ALin in *; simpl in *; rewrite <- Hπ; auto.
    - unfold FirstLive, OfferedBy, AcceptedByFirst, Disj, Conj in *.
      destruct H as [[Hoff Hlin] | [other [Hacc Hlin]]].
      + left. split; [|unfold ALin in *; simpl in *; rewrite <- Hπ; auto].
        destruct Hoff as [? [? ?]]. repeat split; auto.
        unfold ALin in *; simpl in *; rewrite <- Hπ; auto.
      + right. exists other. split; [|unfold ALin in *; simpl in *; rewrite <- Hπ; auto].
        destruct Hacc as [t2 [? [? ?]]].
        exists t2. repeat split; auto.
        unfold ALin in *; simpl in *; rewrite <- Hπ; auto.
    all: unfold ALin in *; simpl in *; try congruence; eauto.
  Qed.

  Lemma R_pres_same_obs t (s1 s2 : @ProofState _ _ (li_lts E) (li_lts F)) :
    state (σ s1) = state (σ s2) ->
    ρ s1 = ρ s2 ->
    TMap.find t (π s1) = TMap.find t (π s2) ->
    R_pres t s1 s2.
  Proof.
    intros Hσ Hρ Hπ.
    destruct s1 as [σ1 ρ1 π1], s2 as [σ2 ρ2 π2]; simpl in *; subst.
	    unfold R_pres, ALin; simpl.
	    repeat split; intros; simpl in *.
	    - rewrite <- Hπ. auto.
	    - rewrite Hπ. auto.
	    - destruct H as [Hlin Hno].
	      unfold ALin in *; simpl in *.
	      change (TMap.find t π2 = Some (Semantics.ls_inv (exch v))).
	      rewrite <- Hπ.
	      change (TMap.find t π1 = Some (Semantics.ls_inv (exch v))) in Hlin.
	      exact Hlin.
	    - destruct H as [_ Hno].
	      unfold NoOfferBy in *. intros vx Hbad. apply (Hno vx). simpl in *. rewrite Hσ. auto.
	    - rewrite <- Hπ. auto.
	    - unfold NoOfferBy in *. intros vx Hbad. apply (H vx). simpl in *. rewrite Hσ. auto.
	    - unfold AcceptedByFirst in *.
      destruct H as [t2 [? [? ?]]].
      exists t2. repeat split; auto.
      * simpl in *. rewrite <- Hσ. auto.
      * unfold ALin in *; simpl in *; rewrite <- Hπ; auto.
    - unfold FirstLive, OfferedBy, AcceptedByFirst, Disj, Conj in *.
      destruct H as [[Hoff Hlin] | [other [Hacc Hlin]]].
      + left. split; [|unfold ALin in *; simpl in *; rewrite <- Hπ; auto].
        destruct Hoff as [? [? ?]]. repeat split; auto.
        * simpl in *. rewrite <- Hσ. auto.
        * unfold ALin in *; simpl in *; rewrite <- Hπ; auto.
      + right. exists other. split; [|unfold ALin in *; simpl in *; rewrite <- Hπ; auto].
        destruct Hacc as [t2 [? [? ?]]].
        exists t2. repeat split; auto.
        * simpl in *. rewrite <- Hσ. auto.
        * unfold ALin in *; simpl in *; rewrite <- Hπ; auto.
    all: unfold ALin in *; simpl in *; try congruence; eauto.
  Qed.

  Lemma no_FirstLive_idle_pending_empty t v0 t0 (op : Sig.op (li_sig E)) ρ π :
    ~ FirstLive t v0
        (@Build_ProofStateSingle (li_sig E) (li_sig F) (li_lts E) (li_lts F)
          (Pending Empty t0 op) ρ π).
  Proof.
    unfold FirstLive, OfferedBy, AcceptedByFirst, Logics.Disj, Logics.Conj, ALin.
    simpl. intros [[[H _] _] | [other [[t2 [H _]] _]]]; discriminate H.
  Qed.

	  Lemma R_pres_offer_pass_other t t0 v (sρ : State (li_lts F)) π :
    t0 <> t ->
    R_pres t
      (@Build_ProofStateSingle (li_sig E) (li_sig F) (li_lts E) (li_lts F)
        (Pending Empty t0 (cas Empty (Offered t0 v))) sρ π)
	      (@Build_ProofStateSingle (li_sig E) (li_sig F) (li_lts E) (li_lts F)
	        (Idle (Offered t0 v)) sρ π).
	  Proof.
	    intros Hneq.
	    unfold R_pres, ALin, NoOfferBy.
	    repeat split; intros; simpl in *;
	    try solve [auto].
	    - destruct H as [Hlin Hno]. exact Hlin.
	    - intro Hbad. inversion Hbad; subst. contradiction.
	    - intro Hbad. inversion Hbad; subst. contradiction.
	    - unfold AcceptedByFirst in H. simpl in H.
	      destruct H as [? [Hbad _]]. discriminate Hbad.
	    - exfalso. eapply no_FirstLive_idle_pending_empty; eauto.
	  Qed.

  Lemma cas_empty_offer_success_ret_true t v ret :
    StepCASReg {| te_tid := t; te_ev := ResEv (cas Empty (Offered t v)) ret |}
      Empty (Offered t v) ->
    ret = true.
  Proof.
    intros Hstep.
    destruct ret; auto.
    inversion Hstep; subst; try congruence.
    all: match goal with
    | H : ?e1 = ?e2 |- _ =>
        pose proof (f_equal
          (fun e => match te_ev e with
                    | ResEv (cas _ _) b => Some b
                    | _ => None
                    end) H) as Hr;
        simpl in Hr; discriminate Hr
    end.
  Qed.

  Lemma cas_empty_offer_fail_ret_false t v u ret :
    StepCASReg {| te_tid := t; te_ev := ResEv (cas Empty (Offered t v)) ret |}
      u u ->
    u <> Empty ->
    ret = false.
  Proof.
    intros Hstep Hneq.
    destruct ret.
    - inversion Hstep; subst; try congruence.
      all: match goal with
      | H : ?e1 = ?e2 |- _ =>
          pose proof (f_equal
            (fun e => match te_ev e with
                      | ResEv (cas _ _) b => Some b
                      | _ => None
                      end) H) as Hr;
          simpl in Hr; discriminate Hr
      end.
    - reflexivity.
  Qed.

  Ltac event_ret_bool_contra :=
    match goal with
    | H : ?e1 = ?e2 |- _ =>
        pose proof (f_equal
          (fun e => match te_ev e with
                    | ResEv (cas _ _) b => Some b
                    | _ => None
                    end) H) as Hr;
        simpl in Hr; discriminate Hr
    end.

  Lemma cas_offer_empty_success_ret_true t v ret :
    StepCASReg {| te_tid := t; te_ev := ResEv (cas (Offered t v) Empty) ret |}
      (Offered t v) Empty ->
    ret = true.
  Proof.
    intros Hstep.
    destruct ret; auto.
    inversion Hstep; subst; try congruence.
    all: event_ret_bool_contra.
  Qed.

  Lemma cas_offer_empty_fail_ret_false t v u ret :
    StepCASReg {| te_tid := t; te_ev := ResEv (cas (Offered t v) Empty) ret |}
      u u ->
    u <> Offered t v ->
    ret = false.
  Proof.
    intros Hstep Hneq.
    destruct ret.
    - inversion Hstep; subst; try congruence.
      all: event_ret_bool_contra.
    - reflexivity.
  Qed.

  Lemma cas_source_success_target t (u w s2 : Offer) ret :
    StepCASReg {| te_tid := t; te_ev := ResEv (cas u w) ret |} u s2 ->
    s2 = w.
  Proof.
    intros Hstep.
    inversion Hstep; subst; try inversion_thread_event_eq; auto.
    all: try match goal with
    | Hneq : ?x <> ?x |- _ => contradiction
    | H : ?e1 = ?e2 |- _ =>
        pose proof (f_equal
          (fun e => match te_ev e with
                    | ResEv (cas x y) _ => Some (x, y)
                    | _ => None
                    end) H) as Hr;
        simpl in Hr; inversion Hr; subst; auto
    end.
  Qed.

  Lemma get_ret_state t (u ret : Offer) :
    StepCASReg {| te_tid := t; te_ev := ResEv get ret |} u u ->
    ret = u.
  Proof.
    intros Hstep.
    inversion Hstep; subst; try inversion_thread_event_eq; auto.
    all: try match goal with
    | H : existT _ get _ = existT _ get _ |- _ =>
        dependent destruction H; auto
    | H : ?e1 = ?e2 |- _ =>
        pose proof (f_equal
          (fun e => match te_ev e with
                    | ResEv get x => Some x
                    | _ => None
                    end) H) as Hr;
        simpl in Hr; inversion Hr; auto
    end.
  Qed.

  Create HintDb stableDB.
  #[local] Hint Resolve
    Istable
    ActiveInvstable
    ALinRetstable
    AcceptedByFirststable
    FirstLivestable
    NoOfferBystable
  : stableDB.

  Ltac solve_no_cas_error :=
    unfold ANoError; intros ? ? Herr;
    inversion Herr; subst;
    repeat match goal with
    | H : ErrorCASReg _ _ |- _ => inversion H; subst; clear H
    | H : {| te_tid := _; te_ev := InvEv (cas _ _) |} =
          {| te_tid := _; te_ev := InvEv (set _) |} |- _ => inversion H
    | H : {| te_tid := _; te_ev := InvEv get |} =
          {| te_tid := _; te_ev := InvEv (set _) |} |- _ => inversion H
    end.

  Ltac solve_exch_obligation :=
    first [
      solve_no_cas_error
    | apply ConjLeftImpl, ImplRefl
    | intros []; apply ConjLeftImpl, ImplRefl
    ].

  Lemma IGinv : forall t f, ⊨ Ginv t f ⊚ I ==>> I //\\ ALin t (Semantics.ls_inv f).
  Proof.
    unfold I, ALin, Ginv, LiftRelation_π.
    intros t f s [s' [HI [? [? [Hnone ?]]]]].
    destruct s, s'; simpl in *; subst.
    split; simpl; auto.
    - destruct σ0; destruct ρ0; destruct s; simpl in *; auto; try contradiction;
	      try match goal with
	      | HI : TMap.find ?to π1 = Some _ |- TMap.find ?to (TMap.add t _ π1) = Some _ =>
	          destruct (PositiveMap.E.eq_dec t to); subst;
	          [rewrite Hnone in HI; discriminate|rewrite PositiveMap.gso; auto]
	      | HI : TMap.find ?to π1 = Some _ /\ _ |- TMap.find ?to (TMap.add t _ π1) = Some _ /\ _ =>
	          destruct HI as [HI ?]; split; auto;
	          destruct (PositiveMap.E.eq_dec t to); subst;
	          [rewrite Hnone in HI; discriminate|rewrite PositiveMap.gso; auto]
	      end.
    - rewrite PositiveMap.gss; auto.
  Qed.

  Lemma IGinvActive : forall t v,
    ⊨ Ginv t (exch v) ⊚ I ==>>
      I //\\ (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t).
  Proof.
    unfold I, ALin, NoOfferBy, Ginv, LiftRelation_π.
    intros t v s [s' [HI [? [? [Hnone ?]]]]].
    destruct s, s'; simpl in *; subst.
    split.
    - destruct σ0; destruct ρ0; destruct s; simpl in *; auto; try contradiction;
        try match goal with
        | HI : TMap.find ?to π1 = Some _ |- TMap.find ?to (TMap.add t _ π1) = Some _ =>
            destruct (PositiveMap.E.eq_dec t to); subst;
            [rewrite Hnone in HI; discriminate|rewrite PositiveMap.gso; auto]
        end.
    - split.
      + change (TMap.find t (TMap.add t (Semantics.ls_inv (exch v)) π1) =
          Some (Semantics.ls_inv (exch v))).
        rewrite PositiveMap.gss; auto.
      + intros v0 Hoff.
        destruct σ0; simpl in Hoff; try discriminate.
        * inversion Hoff; subst.
          simpl in HI.
          destruct ρ0; try contradiction.
          rewrite Hnone in HI. discriminate.
        * destruct s; try discriminate.
          inversion Hoff; subst.
          simpl in HI.
          destruct ρ0; try contradiction.
          rewrite Hnone in HI. discriminate.
        all: auto.
  Qed.

  Lemma IGret : forall t f ret,
    ⊨ Gret t f ret ⊚ (I //\\ ALin t (Semantics.ls_linr f ret)) ==>> I.
  Proof.
    unfold I, ALin, Gret, LiftRelation_π.
    intros t f ret s [s' [[HI Hlin] [? [? [? ?]]]]].
    destruct s, s'; simpl in *; subst.
    destruct σ0; destruct ρ0; destruct s; simpl in *; auto; try contradiction;
	    try match goal with
	    | HI : TMap.find ?to ?pm = Some _ |- TMap.find ?to (TMap.remove t ?pm) = Some _ =>
	        destruct (PositiveMap.E.eq_dec t to); subst;
	        [simpl in Hlin; rewrite HI in Hlin; discriminate|rewrite PositiveMap.gro; auto]
	    | HI : TMap.find ?to ?pm = Some _ /\ _ |- TMap.find ?to (TMap.remove t ?pm) = Some _ /\ _ =>
	        destruct HI as [HI ?]; split; auto;
	        destruct (PositiveMap.E.eq_dec t to); subst;
	        [simpl in Hlin; rewrite HI in Hlin; discriminate|rewrite PositiveMap.gro; auto]
	    end.
  Qed.

  Program Definition Mexchanger : layer_implementation E F := {|
    li_impl m :=
      match m with
      | exch v => exch_impl v
      end
  |}.
  Next Obligation.
    eapply RGILogic.soundness with (R:=R) (G:=G) (I:=I).
    {
      constructor.
      unfold R, R_pres. intros. tauto.
    }
    {
      unfold G, R.
      intros t1 t2 Hneq s1 s2 Hstep.
      destruct Hstep as [HG | [[Hinv | Hret] | Hid]]; eauto.
      - unfold GINV, Ginv, LiftRelation_π in Hinv.
        destruct Hinv as (? & ? & ? & ? & Hπ).
        eapply R_pres_unchanged; [eauto|eauto|].
        rewrite Hπ. rewrite PositiveMap.gso; auto.
      - unfold GRET, Gret, LiftRelation_π in Hret.
        destruct Hret as (? & ? & ? & ? & ? & Hπ).
        eapply R_pres_unchanged; [eauto|eauto|].
        rewrite Hπ. rewrite PositiveMap.gro; auto.
      - unfold GId in Hid. subst. eapply R_pres_unchanged; reflexivity.
    }
    intros t; destruct f as [v].
    exists (I //\\ (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t)).
    exists (fun ret => I //\\ ALin t (Semantics.ls_linr (exch v) ret)).
    constructor;
    try solve_conj_impl;
    try solve_conj_stable stableDB;
    try apply IGinvActive; try apply IGret.
    {
      intros ret σ0 ρ0 π0 H. exact (proj2 H).
    }
    simpl. unfold exch_impl.
    eapply provable_vis_safe with
      (P':=I //\\ (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t))
      (Q':=fun offered =>
        I //\\ match offered with
               | true => FirstLive t v
               | false => ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t
               end);
    try solve [solve_conj_impl|solve_exch_obligation|solve_conj_stable stableDB];
    [intro offered; destruct offered; solve_conj_stable stableDB| | | ].
    {
      pupdate_intros_atomic.
      dependent destruction Hstep0.
      pupdate_finish.
      split.
      - destruct Hpre as [HI [Hlin Hno]]; split; [exact HI|split; [exact Hlin|exact Hno]].
      - unfold G. intros.
        eapply R_pres_same_obs; simpl; auto.
    }
    {
      pupdate_intros_atomic.
      destruct Hpre as [HI [Hlin Hno]].
      inversion Hstep0; subst; try inversion_thread_event_eq; simpl in *; try discriminate; try congruence.
	      - pose proof (cas_empty_offer_success_ret_true t1 v ret Hstep0) as Hret.
	        rewrite Hret.
	        destruct ρ1; simpl in HI; try contradiction.
	        pupdate_finish.
	        split.
	        + split.
	          * unfold I, ALin; simpl; auto.
	          * unfold FirstLive, OfferedBy, ALin, Logics.Disj, Logics.Conj.
	            simpl.
	            left. split.
	            -- repeat split; auto.
	            -- auto.
		        + unfold G. intros.
		          unfold R_pres, ALin, NoOfferBy, AcceptedByFirst, FirstLive, OfferedBy, Disj, Conj.
			          repeat split; intros; simpl in *; auto.
					          -- destruct H1 as [Hlin' Hno']. exact Hlin'.
				          -- intro Hbad. inversion Hbad; subst. auto.
				          -- intro Hbad. inversion Hbad; subst. auto.
				          -- destruct H1 as [? [Hbad _]]. discriminate Hbad.
				          -- destruct H1 as [[[Hbad _] _] | [other [[? [Hbad _]] _]]];
		             [discriminate Hbad|discriminate Hbad].
      - pupdate_finish.
        split.
        + match goal with
          | Hneq : ?u <> Empty |- _ =>
              pose proof (cas_empty_offer_fail_ret_false t1 v u ret Hstep0 Hneq) as Hret;
              subst ret
          end.
          destruct ρ1; destruct s0; unfold I in HI; simpl in HI; try contradiction.
          all: unfold I, ALin, Conj in *; simpl in *; split; auto; split; auto.
        + unfold G. intros.
          eapply R_pres_same_obs; simpl; auto.
    }
    intros offered; destruct offered.
    - eapply provable_vis_safe with
        (P':=I //\\ FirstLive t v)
        (Q':=fun revoked =>
          I //\\ match revoked with
                 | true => ALin t (Semantics.ls_linr (exch v) None)
                 | false => ∃ other, AcceptedByFirst t v other
                 end);
      try solve [solve_conj_impl|solve_exch_obligation|solve_conj_stable stableDB];
      [intro revoked; destruct revoked;
       try solve_conj_stable stableDB;
       apply ConjStable; [apply Istable|apply StableExists; intros; apply AcceptedByFirststable]
      | | | ].
      {
        pupdate_intros_atomic.
        inversion Hstep0; subst; try inversion_thread_event_eq.
        pupdate_finish.
        split.
        - destruct Hpre as [HI Hlive]. split; auto.
        - unfold G. intros.
          eapply R_pres_same_obs; simpl; auto.
      }
      {
        pupdate_intros_atomic.
        destruct Hpre as [HI Hlive].
        unfold FirstLive, OfferedBy, AcceptedByFirst, Disj, Conj, ALin in Hlive.
        inversion Hstep0; subst; try inversion_thread_event_eq; simpl in *; try discriminate; try congruence.
        - pose proof (cas_offer_empty_success_ret_true t1 v ret Hstep0) as Hret.
          subst ret.
          destruct Hlive as [[[Hstate [Hrho Hlini]] _] | [other [[t2 [Hstate [Hrho Hretlin]]] _]]].
	          + subst. simpl in *.
	            pupdate_start.
	            {
	              eapply rt_trans.
	              - eapply rt_step.
	                eapply (Semantics.ps_inv t1 (exch v)).
	                + eapply step_exch_offer. reflexivity.
	                + exact Hlini.
	              - eapply rt_step.
	                eapply (Semantics.ps_ret t1 (exch v) None).
	                + eapply step_exch_revoke. reflexivity.
	                + rewrite PositiveMap.gss. auto.
	            }
            split.
            * split.
              -- unfold I. simpl. auto.
              -- unfold ALin. simpl. rewrite PositiveMap.gss. auto.
	            * unfold G. intros.
	              unfold R_pres, ALin, NoOfferBy.
		              repeat split; intros; simpl in *;
			              try solve [destruct H1 as [Hlin' _]; simpl in Hlin';
			                rewrite PositiveMap.gso; [rewrite PositiveMap.gso; [exact Hlin'|auto]|auto]];
			              try solve [destruct H1 as [_ _]; intro Hbad; discriminate Hbad];
		              try solve [rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto]];
		              try solve [rewrite PositiveMap.gso in H1; [rewrite PositiveMap.gso in H1; auto|auto]];
		              try solve [rewrite PositiveMap.gso; auto];
		              try solve [rewrite PositiveMap.gso in H1; auto];
		              try solve [intro Hbad; discriminate Hbad];
		              try solve [unfold AcceptedByFirst in H1; simpl in H1; destruct H1 as [? [Hbad _]]; discriminate Hbad];
	              try solve [unfold FirstLive, OfferedBy, AcceptedByFirst, Disj, Conj, ALin in H1;
	                destruct H1 as [[[Hbad _] _] | [other [[? [Hbad _]] _]]];
	                [inversion Hbad; subst; contradiction|discriminate Hbad]].
		              all: try match goal with
		              | H : exists _, _ |- _ =>
		                  unfold AcceptedByFirst in H; simpl in H;
		                  destruct H as [? [Hbad _]]; discriminate Hbad
	              | H : _ \/ _ |- _ =>
		                  unfold FirstLive, OfferedBy, AcceptedByFirst, Disj, Conj, ALin in H;
		                  destruct H as [[[Hoff _] _] | [other [[? [Hbad _]] _]]];
			                  [inversion Hoff; subst; contradiction|discriminate Hbad]
			              end.
	          + simpl in Hstate. congruence.
        - pose proof (cas_offer_empty_fail_ret_false t1 v s0 ret Hstep0) as Hret.
          assert (s0 <> Offered t1 v).
          {
            intro Heq. subst.
            destruct Hlive as [[[Hstate _] _] | [other [[t2 [Hstate _]] _]]]; simpl in *; congruence.
          }
          specialize (Hret H1). subst ret.
          pupdate_finish.
          split.
          + destruct Hlive as [[[Hstate [Hrho Hlini]] _] | [other [[t2 [Hstate [Hrho Hretlin]]] _]]].
            * simpl in *. congruence.
            * split.
              -- destruct ρ1; destruct s0; unfold I in *; simpl in *; auto; try contradiction.
              -- exists other. unfold AcceptedByFirst, ALin. simpl.
                 exists t2. repeat split; auto.
          + unfold G. intros.
            eapply R_pres_same_obs; simpl; auto.
      }
      intros revoked; destruct revoked.
      + eapply provable_ret_safe;
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        try apply ImplRefl.
      + eapply provable_vis_safe with
          (P':=I //\\ (∃ other, AcceptedByFirst t v other))
          (Q':=fun w =>
            I //\\ ∃ other,
              AcceptedByFirst t v other //\\
              ⌜exists t2, w = Accepted t t2 v other⌝);
        try solve [solve_conj_impl|solve_exch_obligation|solve_conj_stable stableDB].
        1: apply IAcceptedByFirstStable.
        1: { let w := fresh "w" in intro w; eapply IAcceptedByFirstPureStable. }
        {
          pupdate_intros_atomic.
          inversion Hstep0; subst; try inversion_thread_event_eq.
          pupdate_finish.
          split.
          - destruct Hpre as [HI Hacc]. split; auto.
          - unfold G. intros.
            eapply R_pres_same_obs; simpl; auto.
        }
        {
          pupdate_intros_atomic.
          destruct Hpre as [HI [other Hacc]].
          inversion Hstep0; subst; try inversion_thread_event_eq.
          pose proof (get_ret_state t0 s0 ret Hstep0). subst ret.
          pupdate_finish.
          split.
          - unfold AcceptedByFirst in Hacc.
            destruct Hacc as [t2 [Hstate [Hrho Hlinr]]].
            simpl in *. subst.
            split; auto.
            exists other.
            split.
            + unfold AcceptedByFirst, ALin. simpl.
              exists t2. repeat split; auto.
            + simpl. exists t2. reflexivity.
          - unfold G. intros.
            eapply R_pres_same_obs; simpl; auto.
        }
        intros w.
        destruct w as [ot ov | tw1 tw2 twv1 twv2 |].
        * eapply provable_ret_safe;
          try solve_conj_impl;
          try solve_conj_stable stableDB.
          intros ? [_ [other [_ [t2 Hp]]]]. simpl in Hp. discriminate.
        * eapply provable_vis_safe with
            (P':=I //\\ ∃ other,
              AcceptedByFirst t v other //\\
              ⌜exists t2, Accepted tw1 tw2 twv1 twv2 = Accepted t t2 v other⌝)
            (Q':=fun _ =>
              I //\\ ALin t (Semantics.ls_linr (exch v) (Some twv2)));
          try solve [solve_conj_impl|solve_exch_obligation|solve_conj_stable stableDB].
          1: eapply IAcceptedByFirstPureStable.
          {
            pupdate_intros_atomic.
            inversion Hstep0; subst; try inversion_thread_event_eq.
            pupdate_finish.
            split.
            - destruct Hpre as [HI Hacc]. split; auto.
            - unfold G. intros.
              eapply R_pres_same_obs; simpl; auto.
          }
          {
            intros cleanup_ret σ1 ρ1 π1 Hpre σ2 Hstep.
            destruct Hpre as [HI [other [Hacc [t2eq Hp]]]].
            unfold AcceptedByFirst in Hacc.
            destruct Hacc as [t2 [Hstate [Hrho Hlinr]]].
            simpl in Hp. inversion Hp; subst.
            simpl in Hstate. inversion Hstate; subst.
            inversion Hstep; subst; try inversion_thread_event_eq.
            inversion Hstep0; subst; try inversion_thread_event_eq; try congruence.
            all: do 2 eexists; split; [apply rt_refl|]; split.
            all: try solve [split; [unfold I in *; simpl in *; auto|unfold ALin in *; simpl in *; exact Hlinr]].
	            all: unfold G; intros;
		              unfold R_pres, ALin, NoOfferBy, AcceptedByFirst, AcceptedBySecond, FirstLive, OfferedBy, Disj, Conj in *;
	              repeat split; intros; simpl in *; auto;
	              try match goal with
	              | Hneq : ?x <> ?x |- _ => contradiction
	              | H : TMap.find _ _ = Some _ /\ _ |- TMap.find _ _ = Some _ =>
	                  exact (proj1 H)
	              | H : _ /\ (forall _, _ <> Offered _ _) |- forall _, Empty <> Offered _ _ =>
	                  intros ? Hbad; discriminate Hbad
	              | H : _ /\ (forall _, _ <> Offered _ _) |- forall _, ?s <> Offered _ _ =>
	                  intros ? Hbad; subst; eapply H; reflexivity
	              end;
              try match goal with
	              | H : AcceptedBySecond _ _ _ _ |- _ =>
	                  unfold AcceptedBySecond in H;
	                  destruct H as [? [Hs _]];
	                  inversion Hs; subst; contradiction
	              | H : exists _, _ = Accepted _ _ _ _ /\ _ |- _ =>
	                  destruct H as [? [Hs _]];
	                  inversion Hs; subst; contradiction
              | H : exists _, _ |- _ =>
                  destruct H as [? [Hs _]];
                  rewrite Hstate in Hs; inversion Hs; subst; contradiction
              | H : (_ /\ _) \/ _ |- _ =>
                  destruct H as [[[Hs _] _] | [? [? [Hs _]]]];
                  rewrite Hstate in Hs; inversion Hs; subst; try contradiction; discriminate
              | H : ((_ /\ _ /\ _) /\ _) \/ _ |- _ =>
                  destruct H as [[[Hs _] _] | [? [Hacc _]]];
                  [discriminate Hs
	                  | unfold AcceptedByFirst in Hacc;
	                    destruct Hacc as [? [Hs _]];
	                    inversion Hs; subst; contradiction]
	              end;
	              try match goal with
	              | H : exists _, _ = Accepted _ _ _ _ /\ _ |- exists _, Empty = Accepted _ _ _ _ /\ _ =>
	                  destruct H as [? [Hs _]];
	                  inversion Hs; subst; contradiction
	              end;
		              try match goal with
		              | H : exists _, _ /\ _ |- exists _, Empty = _ /\ _ =>
		                  destruct H as [? [Hs _]];
		                  inversion Hs; subst; contradiction
		              end.
		            all: try match goal with
		            | H : exists _, _ /\ _ |- exists _, Empty = _ /\ _ =>
		                destruct H as [? [Hs _]];
		                inversion Hs; subst; contradiction
		            end.
		            all: try solve [intro Hbad; discriminate Hbad].
		            all: try solve [
		              match goal with
		              | Hstep' : AStep _ _ _ (Idle ?s2) |- ?s2 <> Offered _ _ =>
		                  inversion Hstep'; subst; inversion Hstep0; subst; try congruence;
		                  intro Hbad; discriminate Hbad
		              end].
          }
          intros _.
          eapply provable_ret_safe;
          try solve_conj_stable stableDB.
          {
            intros ? [HI Hlinr].
            split; auto.
          }
	          { apply ConjLeftImpl, ImplRefl. }
        * eapply provable_ret_safe;
          try solve_conj_impl;
          try solve_conj_stable stableDB.
          intros ? [_ [other [_ [t2 Hp]]]]. simpl in Hp. discriminate.
	    - eapply provable_vis_safe with
	        (P':=I //\\ (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t))
		        (Q':=fun w =>
		          I //\\ match w with
		                 | Offered _ _ => ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t
		                 | _ => ALin t (Semantics.ls_linr (exch v) None)
		                 end);
	      try solve [solve_conj_impl|solve_exch_obligation|solve_conj_stable stableDB].
	      1: {
			        intro w; destruct w; solve_conj_stable stableDB.
	      }
	      {
	        pupdate_intros_atomic.
	        inversion Hstep0; subst; try inversion_thread_event_eq.
	        pupdate_finish.
	        split.
	        - destruct Hpre as [HI [Hlin Hno]]. split; [exact HI|split; [exact Hlin|exact Hno]].
	        - unfold G. intros.
	          eapply R_pres_same_obs; simpl; auto.
	      }
	      {
	        pupdate_intros_atomic.
	        destruct Hpre as [HI [Hlin Hno]].
	        inversion Hstep0; subst; try inversion_thread_event_eq.
	        pose proof (get_ret_state t0 s0 ret Hstep0). subst ret.
	        destruct s0 as [ot ov | at1 at2 av1 av2 |].
		        - pupdate_finish.
		          split.
		          + split; auto. split; auto.
		          + unfold G. intros.
		            eapply R_pres_same_obs; simpl; auto.
	        - destruct ρ1; unfold I in HI; simpl in HI; try contradiction.
	          pupdate_start.
	          {
	            eapply rt_trans.
	            - eapply rt_step.
	              eapply (Semantics.ps_inv t0 (exch v)).
	              + eapply step_exch_offer. reflexivity.
	              + exact Hlin.
		            - eapply rt_step.
		              eapply (Semantics.ps_ret t0 (exch v) None).
		              + eapply step_exch_revoke. reflexivity.
		              + rewrite PositiveMap.gss. auto.
			            }
			            split.
			            + split.
			              * unfold I. simpl. auto.
			              * unfold ALin. simpl. rewrite PositiveMap.gss. auto.
		            + unfold G. intros.
		            eapply R_pres_same_obs; simpl; auto.
		            rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto].
	        - destruct ρ1; unfold I in HI; simpl in HI; try contradiction.
	          pupdate_start.
	          {
	            eapply rt_trans.
	            - eapply rt_step.
	              eapply (Semantics.ps_inv t0 (exch v)).
	              + eapply step_exch_offer. reflexivity.
	              + exact Hlin.
	            - eapply rt_step.
	              eapply (Semantics.ps_ret t0 (exch v) None).
	              + eapply step_exch_revoke. reflexivity.
	              + rewrite PositiveMap.gss. auto.
	          }
	          split.
		          + split.
			            * unfold I. simpl. auto.
			            * unfold ALin. simpl. rewrite PositiveMap.gss. auto.
		          + unfold G. intros.
		            eapply R_pres_same_obs; simpl; auto.
		            rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto].
	      }
		      intros w; destruct w as [ot ov | at1 at2 av1 av2 |].
		      + eapply provable_vis_safe with
			          (P':=I //\\ (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t))
		          (Q':=fun accepted : bool =>
		            I //\\ (if accepted
		                    then ALin t (Semantics.ls_linr (exch v) (Some ov))
		                    else ALin t (Semantics.ls_linr (exch v) None)));
		          try solve [solve_conj_impl|solve_exch_obligation|solve_conj_stable stableDB].
		          1: {
		          intro accepted; destruct accepted; solve_conj_stable stableDB.
		          }
		          {
		          pupdate_intros_atomic.
	          inversion Hstep0; subst; try inversion_thread_event_eq.
	          pupdate_finish.
	          split.
		          - destruct Hpre as [HI [Hlin Hno]]. split; [exact HI|split; [exact Hlin|exact Hno]].
	          - unfold G. intros.
	            eapply R_pres_same_obs; simpl; auto.
		          }
		          {
	          pupdate_intros_atomic.
		          destruct Hpre as [HI [Hlin Hno]].
	          inversion Hstep0; subst; try inversion_thread_event_eq; simpl in *; try discriminate; try congruence.
	          - destruct ρ1; unfold I in HI; simpl in HI; try contradiction.
	            dependent destruction H4.
		            assert (Howner : TMap.find ot π1 = Some (Semantics.ls_inv (exch ov))).
	            { exact HI. }
		            assert (Hott : ot <> t1).
		            {
		              intro Heq. subst.
		              unfold NoOfferBy in Hno. simpl in Hno.
		              apply (Hno ov). reflexivity.
		            }
	            pupdate_start.
	            {
	              eapply rt_trans.
	              - eapply rt_step.
	                eapply (Semantics.ps_inv ot (exch ov)).
	                + eapply step_exch_offer. reflexivity.
	                + exact Howner.
	              - eapply rt_trans.
	                + eapply rt_step.
	                  eapply (Semantics.ps_inv t1 (exch v)).
	                  * eapply step_exch_pair. reflexivity.
	                  * rewrite PositiveMap.gso.
	                    -- exact Hlin.
	                    -- auto.
	                + eapply rt_trans.
	                  * eapply rt_step.
	                    eapply (Semantics.ps_ret ot (exch ov) (Some v)).
	                    -- eapply step_exch_accept. reflexivity.
		                    -- rewrite PositiveMap.gso.
		                       ++ rewrite PositiveMap.gss. reflexivity.
		                       ++ auto.
			                  * eapply rt_step.
			                    eapply (Semantics.ps_ret t1 (exch v) (Some ov)).
			                    -- eapply step_exch_finish. reflexivity.
			                    -- rewrite PositiveMap.gso.
			                       ++ rewrite PositiveMap.gss. reflexivity.
			                       ++ auto.
		            }
		            split.
		            + split.
		              * unfold I. simpl. auto.
		              * unfold ALin. simpl.
		                change (TMap.find t1
		                  (TMap.add t1 (Semantics.ls_linr (exch v) (Some ov))
		                    (TMap.add ot (Semantics.ls_linr (exch ov) (Some v))
		                      (TMap.add t1 (Semantics.ls_lini (exch v))
		                        (TMap.add ot (Semantics.ls_lini (exch ov)) π1)))) =
		                  Some (Semantics.ls_linr (exch v) (Some ov))).
		                rewrite PositiveMap.gss. auto.
		            + unfold G. intros.
		              unfold R_pres, ALin, NoOfferBy, AcceptedByFirst, FirstLive, OfferedBy, Disj, Conj.
		              repeat split; intros; simpl in *;
		              try solve [
		                destruct (PositiveMap.E.eq_dec ot t'); subst;
		                [rewrite Howner in H0; discriminate
		                |repeat (rewrite PositiveMap.gso; [|auto]); auto]];
		              try solve [
		                destruct (PositiveMap.E.eq_dec ot t'); subst;
		                [rewrite PositiveMap.gso in H0; [rewrite PositiveMap.gss in H0; discriminate|auto]
		                |repeat (rewrite PositiveMap.gso in H0; [|auto]); auto]];
		              try solve [
		                match goal with
		                | Hact : TMap.find ?tx ?pm = Some _ /\ (forall v, Offered ot ov <> Offered ?tx v) |- _ =>
		                    destruct Hact as [Hlin' Hno'];
		                    destruct (PositiveMap.E.eq_dec ot tx); subst;
		                    [exfalso; apply (Hno ov); reflexivity
		                    |repeat (rewrite PositiveMap.gso; [|auto]); auto]
		                end];
			              try solve [
			                repeat (rewrite PositiveMap.gso; [|auto]);
			                auto].
			              -- destruct H0 as [Hlin' Hno'].
			                 destruct (PositiveMap.E.eq_dec ot t'); subst.
			                 ++ exfalso. apply (Hno' ov). reflexivity.
			                 ++ repeat (rewrite PositiveMap.gso; [|auto]). exact Hlin'.
			              -- intro Hbad; discriminate Hbad.
				              -- intro Hbad; discriminate Hbad.
			              -- destruct H0 as [? [Hs _]]. discriminate Hs.
				              -- destruct H0 as [[[Hs [_ Hlin']] _] | [other [Hacc Hlin']]].
				                 ++ inversion Hs; subst.
				                    right. exists v.
				                    split.
				                    ** exists t1. repeat split; auto.
				                       unfold ALin. simpl.
				                       rewrite PositiveMap.gso; [rewrite PositiveMap.gss; auto|auto].
				                    ** unfold ALin. simpl.
				                       rewrite PositiveMap.gso; [rewrite PositiveMap.gss; auto|auto].
				                 ++ unfold AcceptedByFirst in Hacc.
				                    destruct Hacc as [t2 [Hs _]]. discriminate Hs.
		          - match goal with
		            | Hneq : ?u <> Offered ot ov |- _ =>
		              pose proof (cas_offer_empty_fail_ret_false ot ov u ret) as _
		            end.
		            destruct ρ1; destruct s0; unfold I in HI; simpl in HI; try contradiction.
		            dependent destruction H5.
		            pupdate_start.
	            {
	              eapply rt_trans.
	              - eapply rt_step.
	                eapply (Semantics.ps_inv t1 (exch v)).
	                + eapply step_exch_offer. reflexivity.
	                + exact Hlin.
	              - eapply rt_step.
	                eapply (Semantics.ps_ret t1 (exch v) None).
	                + eapply step_exch_revoke. reflexivity.
	                + rewrite PositiveMap.gss. auto.
	            }
	            split.
	            + split.
		              * unfold I in *; simpl in *; auto.
			                destruct (PositiveMap.E.eq_dec t0 t1); subst.
			                -- exfalso. unfold NoOfferBy in Hno; simpl in Hno.
			                   apply (Hno v1). reflexivity.
			                -- change (TMap.find t0
			                     (TMap.add t1 (Semantics.ls_linr (exch v) None)
			                       (TMap.add t1 (Semantics.ls_lini (exch v)) π1)) =
			                     Some (Semantics.ls_inv (exch v1))).
			                   rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto].
	              * unfold ALin. simpl. rewrite PositiveMap.gss. auto.
		            + unfold G. intros.
		              unfold R_pres, ALin, NoOfferBy, AcceptedByFirst, FirstLive, OfferedBy, Disj, Conj.
		              repeat split; intros; simpl in *;
		              try solve [
		                destruct H1 as [Hlin' Hno'];
		                destruct (PositiveMap.E.eq_dec t0 t'); subst;
		                [exfalso; apply (Hno' v1); reflexivity
		                |rewrite PositiveMap.gso; [rewrite PositiveMap.gso; [exact Hlin'|auto]|auto]]];
		              try solve [
		                destruct (PositiveMap.E.eq_dec t0 t'); subst;
		                [exfalso; apply (H1 v1); reflexivity
		                |intro Hbad; inversion Hbad; subst; auto]];
		              try solve [rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto]];
	              try solve [rewrite PositiveMap.gso in H1; [rewrite PositiveMap.gso in H1; auto|auto]];
	              try solve [destruct H1 as [? [Hbad _]]; destruct u; simpl in *; try discriminate Hbad; auto];
		              try solve [
		                destruct H1 as [[[Hbad _] Hlin'] | [other [[? [Hbad _]] _]]];
		                [left; split; [repeat split; auto;
		                  rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto]
		                 |rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto]]
		                |discriminate Hbad]].
		              all: try solve [destruct H1 as [_ Hno']; auto].
		              all: try solve [destruct H1 as [? [Hbad _]]; discriminate Hbad].
		              all: try solve [
		                destruct H1 as [[[Hstate [Hrho Hlin']] Hlin''] | [other [[? [Hbad _]] _]]];
		                [left; split;
		                  [repeat split; auto;
		                   rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto]
		                  |rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto]]
		                |discriminate Hbad]].
				              destruct H1 as [[[Hstate [Hrho Hlin']] Hlin''] | [other [Hacc Hlin']]].
				              2:{ unfold AcceptedByFirst in Hacc.
				                  destruct Hacc as [t2 [Hs _]]. discriminate Hs. }
				              inversion Hstate; subst.
				              left. split.
				              * repeat split; auto.
				                destruct (PositiveMap.E.eq_dec t' t1); subst.
				                -- exfalso. unfold NoOfferBy in Hno; simpl in Hno.
				                   inversion Hstate; subst. apply (Hno v0). reflexivity.
						                -- change (TMap.find t'
						                     (TMap.add t1 (Semantics.ls_linr (exch v) None)
						                       (TMap.add t1 (Semantics.ls_lini (exch v)) π1)) =
						                     Some (Semantics.ls_inv (exch v0))).
						                   rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto].
				              * destruct (PositiveMap.E.eq_dec t' t1); subst.
				                -- exfalso. unfold NoOfferBy in Hno; simpl in Hno.
				                   inversion Hstate; subst. apply (Hno v0). reflexivity.
				                -- change (TMap.find t'
				                     (TMap.add t1 (Semantics.ls_linr (exch v) None)
				                       (TMap.add t1 (Semantics.ls_lini (exch v)) π1)) =
				                     Some (Semantics.ls_inv (exch v0))).
				                   rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto].
		              all: try solve [
		                inversion Hstep0; subst; try inversion_thread_event_eq; try congruence;
		                pupdate_start;
		                [eapply rt_trans;
		                  [eapply rt_step;
		                   eapply (Semantics.ps_inv t1 (exch v));
		                   [eapply step_exch_offer; reflexivity|exact Hlin]
		                  |eapply rt_step;
		                   eapply (Semantics.ps_ret t1 (exch v) None);
		                   [eapply step_exch_revoke; reflexivity|rewrite PositiveMap.gss; auto]]
		                |split;
		                  [split;
		                    [unfold I in *; simpl in *; auto
		                    |unfold ALin; simpl; rewrite PositiveMap.gss; auto]
			                  |unfold G; intros;
			                   eapply R_pres_same_obs; simpl; auto;
			                   rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto]]]].
				          + try dependent destruction H5.
		            pupdate_start.
		            {
		              eapply rt_trans.
			              * eapply rt_step.
		                eapply (Semantics.ps_inv t1 (exch v)).
			                -- eapply step_exch_offer. reflexivity.
			                -- exact Hlin.
			              * eapply rt_step.
		                eapply (Semantics.ps_ret t1 (exch v) None).
			                -- eapply step_exch_revoke. reflexivity.
			                -- rewrite PositiveMap.gss. auto.
			            }
			            split.
			            * split.
			              -- unfold I in *; simpl in *; auto.
			              -- unfold ALin; simpl; rewrite PositiveMap.gss; auto.
			            * unfold G; intros.
			              eapply R_pres_same_obs; simpl; auto.
				              rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto].
					          + try dependent destruction H5.
		            pupdate_start.
		            {
		              eapply rt_trans.
			              * eapply rt_step.
		                eapply (Semantics.ps_inv t1 (exch v)).
			                -- eapply step_exch_offer. reflexivity.
			                -- exact Hlin.
			              * eapply rt_step.
		                eapply (Semantics.ps_ret t1 (exch v) None).
			                -- eapply step_exch_revoke. reflexivity.
			                -- rewrite PositiveMap.gss. auto.
			            }
			            split.
			            * split.
			              -- unfold I in *; simpl in *; auto.
			              -- unfold ALin; simpl; rewrite PositiveMap.gss; auto.
			            * unfold G; intros.
		              eapply R_pres_same_obs; simpl; auto.
		              rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto].
	        }
	        intros accepted; destruct accepted;
	        eapply provable_ret_safe;
	        try solve_conj_impl;
	        try solve_conj_stable stableDB;
	        try apply ImplRefl.
	      + eapply provable_ret_safe;
	        try solve_conj_impl;
	        try solve_conj_stable stableDB;
	        try apply ImplRefl.
	      + eapply provable_ret_safe;
	        try solve_conj_impl;
	        try solve_conj_stable stableDB;
	        try apply ImplRefl.
	  - unfold I. simpl. auto.
	  Qed.
  End Impl.
End ExchangerImpl.
