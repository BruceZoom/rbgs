Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import TPSimulationSet.
Require Import Logics.
Require Import SeparationAlgebra.
Require Import TensorSeparation.
Require Import LTSLocality.

Module Type ProofState.
  Import Reg LinCCALBase LTSSpec Semantics.

  Parameter ProofState :
    forall {E : Op.t} {F : Op.t} {VE : @LTS E} {VF : @LTS F}, Type.

  Parameter σ :
    forall {E F VE VF}, ProofState (E:=E) (F:=F) (VE:=VE) (VF:=VF) -> State VE.

End ProofState.

Module Assertions (PS : ProofState).
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Semantics.
  Import PS.

  Section AssertionDef.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.

    Definition RGRelation : Type := relation (@ProofState E F VE VF).

    Definition Subset (r1 r2 : RGRelation) : Prop :=
      forall x y, r1 x y -> r2 x y.
    
    Definition Union (r1 r2 : RGRelation) : RGRelation :=
      fun x y => r1 x y \/ r2 x y.
    
    Definition Inter (r1 r2 : RGRelation) : RGRelation :=
      fun x y => r1 x y /\ r2 x y.

    (** A protocol relation often has an extensional component used by
        whole-state stability and a spatial footprint used by framing. *)
    Definition RelyWithAuxiliary
        (Facts Spatial Auxiliary : RGRelation) : RGRelation :=
      Inter Facts (Union Spatial Auxiliary).

    Definition GuaranteeWithFootprint
        (Effects Spatial : RGRelation) : RGRelation :=
      Inter Effects Spatial.

    Definition ComposeA (P : Assertion) (R : RGRelation) : Assertion :=
      fun s => exists s', P s' /\ R s' s.
    
    Definition ComposeR (R S : RGRelation) : RGRelation :=
      fun s s' => exists s'', R s s'' /\ S s'' s'.

    Definition ComposeR' (P : Assertion) (R : RGRelation) : RGRelation :=
      fun s s' => R s s' /\ P s.

    Definition GId : RGRelation := fun x y => x = y.

    (** Figure 8's assertion-to-relation connective [P ⋉ Q]. *)
    Definition RelAssertion (P Q : Assertion) : RGRelation :=
      fun s s' => P s /\ Q s'.

    (** Identity transition restricted to states satisfying the frame. *)
    Definition FrameIdentity (Fr : Assertion) : RGRelation :=
      Inter GId (RelAssertion Fr Fr).

    Definition ANoError (ev : ThreadEvent) : @Assertion (@ProofState E F VE VF) :=
      fun s => ~ Error VE ev (σ s).
  End AssertionDef.

  Section RelationSeparation.
    Context {E : Op.t} {F : Op.t} {VE : @LTS E} {VF : @LTS F}.
    Context {J : Join (@ProofState E F VE VF)}.

    (** Figure 8's relation separating conjunction.  Both endpoints are
        split, and each component relation connects matching pieces. *)
    Definition RelSep (G1 G2 : @RGRelation E F VE VF) :
        @RGRelation E F VE VF :=
      fun s s' => exists s1 s2 s1' s2',
        join s1 s2 s /\ join s1' s2' s' /\
        G1 s1 s1' /\ G2 s2 s2'.

    Definition RelSep3 (G1 G2 G3 : @RGRelation E F VE VF) :
        @RGRelation E F VE VF :=
      RelSep (RelSep G1 G2) G3.

    Lemma RelSep_intro (G1 G2 : @RGRelation E F VE VF)
        s1 s2 s s1' s2' s' :
      join s1 s2 s -> join s1' s2' s' ->
      G1 s1 s1' -> G2 s2 s2' -> RelSep G1 G2 s s'.
    Proof. intros; do 4 eexists; repeat split; eauto. Qed.

    Lemma RelSep3_intro (G1 G2 G3 : @RGRelation E F VE VF)
        s1 s2 s12 s3 s s1' s2' s12' s3' s' :
      join s1 s2 s12 -> join s12 s3 s ->
      join s1' s2' s12' -> join s12' s3' s' ->
      G1 s1 s1' -> G2 s2 s2' -> G3 s3 s3' ->
      RelSep3 G1 G2 G3 s s'.
    Proof.
      intros H12 H123 H12' H123' H1 H2 H3. unfold RelSep3.
      eapply RelSep_intro; [exact H123|exact H123'| |exact H3].
      eapply RelSep_intro; eauto.
    Qed.

    (** An invariant is precise when it identifies at most one owned
        component in any decomposition of a whole state. *)
    Definition Precise (I : @Assertion (@ProofState E F VE VF)) : Prop :=
      forall whole owned1 frame1 owned2 frame2,
        join owned1 frame1 whole ->
        join owned2 frame2 whole ->
        I owned1 -> I owned2 -> owned1 = owned2.

    (** A fenced relation admits invariant identities, has invariant
        endpoints, and is governed by a precise invariant. *)
    Definition Fence (I : @Assertion (@ProofState E F VE VF))
        (R : @RGRelation E F VE VF) : Prop :=
      Subset (FrameIdentity I) R /\
      Subset R (RelAssertion I I) /\
      Precise I.
  End RelationSeparation.
  

  Delimit Scope rg_relation_scope with RGRelation.
  Bind Scope rg_relation_scope with RGRelation.
  
  Notation "R ⊆ S" := (Subset R S) (at level 70) : rg_relation_scope.
  Notation "R ∪ S" := (Union R S) (at level 50) : rg_relation_scope.
  Notation "R ∩ S" := (Inter R S) (at level 40) : rg_relation_scope.
  Notation "R ○ S" := (ComposeR S R) (at level 30) : rg_relation_scope.
  Notation "R ⊚ P" := (ComposeA P R) (at level 30) : rg_relation_scope.
  Notation "P ⊓ R" := (ComposeR' P R) (at level 30) : rg_relation_scope.
  Notation "P ⋉ Q" := (RelAssertion P Q) (at level 35) : rg_relation_scope.
  Notation "R ∗ S" := (RelSep R S) (at level 40, left associativity) : rg_relation_scope.

  Section AssertionLemmas.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.

    Open Scope rg_relation_scope.
    Open Scope assertion_scope.

    Lemma RGSubsetUnion : forall (R1 R2 R3 : @RGRelation _ _ VE VF),
      R1 ⊆ R2 \/ R1 ⊆ R3 ->
      R1 ⊆ R2 ∪ R3.
    Proof.
      intros. destruct H; intros ? ? ?.
      - left. auto.
      - right. auto.
    Qed.

    Lemma RGSubsetRefl (R : @RGRelation _ _ VE VF) : (R ⊆ R)%RGRelation.
    Proof. firstorder. Qed.

    Section RelSepLemmas.
      Context {J : Join (@ProofState E F VE VF)}.

      Lemma RelSep_mono (R1 R1' R2 R2' : @RGRelation _ _ VE VF) :
        (R1 ⊆ R1')%RGRelation -> (R2 ⊆ R2')%RGRelation ->
        (RelSep R1 R2 ⊆ RelSep R1' R2')%RGRelation.
      Proof.
        intros H1 H2 s s' (s1 & s2 & s1' & s2' & Hj & Hj' & HR1 & HR2).
        do 4 eexists; repeat split; eauto.
      Qed.

      Lemma RelSep3_mono
          (R1 R1' R2 R2' R3 R3' : @RGRelation _ _ VE VF) :
        (R1 ⊆ R1')%RGRelation -> (R2 ⊆ R2')%RGRelation ->
        (R3 ⊆ R3')%RGRelation ->
        (RelSep3 R1 R2 R3 ⊆ RelSep3 R1' R2' R3')%RGRelation.
      Proof.
        intros H1 H2 H3. unfold RelSep3.
        apply RelSep_mono; [apply RelSep_mono|]; assumption.
      Qed.
    End RelSepLemmas.

    Lemma GuaranteeWithFootprint_intro
        (Effects Spatial : @RGRelation _ _ VE VF) s s' :
      Effects s s' -> Spatial s s' ->
      GuaranteeWithFootprint Effects Spatial s s'.
    Proof. split; assumption. Qed.

    Lemma RelyWithAuxiliary_spatial_intro
        (Facts Spatial Auxiliary : @RGRelation _ _ VE VF) s s' :
      Facts s s' -> Spatial s s' ->
      RelyWithAuxiliary Facts Spatial Auxiliary s s'.
    Proof. intros; split; [assumption|left; assumption]. Qed.

    Lemma RelyWithAuxiliary_auxiliary_intro
        (Facts Spatial Auxiliary : @RGRelation _ _ VE VF) s s' :
      Facts s s' -> Auxiliary s s' ->
      RelyWithAuxiliary Facts Spatial Auxiliary s s'.
    Proof. intros; split; [assumption|right; assumption]. Qed.

    Lemma RelyWithAuxiliary_facts
        (Facts Spatial Auxiliary : @RGRelation _ _ VE VF) :
      (RelyWithAuxiliary Facts Spatial Auxiliary ⊆ Facts)%RGRelation.
    Proof. intros s s' [Hfacts _]; exact Hfacts. Qed.

    Lemma GuaranteeWithFootprint_rely
        (Effects GSpatial Facts RSpatial Auxiliary
          : @RGRelation _ _ VE VF) :
      (Effects ⊆ Facts)%RGRelation ->
      (GSpatial ⊆ RSpatial)%RGRelation ->
      (GuaranteeWithFootprint Effects GSpatial ⊆
        RelyWithAuxiliary Facts RSpatial Auxiliary)%RGRelation.
    Proof.
      intros HE HS s s' [Heffect Hspatial]. split.
      - eapply HE; exact Heffect.
      - left. eapply HS; exact Hspatial.
    Qed.

    Lemma ImplRefl {P:@Assertion (@ProofState E F VE VF)}: ⊨ P ==>> P.
    Proof. intros. intros ?. auto. Qed.

    Lemma ImplTauto {P Q : @Assertion (@ProofState E F VE VF)} : (⊨ Q) -> ⊨ P ==>> Q.
    Proof. intros. intros ?. auto. Qed.

    Lemma ImplTrans {P Q R : @Assertion (@ProofState E F VE VF)} : (⊨ P ==>> Q) -> (⊨ Q ==>> R) -> ⊨ P ==>> R.
    Proof. intros. intros ?. apply H0, H; auto. Qed.


    Lemma ConjLeftImpl {P1 P2 P3: @Assertion (@ProofState E F VE VF)}:
      (⊨ P1 ==>> P3) ->
      ⊨ P1 //\\ P2 ==>> P3.
    Proof. intros ? ? [? ?]; apply H; auto. Qed.

    Lemma ConjRightImpl {P1 P2 P3 : @Assertion (@ProofState E F VE VF)}:
      (⊨ P2 ==>> P3) ->
      ⊨ P1 //\\ P2 ==>> P3.
    Proof. intros ? ? [? ?]; apply H; auto. Qed.

    Lemma ImplConj {P1 P2 P3 : @Assertion (@ProofState E F VE VF)}:
      (⊨ P1 ==>> P2) ->
      (⊨ P1 ==>> P3) ->
      (⊨ P1 ==>> P2 //\\ P3).
    Proof.
      intros. intros ?.
      pose proof H1.
      apply H in H1. apply H0 in H2.
      split; auto.
    Qed.

    Definition Stable (R : @RGRelation _ _ VE VF) I P := ⊨ (R ⊚ P) //\\ I ==>> P.

    Lemma Stable_invariant (R : @RGRelation _ _ VE VF)
        (I : @Assertion (@ProofState _ _ VE VF)) :
      Stable R I I.
    Proof. unfold Stable. intros s [_ HI]; exact HI. Qed.

    Lemma Stable_RelyWithAuxiliary_facts
        (Facts Spatial Auxiliary : @RGRelation _ _ VE VF)
        (I P : @Assertion (@ProofState _ _ VE VF)) :
      (forall s s', Facts s s' -> I s' -> P s -> P s') ->
      Stable (RelyWithAuxiliary Facts Spatial Auxiliary) I P.
    Proof.
      intros Hpres. unfold Stable. intros s [[pre [HP [Hfacts _]]] HI].
      eapply Hpres; eauto.
    Qed.

    Lemma Stable_from_facts
        (R Facts : @RGRelation _ _ VE VF)
        (I P : @Assertion (@ProofState _ _ VE VF)) :
      (R ⊆ Facts)%RGRelation ->
      (forall s s', Facts s s' -> I s' -> P s -> P s') ->
      Stable R I P.
    Proof.
      intros HR Hpres. unfold Stable. intros s [[pre [HP Hrel]] HI].
      eapply Hpres; [eapply HR; exact Hrel|exact HI|exact HP].
    Qed.

    Section FencedStability.
      Context {J : Join (@ProofState E F VE VF)}.
      Context {SA : @SeparationAlgebra _ J}.
      Context {JC : @JoinLeftCancellative _ J}.

      (** Appendix B.2's compositionality of stability.  Precision aligns
          the two owned components; cancellation then aligns their frames. *)
      Lemma Stable_sep_fenced
          (R Rf : @RGRelation _ _ VE VF)
          (I If P Fr : @Assertion (@ProofState _ _ VE VF)) :
        Fence I R -> Fence If Rf ->
        (⊨ P ==>> I) -> Stable R I P -> Stable Rf If Fr ->
        Stable (RelSep R Rf) (I * If) (P * Fr).
      Proof.
        intros [_ [HRinv Hprec]] [_ [HRfinv _]] HPI HstableP HstableFr.
        unfold Stable. intros post [Hreach _].
        destruct Hreach as [pre [Hpre Hrel]].
        destruct Hpre as [p [fr [HjoinPF [HP HFr]]]].
        destruct Hrel as
          [r [rf [r' [rf' [HjoinRR [HjoinPost [HR HRf]]]]]]].
        pose proof (HPI p HP) as HIp.
        pose proof (proj1 (HRinv _ _ HR)) as HIr.
        assert (Hp : p = r) by (eapply Hprec; eauto).
        subst r.
        assert (Hfr : fr = rf) by (eapply join_left_cancel; eauto).
        subst rf.
        exists r', rf'. split; [exact HjoinPost|]. split.
        - apply HstableP. split.
          + exists p. split; assumption.
          + exact (proj2 (HRinv _ _ HR)).
        - apply HstableFr. split.
          + exists fr. split; assumption.
          + exact (proj2 (HRfinv _ _ HRf)).
      Qed.
    End FencedStability.

    Lemma StableForall {A} : forall R I P,
      (forall x : A, Stable R I (P x)) ->
      Stable R I (∀ x, P x).
    Proof.
      intros. intros ? [[? [? ?]] ?] ?.
      apply H; split; auto.
      eexists. eauto.
    Qed.

    Lemma StableExists {A} : forall R I P,
      (forall x : A, Stable R I (P x)) ->
      Stable R I (∃ x, P x).
    Proof.
      intros. intros ? [[s' [[? ?] ?]] ?].
      exists x. apply H; split; eauto.
      eexists; eauto.
    Qed.

    Lemma StableWeaken : forall R I P1 P2 P3,
      Stable R I P3 ->
      ⊨ P1 ==>> P3 ->
      ⊨ P3 ==>> P2 ->
      ⊨ (R ⊚ P1) //\\ I ==>> P2.
    Proof.
      intros. intros [[? [? ?]] ?].
      apply H1.
      apply H0 in H2.
      apply H.
      split; auto.
      eexists; split; eauto.
    Qed.
    
    Lemma ConjStable {R I P Q}:
      Stable R I P -> Stable R I Q -> Stable R I (P //\\ Q).
    Proof.
      intros. intros ? [[? [[? ?] ?]] ?].
      split.
      - apply H. do 2 (eexists; eauto).
      - apply H0. do 2 (eexists; eauto).
    Qed.

    Lemma ConjStableWeaken {R I P Q}:
      ⊨ (R ⊚ (P //\\ Q)) //\\ I ==>> P ->
      ⊨ (R ⊚ (P //\\ Q)) //\\ I ==>> Q ->
      Stable R I (P //\\ Q).
    Proof.
      intros. intros ? ?.
      split; try apply H; try apply H0; auto.
    Qed.

    Lemma StableExtractPure {R I} {P:Prop} {Q}:
      (P -> Stable R I Q) ->
      Stable R I (⌜P⌝ //\\ Q).
    Proof.
      intros.
      intros ? [[s' [[? ?] ?]] ?].
      split; auto.
      apply H; auto.
      do 2 (eexists; eauto).
    Qed.

    Lemma EquivStable {R I}: forall P Q,
      (⊨ P <<==>> Q) -> Stable R I P -> Stable R I Q.
    Proof.
      intros. intros ? [[? [? ?]] ?].
      destruct (H s).
      destruct (H x).
      apply H4.
      apply H0.
      split; eauto.
      eexists. split; eauto.
    Qed.

    Lemma DisjStable {R I P Q}:
      Stable R I P ->
      Stable R I Q ->
      Stable R I (P \\// Q).
    Proof.
      intros. intros ? [[? [? ?]] ?].
      destruct H1.
      - left. apply H; split; auto. eexists; eauto.
      - right. apply H0; split; auto. eexists; eauto.
    Qed.

    Lemma APureStable {R I P}:
      Stable R I (⌜P⌝).
    Proof.
      intros. intros ? [[? [? ?]] ?].
      unfold APure in *. auto.
    Qed.

    Lemma ImplDisjFrame {P1 P3: @Assertion (@ProofState E F VE VF)} : forall P2,
      (⊨ P1 ==>> P2) ->
      ⊨ P1 \\// P3 ==>> P2 \\// P3.
    Proof.
      intros. intros ?.
      destruct H0.
      - left; apply H; auto.
      - right; auto.
    Qed.

    Lemma ImplDisjLeft {P1 P2 P3: @Assertion (@ProofState E F VE VF)}:
      (⊨ P1 ==>> P2) ->
      ⊨ P1 ==>> P2 \\// P3.
    Proof. intros ? ? ?. left; apply H; auto. Qed.

    Lemma ImplDisjRight {P1 P2 P3: @Assertion (@ProofState E F VE VF)}:
      (⊨ P1 ==>> P3) ->
      ⊨ P1 ==>> P2 \\// P3.
    Proof. intros ? ? ?. right; apply H; auto. Qed.
  
  End AssertionLemmas.


    Open Scope rg_relation_scope.
    Open Scope assertion_scope.

    Ltac inversion_step :=
      repeat match goal with
      (* Case with 5 arguments *)
      | H : Step ?x1 ?x2 ?x3 ?x4 ?x5 |- _ =>
          first [
            match type of x1 with ThreadEvent => inversion H; subst; clear H end |
            match type of x2 with ThreadEvent => inversion H; subst; clear H end |
            match type of x3 with ThreadEvent => inversion H; subst; clear H end |
            match type of x4 with ThreadEvent => inversion H; subst; clear H end |
            match type of x5 with ThreadEvent => inversion H; subst; clear H end
          ]
      (* Case with 4 arguments (common in Assertion.v) *)
      | H : Step ?x1 ?x2 ?x3 ?x4 |- _ =>
          first [
            match type of x1 with ThreadEvent => inversion H; subst; clear H end |
            match type of x2 with ThreadEvent => inversion H; subst; clear H end |
            match type of x3 with ThreadEvent => inversion H; subst; clear H end |
            match type of x4 with ThreadEvent => inversion H; subst; clear H end
          ]
      end.
    
    Ltac solve_conj_impl :=
      try exact ImplRefl;
      match goal with
      | |- _ -> ?P => intro; solve_conj_impl
      | |- forall x:?T, ?P => intro; solve_conj_impl
      (* | |- ⊨ ?P ==>> ?P => exact ImplRefl *)
      | |- ⊨ ?P1 //\\ ?P2 ==>> ?Q =>
        solve [ eapply ConjLeftImpl; solve_conj_impl ] ||
        solve [ eapply ConjRightImpl; solve_conj_impl ] ||
        solve [
          match Q with
          | ?Q1 //\\ ?Q2 => eapply ImplConj; solve_conj_impl
          | _ => fail
          end
        ]
      | _ => fail
      end.

    Ltac solve_conj_stable hint_db :=
      intros;
      match goal with
      | |- Stable _ _ ?P =>
        solve [ eauto with hint_db ] ||
        match P with
        | ?P1 //\\ ?P2 => apply ConjStable; solve_conj_stable hint_db
        | _ => fail
        end
      end.

    Ltac solve_stable hint_db :=
      intros;
      match goal with
      | |- Stable _ _ ?P =>
        solve [ eauto with hint_db ] ||
        match P with
        | ⌜?P⌝ => apply APureStable
        | ?P1 \\// ?P2 =>
            apply DisjStable; solve_stable hint_db
        | ?P1 //\\ ?P2 =>
            match P1 with
            | ⌜?P1⌝ =>
              apply StableExtractPure; intros; subst;
              solve_stable hint_db
            | _ =>
              first [
                apply ConjStable; solve_stable hint_db |
                apply ConjStableWeaken;
                (eapply StableWeaken;
                  [ typeclasses eauto with hint_db
                    | solve_conj_impl
                    | solve_conj_impl ])
              ]
            end
        | _ => fail
        end
      end.

    Ltac solve_no_error:=
      apply ImplTauto; intros ? H; destruct σ;
      inversion H; subst; inversion Herror.
  
End Assertions.



Module SinglePossState <: ProofState.
  Import Reg LinCCALBase LTSSpec Semantics.

  Record ProofStateSingle {E : Op.t} {F : Op.t} {VE : @LTS E} {VF : @LTS F} : Type :=
  {
    σ : State VE;
    ρ : State VF;
    π : tmap (@LinState F);
  }.

  Notation "( σ , ρ , π )" := (Build_ProofStateSingle _ _ _ _ σ ρ π).

  Definition ProofState {E F VE VF} : Type := @ProofStateSingle E F VE VF.

End SinglePossState.

Module AssertionsSingle.
  Module A := Assertions (SinglePossState).
  Export A.
  Export SinglePossState.

  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Semantics.

  Section AssertionDef.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.

    Definition LiftRelation_σ (Rσ : relation (State VE)) : @RGRelation _ _ VE VF :=
      fun x y => Rσ (σ x) (σ y) /\ ρ x = ρ y /\ π x = π y.
    
    Definition LiftRelation_ρ (Rρ : relation (State VF)) : @RGRelation _ _ VE VF :=
      fun x y => σ x = σ y /\ Rρ (ρ x) (ρ y) /\ π x = π y.
    
    Definition LiftRelation_π (Rπ : relation (tmap (@LinState F))) : @RGRelation _ _ VE VF :=
      fun x y => σ x = σ y /\ ρ x = ρ y /\ Rπ (π x) (π y).

    Definition Ginv t f : @RGRelation _ _ VE VF :=
      LiftRelation_π (fun π1 π2 => 
        TMap.find t π1 = None /\
        π2 = TMap.add t (ls_inv f) π1).

    Definition GINV t : @RGRelation _ _ VE VF :=
      fun x y => exists f, Ginv t f x y.

    Definition Gret t f ret : @RGRelation _ _ VE VF :=
      LiftRelation_π (fun π1 π2 => 
        TMap.find t π1 = Some (ls_linr f ret) /\
        π2 = TMap.remove t π1).

    Definition GRET t : @RGRelation _ _ VE VF :=
      fun x y => exists f ret, Gret t f ret x y.

    (** Linearization-map steps performed by threads other
        than the observer.  Keeping this in the singleton framework avoids
        rebuilding the same rely alternative in every client proof. *)
    Definition OtherThreadLinearizationRely (observer : tid) :
        @RGRelation _ _ VE VF :=
      fun s s' =>
        (exists actor, actor <> observer /\ GINV actor s s') \/
        (exists actor, actor <> observer /\ GRET actor s s') \/
        GId s s'.

    (** The program-interference part of a thread's rely can be generated
        directly from the guarantees of all other threads. *)
    Definition OtherThreadGuaranteeRely
        (G : tid -> @RGRelation E F VE VF) (observer : tid) :
        @RGRelation _ _ VE VF :=
      fun s s' => exists actor, actor <> observer /\ G actor s s'.

    Definition GuaranteeGeneratedRely
        (G : tid -> @RGRelation E F VE VF) (observer : tid) :
        @RGRelation _ _ VE VF :=
      A.Union (OtherThreadGuaranteeRely G observer)
        (OtherThreadLinearizationRely observer).

    (** The part of a singleton proof state visible to a thread while some
        other thread performs a linearization-map invocation/return step. *)
    Definition ObserverViewEq (observer : tid) :
        @RGRelation _ _ VE VF :=
      fun s s' =>
        σ s = σ s' /\ ρ s = ρ s' /\
        TMap.find observer (π s) = TMap.find observer (π s').
    
    Definition APError : @Assertion (@ProofState _ _ VE VF) :=
      fun s => poss_steps (ρ s, π s) PossError.

    Definition PUpdate (G : @RGRelation _ _ VE VF) (ev : ThreadEvent) (P Q : Assertion) : Prop :=
      forall σ ρ π, P (σ, ρ, π) ->
      forall σ', Step VE ev σ σ' ->
      exists ρ' π', poss_steps (ρ, π) (ρ', π') /\ Q (σ', ρ', π')
        /\ G (σ, ρ, π) (σ', ρ', π').

    Definition PUpdateId (G : @RGRelation _ _ VE VF) (P Q : Assertion) : Prop :=
      forall σ ρ π, P (σ, ρ, π) ->
      exists ρ' π', poss_steps (ρ, π) (ρ', π') /\ Q (σ, ρ', π')
        /\ G (σ, ρ, π) (σ, ρ', π').
    
    Definition ALin (t : tid) (ls : LinState) : @Assertion (@ProofState _ _ VE VF) :=
      fun s => TMap.find t (π s) = Some ls.

  End AssertionDef.

  Notation "G ⊨ P [ ev ]⭆ Q" := (PUpdate G ev P Q) (at level 100) : assertion_scope.
  Notation "G ⊨ P ⭆ Q" := (PUpdateId G P Q) (at level 100) : assertion_scope.

  
  Section AssertionLemmas.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.

    Lemma PUpdateConseq {P Q P' Q' : @Assertion (@ProofState _ _ VE VF)} {ev} {G} :
      (⊨ P' ==>> P) ->
      (⊨ Q ==>> Q') ->
      (G ⊨ P [ ev ]⭆ Q) ->
      G ⊨ P' [ ev ]⭆ Q'.
    Proof.
      intros. intros ?; intros.
      apply H in H2.
      apply H1 in H2.
      apply H2 in H3 as (? & ?& ? & ? & ?).
      apply H0 in H4.
      eauto.
    Qed.

    (** Generic compatibility rule for a protocol whose program guarantee
        and rely each combine semantic facts with a spatial footprint. *)
    Lemma separated_parallel_compatible
        (Facts RSpatial Effects GSpatial :
          tid -> @RGRelation E F VE VF) :
      (forall actor observer, actor <> observer ->
        (Effects actor ⊆ Facts observer)%RGRelation) ->
      (forall actor observer, actor <> observer ->
        (GSpatial actor ⊆ RSpatial observer)%RGRelation) ->
      (forall actor observer, actor <> observer ->
        (GINV actor ⊆ Facts observer)%RGRelation) ->
      (forall actor observer, actor <> observer ->
        (GRET actor ⊆ Facts observer)%RGRelation) ->
      (forall observer, (GId ⊆ Facts observer)%RGRelation) ->
      forall actor observer, actor <> observer ->
      forall s s',
        (A.GuaranteeWithFootprint (Effects actor) (GSpatial actor) s s' \/
         (GINV actor s s' \/ GRET actor s s') \/ GId s s') ->
        A.RelyWithAuxiliary (Facts observer) (RSpatial observer)
          (OtherThreadLinearizationRely observer) s s'.
    Proof.
      intros HGFacts HGSpatial HinvFacts HretFacts HIdFacts.
      intros actor observer Hneq s s' [HG | [[Hinv | Hret] | Hid]].
      - eapply A.GuaranteeWithFootprint_rely.
        + eapply HGFacts; exact Hneq.
        + eapply HGSpatial; exact Hneq.
        + exact HG.
      - eapply A.RelyWithAuxiliary_auxiliary_intro.
        + eapply HinvFacts; eauto.
        + left. exists actor. auto.
      - eapply A.RelyWithAuxiliary_auxiliary_intro.
        + eapply HretFacts; eauto.
        + right. left. exists actor. auto.
      - eapply A.RelyWithAuxiliary_auxiliary_intro.
        + eapply HIdFacts; exact Hid.
        + right. right. exact Hid.
    Qed.

    Lemma guarantee_generated_parallel_compatible
        (G : tid -> @RGRelation E F VE VF) actor observer :
      actor <> observer -> forall s s',
        (G actor s s' \/ (GINV actor s s' \/ GRET actor s s') \/
          GId s s') ->
        GuaranteeGeneratedRely G observer s s'.
    Proof.
      intros Hneq s s' [HG | [[Hinv | Hret] | Hid]].
      - left. exists actor. auto.
      - right. left. exists actor. auto.
      - right. right. left. exists actor. auto.
      - right. right. right. exact Hid.
    Qed.

    Lemma ginv_other_observer_view actor observer (f : Sig.op F) :
      actor <> observer ->
      (@Ginv E F VE VF actor f ⊆
        @ObserverViewEq E F VE VF observer)%RGRelation.
    Proof.
      intros Hneq s s' [Hsigma [Hrho [_ Hpi]]].
      unfold ObserverViewEq. repeat split; auto.
      rewrite Hpi, TMap.gso; auto.
    Qed.

    Lemma gret_other_observer_view actor observer
        (f : Sig.op F) (ret : Sig.ar f) :
      actor <> observer ->
      (@Gret E F VE VF actor f ret ⊆
        @ObserverViewEq E F VE VF observer)%RGRelation.
    Proof.
      intros Hneq s s' [Hsigma [Hrho [_ Hpi]]].
      unfold ObserverViewEq. repeat split; auto.
      rewrite Hpi, TMap.gro; auto.
    Qed.

    Lemma linearization_rely_observer_view observer :
      (@OtherThreadLinearizationRely E F VE VF observer ⊆
        @ObserverViewEq E F VE VF observer)%RGRelation.
    Proof.
      intros s s' [[actor [Hneq [f Hinv]]] |
        [[actor [Hneq [f [ret Hret]]]] | Hid]].
      - eapply ginv_other_observer_view; eauto.
      - eapply gret_other_observer_view; eauto.
      - unfold A.GId in Hid. destruct Hid.
        unfold ObserverViewEq. auto.
    Qed.

    (** Projection of a guarantee-generated rely into any client fact
        relation.  A client proves facts for program guarantees and once
        for its observer view; invocation/return cases are then generic. *)
    Lemma guarantee_generated_rely_facts
        (G : tid -> @RGRelation E F VE VF)
        (Facts : tid -> @RGRelation E F VE VF) observer :
      (forall actor, actor <> observer ->
        (G actor ⊆ Facts observer)%RGRelation) ->
      (@ObserverViewEq E F VE VF observer ⊆
        Facts observer)%RGRelation ->
      (GuaranteeGeneratedRely G observer ⊆ Facts observer)%RGRelation.
    Proof.
      intros Hprogram Hview s s' [HprogramStep | Hadmin].
      - destruct HprogramStep as [actor [Hneq HG]].
        eapply Hprogram; eauto.
      - eapply Hview. eapply linearization_rely_observer_view; exact Hadmin.
    Qed.

    Section OwnedResidual.
      Context {X : Type}.
      Variable owner : X -> option tid.
      Variable residual : X -> tmap (@LinState F) -> tmap (@LinState F).
      Variable owner_ok : X -> tmap (@LinState F) -> Prop.

      Hypothesis residual_find_other : forall x pi q,
        owner x <> Some q ->
        TMap.find q (residual x pi) = TMap.find q pi.

      Hypothesis owner_ok_find : forall x pi q,
        owner_ok x pi -> owner x = Some q ->
        exists ls, TMap.find q pi = Some ls.

      (** Equality of residual maps recovers whether another thread has a
          full-map cell, even when that cell moves through the distinguished
          owner component. *)
      Lemma owned_residual_find_none_iff x x' pi pi' q :
        (owner x = Some q <-> owner x' = Some q) ->
        owner_ok x pi -> owner_ok x' pi' ->
        TMap.find q (residual x pi) = TMap.find q (residual x' pi') ->
        (TMap.find q pi = None <-> TMap.find q pi' = None).
      Proof.
        intros Howner Hok Hok' Hresidual.
        destruct (owner x) as [r|] eqn:Eowner.
        - destruct (PositiveMap.E.eq_dec r q) as [->|Hdistinct].
          + assert (Eowner' : owner x' = Some q) by (apply Howner; reflexivity).
            destruct (owner_ok_find x pi q Hok Eowner) as [ls Hfind].
            destruct (owner_ok_find x' pi' q Hok' Eowner') as [ls' Hfind'].
            split; intro Hnone.
            * rewrite Hnone in Hfind. discriminate.
            * rewrite Hnone in Hfind'. discriminate.
          + assert (Hother : owner x <> Some q) by congruence.
            assert (Hother' : owner x' <> Some q).
            { intro H. apply (proj2 Howner) in H. congruence. }
            rewrite <- (residual_find_other x pi q Hother).
            rewrite <- (residual_find_other x' pi' q Hother').
            rewrite Hresidual. tauto.
        - assert (Hother : owner x <> Some q) by congruence.
          assert (Hother' : owner x' <> Some q).
          { intro H. apply (proj2 Howner) in H. congruence. }
          rewrite <- (residual_find_other x pi q Hother).
          rewrite <- (residual_find_other x' pi' q Hother').
          rewrite Hresidual. tauto.
      Qed.

      Lemma owned_residual_find x x' pi pi' q :
        (owner x = Some q <-> owner x' = Some q) ->
        owner x <> Some q ->
        TMap.find q (residual x pi) = TMap.find q (residual x' pi') ->
        TMap.find q pi = TMap.find q pi'.
      Proof.
        intros Howner Hother Hresidual.
        assert (Hother' : owner x' <> Some q).
        { intro H. apply Hother. apply (proj2 Howner); exact H. }
        rewrite <- (residual_find_other x pi q Hother).
        rewrite <- (residual_find_other x' pi' q Hother').
        exact Hresidual.
      Qed.
    End OwnedResidual.

  End AssertionLemmas.

  Ltac pupdate_intros_atomic :=
    intros;
    intros σ1 ρ1 π1 Hpre σ2 Hstep;
    try destruct σ1, σ2;
    try inversion_step;
    (* this is the step taken by the encapsulated LTS *)
    (* do not clear it because information from the pre-condition
       could help reducing it to extract more conditions *)
    (* TODO: handle cases where this hypothesis is not named Hstep *)
    try (inversion Hstep; subst);
    try inversion_thread_event_eq;
    repeat match goal with
    | H : existT _ _ _ = existT _ _ _ |- _ =>
      dependent destruction H
    end.
  
  Ltac pupdate_start := do 2 eexists; split.

  Ltac try_pupdate_start tac :=
    first [
      pupdate_start; [idtac tac|] |
      idtac tac
    ].

  Ltac pupdate_finish :=
    first [
      pupdate_start; [apply rt_refl|] |
      apply rt_refl
    ].

  Ltac pupdate_forward t ev :=
    (* try_pupdate_start *)
    eapply rt_trans; [
      constructor;
      match ev with
      | InvEv ?op => eapply (Semantics.ps_inv t op); eauto
      | ResEv ?op ?ret => eapply (Semantics.ps_ret t op ret); eauto;
            try (rewrite PositiveMap.gss; auto)
      | _ => fail "Cannot recognize the event."
      end;
      try solve [ do 2 constructor; eauto ];
      try solve [ do 2 econstructor; eauto ]
    |].

End AssertionsSingle.


Module SetPossState <: ProofState.
  Import Reg LinCCALBase LTSSpec Semantics.

  Record ProofStateSet {E : Op.t} {F : Op.t} {VE : @LTS E} {VF : @LTS F} : Type :=
  {
    σ : State VE;
    Δ : AbstractConfig VF;
  }.

  Notation "( σ , ρ , π )" := (Build_ProofStateSet  _ _ _ _ σ (ac_singleton ρ π)).
  Notation "( σ , Δ )" := (Build_ProofStateSet  _ _ _ _ σ Δ).

  Definition ProofState {E F VE VF} : Type := @ProofStateSet E F VE VF.

  Section ProofStateSA.
    Context {E : Op.t} {F : Op.t} {VE : @LTS E} {VF : @LTS F}.
    Context {EJ : Join (State VE)} {ESA: @SeparationAlgebra _ EJ} {Eunit: @SeparationAlgebraUnit _ _ ESA}.
    Context {FJ : Join (State VF)} {FSA: @SeparationAlgebra _ FJ} {Funit: @SeparationAlgebraUnit _ _ FSA}.

    (** Explicit proof-state algebra constructors.  [PSS_Join] is deliberately
        not global: two RGSimLin developments may choose different algebras
        for the same carrier type in one client file. *)
    #[local] Instance PSS_Join : Join (@ProofState _ _ VE VF) :=
      fun s1 s2 s3 => join (σ s1) (σ s2) (σ s3) /\ join (Δ s1) (Δ s2) (Δ s3).
    Program Instance PSS_SA : SeparationAlgebra (@ProofState _ _ VE VF).
    Next Obligation.
      inversion H; subst.
      constructor; eauto.
      apply join_comm; auto.
    Qed.
    Next Obligation.
      inversion H; inversion H0; subst.
      pose proof join_assoc _ _ _ _ _ H1 H3 as [? [? ?]].
      pose proof join_assoc _ _ _ _ _ H2 H4 as [? [? ?]].
      exists (x, x0).
      split; constructor; auto.
    Defined.
    Program Instance PSS_unit : SeparationAlgebraUnit (@ProofState _ _ VE VF) PSS_SA := {| ue := (ue, ue) |}.
    Next Obligation.
      constructor; simpl; auto.
      apply ac_unit_join.
    Qed.
    Next Obligation.
      intros ? ? ?.
      inversion H; simpl in *.
      apply unit_spec in H0.
      apply (@unit_spec _ _ _ ac_unit) in H1.
      destruct n, n'. simpl in *. subst; auto.
    Defined.

    Definition underlay_assert (P : State VE -> Prop) :
      @Assertion (@ProofState _ _ VE VF) :=
      fun s => P (σ s) /\ Δ s = @ue _ ac_Join ac_SA ac_unit.

    Definition overlay_assert (P : AbstractConfig VF -> Prop) :
      @Assertion (@ProofState _ _ VE VF) :=
      fun s => σ s = @ue _ EJ ESA Eunit /\ P (Δ s).

    Definition make_ProofState_Join : Join (@ProofState _ _ VE VF) :=
      PSS_Join.
    Definition make_ProofState_SA :
      @SeparationAlgebra (@ProofState _ _ VE VF) make_ProofState_Join :=
      PSS_SA.
    Definition make_ProofState_unit :
      @SeparationAlgebraUnit (@ProofState _ _ VE VF)
        make_ProofState_Join make_ProofState_SA := PSS_unit.
  End ProofStateSA.

  Section TensorProofStateAssertions.
    Context {E1 E2 F : Op.t}.
    Context {V1 : @LTS E1} {V2 : @LTS E2} {VF : @LTS F}.
    Context {J1 : Join (State V1)} {SA1 : @SeparationAlgebra _ J1}.
    Context {U1 : @SeparationAlgebraUnit _ J1 SA1}.
    Context {J2 : Join (State V2)} {SA2 : @SeparationAlgebra _ J2}.
    Context {U2 : @SeparationAlgebraUnit _ J2 SA2}.
    Context {FJ : Join (State VF)} {FSA : @SeparationAlgebra _ FJ}.
    Context {Funit : @SeparationAlgebraUnit _ FJ FSA}.

    Definition underlay_left (P : State V1 -> Prop) :
      @Assertion (@ProofState _ _ (tens_lts V1 V2) VF) :=
      underlay_assert (VE := tens_lts V1 V2) (VF := VF)
        (TensorSeparation.tensor_left P).

    Definition underlay_right (Q : State V2 -> Prop) :
      @Assertion (@ProofState _ _ (tens_lts V1 V2) VF) :=
      underlay_assert (VE := tens_lts V1 V2) (VF := VF)
        (TensorSeparation.tensor_right Q).
  End TensorProofStateAssertions.
  
  Variant spec_union {E : Op.t} {F : Op.t} {VE : @LTS E} {VF : @LTS F}
   : @ProofState _ _ VE VF -> @ProofState _ _ VE VF -> @ProofState _ _ VE VF -> Prop :=
  | SpecUnion : forall σ (Δ1 Δ2 : AbstractConfig VF)
      (Hactive : domain_equiv (ac_active Δ1) (ac_active Δ2)),
      spec_union (σ, Δ1) (σ, Δ2) (σ, ac_union Δ1 Δ2 (Hactive := Hactive)).

  Lemma spec_union_same_underlay {E F VE VF}
      (s1 s2 s : @ProofState E F VE VF) :
    spec_union s1 s2 s -> σ s1 = σ s2 /\ σ s2 = σ s.
  Proof. inversion 1; subst; simpl; auto. Qed.

  Lemma spec_union_comm {E F VE VF}
      (s1 s2 s : @ProofState E F VE VF) :
    spec_union s1 s2 s -> spec_union s2 s1 s.
  Proof.
    intros Hunion. inversion Hunion; subst.
    pose (Hreverse := domain_equiv_symm _ _ Hactive).
    assert (Heq : @ac_union _ VF Δ2 Δ1 Hreverse =
        @ac_union _ VF Δ1 Δ2 Hactive).
    { apply AbstractConfig_ext. intros ρ π.
      symmetry. apply ac_union_comm. }
    rewrite <- Heq. constructor.
  Qed.

  Section ProofStateJoinFacts.
    Context {E : Op.t} {F : Op.t} {VE : @LTS E} {VF : @LTS F}.
    Context {EJ : Join (State VE)} {ESA : @SeparationAlgebra _ EJ}.
    Context {Eunit : @SeparationAlgebraUnit _ EJ ESA}.
    Context {FJ : Join (State VF)} {FSA : @SeparationAlgebra _ FJ}.
    Context {Funit : @SeparationAlgebraUnit _ FJ FSA}.

    Lemma proofstate_join_components (s1 s2 s : @ProofState _ _ VE VF) :
      @join _ PSS_Join s1 s2 s ->
      join (σ s1) (σ s2) (σ s) /\ join (Δ s1) (Δ s2) (Δ s).
    Proof. exact (fun H => H). Qed.
  End ProofStateJoinFacts.
  
End SetPossState.


Module AssertionsSet.
  Module A := Assertions (SetPossState).
  Export A.
  Export SetPossState.

  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Semantics.
  Import TPSimulation.

  Open Scope ac_scope.

  Section AssertionDef.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.

    Definition SpecUnion (P Q : Assertion) : @Assertion (@ProofState _ _ VE VF) :=
      fun s => exists s1 s2, P s1 /\ Q s2 /\ spec_union s1 s2 s.

    (** Figure 8's relation connective for independent transitions over two
        sets of speculative possibilities sharing one concrete state. *)
    Definition RelSpecUnion (G1 G2 : @RGRelation _ _ VE VF) :
        @RGRelation _ _ VE VF :=
      fun s s' => exists s1 s2 s1' s2',
        spec_union s1 s2 s /\ spec_union s1' s2' s' /\
        G1 s1 s1' /\ G2 s2 s2'.

    Definition LiftRelation_σ (Rσ : relation (State VE)) : @RGRelation _ _ VE VF :=
      fun x y => Rσ (σ x) (σ y) /\ Δ x = Δ y.

    Definition LiftRelation_Δ (RΔ : relation (AbstractConfig VF)) : @RGRelation _ _ VE VF :=
      fun x y => σ x = σ y /\ RΔ (Δ x) (Δ y).

    Definition Ginv t f : @RGRelation _ _ VE VF :=
      LiftRelation_Δ (fun Δ1 Δ2 => 
        (forall ρ π, Δ1 ρ π -> TMap.find t π = None) /\
        Δ2 ≡ (ac_inv Δ1 t f)).

    Definition GINV t : @RGRelation _ _ VE VF :=
      fun x y => exists f, Ginv t f x y.

    Definition Gret t f ret : @RGRelation _ _ VE VF :=
      LiftRelation_Δ (fun Δ1 Δ2 => 
        (forall ρ π, Δ1 ρ π -> TMap.find t π = Some (ls_linr f ret)) /\
        Δ2 ≡ (ac_res Δ1 t)).

    Definition GRET t : @RGRelation _ _ VE VF :=
      fun x y => exists f ret, Gret t f ret x y.
    
    Variant APError : @Assertion (@ProofState _ _ VE VF) :=
    | APErrorSome s ρ π : Δ s ρ π -> poss_steps (ρ, π) PossError -> APError s.

    Definition PUpdate (G : @RGRelation _ _ VE VF) (ev : ThreadEvent) (P Q : Assertion) : Prop :=
      forall σ Δ, P (σ, Δ) ->
      forall σ', Step VE ev σ σ' ->
      exists Δ', (Δ' ⊆ ac_steps Δ)%AbstractConfig
        /\ Q (σ', Δ') /\ G (σ, Δ) (σ', Δ').

    Definition PUpdateId (G : @RGRelation _ _ VE VF) (P Q : Assertion) : Prop :=
      forall σ Δ, P (σ, Δ) ->
      exists Δ', (Δ' ⊆ ac_steps Δ)%AbstractConfig
        /\ Q (σ, Δ') /\ G (σ, Δ) (σ, Δ').

    (** A client-selected relation between individual abstract
        possibilities.  Reachability remains a separate semantic condition
        in [PStep], so [S] only describes which branches the client keeps or
        creates. *)
    Definition PossibilityRelation : Type :=
      State VE -> State VF -> tmap (@LinState F) ->
      State VF -> tmap (@LinState F) -> Prop.

    Definition PStep (S : PossibilityRelation) :
        @RGRelation _ _ VE VF :=
      fun s s' =>
        σ s = σ s' /\
        forall ρ' π', Δ s' ρ' π' ->
          exists ρ π, Δ s ρ π /\ S (σ s) ρ π ρ' π' /\
            poss_steps (PossOk ρ π) (PossOk ρ' π').

    (** Because [AbstractConfig] is intrinsically nonempty, a primitive
        possibility step must exhibit at least one valid output. *)
    Definition PStepEnabled (S : PossibilityRelation) (P : Assertion) : Prop :=
      forall σ Δ, P (σ, Δ) -> exists Δ', PStep S (σ, Δ) (σ, Δ').
    
    Definition ALin (t : tid) (ls : LinState) : @Assertion (@ProofState _ _ VE VF) :=
      fun s => forall ρ π, Δ s ρ π -> TMap.find t π = Some ls.

    (** The paper's [t |->exists ls]: some nonempty subset of the current
        possibilities fixes [t] to [ls]. *)
    Definition ALinExists (t : tid) (ls : LinState) :
        @Assertion (@ProofState _ _ VE VF) :=
      SpecUnion (ALin t ls) TT.
  
    Definition ALin' t ls : @Assertion (@ProofState _ _ VE VF) :=
      fun s => exists ρ, ac_equiv (Δ s) (ac_singleton ρ (LinCCAL.TMap.add t ls (LinCCAL.TMap.Leaf _))).

    Definition Aρ ρ : @Assertion (@ProofState _ _ VE VF) :=
      fun s => ac_equiv (Δ s) (ac_singleton ρ (LinCCAL.TMap.Leaf _)).

    Lemma ALin_equiv : forall s1 s2 t ls,
      ac_equiv (Δ s1) (Δ s2) ->
      ALin t ls s1 -> ALin t ls s2.
    Proof.
      intros. intros ? ? ?.
      apply H in H1; eauto.
    Qed.

  End AssertionDef.

  Section LinearizationCell.
    Context {E : Op.t} {F : Op.t}.
    Context {VE : @LTS E} {VF : @LTS F}.
    Context {EJ : Join (State VE)} {ESA : @SeparationAlgebra _ EJ}.
    Context {Eunit : @SeparationAlgebraUnit _ EJ ESA}.
    Context {FJ : Join (State VF)} {FSA : @SeparationAlgebra _ FJ}.
    Context {Funit : @SeparationAlgebraUnit _ FJ FSA}.

    #[local] Existing Instance SetPossState.PSS_Join.
    #[local] Existing Instance SetPossState.PSS_SA.

    (** The paper's spatial singleton [t |-> ls].  It owns only the thread's
        linearization-map cell: both the concrete state and the remaining
        abstract machine state are units. *)
    Definition ALinCell (t : tid) (ls : LinState) :
        @Assertion (@ProofState _ _ VE VF) :=
      overlay_assert (VE := VE) (VF := VF)
        (fun Δ => ac_equiv Δ
          (ac_singleton ue
            (TMap.add t ls (TMap.empty (@LinState F))))).

    (** Owning the singleton cell with an arbitrary spatial frame is exactly
        the non-spatial fact that every possibility has decided [t] as [ls]. *)
    Lemma ALinCell_sep_TT_equiv (t : tid) (ls : LinState) :
      ⊨ ALinCell t ls * TT <<==>> ALin t ls.
    Proof.
      intros s; split.
      - intros (scell & sframe & Hjoin & Hcell & _).
        destruct Hjoin as [_ Hjoin].
        destruct Hcell as [_ Hcell].
        intros ρ π Hposs.
        destruct (join_ac_decompose _ _ _ _ _ Hjoin Hposs)
          as (ρ1 & ρ2 & π1 & π2 & Howned & _ & _ & Hmaps).
        apply Hcell in Howned. inversion Howned; subst.
        eapply tree_join_increasing; eauto. apply TMap.gss.
      - intros Hlin.
        exists
          (ue, ac_singleton ue
            (TMap.add t ls (TMap.empty (@LinState F)))),
          (σ s, ac_res (Δ s) t).
        split.
        + split; simpl.
          * apply unit_join_left.
          * apply ac_singleton_res_join. exact Hlin.
        + split.
          * split; simpl; reflexivity.
          * constructor.
    Qed.
  End LinearizationCell.

  (** Paper notation for a spatial singleton cell, universal agreement across
      possibilities, and agreement in some speculative subset, respectively. *)
  Notation "t ↦ ls" := (ALinCell t ls)
    (at level 35, no associativity) : assertion_scope.
  Notation "t ↦∀ ls" := (ALin t ls)
    (at level 35, no associativity) : assertion_scope.
  Notation "t ↦∃ ls" := (ALinExists t ls)
    (at level 35, no associativity) : assertion_scope.

  Notation "G ⊨ P [ ev ]⭆ Q" := (PUpdate G ev P Q) (at level 100) : assertion_scope.
  Notation "G ⊨ P ⭆ Q" := (PUpdateId G P Q) (at level 100) : assertion_scope.
  Notation "P ⨁ Q" := (SpecUnion P Q) (at level 30) : assertion_scope.
  Notation "P ⊕ Q" := (SpecUnion P Q) (at level 30) : assertion_scope.
  Notation "G ⨁ᵣ H" := (RelSpecUnion G H) (at level 40) : rg_relation_scope.
  
  Section AssertionLemmas.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.

    Open Scope rg_relation_scope.

    Lemma SpecUnion_intro (P Q : @Assertion (@ProofState _ _ VE VF))
        σ Δ1 Δ2
        (Hactive : domain_equiv (ac_active Δ1) (ac_active Δ2)) :
      P (σ, Δ1) -> Q (σ, Δ2) ->
      SpecUnion P Q (σ, @ac_union _ VF Δ1 Δ2 Hactive).
    Proof.
      intros HP HQ. exists (σ, Δ1), (σ, Δ2).
      repeat split; auto.
    Qed.

    Lemma SpecUnion_mono
        (P P' Q Q' : @Assertion (@ProofState _ _ VE VF)) :
      (⊨ P ==>> P') -> (⊨ Q ==>> Q') ->
      ⊨ P ⨁ Q ==>> P' ⨁ Q'.
    Proof.
      intros HP HQ s (s1 & s2 & H1 & H2 & Hunion).
      exists s1, s2. split; [apply HP; exact H1|].
      split; [apply HQ; exact H2|exact Hunion].
    Qed.

    Lemma SpecUnion_comm
        (P Q : @Assertion (@ProofState _ _ VE VF)) :
      ⊨ P ⨁ Q <<==>> Q ⨁ P.
    Proof.
      intros s; split; intros (s1 & s2 & HP & HQ & Hunion).
      - exists s2, s1. repeat split; auto using spec_union_comm.
      - exists s2, s1. repeat split; auto using spec_union_comm.
    Qed.

    Lemma RelSpecUnion_mono
        (G1 G1' G2 G2' : @RGRelation _ _ VE VF) :
      (G1 ⊆ G1')%RGRelation -> (G2 ⊆ G2')%RGRelation ->
      (RelSpecUnion G1 G2 ⊆ RelSpecUnion G1' G2')%RGRelation.
    Proof.
      intros HG1 HG2 s s'
        (s1 & s2 & s1' & s2' & Hpre & Hpost & H1 & H2).
      exists s1, s2, s1', s2'. repeat split; eauto.
    Qed.

    Lemma RelSpecUnion_comm
        (G1 G2 : @RGRelation _ _ VE VF) :
      forall s s', RelSpecUnion G1 G2 s s' <->
        RelSpecUnion G2 G1 s s'.
    Proof.
      intros s s'; split;
        intros (s1 & s2 & s1' & s2' & Hpre & Hpost & H1 & H2).
      - exists s2, s1, s2', s1'.
        repeat split; auto using spec_union_comm.
      - exists s2, s1, s2', s1'.
        repeat split; auto using spec_union_comm.
    Qed.

    Lemma PUpdateConseq {P Q P' Q' : @Assertion (@ProofState _ _ VE VF)} {ev} {G} :
      (⊨ P' ==>> P) ->
      (⊨ Q ==>> Q') ->
      (G ⊨ P [ ev ]⭆ Q) ->
      G ⊨ P' [ ev ]⭆ Q'.
    Proof.
      intros. intros ?; intros.
      apply H in H2.
      apply H1 in H2.
      apply H2 in H3 as (? & ?& ? & ?).
      apply H0 in H4.
      eauto.
    Qed.

    Lemma PUpdateIdConseq
        {P Q P' Q' : @Assertion (@ProofState _ _ VE VF)} {G} :
      (⊨ P' ==>> P) -> (⊨ Q ==>> Q') ->
      PUpdateId G P Q -> PUpdateId G P' Q'.
    Proof.
      intros Hpre Hpost Hupd σ Δ HP.
      destruct (Hupd σ Δ (Hpre _ HP)) as [Δ' [Hsteps [HQ HG]]].
      exists Δ'. split; [exact Hsteps|].
      split; [apply Hpost; exact HQ|exact HG].
    Qed.

    (** Figure 10, [pupd-imply]. *)
    Lemma PUpdateIdImply
        (P Q : @Assertion (@ProofState _ _ VE VF)) :
      (⊨ P ==>> Q) -> PUpdateId GId P Q.
    Proof.
      intros Himpl σ Δ HP. exists Δ.
      split; [apply ac_steps_refl|].
      split; [apply Himpl; exact HP|reflexivity].
    Qed.

    (** Figure 10, [pupd-disj]. *)
    Lemma PUpdateIdDisj
        (G1 G2 : @RGRelation _ _ VE VF)
        (P1 P2 Q1 Q2 : @Assertion (@ProofState _ _ VE VF)) :
      PUpdateId G1 P1 Q1 -> PUpdateId G2 P2 Q2 ->
      PUpdateId (Union G1 G2) (P1 \\// P2) (Q1 \\// Q2).
    Proof.
      intros Hupd1 Hupd2 σ Δ [HP1 | HP2].
      - destruct (Hupd1 σ Δ HP1) as [Δ' [Hsteps [HQ HG]]].
        exists Δ'. split; [exact Hsteps|].
        split; [left; exact HQ|left; exact HG].
      - destruct (Hupd2 σ Δ HP2) as [Δ' [Hsteps [HQ HG]]].
        exists Δ'. split; [exact Hsteps|].
        split; [right; exact HQ|right; exact HG].
    Qed.

    (** Figure 10, [pupd-spec].  Each branch evolves independently and the
        results are reunited as alternatives, not spatial resources. *)
    Lemma PUpdateIdSpec
        (G1 G2 : @RGRelation _ _ VE VF)
        (P1 P2 Q1 Q2 : @Assertion (@ProofState _ _ VE VF)) :
      PUpdateId G1 P1 Q1 -> PUpdateId G2 P2 Q2 ->
      PUpdateId (RelSpecUnion G1 G2)
        (SpecUnion P1 P2) (SpecUnion Q1 Q2).
    Proof.
      intros Hupd1 Hupd2 σ Δ
        ([σ1 Δ1] & [σ2 Δ2] & HP1 & HP2 & Hunion).
      inversion Hunion; subst; simpl in *.
      destruct (Hupd1 σ Δ1 HP1) as [Δ1' [Hsteps1 [HQ1 HG1]]].
      destruct (Hupd2 σ Δ2 HP2) as [Δ2' [Hsteps2 [HQ2 HG2]]].
      pose proof (ac_subset_active _ _ Hsteps1) as Hactive1.
      pose proof (ac_subset_active _ _ Hsteps2) as Hactive2.
      assert (Hactive' : domain_equiv (ac_active Δ1') (ac_active Δ2')).
      { eapply domain_equiv_trans; [exact Hactive1|].
        eapply domain_equiv_trans; [exact Hactive|].
        apply domain_equiv_symm; exact Hactive2. }
      exists (@ac_union _ VF Δ1' Δ2' Hactive'). split.
      - eapply ac_union_steps_subset; eauto.
      - split.
        + eapply SpecUnion_intro; eauto.
        + exists (σ, Δ1), (σ, Δ2), (σ, Δ1'), (σ, Δ2').
          split; [constructor|]. split; [constructor|].
          split; assumption.
    Qed.

    Lemma PUpdateIdCompose
        (G1 G2 : @RGRelation _ _ VE VF)
        (P Q R : @Assertion (@ProofState _ _ VE VF)) :
      PUpdateId G1 P Q -> PUpdateId G2 Q R ->
      PUpdateId (ComposeR G1 G2) P R.
    Proof.
      intros Hupd1 Hupd2 σ Δ HP.
      destruct (Hupd1 σ Δ HP) as [Δ1 [Hsteps1 [HQ HG1]]].
      destruct (Hupd2 σ Δ1 HQ) as [Δ2 [Hsteps2 [HR HG2]]].
      exists Δ2. split.
      - eapply ac_steps_subset_trans; eauto.
      - split; [exact HR|]. exists (σ, Δ1); auto.
    Qed.

    Lemma PStepEnabled_refl
        (S : @PossibilityRelation E F VE VF)
        (P : @Assertion (@ProofState _ _ VE VF)) :
      (forall σ (Δ : AbstractConfig VF) ρ π,
        Δ ρ π -> S σ ρ π ρ π) ->
      PStepEnabled S P.
    Proof.
      intros HS σ Δ HP. exists Δ. split; [reflexivity|].
      intros ρ π Hposs. exists ρ, π.
      split; [exact Hposs|]. split.
      - eapply HS; exact Hposs.
      - apply rt_refl.
    Qed.

    (** Figure 10, [pupd-pstep].  The postcondition records the relational
        image of [P], while [PStepEnabled] makes the paper's implicit
        nonemptiness side condition explicit. *)
    Lemma PUpdateIdPStep
        (S : @PossibilityRelation E F VE VF)
        (P : @Assertion (@ProofState _ _ VE VF)) :
      PStepEnabled S P ->
      PUpdateId (PStep S) P (ComposeA P (PStep S)).
    Proof.
      intros Henabled σ Δ HP.
      destruct (Henabled σ Δ HP) as [Δ' Hstep].
      exists Δ'. split.
      - intros ρ' π' Hposs.
        destruct (proj2 Hstep _ _ Hposs)
          as [ρ [π [Hsource [HS Hreach]]]].
        econstructor; eauto.
      - split; [|exact Hstep].
        exists (σ, Δ). split; assumption.
    Qed.

    (** Figure 10's event-triple consequence rule. *)
    Lemma PUpdateConseqUpdates
        (G1 G2 G3 : @RGRelation _ _ VE VF)
        (P P' Q' Q : @Assertion (@ProofState _ _ VE VF)) ev :
      PUpdateId G1 P P' -> PUpdate G2 ev P' Q' ->
      PUpdateId G3 Q' Q ->
      PUpdate (ComposeR (ComposeR G1 G2) G3) ev P Q.
    Proof.
      intros Hbefore Hevent Hafter σ Δ HP σ' Hstep.
      destruct (Hbefore σ Δ HP) as [Δ1 [Hsteps1 [HP' HG1]]].
      destruct (Hevent σ Δ1 HP' σ' Hstep)
        as [Δ2 [Hsteps2 [HQ' HG2]]].
      destruct (Hafter σ' Δ2 HQ') as [Δ3 [Hsteps3 [HQ HG3]]].
      exists Δ3. split.
      - eapply ac_steps_subset_trans; [exact Hsteps1|].
        eapply ac_steps_subset_trans; eauto.
      - split; [exact HQ|].
        exists (σ', Δ2). split; [|exact HG3].
        exists (σ, Δ1). auto.
    Qed.

    Lemma PUpdateGuaranteeWeaken {P Q : @Assertion (@ProofState _ _ VE VF)}
        {ev} {G G'} :
      (G ⊆ G')%RGRelation -> PUpdate G ev P Q -> PUpdate G' ev P Q.
    Proof.
      intros Hsub Hupd σ Δ HP σ' Hstep.
      destruct (Hupd σ Δ HP σ' Hstep) as [Δ' [Hs [HQ HG]]].
      exists Δ'. repeat split; eauto.
    Qed.

    Lemma PUpdateIdGuaranteeWeaken
        {P Q : @Assertion (@ProofState _ _ VE VF)} {G G'} :
      (G ⊆ G')%RGRelation -> PUpdateId G P Q -> PUpdateId G' P Q.
    Proof.
      intros Hsub Hupd σ Δ HP.
      destruct (Hupd σ Δ HP) as [Δ' [Hs [HQ HG]]].
      exists Δ'. repeat split; eauto.
    Qed.
  End AssertionLemmas.

  Section FramedUpdates.
    Context {E : Op.t} {F : Op.t} {VE : @LTS E} {VF : @LTS F}.
    Context {EJ : Join (State VE)} {ESA : @SeparationAlgebra _ EJ}.
    Context {Eunit : @SeparationAlgebraUnit _ EJ ESA}.
    Context {FJ : Join (State VF)} {FSA : @SeparationAlgebra _ FJ}.
    Context {Funit : @SeparationAlgebraUnit _ FJ FSA}.

    #[local] Existing Instance SetPossState.PSS_Join.
    #[local] Existing Instance SetPossState.PSS_SA.

    (** This combines same-frame closure of [G] with existence of the
        overlay post-state join.  Conditional LTS frame closure cannot by
        itself manufacture that compatibility witness. *)
    Definition FramePreservingUpdate (G : @RGRelation _ _ VE VF) : Prop :=
      forall σo Δo σf Δf σw Δw σo' Δo' σw',
        @join _ SetPossState.PSS_Join
          (σo, Δo) (σf, Δf) (σw, Δw) ->
        G (σo, Δo) (σo', Δo') ->
        join σo' σf σw' ->
        exists Δw', join Δo' Δf Δw' /\
          G (σw, Δw) (σw', Δw').

    (** The transformed-context rule only needs existence of a compatible
        framed post-state.  The guarantee itself is transformed to
        [G ∗ GId], so it need not already contain the whole-state step. *)
    Definition FrameCompatibleUpdate (G : @RGRelation _ _ VE VF) : Prop :=
      forall σo Δo σf Δf σw Δw σo' Δo' σw',
        @join _ SetPossState.PSS_Join
          (σo, Δo) (σf, Δf) (σw, Δw) ->
        G (σo, Δo) (σo', Δo') ->
        join σo' σf σw' ->
        exists Δw', join Δo' Δf Δw'.

    Lemma FramePreservingUpdate_compatible G :
      FramePreservingUpdate G -> FrameCompatibleUpdate G.
    Proof.
      intros H σo Δo σf Δf σw Δw σo' Δo' σw' Hj HG Hj'.
      destruct (H σo Δo σf Δf σw Δw σo' Δo' σw' Hj HG Hj')
        as [Δw' [Hjoin _]]. eauto.
    Qed.

    (** Closure is stated for [poss_steps], because one-step
        [FrameClosedLTS] is insufficient without compatibility at every
        intermediate state of a reflexive-transitive execution. *)
    Definition FramePreservingSteps : Prop :=
      forall owned frame whole owned' whole',
        join owned frame whole ->
        ac_subset owned' (ac_steps owned) ->
        join owned' frame whole' ->
        ac_subset whole' (ac_steps whole).

    Definition FrameInvariant (I Fr : @Assertion (@ProofState _ _ VE VF)) : Prop :=
      forall P, (⊨ P ==>> I) -> ⊨ P * Fr ==>> I.

    Definition FrameStable (R : @RGRelation _ _ VE VF) I
        (Fr : @Assertion (@ProofState _ _ VE VF)) : Prop :=
      forall P, Stable R I P -> Stable R I (P * Fr).

    (** Stability after transforming the rely and invariant according to
        Figure 8.  It is kept explicit because the minimal [SeparationAlgebra]
        interface has neither cancellation nor the cross-split property
        needed to reconcile two arbitrary decompositions of one state. *)
    Definition FrameStableContext (R : @RGRelation _ _ VE VF) I
        (Fr : @Assertion (@ProofState _ _ VE VF)) : Prop :=
      forall P, Stable R I P ->
        Stable (RelSep R (FrameIdentity Fr)) (I * Fr) (P * Fr).

    Definition FrameStableWith (R : @RGRelation _ _ VE VF) I
        (Rf : @RGRelation _ _ VE VF) If
        (Fr : @Assertion (@ProofState _ _ VE VF)) : Prop :=
      forall P, (⊨ P ==>> I) -> Stable R I P ->
        Stable (RelSep R Rf) (I * If) (P * Fr).

    Section FencedFrameStability.
      Context {PSSCancel : @JoinLeftCancellative
        (@ProofState E F VE VF) SetPossState.PSS_Join}.

      (** Fences and stability of the frame discharge the weakened,
          invariant-aware framing obligation used by the Hoare proof. *)
      Lemma FrameStableWith_fenced
          (R Rf : @RGRelation _ _ VE VF)
          (I If Fr : @Assertion (@ProofState _ _ VE VF)) :
        Fence I R -> Fence If Rf -> Stable Rf If Fr ->
        FrameStableWith R I Rf If Fr.
      Proof.
        intros Hfence Hfencef Hstable P HPI HPstable.
        eapply Stable_sep_fenced; eauto.
      Qed.
    End FencedFrameStability.

    Definition FramePreservingError
        (Fr : @Assertion (@ProofState _ _ VE VF)) : Prop :=
      ⊨ APError * Fr ==>> APError.

    (** Semantic locality for RGSimLin event updates, packaged so it can be
        established once and reused by framing rules. *)
    Record LogicFrameLocality (G : @RGRelation _ _ VE VF)
        (Fr : @Assertion (@ProofState _ _ VE VF)) : Prop := {
      logic_frame_compatible : FrameCompatibleUpdate G;
      logic_frame_steps : FramePreservingSteps;
      logic_frame_error : FramePreservingError Fr
    }.

    (** Logical compatibility of an assertion frame with additional rely,
        guarantee, and invariant components. *)
    Record FrameContext (R : @RGRelation _ _ VE VF) I
        (Rf Gf : @RGRelation _ _ VE VF) If
        (Fr : @Assertion (@ProofState _ _ VE VF)) : Prop := {
      frame_context_stable : FrameStableWith R I Rf If Fr;
      frame_context_invariant : ⊨ Fr ==>> If;
      frame_context_guarantee :
        (FrameIdentity Fr ⊆ Gf)%RGRelation
    }.

    Section FencedFrameContext.
      Context {PSSCancel : @JoinLeftCancellative
        (@ProofState E F VE VF) SetPossState.PSS_Join}.

      (** Clients may keep fences outside the Hoare judgment and use them
          only when applying the frame rule. *)
      Lemma FrameContext_fenced
          (R Rf Gf : @RGRelation _ _ VE VF)
          (I If Fr : @Assertion (@ProofState _ _ VE VF)) :
        Fence I R -> Fence If Rf -> Fence If Gf ->
        Stable Rf If Fr -> (⊨ Fr ==>> If) ->
        FrameContext R I Rf Gf If Fr.
      Proof.
        intros Hfence Hfencer Hfenceg Hstable HFrInv.
        constructor.
        - eapply FrameStableWith_fenced; eauto.
        - exact HFrInv.
        - intros s s' [Heq [HFr HFr']].
          apply (proj1 Hfenceg). split; [exact Heq|].
          split; [apply HFrInv|apply HFrInv]; assumption.
      Qed.
    End FencedFrameContext.

    Lemma perror_sepcon_frame Punsafe P Fr :
      FramePreservingError Fr ->
      (⊨ Punsafe ==>> P \\// APError) ->
      ⊨ Punsafe * Fr ==>> (P * Fr) \\// APError.
    Proof.
      intros Herr Hperror whole (owned & frame & Hj & Hu & HFr).
      destruct (Hperror owned Hu) as [HP | HE].
      - left. exists owned, frame. split; [exact Hj|]. split; assumption.
      - right. apply Herr. exists owned, frame.
        split; [exact Hj|]. split; assumption.
    Qed.

    Context {Hlocal : @LocalLTS E VE EJ}.

    Lemma ANoError_sepcon_inv t op
        (P Fr : @Assertion (@ProofState _ _ VE VF)) :
      (⊨ P ==>> ANoError (Build_ThreadEvent t (InvEv op))) ->
      ⊨ P * Fr ==>> ANoError (Build_ThreadEvent t (InvEv op)).
    Proof.
      intros Hsafe [σw Δw] ([σo Δo] & [σf Δf] & Hj & HP & HFr).
      unfold ANoError in *. simpl in *.
      eapply ANoError_frame_inv; [exact (proj1 Hj)|].
      exact (Hsafe (σo, Δo) HP).
    Qed.

    Lemma PUpdate_frame_inv (G : @RGRelation _ _ VE VF) t op
        (P Q Fr : @Assertion (@ProofState _ _ VE VF)) :
      FramePreservingUpdate G -> FramePreservingSteps ->
      (⊨ P ==>> ANoError (Build_ThreadEvent t (InvEv op))) ->
      (G ⊨ P [ Build_ThreadEvent t (InvEv op) ]⭆ Q) ->
      (G ⊨ (P * Fr) [ Build_ThreadEvent t (InvEv op) ]⭆ (Q * Fr)).
    Proof.
      intros HG Hsteps Hsafe Hupd σw Δw
        ([σo Δo] & [σf Δf] & Hj & HP & HFr) σw' Hstep.
      simpl in Hj.
      destruct (invocation_step_unframe_safe t op σo σf σw σw'
        (proj1 Hj) (Hsafe (σo, Δo) HP) Hstep)
        as [σo' [Hostep Hσjoin]].
      destruct (Hupd σo Δo HP σo' Hostep)
        as [Δo' [Hosteps [HQ HGowned]]].
      destruct (HG σo Δo σf Δf σw Δw σo' Δo' σw' Hj HGowned Hσjoin)
        as [Δw' [HΔjoin HGwhole]].
      exists Δw'. split.
      - eapply (Hsteps Δo Δf Δw Δo' Δw'); eauto. exact (proj2 Hj).
      - split; [|exact HGwhole].
        exists (σo', Δo'), (σf, Δf).
        split; [exact (conj Hσjoin HΔjoin)|]. split; assumption.
    Qed.

    Lemma PUpdate_frame_res (G : @RGRelation _ _ VE VF) t op ret
        (P Q Fr : @Assertion (@ProofState _ _ VE VF)) :
      FramePreservingUpdate G -> FramePreservingSteps ->
      (G ⊨ P [ Build_ThreadEvent t (ResEv op ret) ]⭆ Q) ->
      (G ⊨ (P * Fr) [ Build_ThreadEvent t (ResEv op ret) ]⭆ (Q * Fr)).
    Proof.
      intros HG Hsteps Hupd σw Δw
        ([σo Δo] & [σf Δf] & Hj & HP & HFr) σw' Hstep.
      simpl in Hj.
      destruct (response_step_unframe t op ret σo σf σw σw'
        (proj1 Hj) Hstep) as [σo' [Hostep Hσjoin]].
      destruct (Hupd σo Δo HP σo' Hostep)
        as [Δo' [Hosteps [HQ HGowned]]].
      destruct (HG σo Δo σf Δf σw Δw σo' Δo' σw' Hj HGowned Hσjoin)
        as [Δw' [HΔjoin HGwhole]].
      exists Δw'. split.
      - eapply (Hsteps Δo Δf Δw Δo' Δw'); eauto. exact (proj2 Hj).
      - split; [|exact HGwhole].
        exists (σo', Δo'), (σf, Δf).
        split; [exact (conj Hσjoin HΔjoin)|]. split; assumption.
    Qed.

    Lemma PUpdateId_frame (G : @RGRelation _ _ VE VF)
        (P Q Fr : @Assertion (@ProofState _ _ VE VF)) :
      FramePreservingUpdate G -> FramePreservingSteps ->
      (G ⊨ P ⭆ Q) -> (G ⊨ (P * Fr) ⭆ (Q * Fr)).
    Proof.
      intros HG Hsteps Hupd σw Δw
        ([σo Δo] & [σf Δf] & Hj & HP & HFr).
      simpl in Hj.
      destruct (Hupd σo Δo HP) as [Δo' [Hosteps [HQ HGowned]]].
      destruct (HG σo Δo σf Δf σw Δw σo Δo' σw Hj HGowned (proj1 Hj))
        as [Δw' [HΔjoin HGwhole]].
      exists Δw'. split.
      - eapply (Hsteps Δo Δf Δw Δo' Δw'); eauto. exact (proj2 Hj).
      - split; [|exact HGwhole].
        exists (σo, Δo'), (σf, Δf).
        split; [exact (conj (proj1 Hj) HΔjoin)|]. split; assumption.
    Qed.

    Lemma PUpdate_frame_inv_context (G : @RGRelation _ _ VE VF) t op
        (P Q Fr : @Assertion (@ProofState _ _ VE VF)) :
      FrameCompatibleUpdate G -> FramePreservingSteps ->
      (⊨ P ==>> ANoError (Build_ThreadEvent t (InvEv op))) ->
      (G ⊨ P [ Build_ThreadEvent t (InvEv op) ]⭆ Q) ->
      (RelSep G (FrameIdentity Fr) ⊨ (P * Fr)
        [ Build_ThreadEvent t (InvEv op) ]⭆ (Q * Fr)).
    Proof.
      intros HG Hsteps Hsafe Hupd σw Δw
        ([σo Δo] & [σf Δf] & Hj & HP & HFr) σw' Hstep.
      simpl in Hj.
      destruct (invocation_step_unframe_safe t op σo σf σw σw'
        (proj1 Hj) (Hsafe (σo, Δo) HP) Hstep)
        as [σo' [Hostep Hσjoin]].
      destruct (Hupd σo Δo HP σo' Hostep)
        as [Δo' [Hosteps [HQ HGowned]]].
      destruct (HG σo Δo σf Δf σw Δw σo' Δo' σw' Hj HGowned Hσjoin)
        as [Δw' HΔjoin].
      exists Δw'. split.
      - eapply (Hsteps Δo Δf Δw Δo' Δw'); eauto. exact (proj2 Hj).
      - split.
        + exists (σo', Δo'), (σf, Δf).
          split; [exact (conj Hσjoin HΔjoin)|]. split; assumption.
        + eapply (RelSep_intro G (FrameIdentity Fr)
            (σo, Δo) (σf, Δf) (σw, Δw)
            (σo', Δo') (σf, Δf) (σw', Δw'));
            [exact Hj|exact (conj Hσjoin HΔjoin)|exact HGowned|].
          split; [reflexivity|]. split; assumption.
    Qed.

    Lemma PUpdate_frame_res_context (G : @RGRelation _ _ VE VF) t op ret
        (P Q Fr : @Assertion (@ProofState _ _ VE VF)) :
      FrameCompatibleUpdate G -> FramePreservingSteps ->
      (G ⊨ P [ Build_ThreadEvent t (ResEv op ret) ]⭆ Q) ->
      (RelSep G (FrameIdentity Fr) ⊨ (P * Fr)
        [ Build_ThreadEvent t (ResEv op ret) ]⭆ (Q * Fr)).
    Proof.
      intros HG Hsteps Hupd σw Δw
        ([σo Δo] & [σf Δf] & Hj & HP & HFr) σw' Hstep.
      simpl in Hj.
      destruct (response_step_unframe t op ret σo σf σw σw'
        (proj1 Hj) Hstep) as [σo' [Hostep Hσjoin]].
      destruct (Hupd σo Δo HP σo' Hostep)
        as [Δo' [Hosteps [HQ HGowned]]].
      destruct (HG σo Δo σf Δf σw Δw σo' Δo' σw' Hj HGowned Hσjoin)
        as [Δw' HΔjoin].
      exists Δw'. split.
      - eapply (Hsteps Δo Δf Δw Δo' Δw'); eauto. exact (proj2 Hj).
      - split.
        + exists (σo', Δo'), (σf, Δf).
          split; [exact (conj Hσjoin HΔjoin)|]. split; assumption.
        + eapply (RelSep_intro G (FrameIdentity Fr)
            (σo, Δo) (σf, Δf) (σw, Δw)
            (σo', Δo') (σf, Δf) (σw', Δw'));
            [exact Hj|exact (conj Hσjoin HΔjoin)|exact HGowned|].
          split; [reflexivity|]. split; assumption.
    Qed.

    Lemma PUpdateId_frame_context (G : @RGRelation _ _ VE VF)
        (P Q Fr : @Assertion (@ProofState _ _ VE VF)) :
      FrameCompatibleUpdate G -> FramePreservingSteps ->
      (G ⊨ P ⭆ Q) ->
      (RelSep G (FrameIdentity Fr) ⊨ (P * Fr) ⭆ (Q * Fr)).
    Proof.
      intros HG Hsteps Hupd σw Δw
        ([σo Δo] & [σf Δf] & Hj & HP & HFr).
      simpl in Hj.
      destruct (Hupd σo Δo HP) as [Δo' [Hosteps [HQ HGowned]]].
      destruct (HG σo Δo σf Δf σw Δw σo Δo' σw Hj HGowned (proj1 Hj))
        as [Δw' HΔjoin].
      exists Δw'. split.
      - eapply (Hsteps Δo Δf Δw Δo' Δw'); eauto. exact (proj2 Hj).
      - split.
        + exists (σo, Δo'), (σf, Δf).
          split; [exact (conj (proj1 Hj) HΔjoin)|]. split; assumption.
        + eapply (RelSep_intro G (FrameIdentity Fr)
            (σo, Δo) (σf, Δf) (σw, Δw)
            (σo, Δo') (σf, Δf) (σw, Δw'));
            [exact Hj|exact (conj (proj1 Hj) HΔjoin)|exact HGowned|].
          split; [reflexivity|]. split; assumption.
    Qed.
  End FramedUpdates.


  Ltac pupdate_intros_atomic :=
    intros;
    intros σ1 Δ1 Hpre σ2 Hstep;
    try destruct σ1, σ2;
    try inversion_step;
    (* this is the step taken by the encapsulated LTS *)
    (* do not clear it because information from the pre-condition
      could help reducing it to extract more conditions *)
    (* TODO: handle cases where this hypothesis is not named Hstep *)
    try (inversion Hstep; subst);
    try inversion_thread_event_eq;
    repeat match goal with
    | H : existT _ _ _ = existT _ _ _ |- _ =>
      dependent destruction H
    end.
  
  Ltac pupdate_start := eexists; split.

  Ltac try_pupdate_start tac :=
    first [
      pupdate_start; [idtac tac|] |
      idtac tac
    ].

  Ltac pupdate_finish :=
    first [
      pupdate_start; [apply rt_refl|] |
      apply rt_refl
    ].

  Ltac pupdate_forward t ev :=
    (* try_pupdate_start *)
    eapply rt_trans; [
      constructor;
      match ev with
      | InvEv ?op => eapply (Semantics.ps_inv t op); eauto
      | ResEv ?op ?ret => eapply (Semantics.ps_ret t op ret); eauto;
            try (rewrite PositiveMap.gss; auto)
      | _ => fail "Cannot recognize the event."
      end;
      try solve [ do 2 constructor; eauto ];
      try solve [ do 2 econstructor; eauto ]
    |].
    
  Ltac pupdate_trylin_from Hposs :=
    unshelve eapply (ac_trylin_subset_steps _ _ _ _ _ Hposs);
    match goal with |- ?G => 
      match type of G with
      | Prop => idtac
      | _ => shelve end
    end.

End AssertionsSet.
