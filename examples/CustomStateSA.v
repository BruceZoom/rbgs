Require Import Coq.micromega.Lia.
Require Import models.EffectSignatures.
Require Import models.LinCCAL.
Require Import models.logics.SeparationAlgebra.
Require Import models.simlin.LTS.
Require Import models.simlin.TensorSeparation.
Require Import models.simlin.Assertion.

Module CustomStateSA.
  Import Reg LinCCALBase LTSSpec.

  Definition nat_join : Join nat := fun a b c => c = Nat.add a b.
  Definition nat_SA : @SeparationAlgebra nat nat_join.
  Proof.
    constructor.
    - intros; unfold join, nat_join in *; lia.
    - intros; unfold join, nat_join in *.
      exists (Nat.add my mz); split; lia.
  Qed.
  Program Definition nat_unit : @SeparationAlgebraUnit nat nat_join nat_SA :=
    {| ue := O |}.
  Next Obligation. unfold join, nat_join; lia. Qed.
  Next Obligation. intros n n' H; unfold join, nat_join in H; lia. Qed.

  Definition bool_join : Join bool := fun a b c => c = orb a b.
  Definition bool_SA : @SeparationAlgebra bool bool_join.
  Proof.
    constructor.
    - intros a b c H; unfold join, bool_join in *.
      subst c. destruct a, b; reflexivity.
    - intros mx my mz mxy mxyz Hxy Hxyz.
      unfold join, bool_join in *; subst mxy mxyz.
      exists (orb my mz); split.
      + reflexivity.
      + destruct mx, my, mz; reflexivity.
  Qed.
  Program Definition bool_unit : @SeparationAlgebraUnit bool bool_join bool_SA :=
    {| ue := false |}.
  Next Obligation. unfold join, bool_join; destruct n; reflexivity. Qed.
  Next Obligation.
    intros n n' H; unfold join, bool_join in H; destruct n; simpl in *; congruence.
  Qed.

  Definition empty_lts (A : Type) : @LTS Sig.Plus.unit :=
    {| State := A; Step := fun _ _ _ => False; Error := fun _ _ => False |}.

  Definition NatLTS := empty_lts nat.
  Definition BoolLTS := empty_lts bool.

  #[local] Existing Instance nat_join.
  #[local] Existing Instance nat_SA.
  #[local] Existing Instance nat_unit.
  #[local] Existing Instance bool_join.
  #[local] Existing Instance bool_SA.
  #[local] Existing Instance bool_unit.

  Definition NestedTensorLTS := tens_lts NatLTS (tens_lts BoolLTS NatLTS).
  Definition NestedTensorJoin : Join (State NestedTensorLTS) :=
    ltac:(typeclasses eauto).
  Definition NestedTensorSA : @SeparationAlgebra _ NestedTensorJoin :=
    ltac:(typeclasses eauto).
  Definition NestedTensorUnit :
    @SeparationAlgebraUnit _ NestedTensorJoin NestedTensorSA :=
    ltac:(typeclasses eauto).

  (** Both orderings coexist without installing either proof-state join as a
      global instance. *)
  Definition NatBoolProofJoin :
    Join (@SetPossState.ProofState _ _ NatLTS BoolLTS) :=
    @SetPossState.PSS_Join _ _ NatLTS BoolLTS nat_join bool_join.
  Definition BoolNatProofJoin :
    Join (@SetPossState.ProofState _ _ BoolLTS NatLTS) :=
    @SetPossState.PSS_Join _ _ BoolLTS NatLTS bool_join nat_join.

  Definition NatBoolProofSA :
    @SeparationAlgebra _ NatBoolProofJoin :=
    @SetPossState.PSS_SA _ _ NatLTS BoolLTS
      nat_join nat_SA bool_join bool_SA.
  Definition BoolNatProofSA :
    @SeparationAlgebra _ BoolNatProofJoin :=
    @SetPossState.PSS_SA _ _ BoolLTS NatLTS
      bool_join bool_SA nat_join nat_SA.
End CustomStateSA.
