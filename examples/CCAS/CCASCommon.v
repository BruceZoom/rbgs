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
Require Import examples.Registers.RegSpec.
Require Import examples.CCAS.CCASSpec.
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

