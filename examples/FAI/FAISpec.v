Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.

(* IMPORTANT *)
(*    
    It turns out Coq is more stupid than this. Doing the following cannot solve all similar problems.

    When a single thread event could have multiple transitions,
    must defined transitions in the following way:
    Variant Step : ... :=
    | rule_name params e:
        e = {| te_tid := t; te_ev := ev |} ->
        Step e s1 s2
    ...
    The event should not appear in the conclusion,
    otherwise inversion on the relation will not work.
    Doing so also make sure it will work with the current automation.
*)

Require Import examples.Common.AtomicLTS.

Module FAISpec.
  Import LinCCALBase.
  Import LTSSpec.
  Import AtomicLTS.

  Variant EFAI_op :=
    | fai.

  Canonical Structure EFAI :=
  {|
    Sig.op := EFAI_op;
    Sig.ar _ := nat;
  |}.

  Definition SFAI : Type := nat.
  
  Variant StepFAI : ThreadEvent -> SFAI -> SFAI -> Prop :=
  | step_fai_inv t n : StepFAI {| te_tid := t; te_ev := InvEv fai |} n n
  | step_fai_res t n : StepFAI {| te_tid := t; te_ev := ResEv fai n |} n (S n)
  .

  Definition VFAI : @LTS EFAI := VAE StepFAI NoError.
  
End FAISpec.

