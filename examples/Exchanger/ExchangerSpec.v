Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.


Module ExchSpec.
  Import LTSSpec.
  Import LinCCALBase.

  Variant EExch_op {A} :=
  | exch (v : A).
  Arguments EExch_op : clear implicits.

  Definition EExch_ar {A} (m : EExch_op A) : Type :=
    match m with
    | exch v => option A
    end.
  
  Canonical Structure EExch A :=
  {|
    Sig.op := EExch_op A;
    Sig.ar := EExch_ar
  |}.

  Variant EExchState {A : Type} : Type := 
  | ExSOffered (t1 : tid) (v1 : A)
  | ExSPaired (t1 : tid) (v1 : A) (t2 : tid) (v2 : A)
  | ExSAccepted (t1 : tid) (v1 : A) (t2 : tid) (v2 : A)
  | ExSIdle.

  Variant StepExch {A} : @ThreadEvent (EExch A) -> EExchState -> EExchState -> Prop :=
  | step_exch_offer t1 v1 e:
    e = {| te_tid := t1; te_ev := InvEv (exch v1) |} ->
    StepExch e ExSIdle (ExSOffered t1 v1)
  | step_exch_revoke t1 v1 e:
    e = {| te_tid := t1; te_ev := ResEv (exch v1) None |} ->
    StepExch e (ExSOffered t1 v1) ExSIdle
  | step_exch_pair t1 v1 t2 v2 e:
    e = {| te_tid := t2; te_ev := InvEv (exch v2) |} ->
    StepExch e (ExSOffered t1 v1) (ExSPaired t1 v1 t2 v2)
  | step_exch_accept t1 v1 t2 v2 e:
    e = {| te_tid := t1; te_ev := ResEv (exch v1) (Some v2) |} ->
    StepExch e (ExSPaired t1 v1 t2 v2) (ExSAccepted t1 v1 t2 v2)
  | step_exch_finish t1 v1 t2 v2 e:
    e = {| te_tid := t2; te_ev := ResEv (exch v2) (Some v1) |} ->
    StepExch e (ExSAccepted t1 v1 t2 v2) ExSIdle
  .
  
  Definition VExch {A} : @LTS (EExch A) := {|
    State := EExchState;
    Step := StepExch;
    Error := NoError
  |}.

End ExchSpec.


