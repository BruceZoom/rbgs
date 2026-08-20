Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import examples.Common.AtomicLTS.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulation.


Module TimestampSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  Import TPSimulation.

  (* Interval timestamps used by the timestamped stack.  [TSTop] is the
     initial, not-yet-stamped value stored in a newly allocated node. *)
  Variant TS : Type :=
  | TSTop
  | TSInterval (lower upper : nat).

  Variant ETimestamp_op :=
  | newTS.
  Arguments ETimestamp_op : clear implicits.

  Definition ETimestamp_ar (m : ETimestamp_op) : Type :=
    match m with
    | newTS => TS
    end.

  Canonical Structure ETimestamp :=
  {|
    Sig.op := ETimestamp_op;
    Sig.ar := ETimestamp_ar
  |}.

  (*
     Timestamp LTS template.

     Add the timestamp generator's abstract state, invocation/response
     transitions for [newTS], its error relation, and its layer interface
     here when the concrete timestamp algorithm is introduced.
  *)

End TimestampSpec.
