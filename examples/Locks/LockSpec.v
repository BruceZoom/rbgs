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

Module LockSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  
  Variant ELock_op :=
    | acq
    | rel.

  Canonical Structure ELock :=
  {|
    Sig.op := ELock_op;
    Sig.ar _ := unit;
  |}.

  Variant SLock : Type :=
  | Locked (t : tid) | Unlocked.
  
  Variant StepLock : ThreadEvent -> SLock -> SLock -> Prop :=
  | step_acq_inv t : StepLock {| te_tid := t; te_ev := InvEv acq |} Unlocked Unlocked
  | step_acq_res t : StepLock {| te_tid := t; te_ev := ResEv acq tt |} Unlocked (Locked t)
  | step_rel_inv t : StepLock {| te_tid := t; te_ev := InvEv rel |} (Locked t) (Locked t)
  | step_rel_res t : StepLock {| te_tid := t; te_ev := ResEv rel tt |} (Locked t) Unlocked
  .

  Variant ErrorLock : ThreadEvent -> SLock -> Prop :=
  | error_rel_rel t : ErrorLock {| te_tid := t; te_ev := InvEv rel |} Unlocked
  | error_rel_race t t' : t <> t' ->
      ErrorLock {| te_tid := t; te_ev := InvEv rel |} (Locked t').
  (* | error_acq_acq t : ErrorLock {| te_tid := t; te_ev := InvEv acq |} Locked. *)

  Definition VLock : @LTS ELock := VAE StepLock (AError ErrorLock).

End LockSpec.

