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

Module RegSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  
  Variant EReg_op {A} :=
  | get
  | set (v : A).
  Arguments EReg_op : clear implicits.

  Definition EReg_ar {A} (m : EReg_op A) :=
    match m with
      | get => A
      | set _ => unit
    end.
  
  Canonical Structure EReg A :=
  {|
    Sig.op := EReg_op A;
    Sig.ar := EReg_ar
  |}.

  Variant StepReg {A} : @ThreadEvent (EReg A) -> A -> A -> Prop :=
  | step_get_inv t v : StepReg {| te_tid := t; te_ev := InvEv get |} v v
  | step_get_res t v : StepReg {| te_tid := t; te_ev := ResEv get v |} v v
  | step_set_inv t v w : StepReg {| te_tid := t; te_ev := InvEv (set w) |} v v
  | step_set_res t v w: StepReg {| te_tid := t; te_ev := ResEv (set w) tt |} v w
  .

  Variant ErrorReg {A} : @ThreadEvent (EReg A) -> @AState (EReg A) A -> Prop :=
  | error_set_racy t t' v u w :
      (* non-sequetial-consisten steps stuck *)
      t <> t' ->
      ErrorReg {| te_tid := t; te_ev := InvEv (set w) |} (Pending v t' (set u)).
  
  Definition VReg {A} : @LTS (EReg A) := VAE StepReg ErrorReg.

End RegSpec.

(* race-free register *)
Module Reg'Spec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  
  Variant EReg_op {A} :=
  | get
  | set (v : A).
  Arguments EReg_op : clear implicits.

  Definition EReg_ar {A} (m : EReg_op A) :=
    match m with
      | get => A
      | set _ => unit
    end.
  
  Canonical Structure EReg A :=
  {|
    Sig.op := EReg_op A;
    Sig.ar := EReg_ar
  |}.

  Variant StepReg {A} : @ThreadEvent (EReg A) -> A -> A -> Prop :=
  | step_get_inv t v : StepReg {| te_tid := t; te_ev := InvEv get |} v v
  | step_get_res t v : StepReg {| te_tid := t; te_ev := ResEv get v |} v v
  | step_set_inv t v w : StepReg {| te_tid := t; te_ev := InvEv (set w) |} v v
  | step_set_res t v w: StepReg {| te_tid := t; te_ev := ResEv (set w) tt |} v w
  .

  Definition VReg {A} : @LTS (EReg A) := VAE StepReg NoError.

End Reg'Spec.

