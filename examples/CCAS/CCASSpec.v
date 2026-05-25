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

Module CCASSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  Variant ECCAS_op {A} :=
  | setFlag (b : bool)
  | cas (o n : A).
  Arguments ECCAS_op : clear implicits.

  Definition ECCAS_ar {A} (m : ECCAS_op A) : Type :=
    match m with
    | setFlag _ => unit
    | cas _ _ => A
    end.
  
  Canonical Structure ECCAS A :=
  {|
    Sig.op := ECCAS_op A;
    Sig.ar := ECCAS_ar
  |}.

  Definition CCASState (A : Type) : Type := A * bool.

  Variant StepCCAS {A} : @ThreadEvent (ECCAS A) -> CCASState A -> CCASState A -> Prop :=
  | step_setFlag_inv t b s:
    StepCCAS {| te_tid := t; te_ev := InvEv (setFlag b) |} s s
  | step_setFlag_res t b b' (v : A) e:
    e = {| te_tid := t; te_ev := ResEv (setFlag b) tt |} ->
    StepCCAS e (v, b') (v, b)
  | step_cas_inv t o n s:
      StepCCAS {| te_tid := t; te_ev := InvEv (cas o n) |} s s
  | step_cas_res_succ t o n b:
      StepCCAS {| te_tid := t; te_ev := ResEv (cas o n) o |} (o, b) (if b then n else o, b)
  | step_cas_res_fail t v o n b e:
      e = {| te_tid := t; te_ev := ResEv (cas o n) v |} ->
      v <> o ->
      StepCCAS e (v, b) (v, b)
  .
  
  Variant ErrorCCAS {T} : @ThreadEvent (ECCAS T) -> (@AState (ECCAS T) (CCASState T)) -> Prop :=
  | error_set_racy t t' (s : CCASState T) b b':
      t <> t' ->
      ErrorCCAS {| te_tid := t; te_ev := InvEv (setFlag b) |} (Pending s t' (setFlag b')).

  (* MARK: for simplicity, use race-free version *)
  Definition VCCAS {A} : @LTS (ECCAS A) := VAE StepCCAS NoError.
  

End CCASSpec.


