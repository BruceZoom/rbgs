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

Module CASRegSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  Variant ECASReg_op {A} :=
  | get
  | set (v : A)
  | cas (v w : A).
  Arguments ECASReg_op : clear implicits.

  Definition ECASReg_ar {A} (m : ECASReg_op A) : Type :=
    match m with
    | get => A
    | set _ => unit
    | cas _ _ => bool
    end.
  
  Canonical Structure ECASReg A :=
  {|
    Sig.op := ECASReg_op A;
    Sig.ar := ECASReg_ar
  |}.

  Variant StepCASReg {A} : @ThreadEvent (ECASReg A) -> A -> A -> Prop :=
  | step_get_inv t v : StepCASReg {| te_tid := t; te_ev := InvEv get |} v v
  | step_get_res t v : StepCASReg {| te_tid := t; te_ev := ResEv get v |} v v
  | step_set_inv t v w : StepCASReg {| te_tid := t; te_ev := InvEv (set w) |} v v
  | step_set_res t v w: StepCASReg {| te_tid := t; te_ev := ResEv (set w) tt |} v w
  | step_cas_inv t u v w:
      StepCASReg {| te_tid := t; te_ev := InvEv (cas v w) |} u u
  | step_cas_res_succ t v w e:
      e = {| te_tid := t; te_ev := ResEv (cas v w) true |} ->
      StepCASReg e v w
  | step_cas_res_fail t u v w e:
      e = {| te_tid := t; te_ev := ResEv (cas v w) false |} ->
      u <> v ->
      StepCASReg e u u
  .

  Variant ErrorCASReg {A} : @ThreadEvent (ECASReg A) -> AState -> Prop :=
  | error_set_racy t t' (v u w : A) e:
      t <> t' ->
      e = {| te_tid := t; te_ev := InvEv (set u) |} ->
      ErrorCASReg e (Pending v t' (set w)).

  Definition VCASReg {A} : @LTS (ECASReg A) := VAE StepCASReg ErrorCASReg.
  
  End CASRegSpec.


Module CAS'Spec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  Variant ECAS'_op {A} :=
  | get
  | cas (v w : A).
  Arguments ECAS'_op : clear implicits.

  Definition ECAS'_ar {A} (m : ECAS'_op A) : Type :=
    match m with
    | get => A
    | cas _ _ => A
    end.
  
  Canonical Structure ECAS' A :=
  {|
    Sig.op := ECAS'_op A;
    Sig.ar := ECAS'_ar
  |}.

  Variant StepCAS' {A} : @ThreadEvent (ECAS' A) -> A -> A -> Prop :=
  | step_get_inv t v : StepCAS' {| te_tid := t; te_ev := InvEv get |} v v
  | step_get_res t v : StepCAS' {| te_tid := t; te_ev := ResEv get v |} v v
  | step_cas_inv t u v w:
      StepCAS' {| te_tid := t; te_ev := InvEv (cas v w) |} u u
  | step_cas_res_succ t v w b e:
      b = true ->
      e = {| te_tid := t; te_ev := ResEv (cas v w) v |} ->
      StepCAS' e v w
  | step_cas_res_fail t u v w b e:
      e = {| te_tid := t; te_ev := ResEv (cas v w) u |} -> 
      b = false ->
      u <> v ->
      StepCAS' e u u
  .

  Definition VCAS' {A} : @LTS (ECAS' A) := VAE StepCAS' NoError.
  
End CAS'Spec.
