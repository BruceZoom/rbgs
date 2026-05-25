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

Module TryStackSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  
  Variant ETryStack_op {A} :=
  | push (v : A)
  | pop.
  Arguments ETryStack_op : clear implicits.

  Variant TryResult {A} : Type :=
  | OK (v : A)
  | FAIL.
  Arguments TryResult : clear implicits.

  Definition ETryStack_ar {A} (m : ETryStack_op A) : Type :=
    match m with
      | push _ => TryResult unit
      | pop => TryResult (option A)
    end.
  
  Canonical Structure ETryStack A :=
  {|
    Sig.op := ETryStack_op A;
    Sig.ar := ETryStack_ar
  |}.

  Variant StepTryStack {A} : @ThreadEvent (ETryStack A) -> list A -> list A -> Prop :=
  | step_push_inv t stk v e:
      e = {| te_tid := t; te_ev := InvEv (push v) |} ->
      StepTryStack e stk stk
  | step_push_ok t stk v e : 
      e = {| te_tid := t; te_ev := ResEv (push v) (OK tt) |} ->
      StepTryStack e stk (v :: stk)
  | step_push_fail t stk v e :
      e = {| te_tid := t; te_ev := ResEv (push v) FAIL |} ->
      StepTryStack e stk stk

  | step_pop_inv t stk e:
      e = {| te_tid := t; te_ev := InvEv pop |} ->
      StepTryStack e stk stk
  | step_pop_emp t e:
      e = {| te_tid := t; te_ev := ResEv pop (OK None) |} ->
      StepTryStack e nil nil
  | step_pop_ok t v stk e :
      e = {| te_tid := t; te_ev := ResEv pop (OK (Some v)) |} ->
      StepTryStack e (v :: stk) stk
  | step_pop_fail t stk e:
      e = {| te_tid := t; te_ev := ResEv pop FAIL |} ->
      StepTryStack e stk stk.
  
  Definition VTryStack {A} : @LTS (ETryStack A) := VAE StepTryStack NoError.

End TryStackSpec.



Module StackSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  
  Variant EStack_op {A} :=
  | push (v : A)
  | pop.
  Arguments EStack_op : clear implicits.

  Definition EStack_ar {A} (m : EStack_op A) : Type :=
    match m with
      | push _ => unit
      | pop => option A
    end.
  
  Canonical Structure EStack A :=
  {|
    Sig.op := EStack_op A;
    Sig.ar := EStack_ar
  |}.

  Variant StepStack {A} : @ThreadEvent (EStack A) -> list A -> list A -> Prop :=
  | step_push_inv t stk v : StepStack {| te_tid := t; te_ev := InvEv (push v) |} stk stk
  | step_push_res t stk v : StepStack {| te_tid := t; te_ev := ResEv (push v) tt |} stk (v :: stk)

  | step_pop_inv t stk : StepStack {| te_tid := t; te_ev := InvEv pop |} stk stk
  | step_pop_emp t : StepStack {| te_tid := t; te_ev := ResEv pop None |} nil nil
  | step_pop_res t v stk : StepStack {| te_tid := t; te_ev := ResEv pop (Some v) |} (v :: stk) stk.
  
  Definition VStack {A} : @LTS (EStack A) := VAE StepStack NoError.

End StackSpec.


