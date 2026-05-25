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

Module AtomicLTS.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  
  Section AtomicLTS.
    Context {E : Op.t}.
    Context {StateE : Type}.
    Context (StepE : @ThreadEvent E -> StateE -> StateE -> Prop).

    Variant AState : Type :=
    | Idle (s : StateE) | Pending (s : StateE) (t : tid) (op : Sig.op E).

    Definition state (s : AState) : StateE := 
      match s with
      | Idle s => s
      | Pending s _ _ => s
      end.

    Variant AStep : ThreadEvent -> AState -> AState -> Prop :=
    | step_inv t op s1 s2
        (Hstep : StepE {| te_tid := t; te_ev := InvEv op |} s1 s2):
        AStep {| te_tid := t; te_ev := InvEv op |} (Idle s1) (Pending s2 t op)
    | step_res t op r s1 s2
        (Hstep : StepE {| te_tid := t; te_ev := ResEv op r |} s1 s2):
        AStep {| te_tid := t; te_ev := ResEv op r |} (Pending s1 t op) (Idle s2).

    (* atomic error *)
    Variant AError (error : @ThreadEvent E -> StateE -> Prop) : ThreadEvent -> AState -> Prop :=
    | aerror ev s
        (Herror : error ev s):
        AError error ev (Idle s).

    Definition VAE (error : ThreadEvent -> AState -> Prop) : @LTS E := {|
      State := AState;
      Step := AStep;
      Error := error;
    |}.
    
  End AtomicLTS.
  
End AtomicLTS.


