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

Module CASTaskSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  Section CASTaskSpec.
    Context {A : Type}.

    Variant CASTask : Type := CTask (t : tid) (o n : A) (i : nat).

    Variant ECASTask_op :=
    | allocTask (o n : A)
    | tryPlaceTask (o n : A) (i : nat)
    | tryResolveTask (tsk : CASTask) (v : A).

    Definition ECASTask_ar (m : ECASTask_op) : Type :=
      match m with
      | allocTask _ _ => nat
      | tryPlaceTask _ _ _ => CASTask + A
      | tryResolveTask _ _ => unit
      end.
    
    Canonical Structure ECASTask :=
    {|
      Sig.op := ECASTask_op;
      Sig.ar := ECASTask_ar
    |}.

    Variant ticket_state : Type :=
      Inactive | Owned (t : tid) | Expired.

    Record CASTaskState : Type := cts {
      current : CASTask + A;
      ticket : nat;
      owner : nat -> ticket_state;
      (* ired : list nat; *)
    }.


    Definition owner_upd (o : nat -> ticket_state) i t : nat -> ticket_state :=
      fun i' => if (i =? i')%nat then t else (o i').

    Variant StepCASTask : @ThreadEvent ECASTask -> CASTaskState -> CASTaskState -> Prop :=
    (* alloc *)
    | step_allocTask_inv cid o n s:
      StepCASTask {| te_tid := cid; te_ev := InvEv (allocTask o n) |} s s
    | step_allocTask_res cid o n c tk  owner e:
      e = {| te_tid := cid; te_ev := ResEv (allocTask o n) tk |} ->
      StepCASTask e
                  (* increase ticket *)
                  (cts c tk owner ) (cts c (S tk) (owner_upd owner tk (Owned cid)) )
    (* try place *)
    | step_tryPlaceTask_inv cid o n i s:
      StepCASTask {| te_tid := cid; te_ev := InvEv (tryPlaceTask o n i) |} s s
    (* succeed if no task placed *)
    | step_tryPlaceTask_succ cid o n i tk owner e:
      e = {| te_tid := cid; te_ev := ResEv (tryPlaceTask o n i) (inr o) |} ->
      StepCASTask e
                  (* replace with the task *)
                  (cts (inr o) tk owner ) (cts (inl (CTask cid o n i)) tk owner )
    (* blocked if have task placed *)
    | step_tryPlaceTask_block cid o n i tk tsk owner e:
      e = {| te_tid := cid; te_ev := ResEv (tryPlaceTask o n i) (inl tsk) |} ->
      StepCASTask e
                  (* do nothing *)
                  (cts (inl tsk) tk owner ) (cts (inl tsk) tk owner )
    (* fail if o[ld] value does not match *)
    | step_tryPlaceTask_fail cid v o n i tk owner e:
      e = {| te_tid := cid; te_ev := ResEv (tryPlaceTask o n i) (inr v) |} ->
      v <> o ->
      StepCASTask e
                  (* replace with the task *)
                  (cts (inr v) tk owner ) (cts (inr v) tk owner )
    (* try resolve *)
    | step_tryResolveTask_inv cid tsk v s:
      StepCASTask {| te_tid := cid; te_ev := InvEv (tryResolveTask tsk v) |} s s
    | step_tryResolveTask_succ cid v t o n i tk owner e:
      e = {| te_tid := cid; te_ev := ResEv (tryResolveTask (CTask t o n i) v) tt |} ->
      StepCASTask e
                  (* resolve to the given value *)
                  (* ticket ires *)
                  (cts (inl (CTask t o n i)) tk owner) (cts (inr v) tk (owner_upd owner i Expired))
    | step_tryResolveTask_fail cid c tsk v tk owner e:
      e = {| te_tid := cid; te_ev := ResEv (tryResolveTask tsk v) tt |} ->
      c <> (inl tsk) ->
      StepCASTask e
                  (* do nothing *)
                  (cts c tk owner) (cts c tk owner)
    .

    Variant ErrorCASTask : @ThreadEvent ECASTask -> CASTaskState  -> Prop :=
    | error_inactive_task e cid t o n i v s tk owner:
        e = {| te_tid := cid; te_ev := InvEv (tryResolveTask (CTask t o n i) v) |} ->
        owner i = Inactive ->
        ErrorCASTask e (cts s tk owner).

    Definition VCASTask : @LTS ECASTask := @VAE _ CASTaskState StepCASTask (AError ErrorCASTask).
    
  End CASTaskSpec.

  Arguments CASTask : clear implicits.
  Arguments ECASTask : clear implicits.
End CASTaskSpec.


