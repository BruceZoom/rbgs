Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.

Require Import examples.Common.ThreadDomain.


(** The one-shot write-snapshot object (docs/paper/main copy.pdf,
    Section 2).

    [write_snapshot v] records [v] and returns the set of all values
    recorded so far.  The paper's concurrent specification [ν_write_snapshot]
    is interval sequential: the invocation of thread [α] adds [v] to the
    state ([snpstate]) at once, provided [α] has not invoked before, and the
    response may be taken at any later point and returns the state at that
    point.  Because a response only reads the state, the object is not an
    atomic ([VAE]) object; the LTS is written directly, as for the
    exchanger and the partial-order queue.

    State: the map from each thread to the value it has written.  Its
    range is the paper's [snpstate]; its domain is the set of threads that
    have invoked.

    One-shot clause: the paper has no trace with two invocations by one
    thread ([α ∉ s']).  Here a second invocation by the same thread is an
    error ([error_ws_double_inv]), the framework's convention for client
    misuse; this lets the implementation write a plain register without
    checking it.

    Result: the paper returns an element of [2^Val].  Here the result type
    is [list A], and the response accepts any list whose members are
    exactly the values in the state ([ws_snapshot]); order and
    multiplicity are not constrained.

    Domain: the implementation indexes the register family with the actor,
    which is a family error for an actor outside the thread domain [D];
    the specification raises the same error at the invocation (as
    [TSStackSpec] does). *)
Module WriteSnapshotSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import TPSimulationSet.TPSimulation.

  Section Sig.
    Context {A : Type}.

    Variant EWriteSnapshot_op :=
    | write_snapshot (v : A).
    Arguments EWriteSnapshot_op : clear implicits.

    Definition EWriteSnapshot_ar (op : EWriteSnapshot_op) : Type :=
      match op with
      | write_snapshot _ => list A
      end.

    Canonical Structure EWriteSnapshot :=
    {|
      Sig.op := EWriteSnapshot_op;
      Sig.ar := EWriteSnapshot_ar
    |}.

    (** The value written by each thread so far. *)
    Definition WSState : Type := TMap.t A.

    Definition ws_initial : WSState := TMap.empty A.

    (** [snpstate]: the values written so far. *)
    Definition ws_value (s : WSState) (x : A) : Prop :=
      exists t, TMap.find t s = Some x.

    (** [l] lists exactly the values written so far. *)
    Definition ws_snapshot (s : WSState) (l : list A) : Prop :=
      forall x, In x l <-> ws_value s x.

    Variant StepWriteSnapshot :
        @ThreadEvent EWriteSnapshot -> WSState -> WSState -> Prop :=
    | step_ws_inv t v s e :
        e = {| te_tid := t; te_ev := InvEv (write_snapshot v) |} ->
        TMap.find t s = None ->
        StepWriteSnapshot e s (TMap.add t v s)
    | step_ws_res t v s l e :
        e = {| te_tid := t; te_ev := ResEv (write_snapshot v) l |} ->
        ws_snapshot s l ->
        StepWriteSnapshot e s s.

  End Sig.

  Arguments EWriteSnapshot_op : clear implicits.
  Arguments WSState : clear implicits.

  Section Spec.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Variant ErrorWriteSnapshot :
        @ThreadEvent (@EWriteSnapshot A) -> WSState A -> Prop :=
    | error_ws_actor_outside actor op s e :
        ~ ThreadDomain.contains D actor ->
        e = {| te_tid := actor; te_ev := InvEv op |} ->
        ErrorWriteSnapshot e s
    | error_ws_double_inv actor op s e :
        TMap.find actor s <> None ->
        e = {| te_tid := actor; te_ev := InvEv op |} ->
        ErrorWriteSnapshot e s.

    Definition VWriteSnapshot : @LTS (@EWriteSnapshot A) :=
    {|
      State := WSState A;
      Step := StepWriteSnapshot;
      Error := ErrorWriteSnapshot
    |}.

  End Spec.

  Module WriteSnapshotLayer.
    Section Layer.
      Context {A : Type}.
      Context (D : ThreadDomain.t).

      Definition L : layer_interface :=
        {|
          li_sig := @EWriteSnapshot A;
          li_lts := @VWriteSnapshot A D;
          li_init := @ws_initial A
        |}.
    End Layer.
  End WriteSnapshotLayer.

End WriteSnapshotSpec.
