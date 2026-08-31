Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.AtomicLTS.
Require Import examples.TSStack.TimestampSpec.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.


Module NodeMemSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  Import TPSimulationSet.TPSimulation.
  Import TimestampSpec.

  Section Spec.
    Context {A : Type}.

  Definition Node : Type := A * TS * bool * Ptr.

  Variant ENodeMem_op :=
  | nmalloc (v : A) (next : Ptr)
  | nmsetTS (l : Addr) (t : TS)
  | nmget (l : Addr)
  | nmtryTake (l : Addr).
  Arguments ENodeMem_op : clear implicits.

  Definition ENodeMem_ar (m : ENodeMem_op) : Type :=
    match m with
    | nmalloc _ _ => Addr
    | nmsetTS _ _ => unit
    | nmget _ => Node
    | nmtryTake _ => bool
    end.

  Canonical Structure ENodeMem :=
  {|
    Sig.op := ENodeMem_op;
    Sig.ar := ENodeMem_ar
  |}.

  Definition NodeMemState := @Heap Node.

  Section Semantics.
    Variant StepNodeMem :
      @ThreadEvent ENodeMem -> NodeMemState -> NodeMemState -> Prop :=
    (* allocation *)
    | step_malloc_inv t h v next e :
        e = {| te_tid := t; te_ev := InvEv (nmalloc v next) |} ->
        StepNodeMem e h h
    | step_malloc_res t h l v next e :
        e = {| te_tid := t; te_ev := ResEv (nmalloc v next) l |} ->
        h l = None ->
        StepNodeMem e h
          (heap_update l (v, TSTop, false, next) h)

    (* timestamp update *)
    | step_setTS_inv t h l ts e :
        e = {| te_tid := t; te_ev := InvEv (nmsetTS l ts) |} ->
        h l <> None ->
        StepNodeMem e h h
    | step_setTS_res t h l v old_ts taken next ts e :
        e = {| te_tid := t; te_ev := ResEv (nmsetTS l ts) tt |} ->
        h l = Some (v, old_ts, taken, next) ->
        StepNodeMem e h (heap_update l (v, match old_ts with TSTop => ts | _ => old_ts end, taken, next) h)

    (* read *)
    | step_get_inv t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmget l) |} ->
        h l <> None ->
        StepNodeMem e h h
    | step_get_res t h l node e :
        e = {| te_tid := t; te_ev := ResEv (nmget l) node |} ->
        h l = Some node ->
        StepNodeMem e h h

    (* atomic test-and-take *)
    | step_tryTake_inv t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmtryTake l) |} ->
        h l <> None ->
        StepNodeMem e h h
    | step_tryTake_res_succ t h l v ts next e :
        e = {| te_tid := t; te_ev := ResEv (nmtryTake l) true |} ->
        h l = Some (v, ts, false, next) ->
        StepNodeMem e h (heap_update l (v, ts, true, next) h)
    | step_tryTake_res_fail t h l v ts next e :
        e = {| te_tid := t; te_ev := ResEv (nmtryTake l) false |} ->
        h l = Some (v, ts, true, next) ->
        StepNodeMem e h h.

    Variant ErrorNodeMem :
      @ThreadEvent ENodeMem -> (@AState ENodeMem NodeMemState) -> Prop :=
    | error_setTS_undefined t h l ts e :
        e = {| te_tid := t; te_ev := InvEv (nmsetTS l ts) |} ->
        h l = None ->
        ErrorNodeMem e (Idle h)
    | error_get_undefined t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmget l) |} ->
        h l = None ->
        ErrorNodeMem e (Idle h)
    | error_tryTake_undefined t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmtryTake l) |} ->
        h l = None ->
        ErrorNodeMem e (Idle h)
    | error_setTS_racy t t' h l l' ts ts' e :
        t <> t' ->
        l = l' ->
        e = {| te_tid := t; te_ev := InvEv (nmsetTS l ts) |} ->
        ErrorNodeMem e (Pending h t' (nmsetTS l' ts')).

    Definition VNodeMem : @LTS ENodeMem :=
      VAE (StepNodeMem) ErrorNodeMem.
  End Semantics.

  End Spec.

  Module NodeMemLayer.
    Section Impl.
      Context {A : Type}.

      Definition L : layer_interface :=
      {|
        li_sig := @ENodeMem A;
        li_lts := @VNodeMem A;
        li_init := Idle empty_heap;
      |}.
    End Impl.
  End NodeMemLayer.

End NodeMemSpec.
