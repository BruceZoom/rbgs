Require Import Coq.PArith.PArith.
Require Import PeanoNat.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.

Require Import examples.Common.AtomicLTS.
Require Import examples.Common.Heap.
Require Import examples.TSStack.TimestampSpec.


(** Node memory for the unlinking variant of the SPList.

    This is [NodeMemSpec] plus one operation, [nmcasNext], a compare-and-swap
    on the successor pointer of a published node.  The unlinking SPList uses
    it to make a taken node skip the taken nodes that follow it.

    The original algorithm uses a plain store here.  Only the thread whose
    [nmtryTake] succeeded on a node ever rewrites that node's successor, so
    the store is race free; but a plain store would carry a racy-write
    error in this specification (as [nmsetTS] does), and discharging it in
    the SPList proof requires tracking which thread took each node.  A CAS
    from the value the taker just read has the same effect, never fails
    in practice, and has no racy error, so the successor field needs no
    ownership argument at all. *)
Module NodeMemUnlinkSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  Import TPSimulationSet.TPSimulation.
  Import TimestampSpec.

  Section Spec.
    Context {A : Type}.

  (** Same layout as [NodeMemSpec.Node]: value, timestamp, taken, next. *)
  Definition Node : Type := A * TS * bool * Ptr.

  Variant ENodeMemU_op :=
  | nmalloc (v : A) (next : Ptr)
  | nmsetTS (l : Addr) (t : TS)
  | nmcasNext (l : Addr) (old new : Ptr)
  | nmgetValue (l : Addr)
  | nmgetTS (l : Addr)
  | nmgetTaken (l : Addr)
  | nmgetNext (l : Addr)
  | nmtryTake (l : Addr).
  Arguments ENodeMemU_op : clear implicits.

  Definition ENodeMemU_ar (m : ENodeMemU_op) : Type :=
    match m with
    | nmalloc _ _ => Addr
    | nmsetTS _ _ => unit
    | nmcasNext _ _ _ => bool
    | nmgetValue _ => A
    | nmgetTS _ => TS
    | nmgetTaken _ => bool
    | nmgetNext _ => Ptr
    | nmtryTake _ => bool
    end.

  Canonical Structure ENodeMemU :=
  {|
    Sig.op := ENodeMemU_op;
    Sig.ar := ENodeMemU_ar
  |}.

  Definition NodeMemState := @Heap Node.

  Section Semantics.
    Variant StepNodeMem :
      @ThreadEvent ENodeMemU -> NodeMemState -> NodeMemState -> Prop :=
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
        StepNodeMem e h
          (heap_update l
             (v, match old_ts with TSTop => ts | _ => old_ts end, taken, next)
             h)

    (* successor compare-and-swap (unlinking) *)
    | step_casNext_inv t h l old new e :
        e = {| te_tid := t; te_ev := InvEv (nmcasNext l old new) |} ->
        h l <> None ->
        StepNodeMem e h h
    | step_casNext_res_succ t h l v ts taken old new e :
        e = {| te_tid := t; te_ev := ResEv (nmcasNext l old new) true |} ->
        h l = Some (v, ts, taken, old) ->
        StepNodeMem e h (heap_update l (v, ts, taken, new) h)
    | step_casNext_res_fail t h l v ts taken cur old new e :
        e = {| te_tid := t; te_ev := ResEv (nmcasNext l old new) false |} ->
        h l = Some (v, ts, taken, cur) ->
        cur <> old ->
        StepNodeMem e h h

    (* per-field reads.  Each field is read on its own; a client that
       needs a consistent view of several fields must argue from the
       monotonicity of [ts] (set once from [TSTop]) and [taken]
       (flipped once from [false]).  The successor is no longer
       immutable: a client must argue from the structure of the
       successor rewrites it performs. *)
    | step_getValue_inv t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetValue l) |} ->
        h l <> None ->
        StepNodeMem e h h
    | step_getValue_res t h l v ts taken next e :
        e = {| te_tid := t; te_ev := ResEv (nmgetValue l) v |} ->
        h l = Some (v, ts, taken, next) ->
        StepNodeMem e h h
    | step_getTS_inv t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetTS l) |} ->
        h l <> None ->
        StepNodeMem e h h
    | step_getTS_res t h l v ts taken next e :
        e = {| te_tid := t; te_ev := ResEv (nmgetTS l) ts |} ->
        h l = Some (v, ts, taken, next) ->
        StepNodeMem e h h
    | step_getTaken_inv t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetTaken l) |} ->
        h l <> None ->
        StepNodeMem e h h
    | step_getTaken_res t h l v ts taken next e :
        e = {| te_tid := t; te_ev := ResEv (nmgetTaken l) taken |} ->
        h l = Some (v, ts, taken, next) ->
        StepNodeMem e h h
    | step_getNext_inv t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetNext l) |} ->
        h l <> None ->
        StepNodeMem e h h
    | step_getNext_res t h l v ts taken next e :
        e = {| te_tid := t; te_ev := ResEv (nmgetNext l) next |} ->
        h l = Some (v, ts, taken, next) ->
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
      @ThreadEvent ENodeMemU -> (@AState ENodeMemU NodeMemState) -> Prop :=
    | error_setTS_undefined t h l ts e :
        e = {| te_tid := t; te_ev := InvEv (nmsetTS l ts) |} ->
        h l = None ->
        ErrorNodeMem e (Idle h)
    | error_casNext_undefined t h l old new e :
        e = {| te_tid := t; te_ev := InvEv (nmcasNext l old new) |} ->
        h l = None ->
        ErrorNodeMem e (Idle h)
    | error_getValue_undefined t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetValue l) |} ->
        h l = None ->
        ErrorNodeMem e (Idle h)
    | error_getTS_undefined t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetTS l) |} ->
        h l = None ->
        ErrorNodeMem e (Idle h)
    | error_getTaken_undefined t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetTaken l) |} ->
        h l = None ->
        ErrorNodeMem e (Idle h)
    | error_getNext_undefined t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetNext l) |} ->
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

    Definition VNodeMemU : @LTS ENodeMemU :=
      VAE (StepNodeMem) ErrorNodeMem.
  End Semantics.

  End Spec.

  Module NodeMemUnlinkLayer.
    Section Impl.
      Context {A : Type}.

      Definition L : layer_interface :=
      {|
        li_sig := @ENodeMemU A;
        li_lts := @VNodeMemU A;
        li_init := Idle empty_heap;
      |}.
    End Impl.
  End NodeMemUnlinkLayer.

End NodeMemUnlinkSpec.
