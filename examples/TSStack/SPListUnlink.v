Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import PeanoNat.
Require Import List.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulationSet.

Require Import examples.Common.AtomicLTS.
Require Import examples.Common.Heap.
Require Import examples.CAS.CASRegSpec.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.NodeMemUnlinkSpec.
Require Import examples.TSStack.SPListSpec.
Require Import examples.TSStack.SPList.


(** The SPList with unlinking of taken nodes, after Dodds, Haas and
    Kirsch (POPL 2015).

    The overlay is the unchanged [SPListSpec] layer ([SPListImpl.F]): the
    specification describes the heap of nodes and the order of untaken
    nodes and never mentions successor pointers, so physical cleanup is
    invisible to every layer above.  The underlay replaces [NodeMemSpec]
    by [NodeMemUnlinkSpec], whose only addition is [nmcasNext].

    Three operations clean up taken nodes:

      - [insert] walks from the current top over taken nodes and allocates
        the new node with the first node it did not skip as successor.  No
        write is needed since the successor is fixed at allocation.

      - [getTop], after its traversal finds the first untaken node, moves
        the top register down to that node with a CAS that keeps the
        insertion counter.  The CAS fails harmlessly when the register
        changed.  The original performs this adjustment in [remove] using
        the top value that [getYoungest] handed over; doing it here keeps
        the interfaces above (which carry only owner and address) intact,
        with the same effect: at most one taken node precedes the first
        untaken node.

      - [tryRemove], once its take succeeded, walks from the taken node's
        successor over taken nodes and rewrites the taken node's successor
        to the first node it did not skip.  The rewrite is a CAS from the
        successor value read after the take.  Only the thread whose take
        succeeded writes that node's successor, so the CAS cannot fail in
        practice; it is a CAS rather than the original's plain store so
        that no data-race argument about successor cells is needed (see
        [NodeMemUnlinkSpec]).  The original's additional write to the
        previous top's successor is not ported: two removers can race on
        it, and racing plain writes are errors in the owner memory.

    Invariant intended for the proof (not carried out here): every
    successor pointer of a published node is [None] or an older published
    node, every published node skipped by a successor pointer was taken
    when the pointer was written, and every untaken node is reachable from
    the top register.  Since [taken] flips once, skipped nodes stay taken,
    so a traversal that follows rewritten pointers passes only over taken
    nodes, exactly as a traversal that inspects each node would.  The
    counter in the top register is never changed by the unlinking CAS, so
    the counter-based emptiness check of the list pool is unaffected. *)
Module SPListUnlinkImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import TPSimulationSet.TPSimulation.
  Import AtomicLTS.
  Import CASRegSpec.
  Import TimestampSpec.
  Import NodeMemUnlinkSpec.
  Import SPListSpec.
  Import ListNotations.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.

  Open Scope prog_scope.
  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  Section Impl.
    Context {A : Type}.
    Context {owner : tid}.

    Definition ENodeMemLayer : layer_interface :=
      @NodeMemUnlinkLayer.L A.

    Definition ECASLayer : layer_interface :=
      SPListImpl.ECASLayer.

    Definition E : layer_interface := ENodeMemLayer ⊗ₗ ECASLayer.

    (** The overlay is literally the one of the non-unlinking SPList. *)
    Definition F : layer_interface := @SPListImpl.F A owner.

    Definition mem_op := Sig.op (@ENodeMemU A).
    Definition cas_op := Sig.op (ECASReg (Ptr * nat)).
    Definition in_mem := @inl mem_op cas_op.
    Definition in_cas := @inr mem_op cas_op.

    (** Follow successors from [p] while the node is taken.  Returns the
        first pointer that is [None] or an untaken node.  Each skipped node
        was observed taken, and [taken] never reverts, so a pointer to the
        result may replace a pointer to [p] without hiding an untaken
        node. *)
    Definition skip_taken_impl (p : Ptr) : Prog (li_sig E) Ptr :=
      From p Do { q =>
        match q with
        | None => Break(@None Addr)
        | Some l =>
            in_mem (nmgetTaken l) >= taken =>
            if taken
            then in_mem (nmgetNext l) >= next => Continue(next)
            else Break(Some l)
        end
      } Loop.

    Definition insert_impl (v : A) (_ : tid) : Prog (li_sig E) Addr :=
      in_cas get >= top_counter =>
      let '(top, count) := top_counter in
      skip_taken_impl top p>= next =>
      (in_mem (nmalloc v next) >= new_loc =>
       in_cas (set (Some new_loc, S count)) >= _ =>
       Ret new_loc).

    Definition setTS_impl (l : Addr) (ts : TS) (_ : tid) : Prog (li_sig E) unit :=
      in_mem (nmsetTS l ts) >= _ =>
      Ret tt.

    (** Same traversal and read order as [SPListImpl.getTop_impl]: the
        timestamp is read before the taken flag.  The successor is read
        before the taken flag as well; it may have been rewritten by the
        node's remover, in which case it skips nodes that were taken before
        the rewrite. *)
    Definition getTop_impl (_ : tid) :
      Prog (li_sig E) (@LNode A + nat) :=
      in_cas get >= top_counter =>
      let '(top, count) := top_counter in
      From top Do { p =>
        match p with
        | None => Break(@inr (@LNode A) nat count)
        | Some l =>
            in_mem (nmgetValue l) >= v =>
            in_mem (nmgetNext l) >= next =>
            in_mem (nmgetTS l) >= ts =>
            in_mem (nmgetTaken l) >= taken =>
            if taken
            then Continue(next)
            else Break(@inl (@LNode A) nat ((v, ts), l))
        end
      } Loop >= result =>
      match result with
      | inl (_, l) =>
          (* Unlink the taken prefix: move the top register down to the
             node found, keeping the counter, unless it is already there. *)
          match top with
          | Some t =>
              if Nat.eqb t l then Ret result
              else in_cas (cas (top, count) (Some l, count)) >= _ => Ret result
          | None => Ret result
          end
      | inr _ => Ret result
      end.

    Definition getCounter_impl (_ : tid) : Prog (li_sig E) nat :=
      in_cas get >= top_counter =>
      Ret (snd top_counter).

    Definition tryRemove_impl (l : Addr) (_ : tid) :
      Prog (li_sig E) bool :=
      in_mem (nmtryTake l) >= taken =>
      if taken then
        (* This thread took [l], so it is the only writer of [l]'s
           successor from now on and the CAS below cannot fail. *)
        in_mem (nmgetNext l) >= next =>
        skip_taken_impl next p>= p =>
        (in_mem (nmcasNext l next p) >= _ =>
         Ret true)
      else
        Ret false.

    Definition splist_unlink_impl : ModuleImpl (li_sig E) (li_sig F) :=
      fun m =>
        match m with
        | linsert v => insert_impl v
        | lsetTS l ts => setTS_impl l ts
        | lgetTop => getTop_impl
        | lgetCounter => getCounter_impl
        | ltryRemove l => tryRemove_impl l
        end.

  End Impl.
End SPListUnlinkImpl.
