Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulationSet.

Require Import examples.Common.AtomicLTS.
Require Import examples.Common.ThreadDomain.
Require Import examples.Common.IndexedFamilySpec.
Require Import examples.Registers.RegSpec.
Require Import examples.WriteSnapshot.WriteSnapshotSpec.


(** The write-snapshot object over a thread-indexed family of registers
    (docs/paper/main copy.pdf, Figure 1).

      write_snapshot(v):
        M[α].write(v);
        new <- {v}; old <- ∅;
        while (new ≠ old) {
          old <- new; new <- ∅;
          for each thread α_i in Υ:
            v' <- M[α_i].read();
            new <- new ∪ {v'}
        };
        return new

    The paper's one-shot register [OMem] is the race-free register
    [Reg'Spec.VReg] at type [option A] ([None] is the paper's ⊥), with one
    register per thread through [IndexedFamilySpec].  The register is not
    one-shot; the one-shot discipline comes from the program, which writes
    only the actor's own cell, and from the specification, where a second
    [write_snapshot] by the same thread is an error.  Only the owner
    writes a cell, so the race-free register's absence of a store race is
    justified by the program alone.

    Value sets are [ListSet] sets over [A], which needs decidable equality
    on [A] to decide [new ≠ old]; the specification itself does not.  The
    paper collects ⊥ into [new] and strips it at the return; here a read of
    ⊥ adds nothing, so [new] and [old] are value sets throughout and the
    loop test compares them as sets.  The scan over [Υ] is a [ForEach] over
    [ThreadDomain.threads D] accumulating the set; the outer [while] is a
    [From ... Do { ... } Loop] whose state is the pair [(new, old)]. *)
Module WriteSnapshotImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import TPSimulationSet.TPSimulation.
  Import AtomicLTS.
  Import IndexedFamilySpec.
  Import WriteSnapshotSpec.
  Import (coercions, canonicals, notations) Sig.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.
    Context (A_eq_dec : forall x y : A, {x = y} + {x <> y}).
    Context (D : ThreadDomain.t).

    (** One register holding [option A] per thread. *)
    Definition ECell := @Reg'Spec.EReg (option A).

    Definition CellObject : IndexedObject ECell :=
      {|
        component_state := @AState ECell (option A);
        component_step := fun _ => Step (@Reg'Spec.VReg (option A));
        component_error := fun _ => Error (@Reg'Spec.VReg (option A));
        component_init := fun _ => Idle None
      |}.

    Definition E : layer_interface := IndexedFamilyLayer D CellObject.

    Definition F : layer_interface := @WriteSnapshotLayer.L A D.

    (** [M[owner].read()] and [M[owner].write(v)]. *)
    Definition cell_read (owner : tid) : Sig.op (li_sig E) :=
      @indexed_call ECell owner Reg'Spec.get.

    Definition cell_write (owner : tid) (v : A) : Sig.op (li_sig E) :=
      @indexed_call ECell owner (Reg'Spec.set (Some v)).

    Definition subset_b (s1 s2 : set A) : bool :=
      forallb (fun x => set_mem A_eq_dec x s2) s1.

    Definition set_eqb (s1 s2 : set A) : bool :=
      subset_b s1 s2 && subset_b s2 s1.

    (** One step of the scan: read the cell of [owner] and add its value,
        if any, to the set collected so far. *)
    Definition scan_step (acc : set A) (owner : tid) :
        Prog (li_sig E) (set A) :=
      cell_read owner >= r =>
      Ret (match r with
           | Some x => set_add A_eq_dec x acc
           | None => acc
           end).

    (** The inner [while (i ≤ |Υ|)] loop. *)
    Definition scan : Prog (li_sig E) (set A) :=
      ForEach ThreadDomain.threads D From (empty_set A) Using scan_step.

    (** The loop state is [(new, old)]. *)
    Definition write_snapshot_impl (v : A) (actor : tid) :
        Prog (li_sig E) (list A) :=
      cell_write actor v >= _ =>
      From (pair (set_add A_eq_dec v (empty_set A)) (empty_set A))
      Do { st =>
        if set_eqb (fst st) (snd st) then
          Break (fst st)
        else
          scan p>= new =>
          Continue (pair new (fst st))
      } Loop.

    Definition ws_impl : ModuleImpl (li_sig E) (li_sig F) :=
      fun op =>
        match op with
        | write_snapshot v => write_snapshot_impl v
        end.

  End Impl.

End WriteSnapshotImpl.
