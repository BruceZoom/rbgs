Require Import Coq.Lists.List.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulation.

Require Import examples.Common.Heap.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.SPListSpec.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.ProgIterator.
Require Import examples.TSStack.SPListFamilySpec.
Require Import examples.TSStack.SPListArraySpec.


(** Implementation of the SPList-array adapter.  Indexed operations are
    routed to one SPList in the family.  The aggregate counter is the only
    operation that traverses every row; resetIter is operationally a no-op
    whose effect is entirely in the array specification's auxiliary state. *)
Module SPListArrayImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import TPSimulation.
  Import TimestampSpec.
  Import SPListSpec.
  Import ProgIterator.
  Import SPListFamilySpec.
  Import SPListArraySpec.
  Import (coercions, canonicals, notations) Sig.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Definition E : layer_interface :=
      @SPListFamilyLayer.L A D.

    Definition F : layer_interface :=
      @SPListArrayLayer.L A D.

    Definition insert_impl
        (v : A) (actor : tid) : Prog (li_sig E) Addr :=
      family_call actor (linsert v) >= loc =>
      Ret loc.

    Definition setTS_impl
        (loc : Addr) (ts : TS) (actor : tid) :
        Prog (li_sig E) unit :=
      family_call actor (lsetTS loc ts) >= _ =>
      Ret tt.

    Definition getTop_impl
        (owner : tid) (_actor : tid) :
        Prog (li_sig E) (@LNode A + nat) :=
      family_call owner lgetTop >= result =>
      Ret result.

    Definition resetIter_impl (_actor : tid) :
        Prog (li_sig E) unit :=
      Ret tt.

    Definition tryRemove_impl
        (owner : tid) (loc : Addr) (_actor : tid) :
        Prog (li_sig E) bool :=
      family_call owner (ltryRemove loc) >= removed =>
      Ret removed.

    Definition counter_step
        (sum : nat) (owner : tid) : Prog (li_sig E) nat :=
      family_call owner lgetCounter >= count =>
      Ret (Nat.add sum count).

    Definition getCounter_impl (_actor : tid) :
        Prog (li_sig E) nat :=
      foldM counter_step (ThreadDomain.threads D) O.

    Definition splist_array_impl :
        ModuleImpl (li_sig E) (li_sig F) :=
      fun op =>
        match op with
        | array_insert v => insert_impl v
        | array_setTS loc ts => setTS_impl loc ts
        | array_getTop owner => getTop_impl owner
        | array_resetIter => resetIter_impl
        | array_tryRemove owner loc => tryRemove_impl owner loc
        | array_getCounter => getCounter_impl
        end.

  End Impl.

End SPListArrayImpl.
