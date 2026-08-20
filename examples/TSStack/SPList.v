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
Require Import TPSimulation.
Require Import RGILogic.

Require Import examples.Common.AtomicLTS.
Require Import examples.Common.Heap.
Require Import examples.CAS.CASRegSpec.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.NodeMemSpec.
Require Import examples.TSStack.SPListSpec.


Module SPListImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS.
  Import CASRegSpec.
  Import TimestampSpec.
  Import NodeMemSpec.
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
      @NodeMemLayer.L A.

    Definition ECASLayer : layer_interface :=
    {|
      li_sig := ECASReg (Ptr * nat);
      li_lts := @VCASReg (Ptr * nat);
      li_init :=
        @Idle (ECASReg (Ptr * nat)) (Ptr * nat) (@None Addr, O)
    |}.

    Definition E : layer_interface := ENodeMemLayer ⊗ₗ ECASLayer.

    Definition empty_splist_state : @SPListState A :=
    {|
      counter := 0;
      nodes := empty_heap;
      order := nil;
      snapshot := TMap.empty (list Addr)
    |}.

    Definition F : layer_interface :=
    {|
      li_sig := ESPList;
      li_lts := @VSPList A owner;
      li_init := Ready empty_splist_state
    |}.

    Definition mem_op := Sig.op (@ENodeMem A).
    Definition cas_op := Sig.op (ECASReg (Ptr * nat)).
    Definition in_mem := @inl mem_op cas_op.
    Definition in_cas := @inr mem_op cas_op.

    Definition insert_impl (v : A) (_ : tid) : Prog (li_sig E) Addr :=
      in_cas get >= top_counter =>
      let '(top, count) := top_counter in
      in_mem (nmalloc v top) >= new_loc =>
      in_cas (set (Some new_loc, S count)) >= _ =>
      Ret new_loc.

    Definition setTS_impl (l : Addr) (ts : TS) (_ : tid) : Prog (li_sig E) unit :=
      in_mem (nmsetTS l ts) >= _ =>
      Ret tt.

    CoFixpoint find_top_impl (p : Ptr) (count : nat) :
      Prog (li_sig E) (@LNode A + nat) :=
      match p with
      | None => Ret (@inr (@LNode A) nat count)
      | Some l =>
          in_mem (nmget l) >= node =>
          let '(((v, ts), taken), next) := node in
          if taken
          then Tau (find_top_impl next count)
          else Ret (@inl (@LNode A) nat ((v, ts), l))
      end.

    Definition getTop_impl (_ : tid) :
      Prog (li_sig E) (@LNode A + nat) :=
      in_cas get >= top_counter =>
      let '(top, count) := top_counter in
      From top Do { p =>
        match p with
        | None => Break(inr count)
        | Some l =>
            in_mem (nmget l) >= node =>
            let '(((v, ts), taken), next) := node in
            if taken
            then Continue(next)
            else Break(@inl (@LNode A) nat ((v, ts), l))
        end
      } Loop.

    Definition getCounter_impl (_ : tid) : Prog (li_sig E) nat :=
      in_cas get >= top_counter =>
      Ret (snd top_counter).

    Definition tryRemove_impl (l : Addr) (_ : tid) :
      Prog (li_sig E) bool :=
      in_mem (nmtryTake l) >= taken =>
      Ret taken.

    Definition splist_impl : ModuleImpl (li_sig E) (li_sig F) :=
      fun m =>
        match m with
        | linsert v => insert_impl v
        | lsetTS l ts => setTS_impl l ts
        | lgetTop => getTop_impl
        | lgetCounter => getCounter_impl
        | ltryRemove l => tryRemove_impl l
        end.

    (* Linearizability-proof template. *)
    Definition assertion :=
      @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).

    Definition rg_relation :=
      @RGRelation _ _ (li_lts E) (li_lts F).

    (* TODO: relate the NodeMem linked list and CAS top/counter pair to the
       SPList [nodes], [order], [counter], and per-thread snapshots. *)
    Definition I : assertion := fun _ => True.

    (* TODO: strengthen these relations with preservation of the owner's
       pending node and of snapshots belonging to other threads. *)
    Definition G (_ : tid) : rg_relation := fun _ _ => True.
    Definition R (_ : tid) : rg_relation := fun _ _ => True.

    Program Definition MSPList : layer_implementation E F :=
    {|
      li_impl := splist_impl
    |}.
    Next Obligation.
      (* TODO: apply [RGILogic.soundness] with [R], [G], and [I], prove one
         method judgment for each SPList operation, then prove the initial
         NodeMem/CAS/SPList states satisfy [I]. *)
    Admitted.

  End Impl.
End SPListImpl.
