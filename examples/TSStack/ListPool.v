Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulationSet.

Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.SPListSpec.
Require Import examples.TSStack.SPListArraySpec.
Require Import examples.TSStack.ListPoolSpec.


(** Implementation of the list-pool layer from Appendix A.2.

    The left component of the underlay is the SPList array and the right
    component is the interval-timestamp object.  A scan keeps both the best
    node seen so far and the sum of the counters returned by empty rows.
    If every row is empty, a second aggregate counter read distinguishes a
    stable empty pool from a push that overlapped the scan. *)
Module ListPoolImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import TPSimulationSet.TPSimulation.
  Import TimestampSpec.
  Import SPListSpec.
  Import SPListArraySpec.
  Import ListPoolSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (canonicals) Sig.Plus.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Definition EArray : layer_interface :=
      @SPListArrayLayer.L A D.

    Definition ETimestampLayer : layer_interface :=
      TimestampLayer.L.

    Definition E : layer_interface := EArray ⊗ₗ ETimestampLayer.

    Definition F : layer_interface :=
      @ListPoolLayer.L A D.

    (** A concrete representative of the optional tuple [r] in Fig. 22.
        Keeping the timestamp is necessary during the scan, but it is not
        exposed in the ListPool result. *)
    Record Candidate : Type := {
      candidate_value : A;
      candidate_owner : tid;
      candidate_loc : Addr;
      candidate_timestamp : TS;
    }.

    Definition ScanState : Type := (option Candidate * nat)%type.

    (** Boolean form of the strict timestamp order from Fig. 14. *)
    Definition timestamp_ltb (older newer : TS) : bool :=
      match older, newer with
      | TSInterval _ older_upper, TSInterval newer_lower _ =>
          older_upper <? newer_lower
      | TSInterval _ _, TSTop => true
      | TSTop, _ => false
      end.

    Lemma timestamp_ltb_spec older newer :
      timestamp_ltb older newer = true <-> timestamp_lt older newer.
    Proof.
      destruct older as [|older_lower older_upper],
          newer as [|newer_lower newer_upper]; simpl.
      - split; [discriminate|contradiction].
      - split; [discriminate|contradiction].
      - tauto.
      - apply Nat.ltb_lt.
    Qed.

    Lemma timestamp_ltb_false_spec older newer :
      timestamp_ltb older newer = false <-> ~ timestamp_lt older newer.
    Proof.
      split.
      - intros Hfalse Hlt. apply timestamp_ltb_spec in Hlt. congruence.
      - intros Hnot. destruct (timestamp_ltb older newer) eqn:Hcmp; auto.
        exfalso. apply Hnot. now apply timestamp_ltb_spec.
    Qed.

    Definition choose_candidate
        (owner : tid) (node : @LNode A)
        (current : option Candidate) : option Candidate :=
      let '(v, ts, loc) := node in
      let next :=
        {|
          candidate_value := v;
          candidate_owner := owner;
          candidate_loc := loc;
          candidate_timestamp := ts
        |} in
      match current with
      | None => Some next
      | Some previous =>
          if timestamp_ltb (candidate_timestamp previous) ts
          then Some next
          else Some previous
      end.

    Definition scan_step
        (scan : ScanState) (owner : tid) :
        Prog (li_sig E) ScanState :=
      inl (array_getTop owner) >= result =>
      match result with
      | inl node => Ret (choose_candidate owner node (fst scan), snd scan)
      | inr count => Ret (fst scan, Nat.add (snd scan) count)
      end.

    Definition push_impl
        (v : A) (_actor : tid) : Prog (li_sig E) unit :=
      inl (array_insert v) >= loc =>
      inr newTS >= ts =>
      inl (array_setTS loc ts) >= _ =>
      Ret tt.

    Definition getTop_impl (_actor : tid) :
        Prog (li_sig E) (@YResult A) :=
      inl array_resetIter >= _ =>
      (ForEach ThreadDomain.threads D From (None, O) Using scan_step)
        p>= scan =>
      match fst scan with
      | Some candidate =>
          Ret (YSuccNode
            (candidate_value candidate)
            (candidate_owner candidate)
            (candidate_loc candidate))
      | None =>
          inl array_getCounter >= current_counter =>
          Ret (if Nat.eqb current_counter (snd scan)
               then YSuccEmpty
               else YFail)
      end.

    Definition tryRemove_impl
        (owner : tid) (loc : Addr) (_actor : tid) :
        Prog (li_sig E) bool :=
      inl (array_tryRemove owner loc) >= removed =>
      Ret removed.

    Definition list_pool_impl :
        ModuleImpl (li_sig E) (li_sig F) :=
      fun op =>
        match op with
        | lpool_push v => push_impl v
        | lpool_getTop => getTop_impl
        | lpool_tryRemove owner loc => tryRemove_impl owner loc
        end.

  End Impl.

End ListPoolImpl.
