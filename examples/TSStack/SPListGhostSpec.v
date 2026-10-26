Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import PeanoNat.
Require Import List.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.AtomicLTS.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.SPListSpec.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.

Open Scope list.

(** The SPList specification with a ghost insertion log.

    The unlinking SPList ([SPListUnlink]) physically removes taken nodes
    from its chain, so the chain no longer determines the order in which
    the nodes were inserted, and the representation invariant of its proof
    needs that order explicitly: it is the only order in which "the nodes
    between [x] and its successor are all taken" is a stable statement.
    No concrete or abstract state records it, so this specification adds
    it as ghost state: the list of all inserted addresses, newest first.

    Transitions are exactly those of [SPListSpec] on the first component;
    the log is extended by the response of [linsert] and left unchanged
    by every other event.  Projecting the log away maps every step and
    every error to one of [SPListSpec], so [CompLinProj] erases it again
    at the layer level and the proof of the unlinking list is a proof
    against the unchanged [SPListSpec]. *)
Module SPListGhostSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  Import TimestampSpec.
  Import SPListSpec.
  Import TPSimulationSet.TPSimulation.

  Section Spec.
    Context {A : Type}.
    Context {owner : tid}.

    Definition log_update (e : @ThreadEvent (@ESPList A)) (log : list Addr) :
        list Addr :=
      match te_ev e with
      | InvEv _ => log
      | ResEv op ret =>
          match op return Sig.ar op -> list Addr with
          | linsert _ => fun l => l :: log
          | _ => fun _ => log
          end ret
      end.

    Definition GhostState : Type := (@SPListControl A * list Addr)%type.

    Definition StepGhost (e : @ThreadEvent (@ESPList A))
        (c c' : GhostState) : Prop :=
      @StepSPList A owner e (fst c) (fst c') /\
      snd c' = log_update e (snd c).

    Definition ErrorGhost (e : @ThreadEvent (@ESPList A))
        (c : GhostState) : Prop :=
      @ErrorSPList A owner e (fst c).

    Definition VSPListGhost : @LTS (@ESPList A) :=
      {|
        State := GhostState;
        Step := StepGhost;
        Error := ErrorGhost
      |}.

    Lemma ghost_step_proj e c c' :
      Step VSPListGhost e c c' -> Step (@VSPList A owner) e (fst c) (fst c').
    Proof. intros [H _]. exact H. Qed.

    Lemma ghost_error_proj e c :
      Error VSPListGhost e c -> Error (@VSPList A owner) e (fst c).
    Proof. intros H. exact H. Qed.

    Lemma log_update_inv t op log :
      log_update {| te_tid := t; te_ev := InvEv op |} log = log.
    Proof. reflexivity. Qed.

    Lemma log_update_insert t v l log :
      log_update {| te_tid := t; te_ev := ResEv (linsert v) l |} log = l :: log.
    Proof. reflexivity. Qed.

    Lemma log_update_setTS t l ts log :
      log_update {| te_tid := t; te_ev := ResEv (lsetTS l ts) tt |} log = log.
    Proof. reflexivity. Qed.

    Lemma log_update_getTop t ret log :
      log_update {| te_tid := t; te_ev := ResEv (@lgetTop A) ret |} log = log.
    Proof. reflexivity. Qed.

    Lemma log_update_getCounter t n log :
      log_update {| te_tid := t; te_ev := ResEv (@lgetCounter A) n |} log = log.
    Proof. reflexivity. Qed.

    Lemma log_update_tryRemove t l b log :
      log_update {| te_tid := t; te_ev := ResEv (ltryRemove l) b |} log = log.
    Proof. reflexivity. Qed.

  End Spec.
End SPListGhostSpec.
