Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import RGILogicSet.
Require Import SingletonPossibility.

Require Import examples.Common.ThreadDomain.
Require Import examples.Common.IndexedFamilySpec.
Require Import examples.TSStack.SPListSpec.
Require Import examples.TSStack.SPListFamilySpec.
Require Import examples.TSStack.SPListArraySpec.
Require Import examples.TSStack.SPListArray.

(** The proof adapter for the operationally empty [resetIter] method.  This
    isolates the newly supported rule shape; it is not a full SPListArray
    refinement proof, whose timestamp-order/row-order obligation is separate. *)
Module SPListArrayProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSingle SingletonPossibility.
  Import IndexedFamilySpec SPListSpec.
  Import SPListFamilySpec SPListArraySpec SPListArrayImpl.
  Module SetLogic := RGILogicSet.RGILogic.

  Open Scope assertion_scope.

  Section ResetAdapter.
    Context {A : Type} (D : ThreadDomain.t).

    Let E : Op.t := EIndexed (@ESPList A).
    Let F : Op.t := @ESPListArray A.
    Let VE : @LTS E := VIndexedFamily D (@SPListIndexedObject A).
    Let VF : @LTS F := @VSPListArray A D.

    Definition reset_assertion :=
      @Logics.Assertion
        (@SinglePossState.ProofState E F VE VF).

    Definition reset_relation :=
      @AssertionsSingle.A.RGRelation E F VE VF.

    Definition ResetActive (actor : tid) : reset_assertion :=
      ALin actor (ls_inv array_resetIter).

    Definition ResetCompleted (actor : tid) : reset_assertion :=
      ALin actor (ls_linr array_resetIter tt).

    (** [resetIter_impl] is exactly [Ret tt].  The abstract reset response is
        established by [singleton_provable_linstep], after which the existing
        pure singleton return rule closes the concrete program. *)
    Lemma resetIter_adapter (actor : tid)
        (R G : reset_relation) (I : reset_assertion) :
      (⊨ ResetCompleted actor ==>> I) ->
      AssertionsSingle.A.Stable R I (ResetCompleted actor) ->
      AssertionsSingle.PUpdateId G (ResetActive actor)
        (ResetCompleted actor) ->
      SetLogic.HTripleProvable
        (lift_relation R) (lift_relation G) (lift_assert I) actor
        (lift_assert (ResetActive actor)) (resetIter_impl D actor)
        (fun _ => lift_assert (ResetCompleted actor)).
    Proof.
      intros HI HS Hreset. unfold resetIter_impl.
      eapply singleton_provable_linstep with
        (P' := ResetCompleted actor); eauto.
      eapply singleton_provable_ret_safe.
      - apply ImplRefl.
      - exact HI.
      - exact HS.
    Qed.
  End ResetAdapter.
End SPListArrayProof.
