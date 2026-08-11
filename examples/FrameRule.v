Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import LTSLocality.
Require Import SeparationAlgebra.
Require Import RGILogicSet.

(** Regression for the deliberately asymmetric error interface: response
    errors may exist in an LTS, but RGSimLin never treats them as program
    errors and therefore locality imposes no response-error axiom. *)
Module FrameRuleRegression.
  Import Reg LinCCALBase LTSSpec.

  Section ResponseErrors.
    Context {E : Op.t}.

    Definition response_error_lts : @LTS E :=
      {| State := unit;
         Step := fun _ _ _ => True;
         Error := fun ev _ =>
           match te_ev ev with
           | InvEv _ => False
           | ResEv _ _ => True
           end |}.

    #[local] Instance response_error_join : Join (State response_error_lts) :=
      unit_Join.
    #[local] Instance response_error_sa :
      SeparationAlgebra (State response_error_lts) := unit_SA.
    #[local] Instance response_error_unit :
      SeparationAlgebraUnit (State response_error_lts) response_error_sa :=
      unit_unit.

    #[local] Instance response_error_local : LocalLTS response_error_lts.
    Proof.
      constructor; intros; simpl in *.
      - contradiction.
      - right. exists tt. split; constructor.
      - exists tt. split; constructor.
    Qed.

    #[local] Instance response_error_frame_closed :
      FrameClosedLTS response_error_lts.
    Proof. constructor; intros; constructor. Qed.

    Lemma response_error_is_allowed t op ret :
      Error response_error_lts (Build_ThreadEvent t (ResEv op ret)) tt.
    Proof. exact I. Qed.
  End ResponseErrors.
End FrameRuleRegression.
