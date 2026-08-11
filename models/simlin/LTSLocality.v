Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import SeparationAlgebra.

(** Locality is an operational property of an LTS, not a property of its
    state separation algebra.  The two directions are deliberately split:
    concrete executions are projected from a whole state to their owned
    part, whereas abstract executions are lifted from an owned state. *)
Module LTSLocality.
  Import Reg LinCCALBase LTSSpec.

  Class LocalLTS {E : Op.t} (V : @LTS E) `{Join (State V)} : Prop := {
    invocation_error_local :
      forall t op owned frame whole,
        join owned frame whole ->
        Error V (Build_ThreadEvent t (InvEv op)) whole ->
        Error V (Build_ThreadEvent t (InvEv op)) owned;

    invocation_step_local :
      forall t op owned frame whole whole',
        join owned frame whole ->
        Step V (Build_ThreadEvent t (InvEv op)) whole whole' ->
        Error V (Build_ThreadEvent t (InvEv op)) owned \/
        exists owned',
          Step V (Build_ThreadEvent t (InvEv op)) owned owned' /\
          join owned' frame whole';

    response_step_local :
      forall t op ret owned frame whole whole',
        join owned frame whole ->
        Step V (Build_ThreadEvent t (ResEv op ret)) whole whole' ->
        exists owned',
          Step V (Build_ThreadEvent t (ResEv op ret)) owned owned' /\
          join owned' frame whole'
  }.

  Class FrameClosedLTS {E : Op.t} (V : @LTS E) `{Join (State V)} : Prop := {
    step_frame_compatible :
      forall ev owned frame whole owned' whole',
        join owned frame whole ->
        Step V ev owned owned' ->
        join owned' frame whole' ->
        Step V ev whole whole'
  }.

  Section LocalFacts.
    Context {E : Op.t} {V : @LTS E} {J : Join (State V)}.
    Context {HL : @LocalLTS E V J}.

    Lemma ANoError_frame_inv : forall t op owned frame whole,
      join owned frame whole ->
      ~ Error V (Build_ThreadEvent t (InvEv op)) owned ->
      ~ Error V (Build_ThreadEvent t (InvEv op)) whole.
    Proof.
      intros t op owned frame whole Hjoin Hsafe Herror.
      apply Hsafe. eapply invocation_error_local; eauto.
    Qed.

    Lemma invocation_step_unframe_safe : forall t op owned frame whole whole',
      join owned frame whole ->
      ~ Error V (Build_ThreadEvent t (InvEv op)) owned ->
      Step V (Build_ThreadEvent t (InvEv op)) whole whole' ->
      exists owned',
        Step V (Build_ThreadEvent t (InvEv op)) owned owned' /\
        join owned' frame whole'.
    Proof.
      intros t op owned frame whole whole' Hjoin Hsafe Hstep.
      destruct (invocation_step_local t op owned frame whole whole' Hjoin Hstep)
        as [Herror | Hlocal]; [contradiction|exact Hlocal].
    Qed.

    Lemma response_step_unframe : forall t op ret owned frame whole whole',
      join owned frame whole ->
      Step V (Build_ThreadEvent t (ResEv op ret)) whole whole' ->
      exists owned',
        Step V (Build_ThreadEvent t (ResEv op ret)) owned owned' /\
        join owned' frame whole'.
    Proof. intros; eapply response_step_local; eauto. Qed.
  End LocalFacts.
End LTSLocality.

Export LTSLocality.
