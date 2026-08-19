Require Import Relation_Operators.

Require Import models.LinCCAL.
Require Import models.logics.Logics.
Require Import models.logics.SeparationAlgebra.
Require Import models.simlin.LTS.
Require Import models.simlin.Semantics.
Require Import models.simlin.Assertion.
Require Import examples.Common.AtomicLTS.
Require Import examples.LazyCoin.CoinSpec.

Module LazyCoinSpeculation.
  Import LinCCALBase LTSSpec Semantics.
  Import AssertionsSet AtomicLTS CoinSpec.

  Open Scope assertion_scope.

  (** Exclusive state ownership, with [Idle false] used as the empty state,
      supplies the concrete/abstract separation algebras for this example. *)
  Inductive coin_join : State VCoin -> State VCoin -> State VCoin -> Prop :=
  | coin_join_owned s : coin_join s (Idle false) s
  | coin_join_frame s : coin_join (Idle false) s s.

  #[local] Instance coin_Join : Join (State VCoin) := coin_join.

  #[local] Definition coin_SA : SeparationAlgebra (State VCoin).
  Proof.
    constructor.
    - inversion 1; subst; constructor.
    - intros mx my mz mxy mxyz Hxy Hyz.
      inversion Hxy; subst; inversion Hyz; subst;
        eexists; split; constructor.
  Defined.

  #[local] Definition coin_unit :
      SeparationAlgebraUnit (State VCoin) coin_SA.
  Proof.
    refine {| ue := Idle false |}.
    - constructor.
    - intros n n' Hjoin. inversion Hjoin; reflexivity.
  Defined.

  #[local] Existing Instance coin_SA.
  #[local] Existing Instance coin_unit.
  #[local] Existing Instance SetPossState.PSS_Join.
  #[local] Existing Instance SetPossState.PSS_SA.

  Definition assertion :=
    @Assertion (@ProofState ECoin ECoin VCoin VCoin).

  (** The two alternatives occurring when an uninitialized LazyCoin may
      resolve to either Boolean value. *)
  Definition coin_alternatives (ρt ρf : State VCoin) : assertion :=
    (Aρ ρt : assertion) ⊕ Aρ ρf.

  (** In LazyCoin, the paper's spatial singleton notation has the expected
      reading: a decided thread cell framed by arbitrary state is equivalent
      to every speculative alternative agreeing on that decision. *)
  Lemma decided_cell_equiv (t : tid) (ls : LinState) :
    ⊨ (t ↦ ls : assertion) * TT <<==>> t ↦∀ ls.
  Proof. apply ALinCell_sep_TT_equiv. Qed.

  Definition decided_in_some_alternative (t : tid) (ls : LinState) :
      assertion := t ↦∃ ls.

  (** Figure 10's [pupd-spec] combines independent identity updates of the
      two LazyCoin alternatives. *)
  Lemma speculation_identity (ρt ρf : State VCoin) :
    PUpdateId (RelSpecUnion GId GId)
      (coin_alternatives ρt ρf) (coin_alternatives ρt ρf).
  Proof.
    apply PUpdateIdSpec; apply PUpdateIdImply; apply ImplRefl.
  Qed.

  Definition keep_overlay_state (b : bool) :
      @PossibilityRelation ECoin ECoin VCoin VCoin :=
    fun _ _ _ ρ' _ => state ρ' = b.

  (** A future observation can discard the false alternative while keeping
      the true alternative.  Selecting the existing left branch also proves
      that the result remains nonempty. *)
  Lemma filter_true_enabled (ρt ρf : State VCoin) :
    state ρt = true ->
    PStepEnabled (keep_overlay_state true) (coin_alternatives ρt ρf).
  Proof.
    intros Htrue σ0 Δ0
      ([σ1 Δ1] & [σ2 Δ2] & Hρt & Hρf & Hunion).
    inversion Hunion; subst; simpl in *.
    exists Δ1. split; [reflexivity|].
    intros ρ' π' Hposs.
    exists ρ', π'. split.
    - apply ac_union_left. exact Hposs.
    - split.
      + unfold keep_overlay_state.
        apply Hρt in Hposs. inversion Hposs; subst. exact Htrue.
      + apply rt_refl.
  Qed.

  (** The checked primitive possibility update corresponding to the filter
      above.  Its postcondition is the relational image prescribed by the
      paper's [pupd-pstep] rule. *)
  Lemma filter_true (ρt ρf : State VCoin) :
    state ρt = true ->
    PUpdateId (PStep (keep_overlay_state true))
      (coin_alternatives ρt ρf)
      (ComposeA (coin_alternatives ρt ρf)
        (PStep (keep_overlay_state true))).
  Proof.
    intros Htrue. apply PUpdateIdPStep.
    apply filter_true_enabled; exact Htrue.
  Qed.
End LazyCoinSpeculation.
