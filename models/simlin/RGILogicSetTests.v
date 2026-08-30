Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import RGISimulationSet.
Require Import RGILogicSet.
Require Import SingletonPossibility.

(** Permanent regression and public-API checks for the production
    set-of-possibilities logic. *)
Module RGILogicSetTests.
  Import Reg LinCCALBase LTSSpec Semantics AssertionsSet Lang.
  Import RGILogicSet.RGILogic RGISimulationSet.RGISimulation.
  Open Scope assertion_scope.

  (** These checks intentionally mention every public family used by clients:
      primitive and safe rules, structural rules, method soundness, and the
      top-level soundness theorem.  A signature-breaking edit therefore fails
      this small target before the examples are rebuilt. *)
  Check @provable_ret.
  Check @provable_vis.
  Check @provable_tau.
  Check @provable_linstep.
  Check @provable_perror.
  Check @provable_vis_safe.
  Check @provable_ret_safe.
  Check @provable_conseq_weak_pre.
  Check @provable_conseq_weak_post.
  Check @provable_conseq_weak.
  Check @provable_seq.
  Check @provable_foreach.
  Check @provable_dowhile_unroll.
  Check @provable_dowhile.
  Check @provable_doloop_data.
  Check @provable_doloop.
  Check @provable_frame_same_context.
  Check @provable_frame.
  Check @MethodProvable.
  Check @logic_soundness.
  Check @soundness.
  Check @SingletonPossibility.singleton_provable_linstep.
  Check @SingletonPossibility.singleton_provable_vis_safe.
  Check @SingletonPossibility.singleton_provable_ret_safe.

  Section RuleShapes.
    Context {E F : Op.t} {VE : @LTS E} {VF : @LTS F}.
    Context (R G : @RGRelation _ _ VE VF)
      (I : @Assertion (@ProofState E F VE VF)) (t : tid).

    Lemma zero_updates {A} P (p : Prog E A) Q :
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q }} ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q }}.
    Proof. auto. Qed.

    Lemma one_update {A} P P' (p : Prog E A) Q :
      (⊨ P' ==>> I) -> Stable R I P' -> (G ⊨ P ⭆ P') ->
      [VE, VF, R, G, I, t] ⊢ {{ P' }} p {{ Q }} ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q }}.
    Proof. intros; eapply provable_linstep; eauto. Qed.

    Lemma two_updates {A} P0 P1 P2 (p : Prog E A) Q :
      (⊨ P1 ==>> I) -> Stable R I P1 -> (G ⊨ P0 ⭆ P1) ->
      (⊨ P2 ==>> I) -> Stable R I P2 -> (G ⊨ P1 ⭆ P2) ->
      [VE, VF, R, G, I, t] ⊢ {{ P2 }} p {{ Q }} ->
      [VE, VF, R, G, I, t] ⊢ {{ P0 }} p {{ Q }}.
    Proof.
      intros HP1I HP1S HU01 HP2I HP2S HU12 Hproof.
      eapply provable_linstep with (P' := P1);
        [exact HP1I|exact HP1S|exact HU01|].
      eapply provable_linstep with (P' := P2); eauto.
    Qed.

    Lemma update_before_ret {A} (a : A) P P' :
      (⊨ P' ==>> I) -> Stable R I P' -> (G ⊨ P ⭆ P') ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} Ret a {{ fun _ => P' }}.
    Proof.
      intros. eapply provable_linstep; eauto.
      eapply provable_ret_safe; eauto using ImplRefl.
    Qed.

    Lemma update_before_vis {A} P P' (m : Sig.op E)
        (k : Sig.ar m -> Prog E A) Q :
      (⊨ P' ==>> I) -> Stable R I P' -> (G ⊨ P ⭆ P') ->
      [VE, VF, R, G, I, t] ⊢ {{ P' }} Vis m k {{ Q }} ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} Vis m k {{ Q }}.
    Proof. intros; eapply provable_linstep; eauto. Qed.

    Lemma update_survives_bind_ret {A B} (a : A)
        (k : A -> Prog E B) P P' Q :
      (⊨ P' ==>> I) -> Stable R I P' -> (G ⊨ P ⭆ P') ->
      (forall x, [VE, VF, R, G, I, t] ⊢ {{ P' }} k x {{ Q }}) ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} bindProg (Ret a) k {{ Q }}.
    Proof.
      intros HI HS HU Hk. eapply provable_seq with (Q' := fun _ => P').
      - eapply update_before_ret; eauto.
      - exact Hk.
    Qed.

    (** The core regression: the abstract result is established before the
        immediate concrete return, with no [Tau] in the program. *)
    Lemma immediate_return_no_tau (f : Sig.op F) (ret : Sig.ar f) :
      (G ⊨ ALin t (ls_inv f) ⭆ ALin t (ls_linr f ret)) ->
      (⊨ ALin t (ls_linr f ret) ==>> I) ->
      Stable R I (ALin t (ls_linr f ret)) ->
      [VE, VF, R, G, I, t] ⊢ {{ ALin t (ls_inv f) }} Ret tt
        {{ fun _ => ALin t (ls_linr f ret) }}.
    Proof.
      intros HU HI HS. eapply provable_linstep; eauto.
      eapply provable_ret_safe; eauto using ImplRefl.
    Qed.
  End RuleShapes.

  Section MethodSoundnessShape.
    Context {E F : Op.t} {VE : @LTS E} {VF : @LTS F}.
    Context (M : ModuleImpl E F).
    Context (R G : @RGRelation _ _ VE VF)
      (I : @Assertion (@ProofState E F VE VF)) (t : tid).

    Lemma immediate_method_reaches_simulation f P Q :
      ValidRGI R G I t -> MethodProvable VE VF M R G I t f P Q ->
      forall sigma Delta,
        (Ginv t f ⊚ I) (sigma, Delta) ->
        (forall rho pi, Delta rho pi ->
          TMap.find t pi = Some (ls_inv f)) ->
        MethodSimulation R (G ∪ (GINV t ∪ GRET t ∪ GId)) I t f
          sigma (M f t) None Delta.
    Proof. intros. eapply logic_soundness; eauto. Qed.
  End MethodSoundnessShape.
End RGILogicSetTests.
