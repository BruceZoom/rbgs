Require Import Relation_Operators Operators_Properties.
Require Import Coq.Program.Equality.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import TPSimulationSet.
Require Import CompLin.


(** Erasing ghost state from a specification.

    A layer proof may be carried out against a specification [VG] whose
    state carries auxiliary (ghost) information, for instance the order
    in which nodes were inserted into a list, that the intended
    specification [VF] does not record.  If every step and every error of
    [VG] projects to a step and an error of [VF] under a state map [f],
    then the identity implementation's traces over [VG] are traces over
    [VF], so compositional linearizability against [VG] implies
    compositional linearizability against [VF].

    This is a statement about the trace semantics of the copy-cat
    implementation only; the object proof itself is unaffected and stays
    in the program logic. *)
Module CompLinProj.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.
  Import CompLin.
  Import TPSimulationSet.TPSimulation.

  Section Proj.
    Context {F : Op.t}.
    Context {VG VF : @LTS F}.
    Context (f : State VG -> State VF).
    Hypothesis Hproj_step :
      forall e g g', Step VG e g g' -> Step VF e (f g) (f g').
    Hypothesis Hproj_error :
      forall e g, Error VG e g -> Error VF e (f g).

    Definition proj_config (c : @TraceConfig F F VG) : @TraceConfig F F VF :=
      mkTraceConfig (tc_trace c) (f (tc_state c)) (tc_pool c).

    Lemma ts_step_proj (fop : Sig.op F) ev g ts g' ts' :
      @ts_step F F VG fop ev g ts g' ts' ->
      @ts_step F F VF fop ev (f g) ts (f g') ts'.
    Proof.
      intros H. inversion H; subst; constructor; apply Hproj_step; assumption.
    Qed.

    Lemma ts_error_proj (fop : Sig.op F) ev g ts :
      @ts_error F F VG fop ev g ts ->
      @ts_error F F VF fop ev (f g) ts.
    Proof.
      intros H. inversion H; subst. constructor. apply Hproj_error; assumption.
    Qed.

    Lemma trace_step_proj (c c' : @TraceConfig F F VG) :
      trace_step (@idImpl F) c c' ->
      trace_step (@idImpl F) (proj_config c) (proj_config c').
    Proof.
      intros H. inversion H; subst; unfold proj_config; simpl.
      - eapply TraceStepInv. exact Hstep.
      - eapply TraceStepRet. exact Hstep.
      - inversion Hstep; subst.
        eapply TraceStepU. econstructor; [exact Hfind| |reflexivity].
        apply ts_step_proj. eassumption.
      - eapply TraceStepTau. exact Hstep.
      - eapply TraceStepError; [exact Hfind|].
        apply ts_error_proj. exact Herror.
    Qed.

    Lemma trace_steps_proj (c c' : @TraceConfig F F VG) :
      trace_steps (@idImpl F) c c' ->
      trace_steps (@idImpl F) (proj_config c) (proj_config c').
    Proof.
      intros H. induction H as [x y Hxy | x | x y z Hxy IHxy Hyz IHyz].
      - apply rt_step. apply trace_step_proj. exact Hxy.
      - apply rt_refl.
      - eapply rt_trans; eassumption.
    Qed.

    Lemma ImplTraces_proj g0 s :
      @ImplTraces F F VG (@idImpl F) g0 s ->
      @ImplTraces F F VF (@idImpl F) (f g0) s.
    Proof.
      intros [g [c Hsteps]].
      exists (f g), c.
      exact (trace_steps_proj _ _ Hsteps).
    Qed.

    Lemma ImplTracesClosed_proj g0 s :
      @ImplTracesClosed F VG (@idImpl F) g0 s ->
      @ImplTracesClosed F VF (@idImpl F) (f g0) s.
    Proof.
      intros [H | [p [fop [tl [H Hs]]]]].
      - left. apply ImplTraces_proj. exact H.
      - right. exists p, fop, tl. split; [apply ImplTraces_proj; exact H | exact Hs].
    Qed.

    Lemma CompLin_proj {E : Op.t} {VE : @LTS E} (M : ModuleImpl E F)
        (sigma0 : State VE) (g0 : State VG) :
      @CompLin E F VE VG M sigma0 g0 ->
      @CompLin E F VE VF M sigma0 (f g0).
    Proof.
      intros H s Hs. apply ImplTracesClosed_proj. apply H. exact Hs.
    Qed.
  End Proj.

  (** The layer-level packaging.  The ghost layer [LG] and the erased
      layer share the signature; the erased layer's initial state is the
      projection of the ghost initial state. *)
  Definition LIProj {L : layer_interface} {Fsig : Op.t} {VG VF : @LTS Fsig}
      (f : State VG -> State VF)
      (Hproj_step : forall e g g', Step VG e g g' -> Step VF e (f g) (f g'))
      (Hproj_error : forall e g, Error VG e g -> Error VF e (f g))
      (g0 : State VG)
      (M : CompLin.layer_implementation_linearizability L
             {| li_sig := Fsig; li_lts := VG; li_init := g0 |}) :
      CompLin.layer_implementation_linearizability L
        {| li_sig := Fsig; li_lts := VF; li_init := f g0 |} :=
    @CompLin.Build_layer_implementation_linearizability L
      {| li_sig := Fsig; li_lts := VF; li_init := f g0 |}
      (CompLin.li_impl M)
      (CompLin_proj f Hproj_step Hproj_error (CompLin.li_impl M) (li_init L) g0
         (CompLin.li_correct M)).

End CompLinProj.
