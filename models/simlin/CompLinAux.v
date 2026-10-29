Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.
Require Import Relation_Operators Operators_Properties.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import CompLin.

(** Auxiliary state for the completeness of the thread-local reasoning.

    Rely-guarantee reasoning over proof states [(σ, Δ)] cannot see the
    threads' continuations, so it is only complete up to auxiliary state.
    Two deterministic, total extensions of the layer interfaces supply it:

    - [hist_lts VE] records the sequence of underlay events;
    - [ops_lts VF] records, per thread, the operations the specification
      has seen invoked (at their linearization points).

    Neither changes the traces an implementation can produce, so
    Compositional Linearizability transfers in both directions
    ([CompLin_aux], [CompLin_unaux]). The generic transfer is stated for
    any forward simulation between underlay LTSs of the same signature
    ([ImplTraces_transfer]). *)
Module CompLinAux.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.
  Import CompLin.CompLin.

  (** * The auxiliary interfaces *)

  Section Hist.
    Context {E : Op.t} (VE : @LTS E).

    Definition hist_lts : @LTS E :=
      {| State := State VE * list (@ThreadEvent E);
         Step := fun ev s s' => Step VE ev (fst s) (fst s') /\ snd s' = snd s ++ ev :: nil;
         Error := fun ev s => Error VE ev (fst s) |}.
  End Hist.

  Section Ops.
    Context {F : Op.t} (VF : @LTS F).

    Definition ops_add (L : tid -> list (Sig.op F)) (ev : @ThreadEvent F) : tid -> list (Sig.op F) :=
      match te_ev ev with
      | InvEv f => fun u => if Pos.eq_dec u (te_tid ev) then L u ++ f :: nil else L u
      | ResEv _ _ => L
      end.

    Definition ops_lts : @LTS F :=
      {| State := State VF * (tid -> list (Sig.op F));
         Step := fun ev s s' => Step VF ev (fst s) (fst s') /\ snd s' = ops_add (snd s) ev;
         Error := fun ev s => Error VF ev (fst s) |}.
  End Ops.

  (** * Transferring traces along a simulation of the underlay *)

  Section Transfer.
    Context {E F : Op.t} {V1 V2 : @LTS E} (M : ModuleImpl E F).
    Variable r : State V1 -> State V2 -> Prop.
    Hypothesis Hstep : forall ev s1 s1' s2,
      Step V1 ev s1 s1' -> r s1 s2 -> exists s2', Step V2 ev s2 s2' /\ r s1' s2'.
    Hypothesis Herr : forall ev s1 s2, Error V1 ev s1 -> r s1 s2 -> Error V2 ev s2.

    Lemma ts_step_transfer f ev s1 ts1 s1' ts1' s2 :
      @ts_step E F V1 f ev s1 ts1 s1' ts1' -> r s1 s2 ->
      exists s2', @ts_step E F V2 f ev s2 ts1 s2' ts1' /\ r s1' s2'.
    Proof.
      intros Hts Hr. inversion Hts; subst.
      - destruct (Hstep _ _ _ _ Hstep0 Hr) as [s2' [Hs2 Hr']].
        exists s2'. split; [constructor; exact Hs2 | exact Hr'].
      - destruct (Hstep _ _ _ _ Hstep0 Hr) as [s2' [Hs2 Hr']].
        exists s2'. split; [constructor; exact Hs2 | exact Hr'].
    Qed.

    Lemma trace_step_transfer (X Y : @TraceConfig E F V1) :
      @trace_step E F V1 M X Y -> forall s2, r (tc_state X) s2 ->
      exists s2', @trace_step E F V2 M
        (mkTraceConfig (tc_trace X) s2 (tc_pool X))
        (mkTraceConfig (tc_trace Y) s2' (tc_pool Y)) /\ r (tc_state Y) s2'.
    Proof.
      intros Hstep1 s2 Hr.
      destruct Hstep1 as [s sigma c tt ff c' Hs | s sigma c tt ff rr c' Hs
                         | s sigma c ev sigma' c' Hs | s sigma c tt c' Hs
                         | s sigma c ff ev ts Hfind Herror]; simpl in *.
      - exists s2. split; [apply TraceStepInv; exact Hs | exact Hr].
      - exists s2. split; [apply TraceStepRet; exact Hs | exact Hr].
      - inversion Hs as [f0 ts1 ts2 Hfind Hts Hupd]; subst.
        destruct (ts_step_transfer _ _ _ _ _ _ s2 Hts Hr) as [s2' [Hts' Hr']].
        exists s2'. split; [| exact Hr'].
        apply (TraceStepU M s s2 c ev s2' (TMap.add (te_tid ev) ts2 c)).
        eapply UStep; [exact Hfind | exact Hts' | reflexivity].
      - exists s2. split; [| exact Hr].
        apply (TraceStepTau M s s2 c tt c'). exact Hs.
      - exists s2. split; [| exact Hr].
        inversion Herror as [t0 op s0 k Herr0]; subst.
        eapply (TraceStepError M s s2 c ff (Build_ThreadEvent t0 (InvEv op))
                  (Build_ThreadState ff (Vis op k) None)); [exact Hfind |].
        constructor. eapply Herr; eauto.
    Qed.

    Lemma trace_steps_transfer_gen (X Y : @TraceConfig E F V1) :
      clos_refl_trans_n1 _ (@trace_step E F V1 M) X Y ->
      forall s2, r (tc_state X) s2 ->
      exists s2', @trace_steps E F V2 M
        (mkTraceConfig (tc_trace X) s2 (tc_pool X))
        (mkTraceConfig (tc_trace Y) s2' (tc_pool Y)) /\ r (tc_state Y) s2'.
    Proof.
      induction 1 as [| Y Z HYZ HY IH]; intros s2 Hr.
      - exists s2. split; [apply rt_refl | exact Hr].
      - destruct (IH s2 Hr) as [s2' [Hsteps Hr']].
        destruct (trace_step_transfer _ _ HYZ s2' Hr') as [s2'' [Hstep' Hr'']].
        exists s2''. split; [| exact Hr''].
        eapply rt_trans; [exact Hsteps | apply rt_step; exact Hstep'].
    Qed.

    Lemma ImplTraces_transfer σ1 σ2 s :
      r σ1 σ2 -> @ImplTraces E F V1 M σ1 s -> @ImplTraces E F V2 M σ2 s.
    Proof.
      intros Hr [σ1' [c Hsteps]].
      apply clos_rt_rtn1 in Hsteps.
      destruct (trace_steps_transfer_gen _ _ Hsteps σ2 Hr) as [σ2' [Hsteps' _]].
      exists σ2', c. exact Hsteps'.
    Qed.
  End Transfer.

  (* Compositional linearizability transfers along a simulation of the
     overlay from the old specification to the new one and a simulation of
     the underlay from the new library to the old one. *)
  Lemma CompLin_transfer {E F : Op.t} {V1 V2 : @LTS E} {W1 W2 : @LTS F}
      (M : ModuleImpl E F)
      (rE : State V2 -> State V1 -> Prop)
      (HEstep : forall ev s1 s1' s2,
        Step V2 ev s1 s1' -> rE s1 s2 -> exists s2', Step V1 ev s2 s2' /\ rE s1' s2')
      (HEerr : forall ev s1 s2, Error V2 ev s1 -> rE s1 s2 -> Error V1 ev s2)
      (rF : State W1 -> State W2 -> Prop)
      (HFstep : forall ev s1 s1' s2,
        Step W1 ev s1 s1' -> rF s1 s2 -> exists s2', Step W2 ev s2 s2' /\ rF s1' s2')
      (HFerr : forall ev s1 s2, Error W1 ev s1 -> rF s1 s2 -> Error W2 ev s2)
      σ1 σ2 ρ1 ρ2 :
    rE σ2 σ1 -> rF ρ1 ρ2 ->
    @CompLin E F V1 W1 M σ1 ρ1 -> @CompLin E F V2 W2 M σ2 ρ2.
  Proof.
    intros HrE HrF Hcl s Htr.
    apply (ImplTraces_transfer M rE HEstep HEerr σ2 σ1 s HrE) in Htr.
    destruct (Hcl s Htr) as [Hid | [p [f [tl [Hid Heq]]]]].
    - left. eapply (ImplTraces_transfer idImpl rF HFstep HFerr); eauto.
    - right. exists p, f, tl. split; [| exact Heq].
      eapply (ImplTraces_transfer idImpl rF HFstep HFerr); eauto.
  Qed.

  (** * Adding and removing the auxiliary state *)

  Section AuxTransfer.
    Context {E F : Op.t} {VE : @LTS E} {VF : @LTS F} (M : ModuleImpl E F).

    Definition hist_init (σ0 : State VE) : State (hist_lts VE) := pair σ0 nil.
    Definition ops_init (ρ0 : State VF) : State (ops_lts VF) := pair ρ0 (fun _ => nil).

    Lemma hist_forget_step ev (s1 s1' : State (hist_lts VE)) (s2 : State VE) :
      Step (hist_lts VE) ev s1 s1' -> fst s1 = s2 ->
      exists s2', Step VE ev s2 s2' /\ fst s1' = s2'.
    Proof. intros [Hs _] <-. exists (fst s1'). auto. Qed.

    Lemma hist_forget_err ev (s1 : State (hist_lts VE)) (s2 : State VE) :
      Error (hist_lts VE) ev s1 -> fst s1 = s2 -> Error VE ev s2.
    Proof. intros H <-. exact H. Qed.

    Lemma hist_add_step ev (s1 s1' : State VE) (s2 : State (hist_lts VE)) :
      Step VE ev s1 s1' -> s1 = fst s2 ->
      exists s2', Step (hist_lts VE) ev s2 s2' /\ s1' = fst s2'.
    Proof.
      intros Hs Heq. destruct s2 as [s2a h]. simpl in Heq. subst s2a.
      exists (pair s1' (h ++ ev :: nil)). simpl. auto.
    Qed.

    Lemma hist_add_err ev (s1 : State VE) (s2 : State (hist_lts VE)) :
      Error VE ev s1 -> s1 = fst s2 -> Error (hist_lts VE) ev s2.
    Proof. intros H Heq. subst s1. exact H. Qed.

    Lemma ops_forget_step ev (s1 s1' : State (ops_lts VF)) (s2 : State VF) :
      Step (ops_lts VF) ev s1 s1' -> fst s1 = s2 ->
      exists s2', Step VF ev s2 s2' /\ fst s1' = s2'.
    Proof. intros [Hs _] <-. exists (fst s1'). auto. Qed.

    Lemma ops_forget_err ev (s1 : State (ops_lts VF)) (s2 : State VF) :
      Error (ops_lts VF) ev s1 -> fst s1 = s2 -> Error VF ev s2.
    Proof. intros H <-. exact H. Qed.

    Lemma ops_add_step ev (s1 s1' : State VF) (s2 : State (ops_lts VF)) :
      Step VF ev s1 s1' -> s1 = fst s2 ->
      exists s2', Step (ops_lts VF) ev s2 s2' /\ s1' = fst s2'.
    Proof.
      intros Hs Heq. destruct s2 as [s2a L]. simpl in Heq. subst s2a.
      exists (pair s1' (ops_add L ev)). simpl. auto.
    Qed.

    Lemma ops_add_err ev (s1 : State VF) (s2 : State (ops_lts VF)) :
      Error VF ev s1 -> s1 = fst s2 -> Error (ops_lts VF) ev s2.
    Proof. intros H Heq. subst s1. exact H. Qed.

    Theorem CompLin_aux σ0 ρ0 :
      @CompLin E F VE VF M σ0 ρ0 ->
      @CompLin E F (hist_lts VE) (ops_lts VF) M (hist_init σ0) (ops_init ρ0).
    Proof.
      apply (@CompLin_transfer E F VE (hist_lts VE) VF (ops_lts VF) M
               (fun s1 s2 => fst s1 = s2) hist_forget_step hist_forget_err
               (fun s1 s2 => s1 = fst s2) ops_add_step ops_add_err);
        reflexivity.
    Qed.

    Theorem CompLin_unaux σ0 ρ0 :
      @CompLin E F (hist_lts VE) (ops_lts VF) M (hist_init σ0) (ops_init ρ0) ->
      @CompLin E F VE VF M σ0 ρ0.
    Proof.
      apply (@CompLin_transfer E F (hist_lts VE) VE (ops_lts VF) VF M
               (fun s1 s2 => s1 = fst s2) hist_add_step hist_add_err
               (fun s1 s2 => fst s1 = s2) ops_forget_step ops_forget_err);
        reflexivity.
    Qed.
  End AuxTransfer.
End CompLinAux.
