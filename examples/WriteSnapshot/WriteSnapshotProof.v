Require Import FMapPositive.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Bool.Bool.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Logic.Classical.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulationSet.
Require Import RGILogicSet.
Require Import CompLinLayer.

Require Import examples.Common.AtomicLTS.
Require Import examples.Common.ThreadDomain.
Require Import examples.Common.IndexedFamilySpec.
Require Import examples.Registers.RegSpec.
Require Import examples.WriteSnapshot.WriteSnapshotSpec.
Require Import examples.WriteSnapshot.WriteSnapshot.


(** Linearizability of the one-shot write-snapshot object
    (docs/paper/main copy.pdf, Sections 2 and 4; see
    docs/plans/WriteSnapshotVerificationPlan.md for the modelling choices
    and the dictionary).

    The proof uses the set-of-possibilities logic because the response of
    a [write_snapshot] is linearized in the past: the returned set is the
    abstract state at the end of some prefix [p] of the linearization,
    which is only identified once the double collect terminates.  The
    abstract configuration therefore keeps, for every thread whose write
    is linearized but whose response is not, one possibility per
    historical snapshot since its write.

    Concretely the configuration is always a *product*: all possibilities
    share the abstract state [ρc] (which mirrors the cells), and the set of
    possibilities is the cartesian product of the per-thread choices
    [proj s t].  A thread's choices are

      {ls_inv}                          before its write is linearized,
      {ls_lini} ∪ {ls_linr l | l ≈ S}   for every snapshot [S] taken since,
      {ls_linr l}                       once it has selected its answer.

    Two abstract updates realise the paper's [G_write] and [G_snapshot]:

    - at the response of the cell write, every possibility linearizes the
      invocation, and every pending thread (including the writer) gets
      one more branch per list representing the new snapshot
      ([write_image]);
    - at the exit of the double collect, the writer keeps exactly the
      possibilities in which it answered the collected set
      ([ac_restrict]).

    Because the product structure is an invariant, a selection by one
    thread never destroys the branches of another, and the frozen
    snapshot [ρp] of the paper's loop invariants ([I_o], [I_n]) is simply
    "a snapshot for which all my branches exist", a stable fact. *)
Module WriteSnapshotProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSet.
  Import TPSimulationSet.TPSimulation CompLinLayer.
  Import AtomicLTS IndexedFamilySpec WriteSnapshotSpec WriteSnapshotImpl.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Module SetLogic := RGILogicSet.RGILogic.
  Import SetLogic.

  Open Scope prog_scope.
  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  Section Proof.
    Context {A : Type}.
    Context (A_eq_dec : forall x y : A, {x = y} + {x <> y}).
    Context (D : ThreadDomain.t).

    Definition E : layer_interface := @WriteSnapshotImpl.E A D.
    Definition F : layer_interface := @WriteSnapshotImpl.F A D.

    (** Notations rather than definitions: [rewrite] matches syntactically
        and must not see two spellings of the same type. *)
    Notation concrete_state := (State (li_lts E)).
    Notation abstract_state := (State (li_lts F)).
    Notation lin_state := (@LinState (li_sig F)).
    Definition assertion := @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).
    Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).
    Definition cell_row := @AState (@ECell A) (option A).

    Definition ws_op (v : A) : Sig.op (li_sig F) := write_snapshot v.
    Definition inv_token (v : A) : lin_state := ls_inv (ws_op v).
    Definition lini_token (v : A) : lin_state := ls_lini (ws_op v).
    Definition linr_token (v : A) (l : list A) : lin_state := ls_linr (ws_op v) l.

    Definition cell_write' (α : tid) (v : A) : Sig.op (li_sig E) :=
      @cell_write A D α v.
    Definition cell_read' (β : tid) : Sig.op (li_sig E) :=
      @cell_read A D β.

    (** * Views of the concrete state *)

    Definition cell_val (σ : concrete_state) (t : tid) : option A :=
      match @TMap.find cell_row t σ with
      | Some row => AtomicLTS.state row
      | None => None
      end.

    Definition row_exists (σ : concrete_state) (t : tid) : Prop :=
      @TMap.find cell_row t σ <> None.

    Lemma cell_val_add_same σ t row :
      cell_val (TMap.add t row σ) t = AtomicLTS.state row.
    Proof. unfold cell_val. rewrite TMap.gss. reflexivity. Qed.

    Lemma cell_val_add_other σ t t' row :
      t' <> t -> cell_val (TMap.add t row σ) t' = cell_val σ t'.
    Proof. intros Hne. unfold cell_val. rewrite TMap.gso by exact Hne. reflexivity. Qed.

    Lemma row_exists_add σ t t' row :
      row_exists (TMap.add t row σ) t' <-> (t' = t \/ row_exists σ t').
    Proof.
      unfold row_exists. destruct (Pos.eq_dec t' t) as [-> | Hne].
      - rewrite TMap.gss. split; [auto | discriminate].
      - rewrite TMap.gso by exact Hne. tauto.
    Qed.

    (** * Shapes of the concrete steps *)

    Ltac crush_eq :=
      repeat match goal with
      | H : {| te_tid := _; te_ev := _ |} = {| te_tid := _; te_ev := _ |} |- _ =>
          injection H; clear H; intros
      | H : InvEv _ = ResEv _ _ |- _ => discriminate H
      | H : ResEv _ _ = InvEv _ |- _ => discriminate H
      | H : InvEv _ = InvEv _ |- _ => injection H; clear H; intros
      | H : ResEv _ _ = ResEv _ _ |- _ => injection H; clear H; intros
      | H : Reg'Spec.set _ = Reg'Spec.set _ |- _ => injection H; clear H; intros
      | H : Reg'Spec.set _ = Reg'Spec.get |- _ => discriminate H
      | H : Reg'Spec.get = Reg'Spec.set _ |- _ => discriminate H
      | H : Some _ = Some _ |- _ => injection H; clear H; intros
      | H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H
      | H : ?x = ?x |- _ => clear H
      | H : ?x = ?y |- _ => is_var y; subst y
      | H : ?x = ?y |- _ => is_var x; subst x
      end;
      try discriminate; try congruence.

    Lemma step_write_inv_shape α v σ σ' :
      Step (li_lts E) {| te_tid := α; te_ev := InvEv (cell_write' α v) |} σ σ' ->
      ThreadDomain.contains D α /\
      exists c, @TMap.find cell_row α σ = Some (Idle c) /\
        σ' = TMap.add α (Pending c α (Reg'Spec.set (Some v) : Sig.op (@ECell A))) σ.
    Proof.
      intros Hstep.
      change (StepIndexedFamily D (@CellObject A)
        {| te_tid := α; te_ev := InvEv (cell_write' α v) |} σ σ') in Hstep.
      dependent destruction Hstep. simpl in *.
      inversion H1; subst; crush_eq.
      inversion Hstep; subst; crush_eq.
      split; [exact H |]. eauto.
    Qed.

    Lemma step_write_res_shape α v σ σ' :
      Step (li_lts E) {| te_tid := α; te_ev := ResEv (cell_write' α v) tt |} σ σ' ->
      ThreadDomain.contains D α /\
      exists c, @TMap.find cell_row α σ = Some (Pending c α (Reg'Spec.set (Some v) : Sig.op (@ECell A))) /\
        σ' = TMap.add α (Idle (Some v)) σ.
    Proof.
      intros Hstep.
      change (StepIndexedFamily D (@CellObject A)
        {| te_tid := α; te_ev := ResEv (cell_write' α v) tt |} σ σ') in Hstep.
      dependent destruction Hstep. simpl in *.
      inversion H1; subst; crush_eq.
      inversion Hstep; subst; crush_eq.
      split; [exact H |]. eauto.
    Qed.

    Lemma step_read_inv_shape α β σ σ' :
      Step (li_lts E) {| te_tid := α; te_ev := InvEv (cell_read' β) |} σ σ' ->
      ThreadDomain.contains D β /\
      exists c, @TMap.find cell_row β σ = Some (Idle c) /\
        σ' = TMap.add β (Pending c α (Reg'Spec.get : Sig.op (@ECell A))) σ.
    Proof.
      intros Hstep.
      change (StepIndexedFamily D (@CellObject A)
        {| te_tid := α; te_ev := InvEv (cell_read' β) |} σ σ') in Hstep.
      dependent destruction Hstep. simpl in *.
      inversion H1; subst; crush_eq.
      inversion Hstep; subst; crush_eq.
      split; [exact H |]. eauto.
    Qed.

    Lemma step_read_res_shape α β r σ σ' :
      Step (li_lts E) {| te_tid := α; te_ev := ResEv (cell_read' β) r |} σ σ' ->
      ThreadDomain.contains D β /\
      @TMap.find cell_row β σ = Some (Pending r α (Reg'Spec.get : Sig.op (@ECell A))) /\
      σ' = TMap.add β (Idle r) σ.
    Proof.
      intros Hstep.
      change (StepIndexedFamily D (@CellObject A)
        {| te_tid := α; te_ev := ResEv (cell_read' β) r |} σ σ') in Hstep.
      dependent destruction Hstep. simpl in *.
      inversion H1; subst; crush_eq.
      inversion Hstep; subst; crush_eq.
      split; [exact H |]. eauto.
    Qed.

    Lemma no_error_family α op owner σ :
      ThreadDomain.contains D owner ->
      row_exists σ owner ->
      ~ Error (li_lts E) {| te_tid := α; te_ev := InvEv (@indexed_call (@ECell A) owner op) |} σ.
    Proof.
      intros Hin Hrow Herr.
      change (ErrorIndexedFamily D (@CellObject A)
        {| te_tid := α; te_ev := InvEv (indexed_call owner op) |} σ) in Herr.
      inversion Herr; subst; simpl in *.
      - exact H1.
      - contradiction.
      - apply Hrow. assumption.
    Qed.

    (** * Response chains: linearizing pending responses at a snapshot *)

    Definition one_resp (ρ : abstract_state) (π1 π2 : tmap lin_state) : Prop :=
      exists t w l,
        TMap.find t π1 = Some (lini_token w) /\
        ws_snapshot ρ l /\
        π2 = TMap.add t (linr_token w l) π1.

    Definition resp_chain (ρ : abstract_state) : tmap lin_state -> tmap lin_state -> Prop :=
      clos_refl_trans _ (one_resp ρ).

    Lemma one_resp_entry ρ π1 π2 :
      one_resp ρ π1 π2 ->
      forall t,
        TMap.find t π2 = TMap.find t π1 \/
        exists w l, TMap.find t π1 = Some (lini_token w) /\
          TMap.find t π2 = Some (linr_token w l) /\ ws_snapshot ρ l.
    Proof.
      intros (t0 & w & l & Hfind & Hsnap & Heq) t. subst π2.
      destruct (Pos.eq_dec t t0) as [-> | Hne].
      - right. exists w, l. rewrite TMap.gss. auto.
      - left. rewrite TMap.gso by exact Hne. reflexivity.
    Qed.

    Lemma resp_chain_entry ρ π π' :
      resp_chain ρ π π' ->
      forall t,
        TMap.find t π' = TMap.find t π \/
        exists w l, TMap.find t π = Some (lini_token w) /\
          TMap.find t π' = Some (linr_token w l) /\ ws_snapshot ρ l.
    Proof.
      intros Hchain. induction Hchain as [π1 π2 Hone | π | π1 π2 π3 H12 IH12 H23 IH23]; intros t.
      - apply one_resp_entry. exact Hone.
      - left. reflexivity.
      - destruct (IH23 t) as [Heq23 | (w & l & Hlini & Hlinr & Hsnap) ].
        + rewrite Heq23. apply IH12.
        + destruct (IH12 t) as [Heq12 | (w' & l' & Hlini' & Hlinr' & _) ].
          * right. exists w, l. rewrite <- Heq12. auto.
          * exfalso. rewrite Hlinr' in Hlini. discriminate Hlini.
    Qed.

    Lemma resp_chain_none ρ π π' t :
      resp_chain ρ π π' ->
      (TMap.find t π = None <-> TMap.find t π' = None).
    Proof.
      intros Hchain. destruct (resp_chain_entry ρ π π' Hchain t)
        as [Heq | (w & l & H1 & H2 & _) ].
      - rewrite Heq. tauto.
      - rewrite H1, H2. split; discriminate.
    Qed.

    Lemma resp_chain_extend ρ π π' t w l :
      resp_chain ρ π π' ->
      TMap.find t π' = Some (lini_token w) ->
      ws_snapshot ρ l ->
      resp_chain ρ π (TMap.add t (linr_token w l) π').
    Proof.
      intros Hchain Hfind Hsnap.
      eapply rt_trans; [exact Hchain |].
      apply rt_step. exists t, w, l. auto.
    Qed.

    Lemma resp_chain_steps ρ π π' :
      resp_chain ρ π π' ->
      @poss_steps _ (li_lts F) (PossOk ρ π) (PossOk ρ π').
    Proof.
      intros Hchain. induction Hchain as [π1 π2 Hone | π | π1 π2 π3 H12 IH12 H23 IH23].
      - destruct Hone as (t & w & l & Hfind & Hsnap & Heq). subst π2.
        apply rt_step.
        apply (ps_ret t (ws_op w) l ρ ρ π1).
        + apply step_ws_res with (t := t) (v := w) (s := ρ) (l := l); [reflexivity | exact Hsnap].
        + exact Hfind.
      - apply rt_refl.
      - eapply rt_trans; eauto.
    Qed.

    (** * The abstract update at the cell write *)

    Variant write_image_prop (Δ1 : AbstractConfig (li_lts F)) (α : tid) (v : A) :
        AbstractConfigProp (li_lts F) :=
    | WriteImage ρ π π' (Hposs : Δ1 ρ π)
        (Hchain : resp_chain (TMap.add α v ρ) (TMap.add α (lini_token v) π) π') :
        write_image_prop Δ1 α v (TMap.add α v ρ) π'.

    Lemma write_image_domain Δ1 α v ρ' π' :
      write_image_prop Δ1 α v ρ' π' ->
      domain_equiv (map_domain π') (domain_add α (ac_active Δ1)).
    Proof.
      intros H. inversion H as [ρ π π'' Hposs Hchain Hρ Hπ]; subst.
      intros t. unfold map_domain, domain_add.
      pose proof (resp_chain_none _ _ _ t Hchain) as Hnone.
      pose proof (ac_domain Δ1 _ _ Hposs t) as Hdom. unfold map_domain in Hdom.
      destruct (Pos.eq_dec t α) as [-> | Hne].
      - split; [auto |]. intros _.
        destruct (TMap.find α π') eqn:Hf; [eauto |].
        exfalso. rewrite TMap.gss in Hnone. destruct Hnone as [_ Hnone].
        specialize (Hnone ltac:(first [exact Hf | reflexivity])). discriminate.
      - rewrite TMap.gso in Hnone by exact Hne.
        split.
        + intros [x Hx]. right. apply Hdom.
          destruct (TMap.find t π) eqn:Hf; [eauto |].
          exfalso. pose proof (eq_trans (eq_sym (proj1 Hnone ltac:(first [exact Hf | reflexivity]))) Hx) as Habs.
          discriminate Habs.
        + intros [Habs | Hact]; [congruence |].
          apply Hdom in Hact. destruct Hact as [x Hx].
          destruct (TMap.find t π') eqn:Hf; [eauto |].
          exfalso. pose proof (eq_trans (eq_sym (proj2 Hnone ltac:(first [exact Hf | reflexivity]))) Hx) as Habs.
          discriminate Habs.
    Qed.

    Program Definition write_image (Δ1 : AbstractConfig (li_lts F)) (α : tid) (v : A) :
        AbstractConfig (li_lts F) :=
      {| ac_active := domain_add α (ac_active Δ1);
         ac_prop := write_image_prop Δ1 α v |}.
    Next Obligation.
      destruct (ac_nonempty Δ1) as (ρ & π & Hposs).
      exists (TMap.add α v ρ), (TMap.add α (lini_token v) π).
      econstructor; [exact Hposs | apply rt_refl].
    Qed.
    Next Obligation.
      intros. match goal with H : write_image_prop _ _ _ _ _ |- _ =>
        exact (write_image_domain _ _ _ _ _ H) end.
    Qed.

    Lemma write_image_subset_steps (Δ1 : AbstractConfig (li_lts F)) α v :
      (forall ρ π, Δ1 ρ π -> TMap.find α ρ = None /\ TMap.find α π = Some (inv_token v)) ->
      (write_image Δ1 α v ⊆ ac_steps Δ1)%AbstractConfig.
    Proof.
      intros Hpre ρ' π' Hposs'. inversion Hposs'; subst.
      destruct (Hpre _ _ Hposs) as [Hρ Hπ].
      econstructor; [exact Hposs |].
      eapply rt_trans.
      - apply rt_step. apply (ps_inv α (ws_op v) ρ (TMap.add α v ρ) π).
        + apply step_ws_inv with (t := α) (v := v) (s := ρ); [reflexivity | exact Hρ].
        + exact Hπ.
      - apply resp_chain_steps. exact Hchain.
    Qed.

    (** * The abstract update at the selection *)

    Program Definition ac_restrict (Δ1 : AbstractConfig (li_lts F)) (t : tid) (ls : lin_state)
        (Hne : exists ρ π, Δ1 ρ π /\ TMap.find t π = Some ls) : AbstractConfig (li_lts F) :=
      {| ac_active := ac_active Δ1;
         ac_prop := fun ρ π => Δ1 ρ π /\ TMap.find t π = Some ls |}.
    Next Obligation.
      destruct Hne as (ρ & π & Hposs & Hfind). exists ρ, π. auto.
    Qed.
    Next Obligation.
      destruct H as [Hposs _]. exact (ac_domain _ _ _ Hposs).
    Qed.

    Lemma ac_restrict_subset_steps (Δ1 : AbstractConfig (li_lts F)) t ls Hne :
      (ac_restrict Δ1 t ls Hne ⊆ ac_steps Δ1)%AbstractConfig.
    Proof.
      intros ρ π [Hposs _]. apply ac_steps_refl. exact Hposs.
    Qed.


    (** * Projections and the invariant *)

    Definition proof_state := @ProofState _ _ (li_lts E) (li_lts F).

    (** Explicitly typed proof-state builder, for pairs whose concrete
        component is not a variable. *)
    Definition mk (σ0 : concrete_state) (Δ1 : AbstractConfig (li_lts F)) : proof_state :=
      @Build_ProofStateSet _ _ (li_lts E) (li_lts F) σ0 Δ1.

    (** The choices of thread [t] in a configuration. *)
    Definition proj_ac (Δ1 : AbstractConfig (li_lts F)) (t : tid) (ols : option lin_state) : Prop :=
      exists ρ π, Δ1 ρ π /\ TMap.find t π = ols.

    Definition proj (s : proof_state) (t : tid) (ols : option lin_state) : Prop :=
      proj_ac (Δ s) t ols.

    Definition find_eq (π π' : tmap lin_state) : Prop :=
      forall t, TMap.find t π = TMap.find t π'.

    (** [Δ1] is the product of its projections, up to the representation of
        the linearization maps; every possibility carries the abstract state
        [ρc], which mirrors the cells. *)
    Record inv_facts (σ0 : concrete_state) (Δ1 : AbstractConfig (li_lts F))
        (ρc : abstract_state) : Prop := {
      inv_common : forall ρ π, Δ1 ρ π -> ρ = ρc;
      inv_cells : forall t, @TMap.find A t ρc = cell_val σ0 t;
      inv_closed : forall π, (forall t, proj_ac Δ1 t (TMap.find t π)) ->
        exists π', find_eq π' π /\ Δ1 ρc π';
      inv_dom : forall t, row_exists σ0 t <-> ThreadDomain.contains D t;
      inv_lini : forall t v, proj_ac Δ1 t (Some (lini_token v)) ->
        cell_val σ0 t = Some v /\
        forall l, ws_snapshot ρc l -> proj_ac Δ1 t (Some (linr_token v l));
      inv_linr : forall t v l, proj_ac Δ1 t (Some (linr_token v l)) ->
        cell_val σ0 t = Some v /\ forall x, In x l -> ws_value ρc x
    }.

    Definition I : assertion := fun s => exists ρc, inv_facts (σ s) (Δ s) ρc.

    (** The only abstract errors: a thread invoked outside the domain, or
        invoked twice. *)
    Definition ErrW_self (t : tid) : assertion := fun s =>
      exists ρ π v, Δ s ρ π /\ TMap.find t π = Some (inv_token v) /\
        (~ ThreadDomain.contains D t \/ @TMap.find A t ρ <> None).

    Definition ErrW : assertion := fun s => exists t, ErrW_self t s.

    Lemma ErrW_APError : forall s, ErrW s -> APError s.
    Proof.
      intros s (t & ρ & π & v & Hposs & Hfind & Herr).
      apply APErrorSome with (ρ := ρ) (π := π); [exact Hposs |].
      apply rt_step. apply (ps_error t (ws_op v) ρ π); [| exact Hfind].
      destruct Herr as [Hout | Hdouble].
      - apply error_ws_actor_outside with (actor := t) (op := ws_op v); auto.
      - apply error_ws_double_inv with (actor := t) (op := ws_op v); auto.
    Qed.

    (** * Rely and guarantee *)

    Record other_view (t : tid) (s s' : proof_state) : Prop := {
      ov_keep : forall ols, proj s t ols -> proj s' t ols;
      ov_new : forall ols, proj s' t ols ->
        proj s t ols \/
        exists w l, ols = Some (linr_token w l) /\ proj s t (Some (lini_token w));
      ov_cell : cell_val (σ s') t = cell_val (σ s) t
    }.

    Record G_core (actor : tid) (s s' : proof_state) : Prop := {
      gc_others : forall t, t <> actor -> other_view t s s';
      gc_mono : forall t x, cell_val (σ s) t = Some x -> cell_val (σ s') t = Some x;
      gc_err : ErrW_self actor s -> ErrW_self actor s'
    }.

    Definition G (actor : tid) : rg_relation := G_core actor.
    Definition R (t : tid) : rg_relation :=
      fun s s' => exists actor, actor <> t /\ G_core actor s s'.

    (** * Thread-local assertions *)

    Definition HasLini (α : tid) (v : A) : assertion :=
      fun s => proj s α (Some (lini_token v)).
    Definition NoInv (α : tid) : assertion :=
      fun s => forall w, ~ proj s α (Some (inv_token w)).
    Definition CellNone (α : tid) : assertion :=
      fun s => cell_val (σ s) α = None.
    Definition Collected (l : list A) : assertion :=
      fun s => forall x, In x l -> exists γ, cell_val (σ s) γ = Some x.
    (** The paper's prefix [p]: a snapshot [ρp] for which all of [α]'s
        branches exist and whose cells are (still) written. *)
    Definition Frozen (α : tid) (v : A) (ρp : abstract_state) : assertion :=
      fun s =>
        (forall l, ws_snapshot ρp l -> proj s α (Some (linr_token v l))) /\
        (forall β x, @TMap.find A β ρp = Some x -> cell_val (σ s) β = Some x).
    Definition Under (l : list A) (ρp : abstract_state) : Prop :=
      forall x, In x l -> ws_value ρp x.
    Definition Covers (ρp : abstract_state) (l : list A) : Prop :=
      forall x, ws_value ρp x -> In x l.

    Definition Pgood (α : tid) (v : A) : assertion :=
      I //\\ ALin α (inv_token v) //\\ ⌜ThreadDomain.contains D α⌝ //\\ CellNone α.
    Definition Perr : assertion := I //\\ ErrW.
    Definition P (α : tid) (v : A) : assertion := Pgood α v \\// Perr.
    Definition Written (α : tid) (v : A) : assertion :=
      I //\\ HasLini α v //\\ NoInv α //\\ ⌜ThreadDomain.contains D α⌝.
    Definition LoopInv (α : tid) (v : A) (st : set A * set A) : assertion :=
      Written α v //\\ Collected (fst st) //\\
      (⌜snd st = nil /\ In v (fst st)⌝ \\//
       (∃ ρp, Frozen α v ρp //\\ ⌜Under (snd st) ρp /\ Covers ρp (fst st)⌝)).
    Definition ScanInv (α : tid) (v : A) (old : set A)
        (remaining : list tid) (acc : set A) : assertion :=
      Written α v //\\ Collected acc //\\
      (∃ ρp, Frozen α v ρp //\\
        ⌜Under old ρp /\
         exists done, ThreadDomain.threads D = done ++ remaining /\
           forall β x, In β done -> @TMap.find A β ρp = Some x -> In x acc⌝).
    Definition Qpost (α : tid) (v : A) (l : list A) : assertion :=
      I //\\ ALin α (linr_token v l).

    (** * Small facts *)

    Lemma some_inj {X : Type} (x y : X) : Some x = Some y -> x = y.
    Proof. intros H. injection H. auto. Qed.

    Lemma lini_token_inj v w : lini_token v = lini_token w -> v = w.
    Proof. intros H. injection H. auto. Qed.

    (** [injection] drops the dependent component of [ls_linr]; read it
        through a projection instead. *)
    Definition token_ret (ls : lin_state) : option (list A) :=
      match ls with
      | ls_linr f r =>
          match f return Sig.ar f -> option (list A) with
          | write_snapshot _ => fun r => Some r
          end r
      | _ => None
      end.

    Lemma linr_token_inj v w l l' :
      linr_token v l = linr_token w l' -> v = w /\ l = l'.
    Proof.
      intros H. pose proof (f_equal token_ret H) as Hret. simpl in Hret.
      injection Hret. intros ->.
      unfold linr_token, ws_op in H. injection H. auto.
    Qed.

    Lemma proj_ac_elements (Δ1 : AbstractConfig (li_lts F)) ρ π t :
      Δ1 ρ π -> proj_ac Δ1 t (TMap.find t π).
    Proof. intros Hposs. exists ρ, π. auto. Qed.

    Lemma ws_value_add_mono (ρc : abstract_state) α v x :
      @TMap.find A α ρc = None ->
      ws_value ρc x -> ws_value (TMap.add α v ρc) x.
    Proof.
      intros Hnone [γ Hγ]. exists γ.
      destruct (Pos.eq_dec γ α) as [-> | Hne].
      - rewrite Hγ in Hnone. discriminate.
      - rewrite TMap.gso by exact Hne. exact Hγ.
    Qed.

    Lemma set_eqb_true l1 l2 :
      set_eqb A_eq_dec l1 l2 = true -> forall x, In x l1 <-> In x l2.
    Proof.
      unfold set_eqb, subset_b. intros H x.
      apply andb_true_iff in H. destruct H as [H12 H21].
      rewrite forallb_forall in H12, H21.
      split; intros Hin.
      - apply set_mem_correct1 with (Aeq_dec := A_eq_dec). apply H12. exact Hin.
      - apply set_mem_correct1 with (Aeq_dec := A_eq_dec). apply H21. exact Hin.
    Qed.

    Lemma set_eqb_nil_false x l :
      In x l -> set_eqb A_eq_dec l nil = false.
    Proof.
      intros Hin. unfold set_eqb, subset_b.
      destruct (forallb (fun y => set_mem A_eq_dec y nil) l) eqn:Hall; [| reflexivity].
      rewrite forallb_forall in Hall. specialize (Hall x Hin). simpl in Hall. discriminate.
    Qed.

    Lemma threads_contains t :
      In t (ThreadDomain.threads D) <-> ThreadDomain.contains D t.
    Proof. reflexivity. Qed.

    (** * Stability *)

    Lemma R_other_view α s s' :
      R α s s' -> other_view α s s'.
    Proof. intros (actor & Hne & HG). apply (gc_others _ _ _ HG). auto. Qed.

    Lemma R_mono α s s' :
      R α s s' -> forall t x, cell_val (σ s) t = Some x -> cell_val (σ s') t = Some x.
    Proof. intros (actor & Hne & HG). apply (gc_mono _ _ _ HG). Qed.

    Lemma stable_I α : Stable (R α) I I.
    Proof. apply Stable_invariant. Qed.

    Lemma stable_ALin_inv α v : Stable (R α) I (ALin α (inv_token v)).
    Proof.
      intros s' [[s [Hpre HR]] _]. apply R_other_view in HR.
      intros ρ' π' Hposs'.
      destruct (ov_new _ _ _ HR _ (proj_ac_elements _ _ _ α Hposs'))
        as [ (ρ & π & Hposs & Hfind) | (w & l & Heq & (ρ & π & Hposs & Hfind)) ].
      - rewrite <- Hfind. exact (Hpre _ _ Hposs).
      - exfalso. rewrite (Hpre _ _ Hposs) in Hfind. discriminate.
    Qed.

    Lemma stable_ALin_linr α v l : Stable (R α) I (ALin α (linr_token v l)).
    Proof.
      intros s' [[s [Hpre HR]] _]. apply R_other_view in HR.
      intros ρ' π' Hposs'.
      destruct (ov_new _ _ _ HR _ (proj_ac_elements _ _ _ α Hposs'))
        as [ (ρ & π & Hposs & Hfind) | (w & l' & Heq & (ρ & π & Hposs & Hfind)) ].
      - rewrite <- Hfind. exact (Hpre _ _ Hposs).
      - exfalso. rewrite (Hpre _ _ Hposs) in Hfind. discriminate.
    Qed.

    Lemma stable_CellNone α : Stable (R α) I (CellNone α).
    Proof.
      intros s' [[s [Hpre HR]] _]. apply R_other_view in HR.
      unfold CellNone in *. rewrite (ov_cell _ _ _ HR). exact Hpre.
    Qed.

    Lemma stable_HasLini α v : Stable (R α) I (HasLini α v).
    Proof.
      intros s' [[s [Hpre HR]] _]. apply R_other_view in HR.
      apply (ov_keep _ _ _ HR). exact Hpre.
    Qed.

    Lemma stable_NoInv α : Stable (R α) I (NoInv α).
    Proof.
      intros s' [[s [Hpre HR]] _]. apply R_other_view in HR.
      intros w Hproj.
      destruct (ov_new _ _ _ HR _ Hproj) as [Hold | (w' & l & Heq & _) ].
      - exact (Hpre w Hold).
      - discriminate Heq.
    Qed.

    Lemma stable_Collected α l : Stable (R α) I (Collected l).
    Proof.
      intros s' [[s [Hpre HR]] _]. intros x Hx.
      destruct (Hpre x Hx) as [γ Hγ]. exists γ. eapply R_mono; eauto.
    Qed.

    Lemma stable_Frozen α v ρp : Stable (R α) I (Frozen α v ρp).
    Proof.
      intros s' [[s [[Hbr Hcells] HR]] _].
      split.
      - intros l Hl. apply (ov_keep _ _ _ (R_other_view _ _ _ HR)). apply Hbr. exact Hl.
      - intros β x Hβ. eapply R_mono; eauto.
    Qed.

    Lemma stable_Perr α : Stable (R α) I Perr.
    Proof.
      intros s' [[s [[HI (t & ρ & π & v & Hposs & Hfind & Herr) ] HR ] ] HI' ].
      split; [exact HI' |].
      destruct HR as (actor & Hne & HG).
      destruct (Pos.eq_dec t actor) as [-> | Hneq].
      - exists actor. apply (gc_err _ _ _ HG). exists ρ, π, v. auto.
      - destruct (ov_keep _ _ _ (gc_others _ _ _ HG t Hneq) (Some (inv_token v)))
          as (ρ' & π' & Hposs' & Hfind'); [exists ρ, π; auto |].
        exists t, ρ', π', v. split; [exact Hposs' |]. split; [exact Hfind' |].
        destruct Herr as [Hout | Hdouble]; [left; exact Hout |]. right.
        destruct HI as [ρc Hfacts]. destruct HI' as [ρc' Hfacts'].
        rewrite (inv_common _ _ _ Hfacts _ _ Hposs) in Hdouble.
        rewrite (inv_cells _ _ _ Hfacts) in Hdouble.
        rewrite (inv_common _ _ _ Hfacts' _ _ Hposs').
        rewrite (inv_cells _ _ _ Hfacts').
        destruct (cell_val (σ s) t) eqn:Hc; [| congruence].
        rewrite (gc_mono _ _ _ HG _ _ Hc). discriminate.
    Qed.

    Create HintDb stableDB.
    Hint Resolve stable_I stable_ALin_inv stable_ALin_linr stable_CellNone
      stable_HasLini stable_NoInv stable_Collected stable_Frozen stable_Perr
      APureStable : stableDB.

    Lemma stable_Pgood α v : Stable (R α) I (Pgood α v).
    Proof. unfold Pgood. solve_stable stableDB. Qed.

    Lemma stable_P α v : Stable (R α) I (P α v).
    Proof. unfold P. apply DisjStable; [apply stable_Pgood | apply stable_Perr]. Qed.

    Lemma stable_Written α v : Stable (R α) I (Written α v).
    Proof. unfold Written. solve_stable stableDB. Qed.

    Hint Resolve stable_Pgood stable_P stable_Written : stableDB.

    Lemma stable_LoopInv α v st : Stable (R α) I (LoopInv α v st).
    Proof.
      unfold LoopInv. apply ConjStable; [auto with stableDB |].
      apply ConjStable; [auto with stableDB |].
      apply DisjStable; [apply APureStable |].
      apply StableExists. intros ρp. solve_stable stableDB.
    Qed.

    Lemma stable_ScanInv α v old remaining acc :
      Stable (R α) I (ScanInv α v old remaining acc).
    Proof.
      unfold ScanInv. apply ConjStable; [auto with stableDB |].
      apply ConjStable; [auto with stableDB |].
      apply StableExists. intros ρp. solve_stable stableDB.
    Qed.

    Lemma stable_Qpost α v l : Stable (R α) I (Qpost α v l).
    Proof. unfold Qpost. solve_stable stableDB. Qed.

    Hint Resolve stable_LoopInv stable_ScanInv stable_Qpost : stableDB.

    (** * Entailments into the invariant *)

    Lemma Pgood_I α v : ⊨ Pgood α v ==>> I.
    Proof. intros s [HI _]. exact HI. Qed.
    Lemma P_I α v : ⊨ P α v ==>> I.
    Proof. intros s [[HI _] | [HI _]]; exact HI. Qed.
    Lemma Written_I α v : ⊨ Written α v ==>> I.
    Proof. intros s [HI _]. exact HI. Qed.
    Lemma LoopInv_I α v st : ⊨ LoopInv α v st ==>> I.
    Proof. intros s [[HI _] _]. exact HI. Qed.
    Lemma ScanInv_I α v old remaining acc : ⊨ ScanInv α v old remaining acc ==>> I.
    Proof. intros s [[HI _] _]. exact HI. Qed.
    Lemma Qpost_I α v l : ⊨ Qpost α v l ==>> I.
    Proof. intros s [HI _]. exact HI. Qed.

    (** * Concrete steps that do not change the cells *)

    Definition cells_eq (σ0 σ1 : concrete_state) : Prop :=
      (forall t, cell_val σ1 t = cell_val σ0 t) /\
      (forall t, row_exists σ1 t <-> row_exists σ0 t).

    Lemma inv_facts_cells_eq σ0 σ1 Δ1 ρc :
      cells_eq σ0 σ1 -> inv_facts σ0 Δ1 ρc -> inv_facts σ1 Δ1 ρc.
    Proof.
      intros [Hcells Hrows] Hf. constructor.
      - exact (inv_common _ _ _ Hf).
      - intros t. rewrite Hcells. exact (inv_cells _ _ _ Hf t).
      - exact (inv_closed _ _ _ Hf).
      - intros t. rewrite Hrows. exact (inv_dom _ _ _ Hf t).
      - intros t v Hp. rewrite Hcells. exact (inv_lini _ _ _ Hf t v Hp).
      - intros t v l Hp. rewrite Hcells. exact (inv_linr _ _ _ Hf t v l Hp).
    Qed.

    Lemma I_cells_eq σ0 σ1 Δ1 :
      cells_eq σ0 σ1 -> I (σ0, Δ1) -> I (σ1, Δ1).
    Proof.
      intros Heq [ρc Hf]. exists ρc. simpl in *. eapply inv_facts_cells_eq; eauto.
    Qed.

    Lemma Written_cells_eq α v σ0 σ1 Δ1 :
      cells_eq σ0 σ1 -> Written α v (σ0, Δ1) -> Written α v (σ1, Δ1).
    Proof.
      intros Heq [HI [Hlini [Hno Hin]]].
      split; [eapply I_cells_eq; eauto |]. split; [exact Hlini |]. split; [exact Hno | exact Hin].
    Qed.

    Lemma Collected_cells_eq l σ0 σ1 Δ1 :
      cells_eq σ0 σ1 -> Collected l (σ0, Δ1) -> Collected l (σ1, Δ1).
    Proof.
      intros [Hcells _] Hc x Hx. destruct (Hc x Hx) as [γ Hγ]. exists γ. simpl. rewrite Hcells. exact Hγ.
    Qed.

    Lemma Frozen_cells_eq α v ρp σ0 σ1 Δ1 :
      cells_eq σ0 σ1 -> Frozen α v ρp (σ0, Δ1) -> Frozen α v ρp (σ1, Δ1).
    Proof.
      intros [Hcells _] [Hbr Hc]. split; [exact Hbr |].
      intros β x Hβ. simpl. rewrite Hcells. apply Hc. exact Hβ.
    Qed.

    Lemma ScanInv_cells_eq α v old remaining acc σ0 σ1 Δ1 :
      cells_eq σ0 σ1 ->
      ScanInv α v old remaining acc (σ0, Δ1) -> ScanInv α v old remaining acc (σ1, Δ1).
    Proof.
      intros Heq [Hw [Hc [ρp [Hfr Hpure]]]].
      split; [eapply Written_cells_eq; eauto |].
      split; [eapply Collected_cells_eq; eauto |].
      exists ρp. split; [eapply Frozen_cells_eq; eauto | exact Hpure].
    Qed.

    Lemma G_core_same_config actor σ0 σ1 Δ1 :
      cells_eq σ0 σ1 -> G_core actor (σ0, Δ1) (σ1, Δ1).
    Proof.
      intros [Hcells Hrows]. constructor.
      - intros t _. constructor; simpl.
        + auto.
        + intros ols Hp. left. exact Hp.
        + apply Hcells.
      - intros t x. simpl. rewrite Hcells. auto.
      - intros (ρ & π & v & Hposs & Hfind & Herr). exists ρ, π, v. auto.
    Qed.

    Lemma read_inv_cells_eq α β σ0 σ1 :
      Step (li_lts E) {| te_tid := α; te_ev := InvEv (cell_read' β) |} σ0 σ1 ->
      cells_eq σ0 σ1.
    Proof.
      intros Hstep. destruct (step_read_inv_shape _ _ _ _ Hstep) as [Hin (c & Hrow & ->) ].
      split.
      - intros t. destruct (Pos.eq_dec t β) as [-> | Hne].
        + rewrite cell_val_add_same. unfold cell_val. rewrite Hrow. reflexivity.
        + apply cell_val_add_other. exact Hne.
      - intros t. rewrite row_exists_add. split; [| tauto].
        intros [-> | Hr]; [| exact Hr]. unfold row_exists. rewrite Hrow. discriminate.
    Qed.

    Lemma read_res_cells_eq α β r σ0 σ1 :
      Step (li_lts E) {| te_tid := α; te_ev := ResEv (cell_read' β) r |} σ0 σ1 ->
      cells_eq σ0 σ1 /\ cell_val σ0 β = r.
    Proof.
      intros Hstep. destruct (step_read_res_shape _ _ _ _ _ Hstep) as [Hin [Hrow ->]].
      split; [split |].
      - intros t. destruct (Pos.eq_dec t β) as [-> | Hne].
        + rewrite cell_val_add_same. unfold cell_val. rewrite Hrow. reflexivity.
        + apply cell_val_add_other. exact Hne.
      - intros t. rewrite row_exists_add. split; [| tauto].
        intros [-> | Hr]; [| exact Hr]. unfold row_exists. rewrite Hrow. discriminate.
      - unfold cell_val. rewrite Hrow. reflexivity.
    Qed.

    Lemma write_inv_cells_eq α v σ0 σ1 :
      Step (li_lts E) {| te_tid := α; te_ev := InvEv (cell_write' α v) |} σ0 σ1 ->
      cells_eq σ0 σ1.
    Proof.
      intros Hstep. destruct (step_write_inv_shape _ _ _ _ Hstep) as [Hin (c & Hrow & ->) ].
      split.
      - intros t. destruct (Pos.eq_dec t α) as [-> | Hne].
        + rewrite cell_val_add_same. unfold cell_val. rewrite Hrow. reflexivity.
        + apply cell_val_add_other. exact Hne.
      - intros t. rewrite row_exists_add. split; [| tauto].
        intros [-> | Hr]; [| exact Hr]. unfold row_exists. rewrite Hrow. discriminate.
    Qed.

    (** No concrete error in the method: the actor is in the domain and its
        row exists; every scanned owner is in the domain. *)
    Lemma no_error_write α v :
      ⊨ Pgood α v ==>> ANoError {| te_tid := α; te_ev := InvEv (cell_write' α v) |}.
    Proof.
      intros [σ0 Δ0] [[ρc Hf] [_ [Hin _]]]. simpl in *.
      apply no_error_family; [exact Hin |]. apply (inv_dom _ _ _ Hf). exact Hin.
    Qed.

    Lemma no_error_read α β Pre :
      ThreadDomain.contains D β ->
      (⊨ Pre ==>> I) ->
      ⊨ Pre ==>> ANoError {| te_tid := α; te_ev := InvEv (cell_read' β) |}.
    Proof.
      intros Hin HPI [σ0 Δ0] Hpre. destruct (HPI _ Hpre) as [ρc Hf]. simpl in *.
      apply no_error_family; [exact Hin |]. apply (inv_dom _ _ _ Hf). exact Hin.
    Qed.

    (** * Rebuilding a possibility from its projections *)

    (** Choose, thread by thread over a finite list, a base entry for every
        entry of [π2]. *)
    Lemma build_base (Pb : tid -> option lin_state -> option lin_state -> Prop)
        (π2 : tmap lin_state) :
      (forall t, exists e0, Pb t (TMap.find t π2) e0) ->
      forall L : list tid, exists π0 : tmap lin_state,
        (forall t, In t L -> Pb t (TMap.find t π2) (TMap.find t π0)) /\
        (forall t, ~ In t L -> TMap.find t π0 = TMap.find t π2).
    Proof.
      intros Hex L. induction L as [| t L IH].
      - exists π2. split; [intros t [] | auto].
      - destruct IH as (π0 & HL & Hout).
        destruct (Hex t) as [e0 He0].
        exists (match e0 with
                | Some ls => TMap.add t ls π0
                | None => TMap.remove t π0
                end).
        split.
        + intros t' [Heq | Hin].
          * subst t'. destruct e0; [rewrite TMap.gss | rewrite TMap.grs]; exact He0.
          * destruct (Pos.eq_dec t' t) as [-> | Hne].
            -- destruct e0; [rewrite TMap.gss | rewrite TMap.grs]; exact He0.
            -- destruct e0; [rewrite TMap.gso by exact Hne | rewrite TMap.gro by exact Hne];
               apply HL; exact Hin.
        + intros t' Hnin.
          assert (Hne : t' <> t) by (intros ->; apply Hnin; left; reflexivity).
          assert (Hnin' : ~ In t' L) by (intros Hin; apply Hnin; right; exact Hin).
          destruct e0; [rewrite TMap.gso by exact Hne | rewrite TMap.gro by exact Hne];
            apply Hout; exact Hnin'.
    Qed.

    (** Replay the responses that separate a base map from [π2]. *)
    Lemma build_chain (ρ' : abstract_state) (π2 : tmap lin_state) :
      forall (L : list tid) (πs : tmap lin_state),
        (forall t, In t L ->
          TMap.find t πs = TMap.find t π2 \/
          exists w l, TMap.find t πs = Some (lini_token w) /\
            TMap.find t π2 = Some (linr_token w l) /\ ws_snapshot ρ' l) ->
        (forall t, ~ In t L -> TMap.find t πs = TMap.find t π2) ->
        exists πe, resp_chain ρ' πs πe /\ find_eq πe π2.
    Proof.
      intros L. induction L as [| t L IH]; intros πs HL Hout.
      - exists πs. split; [apply rt_refl |]. intros t. apply Hout. auto.
      - destruct (HL t (or_introl eq_refl)) as [Hsame | (w & l & Hs & Ht & Hsnap) ].
        + apply IH.
          * intros t' Hin. destruct (Pos.eq_dec t' t) as [-> | Hne]; [left; exact Hsame |].
            apply HL. right. exact Hin.
          * intros t' Hnin. destruct (Pos.eq_dec t' t) as [-> | Hne]; [exact Hsame |].
            apply Hout. intros [Heq | Hin]; [exact (Hne (eq_sym Heq)) | exact (Hnin Hin) ].
        + destruct (IH (TMap.add t (linr_token w l) πs)) as (πe & Hchain & Heq).
          * intros t' Hin. destruct (Pos.eq_dec t' t) as [-> | Hne].
            -- left. rewrite TMap.gss. symmetry. exact Ht.
            -- rewrite TMap.gso by exact Hne. apply HL. right. exact Hin.
          * intros t' Hnin. destruct (Pos.eq_dec t' t) as [-> | Hne].
            -- rewrite TMap.gss. symmetry. exact Ht.
            -- rewrite TMap.gso by exact Hne. apply Hout.
               intros [Heq | Hin]; [exact (Hne (eq_sym Heq)) | exact (Hnin Hin) ].
          * exists πe. split; [| exact Heq].
            eapply rt_trans; [| exact Hchain]. apply rt_step. exists t, w, l. auto.
    Qed.

    (** * The branching update at the cell write *)

    Record write_pre (α : tid) (v : A) (σ0 : concrete_state)
        (Δ0 : AbstractConfig (li_lts F)) (ρc : abstract_state) : Prop := {
      wp_facts : inv_facts σ0 Δ0 ρc;
      wp_inv : forall ρ π, Δ0 ρ π -> TMap.find α π = Some (inv_token v);
      wp_in : ThreadDomain.contains D α;
      wp_none : cell_val σ0 α = None
    }.

    Lemma wi_common α v σ0 Δ0 ρc (Hw : write_pre α v σ0 Δ0 ρc) :
      forall ρ π, write_image Δ0 α v ρ π -> ρ = TMap.add α v ρc.
    Proof.
      intros ρ π Hposs. inversion Hposs as [ρ0 π0 π' Hposs0 Hchain Hρ Hπ]; subst.
      rewrite (inv_common _ _ _ (wp_facts _ _ _ _ _ Hw) _ _ Hposs0). reflexivity.
    Qed.

    Lemma wi_proj_elim α v σ0 Δ0 ρc (Hw : write_pre α v σ0 Δ0 ρc) :
      forall t ols, proj_ac (write_image Δ0 α v) t ols ->
        (t = α /\ (ols = Some (lini_token v) \/
                   exists l, ols = Some (linr_token v l) /\ ws_snapshot (TMap.add α v ρc) l)) \/
        (t <> α /\ (proj_ac Δ0 t ols \/
                    exists w l, ols = Some (linr_token w l) /\
                      ws_snapshot (TMap.add α v ρc) l /\ proj_ac Δ0 t (Some (lini_token w)))).
    Proof.
      intros t ols (ρ' & π' & Hposs' & Hfind). revert Hfind.
      inversion Hposs' as [ρ0 π0 π'' Hposs0 Hchain Hρ Hπ]; subst. intros Hfind.
      pose proof (inv_common _ _ _ (wp_facts _ _ _ _ _ Hw) _ _ Hposs0) as Hρ0. subst ρ0.
      destruct (resp_chain_entry _ _ _ Hchain t) as [Hsame | (w & l & Hs & Ht & Hsnap) ].
      - destruct (Pos.eq_dec t α) as [-> | Hne].
        + left. split; [reflexivity |]. left.
          exact (eq_trans (eq_sym Hfind) (eq_trans Hsame (TMap.gss _ _ _))).
        + right. split; [exact Hne |]. left. exists ρc, π0. split; [exact Hposs0 |].
          exact (eq_sym (eq_trans (eq_sym Hfind) (eq_trans Hsame (TMap.gso _ _ Hne)))).
      - destruct (Pos.eq_dec t α) as [-> | Hne].
        + left. split; [reflexivity |]. right.
          rewrite TMap.gss in Hs. apply some_inj, lini_token_inj in Hs. subst w.
          exists l. rewrite <- Hfind. auto.
        + right. split; [exact Hne |]. right.
          rewrite TMap.gso in Hs by exact Hne.
          exists w, l. rewrite <- Hfind. split; [exact Ht |]. split; [exact Hsnap |].
          exists ρc, π0. auto.
    Qed.

    Lemma wi_proj_old α v σ0 Δ0 ρc (Hw : write_pre α v σ0 Δ0 ρc) :
      forall t ols, t <> α -> proj_ac Δ0 t ols -> proj_ac (write_image Δ0 α v) t ols.
    Proof.
      intros t ols Hne (ρ & π & Hposs & Hfind).
      exists (TMap.add α v ρ), (TMap.add α (lini_token v) π). split.
      - econstructor; [exact Hposs | apply rt_refl].
      - rewrite TMap.gso by exact Hne. exact Hfind.
    Qed.

    Lemma wi_proj_lini α v (Δ0 : AbstractConfig (li_lts F)) :
      proj_ac (write_image Δ0 α v) α (Some (lini_token v)).
    Proof.
      destruct (ac_nonempty Δ0) as (ρ & π & Hposs).
      exists (TMap.add α v ρ), (TMap.add α (lini_token v) π). split.
      - econstructor; [exact Hposs | apply rt_refl].
      - apply TMap.gss.
    Qed.

    Lemma wi_proj_branch α v σ0 Δ0 ρc (Hw : write_pre α v σ0 Δ0 ρc) :
      forall t w l, proj_ac (write_image Δ0 α v) t (Some (lini_token w)) ->
        ws_snapshot (TMap.add α v ρc) l ->
        proj_ac (write_image Δ0 α v) t (Some (linr_token w l)).
    Proof.
      intros t w l (ρ' & π' & Hposs' & Hfind) Hsnap. revert Hfind.
      inversion Hposs' as [ρ0 π0 π'' Hposs0 Hchain Hρ Hπ]; subst. intros Hfind.
      pose proof (inv_common _ _ _ (wp_facts _ _ _ _ _ Hw) _ _ Hposs0) as Hρ0. subst ρ0.
      exists (TMap.add α v ρc), (TMap.add t (linr_token w l) π'). split; [| apply TMap.gss].
      econstructor; [exact Hposs0 |].
      eapply resp_chain_extend; eauto.
    Qed.

    Lemma wi_closed α v σ0 Δ0 ρc (Hw : write_pre α v σ0 Δ0 ρc) :
      forall π2, (forall t, proj_ac (write_image Δ0 α v) t (TMap.find t π2)) ->
        exists π3, find_eq π3 π2 /\ write_image Δ0 α v (TMap.add α v ρc) π3.
    Proof.
      intros π2 Hall.
      pose proof (wp_facts _ _ _ _ _ Hw) as Hf.
      pose proof (wp_in _ _ _ _ _ Hw) as HinD.
      set (Pb := fun (t : tid) (e' e0 : option lin_state) =>
        (t = α /\ e0 = Some (inv_token v)) \/
        (t <> α /\ e0 = e' /\ proj_ac Δ0 t e') \/
        (t <> α /\ exists w l, e' = Some (linr_token w l) /\ e0 = Some (lini_token w) /\
           ws_snapshot (TMap.add α v ρc) l /\ proj_ac Δ0 t (Some (lini_token w)))).
      assert (Hex : forall t, exists e0, Pb t (TMap.find t π2) e0).
      { intros t. destruct (wi_proj_elim _ _ _ _ _ Hw t _ (Hall t))
          as [[Heqt _] | [Hne [Hold | (w & l & He & Hsnap & Hlini) ] ] ].
        - exists (Some (inv_token v)). left. auto.
        - exists (TMap.find t π2). right; left. auto.
        - exists (Some (lini_token w)). right; right. split; [exact Hne |]. exists w, l. auto. }
      destruct (build_base Pb π2 Hex (ThreadDomain.threads D)) as (π0 & HL & Hout).
      assert (Hπ0 : forall t, proj_ac Δ0 t (TMap.find t π0)).
      { intros t. destruct (in_dec Pos.eq_dec t (ThreadDomain.threads D)) as [Hin | Hnin].
        - destruct (HL t Hin) as [[Heqt He0] | [[_ [He0 Hp] ] | [_ (w & l & _ & He0 & _ & Hp) ] ] ].
          + subst t. rewrite He0. destruct (ac_nonempty Δ0) as (ρ & π & Hposs).
            exists ρ, π. split; [exact Hposs |]. exact (wp_inv _ _ _ _ _ Hw _ _ Hposs).
          + rewrite He0. exact Hp.
          + rewrite He0. exact Hp.
        - rewrite (Hout t Hnin).
          destruct (wi_proj_elim _ _ _ _ _ Hw t _ (Hall t))
            as [[Heqt _] | [Hne [Hold | (w & l & He & Hsnap & Hlini) ] ] ].
          + exfalso. subst t. apply Hnin. exact HinD.
          + exact Hold.
          + exfalso. apply Hnin.
            destruct (inv_lini _ _ _ Hf _ _ Hlini) as [Hc _].
            apply (inv_dom _ _ _ Hf). unfold row_exists. intros Hn.
            unfold cell_val in Hc. rewrite Hn in Hc. discriminate. }
      destruct (inv_closed _ _ _ Hf π0 Hπ0) as (π0' & Heq0 & Hposs0).
      destruct (build_chain (TMap.add α v ρc) π2 (ThreadDomain.threads D)
                  (TMap.add α (lini_token v) π0')) as (πe & Hchain & Heqe).
      { intros t Hin. destruct (Pos.eq_dec t α) as [-> | Hne].
        - rewrite TMap.gss.
          destruct (wi_proj_elim _ _ _ _ _ Hw α _ (Hall α))
            as [[_ [Hl | (l & Hl & Hsnap) ] ] | [Hne _] ]; [left; symmetry; exact Hl | | congruence].
          right. exists v, l. auto.
        - rewrite TMap.gso by exact Hne. rewrite Heq0.
          destruct (HL t Hin) as [[Heq _] | [[_ [He0 _] ] | [_ (w & l & He' & He0 & Hsnap & _) ] ] ];
            [congruence | left; exact He0 |].
          right. exists w, l. rewrite He0, He'. auto. }
      { intros t Hnin. assert (Hne : t <> α) by (intros ->; apply Hnin; exact HinD).
        rewrite TMap.gso by exact Hne. rewrite Heq0. apply Hout. exact Hnin. }
      exists πe. split; [exact Heqe |].
      apply WriteImage with (π := π0'); [exact Hposs0 | exact Hchain].
    Qed.

    Lemma wi_inv_facts α v σ0 Δ0 ρc (Hw : write_pre α v σ0 Δ0 ρc) :
      inv_facts (TMap.add α (Idle (Some v)) σ0) (write_image Δ0 α v) (TMap.add α v ρc).
    Proof.
      pose proof (wp_facts _ _ _ _ _ Hw) as Hf.
      pose proof (wp_in _ _ _ _ _ Hw) as HinD.
      pose proof (wp_none _ _ _ _ _ Hw) as Hnone.
      constructor.
      - apply (wi_common _ _ _ _ _ Hw).
      - intros t. destruct (Pos.eq_dec t α) as [-> | Hne].
        + rewrite TMap.gss, cell_val_add_same. reflexivity.
        + rewrite TMap.gso by exact Hne. rewrite cell_val_add_other by exact Hne.
          apply (inv_cells _ _ _ Hf).
      - apply (wi_closed _ _ _ _ _ Hw).
      - intros t. rewrite row_exists_add. split.
        + intros [-> | Hr]; [exact HinD | apply (inv_dom _ _ _ Hf); exact Hr].
        + intros Hin. destruct (Pos.eq_dec t α) as [-> | Hne]; [left; reflexivity | right].
          apply (inv_dom _ _ _ Hf). exact Hin.
      - intros t w Hp.
        destruct (wi_proj_elim _ _ _ _ _ Hw t _ Hp)
          as [[Heqt [Hl | (l & Hl & _) ] ] | [Hne [Hold | (w' & l & Hl & _ & _) ] ] ].
        + subst t. apply some_inj, lini_token_inj in Hl. subst w.
          split; [rewrite cell_val_add_same; reflexivity |].
          intros l Hsnap. apply (wi_proj_branch _ _ _ _ _ Hw); [exact Hp | exact Hsnap].
        + discriminate Hl.
        + destruct (inv_lini _ _ _ Hf _ _ Hold) as [Hc _].
          split; [rewrite cell_val_add_other by exact Hne; exact Hc |].
          intros l Hsnap. apply (wi_proj_branch _ _ _ _ _ Hw); [exact Hp | exact Hsnap].
        + discriminate Hl.
      - intros t w l Hp.
        destruct (wi_proj_elim _ _ _ _ _ Hw t _ Hp)
          as [[Heqt [Hl | (l' & Hl & Hsnap) ] ] | [Hne [Hold | (w' & l' & Hl & Hsnap & Hlini) ] ] ].
        + discriminate Hl.
        + subst t. apply some_inj, linr_token_inj in Hl. destruct Hl as [-> ->].
          split; [rewrite cell_val_add_same; reflexivity |].
          intros x Hx. apply (proj1 (Hsnap x)). exact Hx.
        + destruct (inv_linr _ _ _ Hf _ _ _ Hold) as [Hc Hvals].
          split; [rewrite cell_val_add_other by exact Hne; exact Hc |].
          intros x Hx. apply ws_value_add_mono; [| apply Hvals; exact Hx].
          rewrite (inv_cells _ _ _ Hf). exact Hnone.
        + apply some_inj, linr_token_inj in Hl. destruct Hl as [-> ->].
          destruct (inv_lini _ _ _ Hf _ _ Hlini) as [Hc _].
          split; [rewrite cell_val_add_other by exact Hne; exact Hc |].
          intros x Hx. apply (proj1 (Hsnap x)). exact Hx.
    Qed.

    Lemma wi_G α v σ0 Δ0 ρc (Hw : write_pre α v σ0 Δ0 ρc) :
      G_core α (σ0, Δ0) (mk (TMap.add α (Idle (Some v)) σ0) (write_image Δ0 α v)).
    Proof.
      pose proof (wp_facts _ _ _ _ _ Hw) as Hf.
      pose proof (wp_in _ _ _ _ _ Hw) as HinD.
      pose proof (wp_none _ _ _ _ _ Hw) as Hnone.
      constructor.
      - intros t Hne. constructor; unfold proj; simpl.
        + intros ols Hp. apply (wi_proj_old _ _ _ _ _ Hw); assumption.
        + intros ols Hp. destruct (wi_proj_elim _ _ _ _ _ Hw t _ Hp) as [[Heqt _] | [_ Hc] ];
            [congruence |].
          destruct Hc as [Hold | (w & l & He & _ & Hl) ]; [left; exact Hold |].
          right. exists w, l. auto.
        + apply cell_val_add_other. exact Hne.
      - intros t x Hc. simpl in *. destruct (Pos.eq_dec t α) as [-> | Hne].
        + rewrite Hnone in Hc. discriminate.
        + rewrite cell_val_add_other by exact Hne. exact Hc.
      - intros (ρ & π & w & Hposs & Hfind & Herr). exfalso. simpl in *.
        destruct Herr as [Hout | Hdouble]; [exact (Hout HinD) |].
        apply Hdouble. rewrite (inv_common _ _ _ Hf _ _ Hposs). rewrite (inv_cells _ _ _ Hf). exact Hnone.
    Qed.

    Lemma wi_Written α v σ0 Δ0 ρc (Hw : write_pre α v σ0 Δ0 ρc) :
      Written α v (mk (TMap.add α (Idle (Some v)) σ0) (write_image Δ0 α v)).
    Proof.
      split; [exists (TMap.add α v ρc); apply (wi_inv_facts _ _ _ _ _ Hw) |].
      split; [apply wi_proj_lini |].
      split; [| exact (wp_in _ _ _ _ _ Hw) ].
      intros w Hp. destruct (wi_proj_elim _ _ _ _ _ Hw α _ Hp)
        as [[_ [Hl | (l & Hl & _) ] ] | [Hne _] ]; [discriminate Hl | discriminate Hl | exact (Hne eq_refl) ].
    Qed.

    Lemma write_res_update α v :
      PUpdate (G α) {| te_tid := α; te_ev := ResEv (cell_write' α v) tt |}
        (Pgood α v) (Written α v).
    Proof.
      intros σ0 Δ0 [[ρc Hf] [Hinv [HinD Hnone] ] ] σ1 Hstep. simpl in *.
      destruct (step_write_res_shape _ _ _ _ Hstep) as [_ (c & Hrow & ->) ].
      pose (Hw := {| wp_facts := Hf; wp_inv := Hinv; wp_in := HinD; wp_none := Hnone |}
                  : write_pre α v σ0 Δ0 ρc).
      exists (write_image Δ0 α v). split; [| split].
      - apply write_image_subset_steps. intros ρ π Hposs. split; [| exact (Hinv _ _ Hposs) ].
        rewrite (inv_common _ _ _ Hf _ _ Hposs). rewrite (inv_cells _ _ _ Hf). exact Hnone.
      - apply (wi_Written _ _ _ _ _ Hw).
      - apply (wi_G _ _ _ _ _ Hw).
    Qed.

    Lemma write_inv_update α v :
      PUpdate (G α) {| te_tid := α; te_ev := InvEv (cell_write' α v) |}
        (Pgood α v) (Pgood α v).
    Proof.
      intros σ0 Δ0 [HI [Hinv [HinD Hnone] ] ] σ1 Hstep. simpl in *.
      pose proof (write_inv_cells_eq _ _ _ _ Hstep) as Heq.
      exists Δ0. split; [apply ac_steps_refl |]. split.
      - split; [eapply I_cells_eq; eauto |]. split; [exact Hinv |]. split; [exact HinD |].
        unfold CellNone. simpl. rewrite (proj1 Heq). exact Hnone.
      - apply G_core_same_config. exact Heq.
    Qed.

    (** * The selection update at the loop exit *)

    Record select_pre (α : tid) (v : A) (l : list A) (σ0 : concrete_state)
        (Δ0 : AbstractConfig (li_lts F)) (ρc : abstract_state) : Prop := {
      sp_facts : inv_facts σ0 Δ0 ρc;
      sp_branch : proj_ac Δ0 α (Some (linr_token v l));
      sp_noinv : forall w, ~ proj_ac Δ0 α (Some (inv_token w))
    }.

    Definition select_config α v l σ0 Δ0 ρc (Hw : select_pre α v l σ0 Δ0 ρc) :
        AbstractConfig (li_lts F) :=
      ac_restrict Δ0 α (linr_token v l) (sp_branch _ _ _ _ _ _ Hw).

    Lemma sel_member α v l σ0 Δ0 ρc (Hw : select_pre α v l σ0 Δ0 ρc) ρ π :
      select_config α v l σ0 Δ0 ρc Hw ρ π <-> (Δ0 ρ π /\ TMap.find α π = Some (linr_token v l)).
    Proof. reflexivity. Qed.

    Lemma sel_proj_keep α v l σ0 Δ0 ρc (Hw : select_pre α v l σ0 Δ0 ρc) :
      forall t ols, t <> α -> proj_ac Δ0 t ols -> proj_ac (select_config α v l σ0 Δ0 ρc Hw) t ols.
    Proof.
      intros t ols Hne (ρ & π & Hposs & Hfind).
      pose proof (sp_facts _ _ _ _ _ _ Hw) as Hf.
      assert (Hall : forall t', proj_ac Δ0 t' (TMap.find t' (TMap.add α (linr_token v l) π))).
      { intros t'. destruct (Pos.eq_dec t' α) as [-> | Hne'].
        - rewrite TMap.gss. exact (sp_branch _ _ _ _ _ _ Hw).
        - rewrite TMap.gso by exact Hne'. exists ρ, π. auto. }
      destruct (inv_closed _ _ _ Hf _ Hall) as (π' & Heq & Hposs').
      exists ρc, π'. split.
      - apply sel_member. split; [exact Hposs' |]. rewrite Heq, TMap.gss. reflexivity.
      - rewrite Heq, TMap.gso by exact Hne. exact Hfind.
    Qed.

    Lemma sel_proj_elim α v l σ0 Δ0 ρc (Hw : select_pre α v l σ0 Δ0 ρc) :
      forall t ols, proj_ac (select_config α v l σ0 Δ0 ρc Hw) t ols ->
        proj_ac Δ0 t ols /\ (t = α -> ols = Some (linr_token v l)).
    Proof.
      intros t ols (ρ & π & Hposs & Hfind). apply sel_member in Hposs. destruct Hposs as [Hposs Hα].
      split; [exists ρ, π; auto |]. intros ->. rewrite <- Hfind. exact Hα.
    Qed.

    Lemma sel_inv_facts α v l σ0 Δ0 ρc (Hw : select_pre α v l σ0 Δ0 ρc) :
      inv_facts σ0 (select_config α v l σ0 Δ0 ρc Hw) ρc.
    Proof.
      pose proof (sp_facts _ _ _ _ _ _ Hw) as Hf.
      constructor.
      - intros ρ π Hposs. apply sel_member in Hposs. exact (inv_common _ _ _ Hf _ _ (proj1 Hposs)).
      - apply (inv_cells _ _ _ Hf).
      - intros π2 Hall.
        assert (Hall0 : forall t, proj_ac Δ0 t (TMap.find t π2)).
        { intros t. apply (sel_proj_elim _ _ _ _ _ _ Hw). apply Hall. }
        destruct (inv_closed _ _ _ Hf _ Hall0) as (π3 & Heq & Hposs).
        exists π3. split; [exact Heq |]. apply sel_member. split; [exact Hposs |].
        rewrite Heq. apply (sel_proj_elim _ _ _ _ _ _ Hw α _ (Hall α)). reflexivity.
      - apply (inv_dom _ _ _ Hf).
      - intros t w Hp. destruct (sel_proj_elim _ _ _ _ _ _ Hw _ _ Hp) as [Hold Hα].
        assert (Hne : t <> α) by (intros ->; discriminate (Hα eq_refl)).
        destruct (inv_lini _ _ _ Hf _ _ Hold) as [Hc Hbr]. split; [exact Hc |].
        intros l' Hsnap. apply (sel_proj_keep _ _ _ _ _ _ Hw); [exact Hne |]. apply Hbr. exact Hsnap.
      - intros t w l' Hp. destruct (sel_proj_elim _ _ _ _ _ _ Hw _ _ Hp) as [Hold _].
        apply (inv_linr _ _ _ Hf). exact Hold.
    Qed.

    Lemma sel_G α v l σ0 Δ0 ρc (Hw : select_pre α v l σ0 Δ0 ρc) :
      G_core α (σ0, Δ0) (σ0, select_config α v l σ0 Δ0 ρc Hw).
    Proof.
      constructor.
      - intros t Hne. constructor; unfold proj; simpl.
        + intros ols Hp. apply (sel_proj_keep _ _ _ _ _ _ Hw); assumption.
        + intros ols Hp. left. apply (sel_proj_elim _ _ _ _ _ _ Hw _ _ Hp).
        + reflexivity.
      - intros t x Hc. exact Hc.
      - intros (ρ & π & w & Hposs & Hfind & Herr). exfalso. simpl in *.
        apply (sp_noinv _ _ _ _ _ _ Hw w). exists ρ, π. auto.
    Qed.

    Lemma select_update α v st :
      PUpdateId (G α)
        (LoopInv α v st //\\ ⌜set_eqb A_eq_dec (fst st) (snd st) = true⌝)
        (Qpost α v (fst st)).
    Proof.
      intros σ0 Δ0 [[[HI [Hlini [Hno HinD] ] ] [Hcol Hcase] ] Heqb]. simpl in *.
      destruct HI as [ρc Hf].
      destruct Hcase as [[Hnil Hin] | [ρp [[Hbr Hcells] [Hunder Hcovers] ] ] ].
      - exfalso. rewrite Hnil in Heqb. rewrite (set_eqb_nil_false _ _ Hin) in Heqb. discriminate.
      - assert (Hsnap : ws_snapshot ρp (fst st)).
        { intros x. split; intros Hx.
          - apply Hunder. apply (set_eqb_true _ _ Heqb). exact Hx.
          - apply Hcovers. exact Hx. }
        pose (Hw := {| sp_facts := Hf; sp_branch := Hbr _ Hsnap; sp_noinv := Hno |}
                    : select_pre α v (fst st) σ0 Δ0 ρc).
        exists (select_config _ _ _ _ _ _ Hw).
        split; [apply ac_restrict_subset_steps |]. split.
        + split; [exists ρc; apply (sel_inv_facts _ _ _ _ _ _ Hw) |].
          intros ρ π Hposs. apply sel_member in Hposs. apply Hposs.
        + apply (sel_G _ _ _ _ _ _ Hw).
    Qed.

    (** * Reads *)

    Lemma read_inv_update α β (Pre : assertion) :
      (forall σ0 σ1 Δ0, cells_eq σ0 σ1 -> Pre (σ0, Δ0) -> Pre (σ1, Δ0)) ->
      PUpdate (G α) {| te_tid := α; te_ev := InvEv (cell_read' β) |} Pre Pre.
    Proof.
      intros Hins σ0 Δ0 Hpre σ1 Hstep.
      pose proof (read_inv_cells_eq _ _ _ _ Hstep) as Heq.
      exists Δ0. split; [apply ac_steps_refl |].
      split; [eapply Hins; eauto | apply G_core_same_config; exact Heq].
    Qed.

    Lemma read_res_update α β (Pre : assertion) (Post : option A -> assertion) :
      (forall σ0 σ1 Δ0 r, cells_eq σ0 σ1 -> cell_val σ0 β = r ->
        Pre (σ0, Δ0) -> Post r (σ1, Δ0)) ->
      forall r, PUpdate (G α) {| te_tid := α; te_ev := ResEv (cell_read' β) r |} Pre (Post r).
    Proof.
      intros Hins r σ0 Δ0 Hpre σ1 Hstep.
      destruct (read_res_cells_eq _ _ _ _ _ Hstep) as [Heq Hr].
      exists Δ0. split; [apply ac_steps_refl |].
      split; [eapply Hins; eauto | apply G_core_same_config; exact Heq].
    Qed.

    (** * Invocation and return bookkeeping *)

    Lemma ginv_I t f : ⊨ Ginv t f ⊚ I ==>> I.
    Proof.
      intros s' [s [[ρc Hf] [Hσ [Hnone HΔ] ] ] ].
      exists ρc. constructor.
      - intros ρ π Hposs. apply HΔ in Hposs. inversion Hposs as [ρ0 π0 Hposs0 Hρ Hπ]; subst.
        exact (inv_common _ _ _ Hf _ _ Hposs0).
      - intros t'. rewrite <- Hσ. apply (inv_cells _ _ _ Hf).
      - intros π2 Hall.
        assert (Hall1 : forall t', proj_ac (Δ s) t' (TMap.find t' (TMap.remove t π2))).
        { intros t'. destruct (Pos.eq_dec t' t) as [-> | Hne].
          - rewrite TMap.grs. destruct (ac_nonempty (Δ s)) as (ρ & π & Hposs).
            exists ρ, π. split; [exact Hposs | exact (Hnone _ _ Hposs) ].
          - rewrite TMap.gro by exact Hne.
            destruct (Hall t') as (ρ & π & Hposs & Hfind). apply HΔ in Hposs.
            inversion Hposs; subst. exists ρ, π0. split; [assumption |].
            rewrite <- Hfind, TMap.gso by exact Hne. reflexivity. }
        destruct (inv_closed _ _ _ Hf _ Hall1) as (π1 & Heq & Hposs1).
        exists (TMap.add t (ls_inv f) π1). split.
        + intros t'. destruct (Pos.eq_dec t' t) as [-> | Hne].
          * rewrite TMap.gss. destruct (Hall t) as (ρ & π & Hposs & Hfind). apply HΔ in Hposs.
            rewrite <- Hfind. symmetry. eapply ac_inv_find_eq. exact Hposs.
          * rewrite TMap.gso by exact Hne. rewrite Heq, TMap.gro by exact Hne. reflexivity.
        + apply HΔ. constructor. exact Hposs1.
      - intros t'. rewrite <- Hσ. apply (inv_dom _ _ _ Hf).
      - intros t' w (ρ & π & Hposs & Hfind). apply HΔ in Hposs.
        inversion Hposs as [ρ0 π0 Hposs0 Hρ Hπ]; subst.
        assert (Hne : t' <> t) by (intros ->; rewrite TMap.gss in Hfind; discriminate).
        rewrite TMap.gso in Hfind by exact Hne.
        destruct (inv_lini _ _ _ Hf t' w) as [Hc Hbr]; [exists ρ, π0; auto |].
        split; [rewrite <- Hσ; exact Hc |].
        intros l Hsnap. destruct (Hbr l Hsnap) as (ρ1 & π1 & Hposs1 & Hfind1).
        exists ρ1, (TMap.add t (ls_inv f) π1). split; [apply HΔ; constructor; exact Hposs1 |].
        rewrite TMap.gso by exact Hne. exact Hfind1.
      - intros t' w l (ρ & π & Hposs & Hfind). apply HΔ in Hposs.
        inversion Hposs as [ρ0 π0 Hposs0 Hρ Hπ]; subst.
        assert (Hne : t' <> t) by (intros ->; rewrite TMap.gss in Hfind; discriminate).
        rewrite TMap.gso in Hfind by exact Hne.
        destruct (inv_linr _ _ _ Hf t' w l) as [Hc Hvals]; [exists ρ, π0; auto |].
        split; [rewrite <- Hσ; exact Hc | exact Hvals].
    Qed.

    Lemma gret_I t f ret : ⊨ Gret t f ret ⊚ (I //\\ ALin t (ls_linr f ret)) ==>> I.
    Proof.
      intros s' [s [[[ρc Hf] Hlin] [Hσ [Hall HΔ] ] ] ].
      exists ρc. constructor.
      - intros ρ π Hposs. apply HΔ in Hposs. inversion Hposs as [ρ0 π0 Hposs0 Hρ Hπ]; subst.
        exact (inv_common _ _ _ Hf _ _ Hposs0).
      - intros t'. rewrite <- Hσ. apply (inv_cells _ _ _ Hf).
      - intros π2 Hallp.
        assert (Hall1 : forall t', proj_ac (Δ s) t' (TMap.find t' (TMap.add t (ls_linr f ret) π2))).
        { intros t'. destruct (Pos.eq_dec t' t) as [-> | Hne].
          - rewrite TMap.gss. destruct (ac_nonempty (Δ s)) as (ρ & π & Hposs).
            exists ρ, π. split; [exact Hposs | exact (Hall _ _ Hposs) ].
          - rewrite TMap.gso by exact Hne.
            destruct (Hallp t') as (ρ & π & Hposs & Hfind). apply HΔ in Hposs.
            inversion Hposs; subst. exists ρ, π0. split; [assumption |].
            rewrite <- Hfind, TMap.gro by exact Hne. reflexivity. }
        destruct (inv_closed _ _ _ Hf _ Hall1) as (π1 & Heq & Hposs1).
        exists (TMap.remove t π1). split.
        + intros t'. destruct (Pos.eq_dec t' t) as [-> | Hne].
          * rewrite TMap.grs. destruct (Hallp t) as (ρ & π & Hposs & Hfind). apply HΔ in Hposs.
            rewrite <- Hfind. symmetry. eapply ac_res_find_eq. exact Hposs.
          * rewrite TMap.gro by exact Hne. rewrite Heq, TMap.gso by exact Hne. reflexivity.
        + apply HΔ. constructor. exact Hposs1.
      - intros t'. rewrite <- Hσ. apply (inv_dom _ _ _ Hf).
      - intros t' w (ρ & π & Hposs & Hfind). apply HΔ in Hposs.
        inversion Hposs as [ρ0 π0 Hposs0 Hρ Hπ]; subst.
        assert (Hne : t' <> t) by (intros ->; rewrite TMap.grs in Hfind; discriminate).
        rewrite TMap.gro in Hfind by exact Hne.
        destruct (inv_lini _ _ _ Hf t' w) as [Hc Hbr]; [exists ρ, π0; auto |].
        split; [rewrite <- Hσ; exact Hc |].
        intros l Hsnap. destruct (Hbr l Hsnap) as (ρ1 & π1 & Hposs1 & Hfind1).
        exists ρ1, (TMap.remove t π1). split; [apply HΔ; constructor; exact Hposs1 |].
        rewrite TMap.gro by exact Hne. exact Hfind1.
      - intros t' w l (ρ & π & Hposs & Hfind). apply HΔ in Hposs.
        inversion Hposs as [ρ0 π0 Hposs0 Hρ Hπ]; subst.
        assert (Hne : t' <> t) by (intros ->; rewrite TMap.grs in Hfind; discriminate).
        rewrite TMap.gro in Hfind by exact Hne.
        destruct (inv_linr _ _ _ Hf t' w l) as [Hc Hvals]; [exists ρ, π0; auto |].
        split; [rewrite <- Hσ; exact Hc | exact Hvals].
    Qed.

    Lemma ginv_P α v : ⊨ Ginv α (ws_op v) ⊚ I ==>> P α v.
    Proof.
      intros s' Hc. pose proof (ginv_I _ _ _ Hc) as HI'.
      destruct Hc as [s [[ρc Hf] [Hσ [Hnone HΔ] ] ] ].
      assert (HALin : ALin α (inv_token v) s').
      { intros ρ π Hposs. apply HΔ in Hposs. eapply ac_inv_find_eq. exact Hposs. }
      destruct (classic (ThreadDomain.contains D α /\ cell_val (σ s') α = None))
        as [[HinD Hc] | Hbad].
      - left. split; [exact HI' |]. split; [exact HALin |]. split; [exact HinD | exact Hc].
      - right. split; [exact HI' |].
        destruct (ac_nonempty (Δ s')) as (ρ & π & Hposs).
        exists α, ρ, π, v. split; [exact Hposs |]. split; [exact (HALin _ _ Hposs) |].
        destruct HI' as [ρc' Hf']. rewrite (inv_common _ _ _ Hf' _ _ Hposs).
        rewrite (inv_cells _ _ _ Hf').
        destruct (classic (ThreadDomain.contains D α)) as [HinD | Hout]; [right | left; exact Hout].
        intros Hc. apply Hbad. split; [exact HinD | exact Hc].
    Qed.

    (** * Rely/guarantee side conditions *)

    Lemma G_core_refl actor s : G_core actor s s.
    Proof.
      constructor.
      - intros t _. constructor; auto.
      - auto.
      - auto.
    Qed.

    Lemma ginv_G actor f s s' : Ginv actor f s s' -> G_core actor s s'.
    Proof.
      intros [Hσ [Hnone HΔ] ]. constructor.
      - intros t Hne. constructor; unfold proj.
        + intros ols (ρ & π & Hposs & Hfind). exists ρ, (TMap.add actor (ls_inv f) π).
          split; [apply HΔ; constructor; exact Hposs |]. rewrite TMap.gso by exact Hne. exact Hfind.
        + intros ols (ρ & π & Hposs & Hfind). left. apply HΔ in Hposs. revert Hfind.
          inversion Hposs as [ρ0 π0 Hposs0 Hρ Hπ]; subst. intros Hfind.
          exists ρ, π0. split; [exact Hposs0 |].
          rewrite <- Hfind, TMap.gso by exact Hne. reflexivity.
        + rewrite Hσ. reflexivity.
      - intros t x. rewrite Hσ. auto.
      - intros (ρ & π & w & Hposs & Hfind & _). exfalso.
        rewrite (Hnone _ _ Hposs) in Hfind. discriminate.
    Qed.

    Lemma gret_G actor f ret s s' : Gret actor f ret s s' -> G_core actor s s'.
    Proof.
      intros [Hσ [Hall HΔ] ]. constructor.
      - intros t Hne. constructor; unfold proj.
        + intros ols (ρ & π & Hposs & Hfind). exists ρ, (TMap.remove actor π).
          split; [apply HΔ; constructor; exact Hposs |]. rewrite TMap.gro by exact Hne. exact Hfind.
        + intros ols (ρ & π & Hposs & Hfind). left. apply HΔ in Hposs. revert Hfind.
          inversion Hposs as [ρ0 π0 Hposs0 Hρ Hπ]; subst. intros Hfind.
          exists ρ, π0. split; [exact Hposs0 |].
          rewrite <- Hfind, TMap.gro by exact Hne. reflexivity.
        + rewrite Hσ. reflexivity.
      - intros t x. rewrite Hσ. auto.
      - intros (ρ & π & w & Hposs & Hfind & _). exfalso.
        rewrite (Hall _ _ Hposs) in Hfind. discriminate.
    Qed.

    Lemma rg_compatible t1 t2 :
      t1 <> t2 -> (I ⊓ (G t1 ∪ (GINV t1 ∪ GRET t1 ∪ GId)) ⊆ R t2)%RGRelation.
    Proof.
      intros Hne s s' [[HG | [[Hinv | Hret] | Hid] ] _]; exists t1; (split; [exact Hne |]).
      - exact HG.
      - destruct Hinv as [f Hinv]. eapply ginv_G. exact Hinv.
      - destruct Hret as [f [ret Hret] ]. eapply gret_G. exact Hret.
      - unfold GId in Hid. subst s'. apply G_core_refl.
    Qed.

    Lemma valid_rg t : RGISimulationSet.RGISimulation.ValidRGI (R t) (G t) I t.
    Proof.
      constructor. intros s s' HR HI'. apply R_other_view in HR. split.
      - intros Hall ρ' π' Hposs'.
        destruct (ov_new _ _ _ HR _ (proj_ac_elements _ _ _ t Hposs'))
          as [ (ρ & π & Hposs & Hfind) | (w & l & _ & (ρ & π & Hposs & Hfind)) ].
        + rewrite <- Hfind. exact (Hall _ _ Hposs).
        + exfalso. rewrite (Hall _ _ Hposs) in Hfind. discriminate.
      - intros Hall ρ π Hposs.
        destruct (ov_keep _ _ _ HR _ (proj_ac_elements _ _ _ t Hposs)) as (ρ' & π' & Hposs' & Hfind).
        rewrite <- Hfind. exact (Hall _ _ Hposs').
    Qed.

    (** * The method triple *)

    Lemma scanned_in_domain α v old β remaining acc :
      ⊨ ScanInv α v old (β :: remaining) acc ==>> ⌜ThreadDomain.contains D β⌝.
    Proof.
      intros s [_ [_ [ρp [_ [_ (done & Hsplit & _) ] ] ] ] ].
      unfold ThreadDomain.contains. rewrite Hsplit. apply in_or_app. right. left. reflexivity.
    Qed.

    Lemma scan_step_triple α v old β remaining acc :
      [li_lts E, li_lts F, R α, G α, I, α] ⊢
        {{ ScanInv α v old (β :: remaining) acc }}
        scan_step A_eq_dec D acc β
        {{ fun acc' => ScanInv α v old remaining acc' }}.
    Proof.
      unfold scan_step.
      eapply provable_vis_safe with
        (P' := ScanInv α v old (β :: remaining) acc)
        (Q' := fun r => ScanInv α v old remaining
                 (match r with Some x => set_add A_eq_dec x acc | None => acc end)).
      - intros s Hs. apply (no_error_read α β (ScanInv α v old (β :: remaining) acc));
          [exact (scanned_in_domain _ _ _ _ _ _ _ Hs) | apply ScanInv_I | exact Hs].
      - apply ScanInv_I.
      - intros r. apply ScanInv_I.
      - apply stable_ScanInv.
      - intros r. apply stable_ScanInv.
      - apply read_inv_update. intros σ0 σ1 Δ0 Heq Hpre. eapply ScanInv_cells_eq; eauto.
      - intros r.
        apply (read_res_update α β (ScanInv α v old (β :: remaining) acc)
          (fun r => ScanInv α v old remaining
             (match r with Some x => set_add A_eq_dec x acc | None => acc end))).
        intros σ0 σ1 Δ0 r' Heq Hr Hpre.
        apply (ScanInv_cells_eq _ _ _ _ _ σ0 σ1 Δ0 Heq).
        destruct Hpre as [Hw [Hcol [ρp [Hfr [Hunder (done & Hsplit & Hcov) ] ] ] ] ].
        split; [exact Hw |]. split.
        + intros x Hx. destruct r' as [y |]; [| apply Hcol; exact Hx].
          apply set_add_iff in Hx. destruct Hx as [-> | Hx]; [| apply Hcol; exact Hx].
          exists β. exact Hr.
        + exists ρp. split; [exact Hfr |]. split; [exact Hunder |].
          exists (done ++ β :: nil). split; [rewrite <- app_assoc; exact Hsplit |].
          intros γ x Hγ Hfindγ. apply in_app_or in Hγ.
          destruct Hγ as [Hγ | [Heq' | [] ] ].
          * destruct r'; [apply set_add_iff; right |]; apply (Hcov γ x Hγ Hfindγ).
          * subst γ. destruct Hfr as [_ Hcells].
            specialize (Hcells β x Hfindγ).
            assert (Hr' : r' = Some x) by (rewrite <- Hr; exact Hcells). rewrite Hr'.
            apply set_add_iff. left. reflexivity.
      - intros r. apply provable_ret_safe; [apply ImplRefl | apply ScanInv_I | apply stable_ScanInv].
    Qed.

    Lemma scan_triple α v old :
      [li_lts E, li_lts F, R α, G α, I, α] ⊢
        {{ ScanInv α v old (ThreadDomain.threads D) (empty_set A) }}
        scan A_eq_dec D
        {{ fun acc => ScanInv α v old nil acc }}.
    Proof.
      unfold scan.
      apply provable_foreach with (Inv := fun remaining acc => ScanInv α v old remaining acc).
      - intros acc. apply provable_ret_safe; [apply ImplRefl | apply ScanInv_I | apply stable_ScanInv].
      - intros β remaining acc. apply scan_step_triple.
    Qed.

    (** Freezing the snapshot: the current abstract state is one for which
        all of the writer's branches exist. *)
    Lemma freeze α v st :
      ⊨ LoopInv α v st ==>> ScanInv α v (fst st) (ThreadDomain.threads D) (empty_set A).
    Proof.
      intros s [[HI [Hlini [Hno HinD] ] ] [Hcol _] ].
      destruct HI as [ρc Hf].
      split; [split; [exists ρc; exact Hf |]; split; [exact Hlini |]; split; [exact Hno | exact HinD] |].
      split; [intros x [] |].
      exists ρc. split.
      - split.
        + intros l Hsnap. apply (inv_lini _ _ _ Hf _ _ Hlini). exact Hsnap.
        + intros β x Hβ. rewrite <- (inv_cells _ _ _ Hf). exact Hβ.
      - split.
        + intros x Hx. destruct (Hcol x Hx) as [γ Hγ]. exists γ. rewrite (inv_cells _ _ _ Hf). exact Hγ.
        + exists nil. split; [reflexivity | intros β x [] _].
    Qed.

    Lemma scan_exit α v old acc :
      ⊨ ScanInv α v old nil acc ==>> LoopInv α v (pair acc old).
    Proof.
      intros s [Hw [Hcol [ρp [Hfr [Hunder (done & Hsplit & Hcov) ] ] ] ] ].
      split; [exact Hw |]. split; [exact Hcol |]. right.
      exists ρp. split; [exact Hfr |]. split; [exact Hunder |].
      intros x [β Hβ]. rewrite app_nil_r in Hsplit.
      apply (Hcov β x); [| exact Hβ]. rewrite <- Hsplit.
      destruct Hfr as [_ Hcells]. specialize (Hcells β x Hβ).
      destruct Hw as [[ρc' Hf'] _].
      apply (inv_dom _ _ _ Hf'). unfold row_exists. intros Hn.
      unfold cell_val in Hcells. rewrite Hn in Hcells. discriminate.
    Qed.

    Lemma loop_body_triple α v st :
      [li_lts E, li_lts F, R α, G α, I, α] ⊢
        {{ LoopInv α v st }}
        (if set_eqb A_eq_dec (fst st) (snd st) then Break (fst st)
         else scan A_eq_dec D p>= new => Continue (pair new (fst st)))
        {{ fun r => match r with
                    | inl st' => LoopInv α v st'
                    | inr l => Qpost α v l
                    end }}.
    Proof.
      destruct (set_eqb A_eq_dec (fst st) (snd st)) eqn:Heqb.
      - eapply provable_conseq_weak_pre with
          (P' := LoopInv α v st //\\ ⌜set_eqb A_eq_dec (fst st) (snd st) = true⌝).
        { intros s Hs. split; [exact Hs | exact Heqb]. }
        eapply provable_linstep with (P' := Qpost α v (fst st)).
        + apply Qpost_I.
        + apply stable_Qpost.
        + apply select_update.
        + apply provable_ret_safe; [intros s Hs; exact Hs | apply Qpost_I | apply stable_Qpost].
      - eapply provable_seq with (Q' := fun acc => ScanInv α v (fst st) nil acc).
        + eapply provable_conseq_weak_pre; [apply freeze | apply scan_triple].
        + intros acc. apply provable_ret_safe;
            [apply scan_exit | apply LoopInv_I | apply stable_LoopInv].
    Qed.

    Lemma method_triple α v :
      [li_lts E, li_lts F, R α, G α, I, α] ⊢
        {{ P α v }} write_snapshot_impl A_eq_dec D v α {{ Qpost α v }}.
    Proof.
      unfold write_snapshot_impl.
      eapply provable_vis with (P := Pgood α v) (P' := Pgood α v) (Q' := fun _ => Written α v).
      - intros s [Hg | Herr]; [left; exact Hg | right; apply ErrW_APError; exact (proj2 Herr) ].
      - apply no_error_write.
      - apply Pgood_I.
      - intros _. apply Written_I.
      - apply stable_Pgood.
      - intros _. apply stable_Written.
      - apply write_inv_update.
      - intros ret. destruct ret. apply write_res_update.
      - intros _.
        eapply provable_conseq_weak_pre with
          (P' := LoopInv α v (pair (set_add A_eq_dec v (empty_set A)) (empty_set A))).
        { intros s Hw. split; [exact Hw |]. split.
          - intros x Hx. simpl in Hx. destruct Hx as [-> | [] ].
            destruct Hw as [[ρc Hf] [Hlini _] ]. exists α.
            apply (inv_lini _ _ _ Hf _ _ Hlini).
          - left. split; [reflexivity | left; reflexivity]. }
        apply provable_doloop_data with (Iloop := LoopInv α v) (Q := Qpost α v).
        + apply Qpost_I.
        + apply stable_Qpost.
        + apply loop_body_triple.
    Qed.

    (** * The initial state *)

    Lemma initial_rows_find (l : list tid) t :
      @TMap.find cell_row t (initial_rows (@CellObject A) l) =
      if in_dec Pos.eq_dec t l then Some (Idle None) else None.
    Proof.
      induction l as [| t' l IH].
      - apply TMap.gempty.
      - destruct (Pos.eq_dec t' t) as [-> | Hne].
        + destruct (in_dec Pos.eq_dec t (t :: l)) as [_ | Habs];
            [| exfalso; apply Habs; left; reflexivity].
          exact (TMap.gss _ _ _).
        + assert (Hne' : t <> t') by (intros Heq; apply Hne; symmetry; exact Heq).
          refine (eq_trans (TMap.gso _ _ Hne') (eq_trans IH _)).
          destruct (in_dec Pos.eq_dec t l) as [Hin | Hnin];
            destruct (in_dec Pos.eq_dec t (t' :: l)) as [Hin' | Hnin']; try reflexivity.
          * exfalso. apply Hnin'. right. exact Hin.
          * exfalso. destruct Hin' as [Heq | Hin']; [exact (Hne Heq) | exact (Hnin Hin') ].
    Qed.

    Lemma initial_I : I (li_init E, li_init F, @TMap.empty lin_state).
    Proof.
      exists (@TMap.empty A). constructor; cbn [σ Δ].
      - intros ρ π Hposs. inversion Hposs; subst. reflexivity.
      - intros t. rewrite TMap.gempty. unfold cell_val.
        change (li_init E) with (initial_rows (@CellObject A) (ThreadDomain.threads D)).
        rewrite initial_rows_find. destruct (in_dec Pos.eq_dec t (ThreadDomain.threads D)); reflexivity.
      - intros π Hall. exists (@TMap.empty lin_state). split; [| constructor].
        intros t. destruct (Hall t) as (ρ & π' & Hposs & Hfind). inversion Hposs; subst.
        rewrite <- Hfind. reflexivity.
      - intros t. unfold row_exists.
        change (li_init E) with (initial_rows (@CellObject A) (ThreadDomain.threads D)).
        rewrite initial_rows_find. unfold ThreadDomain.contains.
        destruct (in_dec Pos.eq_dec t (ThreadDomain.threads D)) as [Hin | Hnin].
        + split; [intros _; exact Hin | discriminate].
        + split; [intros Habs; exfalso; apply Habs; reflexivity | intros Hin; exfalso; exact (Hnin Hin) ].
      - intros t w (ρ & π & Hposs & Hfind). inversion Hposs; subst.
        rewrite TMap.gempty in Hfind. discriminate.
      - intros t w l (ρ & π & Hposs & Hfind). inversion Hposs; subst.
        rewrite TMap.gempty in Hfind. discriminate.
    Qed.

    (** * The layer *)

    Program Definition MWriteSnapshot : layer_implementation_simulation E F :=
      {| li_impl := ws_impl A_eq_dec D |}.
    Next Obligation.
      eapply SetLogic.soundness with (R := R) (G := G) (I := I).
      - exact valid_rg.
      - exact rg_compatible.
      - intros t f. destruct f as [v].
        exists (P t v), (Qpost t v). constructor.
        + apply ginv_P.
        + apply P_I.
        + apply stable_P.
        + intros ret. apply gret_I.
        + intros ret σ0 Δ0 Hq ρ π Hposs. exact (proj2 Hq _ _ Hposs).
        + apply method_triple.
      - apply initial_I.
    Defined.

    Definition MWriteSnapshotLinearizable : layer_implementation_linearizability E F :=
      LISim2LILin MWriteSnapshot.

  End Proof.

  Print Assumptions MWriteSnapshot.
End WriteSnapshotProof.
