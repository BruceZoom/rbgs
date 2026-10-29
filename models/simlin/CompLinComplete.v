Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.
Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.Program.Equality.
Require Import Classical.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import TPSimulationSet.
Require Import CompLin.
Require Import CompLinSound.

(** Completeness of [TPSimulationSet.cal] (Definition 5.2, the Threadpool
    Simulation) with respect to [CompLin.CompLin] (Definition 4.1,
    Compositional Linearizability): the hard direction of Lemma 5.3.

    The simulation is built from the trace-based criterion by running the
    identity implementation [CompLin.idImpl] speculatively: at every point
    of a concrete run the abstract configuration is the set of all
    possibilities the identity implementation can reach with the overlay
    trace produced so far. Two points make this more than a textbook
    determinization argument:

    - [ContinueCore]'s return clause requires *every* possibility to have
      already linearized a thread by the time it returns, and the
      possibility set is fixed before the next concrete step is known. The
      abstract configuration therefore tracks the trace in which every
      thread returns as soon as it is ready ([ready]/[strip_rel]), the
      *eager* trace, and treats ready threads as already returned on the
      identity side while keeping their [ls_linr] entry in the possibility
      ([is_union]). The eager trace is itself a trace of [M] (a ready thread
      can neither step nor error, so [M] may return it at any time), so the
      criterion applies to it, and it only ever grows by appending.
    - Undefined behavior on the identity side only licenses continuations
      of the prefix where the error happened, while [ErrorCore] needs a
      possibility of the *current* configuration to error. The invariant
      therefore records that no prefix of the eager trace errors
      ([NoErr]); whenever a newly appended prefix can error, the erroring
      possibility is lifted into the next abstract configuration and the
      simulation switches to [ErrorCore] there.

    Possibilities reached by replaying identity steps are only determined
    up to pointwise equality of the linearization map ([pt_eq]), which is
    why the invariant compares the candidate set with [ac_steps] up to
    [pt_eq] rather than on the nose. *)
Module CompLinComplete.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.
  Import TPSimulationSet.TPSimulation.
  Import CompLin.CompLin.

  Section Completeness.
    Context {E F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.
    Context (M : ModuleImpl E F).
    Context (σ0 : State VE) (ρ0 : State VF).

    (** * Traces, thread domains and ready threads *)

    (* The set of threads with an open (invoked, not yet returned) overlay
       operation after a trace, computed from the trace alone: both the
       concrete pool of [M] and the linearization map of the identity
       implementation have exactly this domain. *)
    Definition tdom_item (b : tid -> bool) (x : TraceItem F) : tid -> bool :=
      match x with
      | TEvent ev =>
          match te_ev ev with
          | InvEv _ => fun t => if Pos.eq_dec t (te_tid ev) then true else b t
          | ResEv _ _ => fun t => if Pos.eq_dec t (te_tid ev) then false else b t
          end
      | TErr _ => b
      end.

    Definition tdom (s : Trace F) : tid -> bool :=
      fold_left tdom_item s (fun _ => false).

    Lemma tdom_snoc s x : tdom (s ++ x :: nil) = tdom_item (tdom s) x.
    Proof. unfold tdom. rewrite fold_left_app. reflexivity. Qed.

    (* A thread whose method body has returned a value and has no pending
       underlay operation is ready: it can neither step nor error, and the
       only thing left for it is [retstep]. *)
    Definition ready (ts : @ThreadState E F) : option (@LinState F) :=
      match ts with
      | Build_ThreadState f p b =>
          match p with
          | Ret r => match b with None => Some (ls_linr f r) | Some _ => None end
          | _ => None
          end
      end.

    Definition rfind (c : @ThreadPoolState E F) (t : tid) : option (@LinState F) :=
      match TMap.find t c with Some ts => ready ts | None => None end.

    Lemma rfind_add_eq c t ts : rfind (TMap.add t ts c) t = ready ts.
    Proof. unfold rfind. rewrite TMap.gss. reflexivity. Qed.

    Lemma rfind_add_neq c t ts t' : t' <> t -> rfind (TMap.add t ts c) t' = rfind c t'.
    Proof. intros Hne. unfold rfind. rewrite TMap.gso; auto. Qed.

    Lemma rfind_remove_eq c t : rfind (TMap.remove t c) t = None.
    Proof. unfold rfind. rewrite TMap.grs. reflexivity. Qed.

    Lemma rfind_remove_neq c t t' : t' <> t -> rfind (TMap.remove t c) t' = rfind c t'.
    Proof. intros Hne. unfold rfind. rewrite TMap.gro; auto. Qed.

    (* [ce] is [c] with its ready threads removed: the pool reached by the
       eager trace. *)
    Definition strip_rel (c ce : @ThreadPoolState E F) : Prop :=
      forall t, TMap.find t ce =
        match rfind c t with Some _ => None | None => TMap.find t c end.

    Lemma strip_rel_not_ready c ce t :
      strip_rel c ce -> rfind c t = None -> TMap.find t ce = TMap.find t c.
    Proof. intros Hs Hr. rewrite Hs, Hr. reflexivity. Qed.

    Lemma strip_rel_ready c ce t ls :
      strip_rel c ce -> rfind c t = Some ls -> TMap.find t ce = None.
    Proof. intros Hs Hr. rewrite Hs, Hr. reflexivity. Qed.

    (** * Linearization maps up to pointwise equality, and overlays *)

    Definition pt_eq (π1 π2 : tmap (@LinState F)) : Prop :=
      forall t, TMap.find t π1 = TMap.find t π2.

    (* [π2] is [π] with the entries of [X] filled in wherever [π] is
       undefined. Overlaying ready threads' [ls_linr] entries this way is
       how the identity-side configuration of the eager trace is turned
       into a possibility for the actual (lagging) trace. *)
    Definition pt_union (o1 o2 : option (@LinState F)) : option (@LinState F) :=
      match o1 with Some x => Some x | None => o2 end.

    Definition is_union (π : tmap (@LinState F)) (X : tid -> option (@LinState F))
        (π2 : tmap (@LinState F)) : Prop :=
      forall t, TMap.find t π2 = pt_union (TMap.find t π) (X t).

    Lemma is_union_pt_eq π X π2 π2' :
      is_union π X π2 -> is_union π X π2' -> pt_eq π2 π2'.
    Proof. intros H1 H2 t. rewrite H1, H2. reflexivity. Qed.

    Lemma is_union_rfind_exists π (c : @ThreadPoolState E F) :
      exists π2, is_union π (rfind c) π2.
    Proof.
      exists (TMap._map2
                (fun o1 o2 => pt_union o1 (match o2 with Some ts => ready ts | None => None end))
                π c).
      intros t. rewrite TMap.gmap2; auto.
    Qed.

    (* Possibility steps never look at undefined entries, so they commute
       with filling them in. *)
    Lemma poss_step_union (ρ ρ' : State VF) π π' X π2 :
      is_union π X π2 ->
      poss_step (PossOk ρ π) (PossOk ρ' π') ->
      exists π2', is_union π' X π2' /\ poss_step (PossOk ρ π2) (PossOk ρ' π2').
    Proof.
      intros Hu Hstep.
      inversion Hstep as [tt ff s1 s2 pp Hstep0 Hlin0 | tt ff rr s1 s2 pp Hstep0 Hlin0 | ]; subst.
      - exists (TMap.add tt (ls_lini ff) π2). split.
        + intros t'. destruct (Pos.eq_dec t' tt); subst.
          * rewrite !TMap.gss. reflexivity.
          * rewrite !TMap.gso; auto.
        + constructor; auto. rewrite Hu, Hlin0. reflexivity.
      - exists (TMap.add tt (ls_linr ff rr) π2). split.
        + intros t'. destruct (Pos.eq_dec t' tt); subst.
          * rewrite !TMap.gss. reflexivity.
          * rewrite !TMap.gso; auto.
        + constructor; auto. rewrite Hu, Hlin0. reflexivity.
    Qed.

    Lemma poss_steps_union_gen : forall (p q : @Poss F VF), poss_steps p q ->
      forall ρ π ρ' π' X π2,
        p = PossOk ρ π -> q = PossOk ρ' π' -> is_union π X π2 ->
        exists π2', is_union π' X π2' /\ poss_steps (PossOk ρ π2) (PossOk ρ' π2').
    Proof.
      intros p q H. induction H; intros ρ π ρ' π' X π2 Hp Hq Hu; subst.
      - destruct (poss_step_union _ _ _ _ _ _ Hu H) as [π2' [Hu' Hstep]].
        exists π2'. split; auto. apply rt_step; auto.
      - inversion Hq; subst. exists π2. split; auto. apply rt_refl.
      - destruct y as [ρm πm |].
        + destruct (IHclos_refl_trans1 _ _ _ _ _ _ eq_refl eq_refl Hu) as [πm2 [Hum Hsm]].
          destruct (IHclos_refl_trans2 _ _ _ _ _ _ eq_refl eq_refl Hum) as [π2' [Hu' Hs']].
          exists π2'. split; auto. eapply rt_trans; eauto.
        + exfalso. eapply CompLinSound.poss_steps_from_error in H0; [discriminate | reflexivity].
    Qed.

    Lemma poss_steps_union (ρ ρ' : State VF) π π' X π2 :
      is_union π X π2 ->
      poss_steps (PossOk ρ π) (PossOk ρ' π') ->
      exists π2', is_union π' X π2' /\ poss_steps (PossOk ρ π2) (PossOk ρ' π2').
    Proof.
      intros Hu Hsteps. eapply poss_steps_union_gen; eauto.
    Qed.

    Lemma poss_error_union (ρ : State VF) π X π2 :
      is_union π X π2 ->
      poss_step (PossOk ρ π) PossError ->
      poss_step (PossOk ρ π2) PossError.
    Proof.
      intros Hu Hstep.
      inversion Hstep as [ | | tt ff s1 pp Herror0 Hlin0]; subst.
      econstructor; eauto. rewrite Hu, Hlin0. reflexivity.
    Qed.

    (** * The identity implementation on linearization maps *)

    (* The configurations the identity implementation [idImpl] can reach
       over [VF] with a given overlay trace, stated directly on
       possibilities: [LRInv]/[LRRet] are its [invstep]/[retstep], and
       [LRStep] its library steps, which are exactly [poss_step]s. *)
    Inductive lin_reach : Trace F -> State VF -> tmap (@LinState F) -> Prop :=
    | LRInit : lin_reach nil ρ0 (TMap.empty _)
    | LRInv s ρ π t f
        (Hlr : lin_reach s ρ π)
        (Hnone : TMap.find t π = None) :
        lin_reach (s ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil)
          ρ (TMap.add t (ls_inv f) π)
    | LRRet s ρ π t f r
        (Hlr : lin_reach s ρ π)
        (Hlin : TMap.find t π = Some (ls_linr f r)) :
        lin_reach (s ++ TEvent (Build_ThreadEvent t (ResEv f r)) :: nil)
          ρ (TMap.remove t π)
    | LRStep s ρ π ρ' π'
        (Hlr : lin_reach s ρ π)
        (Hstep : poss_step (PossOk ρ π) (PossOk ρ' π')) :
        lin_reach s ρ' π'.

    (* [idImpl] can error with trace [s] on operation [f]. *)
    Definition lin_err (s : Trace F) (f : Sig.op F) : Prop :=
      exists ρ π t, lin_reach s ρ π /\
        Error VF (Build_ThreadEvent t (InvEv f)) ρ /\
        TMap.find t π = Some (ls_inv f).

    (* No prefix of [s] (including [s] itself) lets [idImpl] error. *)
    Definition NoErr (s : Trace F) : Prop :=
      forall p f, (exists tl, s = p ++ tl) -> ~ lin_err p f.

    Lemma lin_reach_steps_gen : forall (p q : @Poss F VF), poss_steps p q ->
      forall s ρ π ρ' π', p = PossOk ρ π -> q = PossOk ρ' π' ->
        lin_reach s ρ π -> lin_reach s ρ' π'.
    Proof.
      intros p q H. induction H; intros s ρ π ρ' π' Hp Hq Hlr; subst.
      - eapply LRStep; eauto.
      - inversion Hq; subst. exact Hlr.
      - destruct y as [ρm πm |].
        + eapply IHclos_refl_trans2; eauto.
        + exfalso. eapply CompLinSound.poss_steps_from_error in H0; [discriminate | reflexivity].
    Qed.

    Lemma lin_reach_steps s ρ π ρ' π' :
      lin_reach s ρ π -> poss_steps (PossOk ρ π) (PossOk ρ' π') -> lin_reach s ρ' π'.
    Proof. intros Hlr Hsteps. eapply lin_reach_steps_gen; eauto. Qed.

    Lemma lin_reach_dom s ρ π :
      lin_reach s ρ π -> forall t, TMap.find t π = None <-> tdom s t = false.
    Proof.
      induction 1 as [| s ρ π tt ff Hlr IH Hnone | s ρ π tt ff rr Hlr IH Hlin
                      | s ρ π ρ' π' Hlr IH Hstep]; intros t'.
      - rewrite TMap.gempty. unfold tdom. simpl. tauto.
      - rewrite tdom_snoc. simpl. destruct (Pos.eq_dec t' tt); subst.
        + rewrite TMap.gss. split; discriminate.
        + rewrite TMap.gso; auto.
      - rewrite tdom_snoc. simpl. destruct (Pos.eq_dec t' tt); subst.
        + rewrite TMap.grs. tauto.
        + rewrite TMap.gro; auto.
      - rewrite <- IH.
        pose proof (poss_step_domain _ _ _ _ Hstep t') as Hd. unfold map_domain in Hd.
        destruct (TMap.find t' π) as [l|] eqn:Hp; destruct (TMap.find t' π') as [l'|] eqn:Hp'.
        + split; discriminate.
        + exfalso. destruct (proj1 Hd (ex_intro _ l eq_refl)) as [x Hx]. discriminate.
        + exfalso. destruct (proj2 Hd (ex_intro _ l' eq_refl)) as [x Hx]. discriminate.
        + tauto.
    Qed.

    Lemma lin_reach_nil_gen : forall s ρ π, lin_reach s ρ π -> s = nil ->
      ρ = ρ0 /\ (forall t, TMap.find t π = None).
    Proof.
      induction 1; intros Hs.
      - split; auto. intros; apply TMap.gempty.
      - exfalso. symmetry in Hs. eapply app_cons_not_nil; eauto.
      - exfalso. symmetry in Hs. eapply app_cons_not_nil; eauto.
      - destruct (IHlin_reach Hs) as [Hρ Hn]. subst.
        exfalso. inversion Hstep; subst; rewrite Hn in Hlin; discriminate.
    Qed.

    Lemma lin_reach_nil ρ π :
      lin_reach nil ρ π -> ρ = ρ0 /\ (forall t, TMap.find t π = None).
    Proof. intros H. eapply lin_reach_nil_gen; eauto. Qed.

    Lemma lin_reach_clean s ρ π :
      lin_reach s ρ π -> forall g, ~ In (TErr g) s.
    Proof.
      induction 1; intros g Hin.
      - inversion Hin.
      - apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [eapply IHlin_reach; eauto |].
        inversion Hin as [Hx | Hx]; [discriminate | inversion Hx].
      - apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [eapply IHlin_reach; eauto |].
        inversion Hin as [Hx | Hx]; [discriminate | inversion Hx].
      - eapply IHlin_reach; eauto.
    Qed.

    (* Reading the last event off a reachable configuration. *)
    Lemma lin_reach_inv_inv_gen : forall s' ρ' π', lin_reach s' ρ' π' ->
      forall s t f, s' = s ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil ->
      exists ρ π, lin_reach s ρ π /\ TMap.find t π = None /\
        poss_steps (PossOk ρ (TMap.add t (ls_inv f) π)) (PossOk ρ' π').
    Proof.
      induction 1 as [| s ρ π tt ff Hlr IH Hnone | s ρ π tt ff rr Hlr IH Hlin
                      | s ρ π ρ' π' Hlr IH Hstep]; intros s0 t0 f0 Heq.
      - exfalso. symmetry in Heq. eapply app_cons_not_nil; eauto.
      - apply app_inj_tail in Heq. destruct Heq as [Heqs Heqx]. subst s0.
        injection Heqx. intros Heqf Heqt. subst.
        exists ρ, π. repeat split; auto. apply rt_refl.
      - apply app_inj_tail in Heq. destruct Heq as [_ Heqx]. discriminate Heqx.
      - destruct (IH _ _ _ Heq) as (ρ1 & π1 & Hlr1 & Hn1 & Hs1).
        exists ρ1, π1. repeat split; auto.
        eapply rt_trans; [exact Hs1 | apply rt_step; exact Hstep].
    Qed.

    Lemma lin_reach_inv_inv s t f ρ' π' :
      lin_reach (s ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil) ρ' π' ->
      exists ρ π, lin_reach s ρ π /\ TMap.find t π = None /\
        poss_steps (PossOk ρ (TMap.add t (ls_inv f) π)) (PossOk ρ' π').
    Proof. intros H. eapply lin_reach_inv_inv_gen; eauto. Qed.

    Lemma lin_reach_inv_ret_gen : forall s' ρ' π', lin_reach s' ρ' π' ->
      forall s t f r, s' = s ++ TEvent (Build_ThreadEvent t (ResEv f r)) :: nil ->
      exists ρ π, lin_reach s ρ π /\ TMap.find t π = Some (ls_linr f r) /\
        poss_steps (PossOk ρ (TMap.remove t π)) (PossOk ρ' π').
    Proof.
      induction 1 as [| s ρ π tt ff Hlr IH Hnone | s ρ π tt ff rr Hlr IH Hlin
                      | s ρ π ρ' π' Hlr IH Hstep]; intros s0 t0 f0 r0 Heq.
      - exfalso. symmetry in Heq. eapply app_cons_not_nil; eauto.
      - apply app_inj_tail in Heq. destruct Heq as [_ Heqx]. discriminate Heqx.
      - apply app_inj_tail in Heq. destruct Heq as [Heqs Heqx]. subst s0.
        inversion Heqx. subst t0 f0.
        match goal with
        | H : existT _ _ _ = existT _ _ _ |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H; subst
        end.
        exists ρ, π. repeat split; auto. apply rt_refl.
      - destruct (IH _ _ _ _ Heq) as (ρ1 & π1 & Hlr1 & Hn1 & Hs1).
        exists ρ1, π1. repeat split; auto.
        eapply rt_trans; [exact Hs1 | apply rt_step; exact Hstep].
    Qed.

    Lemma lin_reach_inv_ret s t f r ρ' π' :
      lin_reach (s ++ TEvent (Build_ThreadEvent t (ResEv f r)) :: nil) ρ' π' ->
      exists ρ π, lin_reach s ρ π /\ TMap.find t π = Some (ls_linr f r) /\
        poss_steps (PossOk ρ (TMap.remove t π)) (PossOk ρ' π').
    Proof. intros H. eapply lin_reach_inv_ret_gen; eauto. Qed.


    (** * Reflecting runs of the identity implementation *)

    Ltac inj_existT :=
      repeat match goal with
             | H : existT _ _ _ = existT _ _ _ |- _ =>
                 apply Eqdep.EqdepTheory.inj_pair2 in H
             end.

    Lemma linstate_to_ts_ret (ls : @LinState F) f r :
      CompLinSound.linstate_to_ts ls = Build_ThreadState f (Ret r) None -> ls = ls_linr f r.
    Proof.
      destruct ls as [g | g | g r0]; simpl; intros H; inversion H; subst; inj_existT;
        subst; reflexivity.
    Qed.

    (* A run of [idImpl] either stays clean, in which case its configuration
       is a [lin_reach] configuration (with the pool mirroring the
       linearization map, [pool_matches_lin]), or has errored at some
       prefix. *)
    Definition idrefl (X : @TraceConfig F F VF) : Prop :=
      (exists π, lin_reach (tc_trace X) (tc_state X) π /\
                 CompLinSound.pool_matches_lin (tc_pool X) π) \/
      (exists p f tl, tc_trace X = p ++ TErr f :: tl /\ lin_err p f).

    Lemma idrefl_err_app (X : @TraceConfig F F VF) s' ρ' cabs' :
      (exists p f tl, tc_trace X = p ++ TErr f :: tl /\ lin_err p f) ->
      (exists tl', s' = tc_trace X ++ tl') ->
      idrefl (mkTraceConfig s' ρ' cabs').
    Proof.
      intros [p [g [tl [Heq Herr]]]] [tl' Heq']. right. simpl.
      exists p, g, (tl ++ tl'). split; auto. rewrite Heq', Heq, <- app_assoc. reflexivity.
    Qed.

    Lemma idImpl_reflect_step (X Y : @TraceConfig F F VF) :
      @trace_step F F VF idImpl X Y -> idrefl X -> idrefl Y.
    Proof.
      intros Hstep HX.
      destruct Hstep as [s sigma c tt ff c' Hstep | s sigma c tt ff rr c' Hstep
                        | s sigma c ev sigma' c' Hstep | s sigma c tt c' Hstep
                        | s sigma c ff ev ts Hfind Herror].
      - (* tp-inv *)
        destruct HX as [[π [Hlr Hpm]] | Herr];
          [| eapply idrefl_err_app; [exact Herr | simpl; eauto]].
        simpl in *. left. simpl.
        inversion Hstep as [Hfind Hupd]; subst.
        pose proof (Hpm tt) as Hm. rewrite Hfind in Hm.
        destruct (TMap.find tt π) as [ls|] eqn:Hp; [discriminate |].
        exists (TMap.add tt (ls_inv ff) π). split; [constructor; auto |].
        intros t'. destruct (Pos.eq_dec t' tt); subst.
        + rewrite !TMap.gss. reflexivity.
        + rewrite !TMap.gso; auto.
      - (* tp-ret *)
        destruct HX as [[π [Hlr Hpm]] | Herr];
          [| eapply idrefl_err_app; [exact Herr | simpl; eauto]].
        simpl in *. left. simpl.
        inversion Hstep as [Hfind Hupd]; subst.
        pose proof (Hpm tt) as Hm. rewrite Hfind in Hm.
        destruct (TMap.find tt π) as [ls|] eqn:Hp; [| discriminate].
        simpl in Hm. injection Hm. intros Hm'. symmetry in Hm'.
        apply linstate_to_ts_ret in Hm'. subst ls.
        exists (TMap.remove tt π). split; [constructor; auto |].
        intros t'. destruct (Pos.eq_dec t' tt); subst.
        + rewrite !TMap.grs. reflexivity.
        + rewrite !TMap.gro; auto.
      - (* tp-step: a linearization point *)
        destruct HX as [[π [Hlr Hpm]] | Herr];
          [| eapply idrefl_err_app; [exact Herr | simpl; exists nil; rewrite app_nil_r; auto]].
        simpl in *. left. simpl.
        inversion Hstep as [f0 ts1 ts2 Hfind Hstep0 Hupd]; subst.
        pose proof (Hpm (te_tid ev)) as Hm. rewrite Hfind in Hm.
        destruct (TMap.find (te_tid ev) π) as [ls|] eqn:Hp; [| discriminate].
        simpl in Hm. injection Hm. intros Hm'. subst ts1.
        destruct ls as [g | g | g r]; simpl in Hstep0.
        + inversion Hstep0 as [tt op k s1 s2 Hvf | tt op rr k s1 s2 Hvf]; subst; inj_existT; subst.
          simpl in *.
          exists (TMap.add tt (ls_lini g) π). split.
          * eapply LRStep; [exact Hlr |]. constructor; auto.
          * intros t'. destruct (Pos.eq_dec t' tt); subst.
            { rewrite !TMap.gss. reflexivity. }
            { rewrite !TMap.gso; auto. }
        + inversion Hstep0 as [tt op k s1 s2 Hvf | tt op rr k s1 s2 Hvf]; subst; inj_existT; subst.
          simpl in *.
          exists (TMap.add tt (ls_linr g rr) π). split.
          * eapply LRStep; [exact Hlr |]. constructor; auto.
          * intros t'. destruct (Pos.eq_dec t' tt); subst.
            { rewrite !TMap.gss. reflexivity. }
            { rewrite !TMap.gso; auto. }
        + inversion Hstep0; subst; inj_existT; discriminate.
      - (* tp-tau: [idImpl] never has a silent step *)
        destruct HX as [[π [Hlr Hpm]] | Herr];
          [| eapply idrefl_err_app; [exact Herr | simpl; exists nil; rewrite app_nil_r; auto]].
        exfalso. simpl in *.
        inversion Hstep as [ts1 ts2 Hfind Hstep0 Hupd]; subst.
        pose proof (Hpm tt) as Hm. rewrite Hfind in Hm.
        destruct (TMap.find tt π) as [ls|] eqn:Hp; [| discriminate].
        simpl in Hm. injection Hm. intros Hm'. subst ts1.
        destruct ls; simpl in Hstep0; inversion Hstep0; subst; inj_existT; discriminate.
      - (* tp-error *)
        destruct HX as [[π [Hlr Hpm]] | Herr];
          [| eapply idrefl_err_app; [exact Herr | simpl; eauto]].
        simpl in *. right. simpl.
        inversion Herror as [tt op s' k Hvf]; subst. simpl in Hfind.
        pose proof (Hpm tt) as Hm. rewrite Hfind in Hm.
        destruct (TMap.find tt π) as [ls|] eqn:Hp; [| discriminate].
        simpl in Hm. injection Hm. intros Hm'.
        destruct ls as [g | g | g r]; simpl in Hm'; inversion Hm'; subst; inj_existT;
          try discriminate; subst.
        exists s, g, nil. split; auto.
        exists sigma, π, tt. auto.
    Qed.

    Lemma idImpl_reflect_gen (Y : @TraceConfig F F VF) :
      clos_refl_trans_n1 _ (@trace_step F F VF idImpl)
        (mkTraceConfig nil ρ0 (TMap.empty _)) Y ->
      idrefl Y.
    Proof.
      induction 1 as [| Y Z HYZ HY IH].
      - left. simpl. exists (TMap.empty _).
        split; [constructor | apply CompLinSound.pool_matches_lin_empty].
      - eapply idImpl_reflect_step; eauto.
    Qed.

    Lemma idImpl_reflect s ρ cabs :
      @trace_steps F F VF idImpl (mkTraceConfig nil ρ0 (TMap.empty _)) (mkTraceConfig s ρ cabs) ->
      (exists π, lin_reach s ρ π) \/ (exists p f tl, s = p ++ TErr f :: tl /\ lin_err p f).
    Proof.
      intros H. apply clos_rt_rtn1 in H. apply idImpl_reflect_gen in H.
      destruct H as [[π [Hlr _]] | Herr]; simpl in *; eauto.
    Qed.

    (** * What the criterion says about traces of [M] *)

    (* Definition 4.1 read through [lin_reach]: a trace of [M] is either
       reachable by [idImpl], or extends a prefix on which [idImpl] can
       error. *)
    Lemma ImplTraces_spec s :
      CompLin M σ0 ρ0 -> ImplTraces M σ0 s ->
      (exists ρ π, lin_reach s ρ π) \/ (exists p f tl, lin_err p f /\ s = p ++ tl).
    Proof.
      intros Hcl Htr. specialize (Hcl s Htr).
      destruct Hcl as [Hid | [p [f [tl [Hid Heq]]]]].
      - destruct Hid as [ρ [cabs Hrun]]. apply idImpl_reflect in Hrun.
        destruct Hrun as [[π Hlr] | [p [g [tl [Heq Herr]]]]].
        + left. eauto.
        + right. exists p, g, (TErr g :: tl). auto.
      - destruct Hid as [ρ [cabs Hrun]]. apply idImpl_reflect in Hrun.
        destruct Hrun as [[π Hlr] | [p' [g [tl' [Heq' Herr]]]]].
        + exfalso. eapply lin_reach_clean; [exact Hlr |].
          apply in_or_app. right. left. reflexivity.
        + right.
          destruct (CompLinSound.trace_snoc_prefix p' (TErr g :: tl') p (TErr f))
            as [q [Hp Htl]]; [discriminate | symmetry; exact Heq' |].
          exists p', g, (q ++ tl). split; auto.
          rewrite Heq, Hp, app_assoc. reflexivity.
    Qed.

    Lemma NoErr_lin_reach s :
      CompLin M σ0 ρ0 -> NoErr s -> ImplTraces M σ0 s ->
      exists ρ π, lin_reach s ρ π.
    Proof.
      intros Hcl Hne Htr.
      destruct (ImplTraces_spec s Hcl Htr) as [H | [p [f [tl [Herr Heq]]]]]; auto.
      exfalso. eapply Hne; eauto.
    Qed.

    Lemma NoErr_no_TErr s f :
      CompLin M σ0 ρ0 -> NoErr s -> ImplTraces M σ0 (s ++ TErr f :: nil) -> False.
    Proof.
      intros Hcl Hne Htr.
      destruct (ImplTraces_spec _ Hcl Htr) as [[ρ [π Hlr]] | [p [g [tl [Herr Heq]]]]].
      - eapply lin_reach_clean; [exact Hlr |]. apply in_or_app. right. left. reflexivity.
      - destruct tl as [| x tl].
        + rewrite app_nil_r in Heq. subst p.
          destruct Herr as [ρ [π [t [Hlr _]]]].
          eapply lin_reach_clean; [exact Hlr |]. apply in_or_app. right. left. reflexivity.
        + destruct (CompLinSound.trace_snoc_prefix p (x :: tl) s (TErr f))
            as [q [Hs _]]; [discriminate | symmetry; exact Heq |].
          eapply Hne; eauto.
    Qed.

    Lemma NoErr_nil : NoErr nil.
    Proof.
      intros p f [tl Heq] Herr. symmetry in Heq. apply app_eq_nil in Heq.
      destruct Heq; subst.
      destruct Herr as [ρ [π [t [Hlr [_ Hfind]]]]].
      apply lin_reach_nil in Hlr. destruct Hlr as [_ Hn].
      rewrite Hn in Hfind. discriminate.
    Qed.

    Lemma NoErr_snoc s x :
      NoErr s -> (forall f, ~ lin_err (s ++ x :: nil) f) -> NoErr (s ++ x :: nil).
    Proof.
      intros Hne Hx p f [tl Heq] Herr. destruct tl as [| y tl].
      - rewrite app_nil_r in Heq. subst p. eapply Hx; eauto.
      - destruct (CompLinSound.trace_snoc_prefix p (y :: tl) s x)
          as [q [Hs _]]; [discriminate | symmetry; exact Heq |].
        eapply Hne; eauto.
    Qed.

    (** * Runs of [M] *)

    Definition run (e : Trace F) (σ : State VE) (c : @ThreadPoolState E F) : Prop :=
      trace_steps M (mkTraceConfig nil σ0 (TMap.empty _)) (mkTraceConfig e σ c).

    Lemma run_ImplTraces e σ c : run e σ c -> ImplTraces M σ0 e.
    Proof. intros H. exists σ, c. exact H. Qed.

    Lemma run_step e σ c e' σ' c' :
      run e σ c -> trace_step M (mkTraceConfig e σ c) (mkTraceConfig e' σ' c') -> run e' σ' c'.
    Proof. intros H1 H2. eapply rt_trans; [exact H1 | apply rt_step; exact H2]. Qed.

    Lemma run_dom_step (X Y : @TraceConfig E F VE) :
      trace_step M X Y ->
      (forall t, TMap.find t (tc_pool X) = None <-> tdom (tc_trace X) t = false) ->
      (forall t, TMap.find t (tc_pool Y) = None <-> tdom (tc_trace Y) t = false).
    Proof.
      intros Hstep HX.
      destruct Hstep as [s sigma c tt ff c' Hstep | s sigma c tt ff rr c' Hstep
                        | s sigma c ev sigma' c' Hstep | s sigma c tt c' Hstep
                        | s sigma c ff ev ts Hfind Herror]; simpl in *; intros t'.
      - inversion Hstep as [Hfind Hupd]; subst. rewrite tdom_snoc. simpl.
        destruct (Pos.eq_dec t' tt); subst.
        + rewrite TMap.gss. split; discriminate.
        + rewrite TMap.gso; auto.
      - inversion Hstep as [Hfind Hupd]; subst. rewrite tdom_snoc. simpl.
        destruct (Pos.eq_dec t' tt); subst.
        + rewrite TMap.grs. tauto.
        + rewrite TMap.gro; auto.
      - pose proof (CompLinSound.ustep_dom_preserved _ _ _ _ _ Hstep t') as Hd.
        pose proof (HX t') as Hx. tauto.
      - pose proof (CompLinSound.taustep_dom_preserved _ _ _ Hstep t') as Hd.
        pose proof (HX t') as Hx. tauto.
      - rewrite tdom_snoc. simpl. auto.
    Qed.

    Lemma run_dom_gen (Y : @TraceConfig E F VE) :
      clos_refl_trans_n1 _ (trace_step M) (mkTraceConfig nil σ0 (TMap.empty _)) Y ->
      forall t, TMap.find t (tc_pool Y) = None <-> tdom (tc_trace Y) t = false.
    Proof.
      induction 1 as [| Y Z HYZ HY IH].
      - intros t. simpl. rewrite TMap.gempty. unfold tdom. simpl. tauto.
      - eapply run_dom_step; eauto.
    Qed.

    Lemma run_dom e σ c :
      run e σ c -> forall t, TMap.find t c = None <-> tdom e t = false.
    Proof.
      intros H. apply clos_rt_rtn1 in H. exact (run_dom_gen _ H).
    Qed.

    (* A ready thread has already returned in the eager trace, so the
       identity implementation has no entry for it. *)
    Lemma ready_lin_none e σ c ce ρ π t ls :
      run e σ ce -> strip_rel c ce -> rfind c t = Some ls ->
      lin_reach e ρ π -> TMap.find t π = None.
    Proof.
      intros Hrun Hs Hr Hlr.
      apply (lin_reach_dom _ _ _ Hlr). apply (run_dom _ _ _ Hrun).
      eapply strip_rel_ready; eauto.
    Qed.

    Lemma ready_some ts ls :
      ready ts = Some ls ->
      exists f r, ls = ls_linr f r /\ ts = Build_ThreadState f (Ret r) None.
    Proof.
      destruct ts as [f p b]. destruct p; simpl; try discriminate.
      destruct b; [discriminate |]. intros H. injection H. intros; subst. eauto.
    Qed.

    (** * The candidate abstract configuration *)

    Program Definition ac_restrict (Δ : AbstractConfig VF)
        (P : State VF -> tmap (@LinState F) -> Prop)
        (Hne : exists ρ π, Δ ρ π /\ P ρ π) : AbstractConfig VF :=
      {| ac_active := ac_active Δ;
         ac_prop := fun ρ π => Δ ρ π /\ P ρ π |}.
    Next Obligation.
      destruct Hne as [ρ [π H]]. exists ρ, π. exact H.
    Qed.
    Next Obligation.
      intros. simpl in *.
      match goal with
      | H : _ /\ _ |- _ => destruct H as [H0 _]; eapply ac_domain; exact H0
      end.
    Qed.

    (* The possibilities of the actual trace that are compatible with the
       eager trace [e]: an identity-side configuration of [e], overlaid
       with the [ls_linr] entries of the threads that are ready in [c]. *)
    Definition Dset (e : Trace F) (c : @ThreadPoolState E F)
        (ρ : State VF) (π : tmap (@LinState F)) : Prop :=
      exists πe, lin_reach e ρ πe /\ is_union πe (rfind c) π.

    Lemma Dset_pt_eq e c ρ π π' : pt_eq π π' -> Dset e c ρ π -> Dset e c ρ π'.
    Proof.
      intros Heq [πe [Hlr Hu]]. exists πe. split; auto.
      intros t. rewrite <- Heq. apply Hu.
    Qed.

    Lemma Dset_nonempty e c ρ πe : lin_reach e ρ πe -> exists π, Dset e c ρ π.
    Proof.
      intros H. destruct (is_union_rfind_exists πe c) as [π Hu]. exists π, πe. auto.
    Qed.

    Definition pt_in (D : State VF -> tmap (@LinState F) -> Prop) ρ π : Prop :=
      exists π2, pt_eq π π2 /\ D ρ π2.

    Lemma ac_steps_poss (Δ : AbstractConfig VF) ρ π ρ' π' :
      ac_steps Δ ρ π -> poss_steps (PossOk ρ π) (PossOk ρ' π') -> ac_steps Δ ρ' π'.
    Proof.
      intros H Hs. inversion H as [ρ1 π1 ρ2 π2 Hposs Hsteps]; subst.
      econstructor; eauto. eapply rt_trans; eauto.
    Qed.

    Lemma ac_steps_error (Δ : AbstractConfig VF) ρ π :
      ac_steps Δ ρ π -> poss_step (PossOk ρ π) PossError -> ErrorCore Δ.
    Proof.
      intros H He. inversion H as [ρ1 π1 ρ2 π2 Hposs Hsteps]; subst.
      exists ρ1, π1. split; auto.
      eapply rt_trans; [exact Hsteps | apply rt_step; exact He].
    Qed.

    (* The simulation invariant: either the abstract configuration can
       already error, or it is (after speculation) the candidate set of the
       eager trace [e] reached by [M] with pool [ce]. *)
    Definition Inv (σ : State VE) (c : @ThreadPoolState E F) (Δ : AbstractConfig VF) : Prop :=
      ErrorCore Δ \/
      exists e ce, run e σ ce /\ strip_rel c ce /\ NoErr e /\
        (forall ρ π, Dset e c ρ π -> pt_in (ac_steps Δ) ρ π).

    (* What is known at a node once the candidate set [Δ0] has been
       selected and found not to error. *)
    Record Node (e : Trace F) (ce : @ThreadPoolState E F) (σ : State VE)
        (c : @ThreadPoolState E F) (Δ0 : AbstractConfig VF) : Prop := mkNode {
      nd_run : run e σ ce;
      nd_strip : strip_rel c ce;
      nd_noerr : NoErr e;
      nd_D0 : forall ρ π, Dset e c ρ π -> pt_in Δ0 ρ π;
      nd_sub : forall ρ π, Δ0 ρ π -> Dset e c ρ π;
      nd_noerr0 : ~ ErrorCore Δ0
    }.

    (** * Lifting identity-side configurations of the extended trace *)

    Section Lift.
      Variables (e : Trace F) (ce : @ThreadPoolState E F) (σ : State VE)
                (c : @ThreadPoolState E F) (Δ0 : AbstractConfig VF).
      Hypothesis N : Node e ce σ c Δ0.

      (* A fresh invocation: delay nothing, just replay. *)
      Lemma inv_lift t f ρ' πe' :
        TMap.find t c = None ->
        lin_reach (e ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil) ρ' πe' ->
        exists π2', is_union πe' (rfind c) π2' /\ ac_steps (ac_inv Δ0 t f) ρ' π2'.
      Proof.
        intros Hc Hlr. apply lin_reach_inv_inv in Hlr.
        destruct Hlr as (ρ & π & Hlr & Hn & Hs).
        destruct (is_union_rfind_exists π c) as [πu Hu].
        destruct (nd_D0 _ _ _ _ _ N ρ πu (ex_intro _ π (conj Hlr Hu))) as [π2 [Heq H0]].
        assert (Hu2 : is_union (TMap.add t (ls_inv f) π) (rfind c) (TMap.add t (ls_inv f) π2)).
        { intros t'. destruct (Pos.eq_dec t' t); subst.
          - rewrite !TMap.gss. reflexivity.
          - rewrite !TMap.gso; auto. rewrite <- Heq. apply Hu. }
        destruct (poss_steps_union _ _ _ _ _ _ Hu2 Hs) as [π2' [Hu' Hs']].
        exists π2'. split; auto.
        econstructor; [constructor; exact H0 | exact Hs'].
      Qed.

      Lemma inv_lift_err t f g :
        TMap.find t c = None ->
        lin_err (e ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil) g ->
        ErrorCore (ac_inv Δ0 t f).
      Proof.
        intros Hc (ρ' & πe' & t' & Hlr & Herr & Hfind).
        destruct (inv_lift _ _ _ _ Hc Hlr) as [π2' [Hu' Hst]].
        eapply ac_steps_error; [exact Hst |].
        econstructor; [exact Herr |]. rewrite Hu', Hfind. reflexivity.
      Qed.

      (* An invocation whose method body is already a value: the eager
         trace returns it at once; the possibility keeps its [ls_linr]
         entry instead. *)
      Lemma invret_lift t f v ρ' πe' :
        TMap.find t c = None ->
        lin_reach ((e ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil)
                     ++ TEvent (Build_ThreadEvent t (ResEv f v)) :: nil) ρ' πe' ->
        exists π2',
          is_union πe' (rfind (TMap.add t (Build_ThreadState f (Ret v) None) c)) π2' /\
          ac_steps (ac_inv Δ0 t f) ρ' π2'.
      Proof.
        intros Hc Hlr. apply lin_reach_inv_ret in Hlr.
        destruct Hlr as (ρ1 & π1 & Hlr1 & Hl1 & Hs1).
        destruct (inv_lift _ _ _ _ Hc Hlr1) as [π21 [Hu1 Hst1]].
        assert (Hu2 : is_union (TMap.remove t π1)
                        (rfind (TMap.add t (Build_ThreadState f (Ret v) None) c)) π21).
        { intros t'. destruct (Pos.eq_dec t' t); subst.
          - rewrite TMap.grs, rfind_add_eq. simpl. rewrite Hu1, Hl1. reflexivity.
          - rewrite TMap.gro, rfind_add_neq; auto. }
        destruct (poss_steps_union _ _ _ _ _ _ Hu2 Hs1) as [π2' [Hu' Hs']].
        exists π2'. split; auto. eapply ac_steps_poss; eauto.
      Qed.

      Lemma invret_lift_err t f v g :
        TMap.find t c = None ->
        lin_err ((e ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil)
                   ++ TEvent (Build_ThreadEvent t (ResEv f v)) :: nil) g ->
        ErrorCore (ac_inv Δ0 t f).
      Proof.
        intros Hc (ρ' & πe' & t' & Hlr & Herr & Hfind).
        destruct (invret_lift _ _ _ _ _ Hc Hlr) as [π2' [Hu' Hst]].
        eapply ac_steps_error; [exact Hst |].
        econstructor; [exact Herr |]. rewrite Hu', Hfind. reflexivity.
      Qed.

      (* A thread becoming ready: the eager trace returns it. *)
      Lemma ret_lift t f r ts ρ' πe' :
        rfind c t = None -> ready ts = Some (ls_linr f r) ->
        lin_reach (e ++ TEvent (Build_ThreadEvent t (ResEv f r)) :: nil) ρ' πe' ->
        exists π2', is_union πe' (rfind (TMap.add t ts c)) π2' /\ ac_steps Δ0 ρ' π2'.
      Proof.
        intros Hr Hready Hlr. apply lin_reach_inv_ret in Hlr.
        destruct Hlr as (ρ1 & π1 & Hlr1 & Hl1 & Hs1).
        destruct (is_union_rfind_exists π1 c) as [πu Hu].
        destruct (nd_D0 _ _ _ _ _ N ρ1 πu (ex_intro _ π1 (conj Hlr1 Hu))) as [π2 [Heq H0]].
        assert (Hu2 : is_union (TMap.remove t π1) (rfind (TMap.add t ts c)) π2).
        { intros t'. destruct (Pos.eq_dec t' t); subst.
          - rewrite TMap.grs, rfind_add_eq, Hready. simpl. rewrite <- Heq, Hu, Hl1. reflexivity.
          - rewrite TMap.gro, rfind_add_neq; auto. rewrite <- Heq. apply Hu. }
        destruct (poss_steps_union _ _ _ _ _ _ Hu2 Hs1) as [π2' [Hu' Hs']].
        exists π2'. split; auto. econstructor; eauto.
      Qed.

      Lemma ret_lift_err t f r ts g :
        rfind c t = None -> ready ts = Some (ls_linr f r) ->
        lin_err (e ++ TEvent (Build_ThreadEvent t (ResEv f r)) :: nil) g ->
        ErrorCore Δ0.
      Proof.
        intros Hr Hready (ρ' & πe' & t' & Hlr & Herr & Hfind).
        destruct (ret_lift _ _ _ ts _ _ Hr Hready Hlr) as [π2' [Hu' Hst]].
        eapply ac_steps_error; [exact Hst |].
        econstructor; [exact Herr |]. rewrite Hu', Hfind. reflexivity.
      Qed.

      (* A ready thread returning: drop its entry. *)
      Lemma res_lift t ls ρ' π' :
        rfind c t = Some ls ->
        Dset e (TMap.remove t c) ρ' π' -> pt_in (ac_steps (ac_res Δ0 t)) ρ' π'.
      Proof.
        intros Hr [πe [Hlr Hu]].
        destruct (is_union_rfind_exists πe c) as [πu Hu0].
        destruct (nd_D0 _ _ _ _ _ N ρ' πu (ex_intro _ πe (conj Hlr Hu0))) as [π2 [Heq H0]].
        assert (Hnone : TMap.find t πe = None)
          by (eapply ready_lin_none; [exact (nd_run _ _ _ _ _ N) | exact (nd_strip _ _ _ _ _ N) | exact Hr | exact Hlr]).
        exists (TMap.remove t π2). split.
        - intros t'. destruct (Pos.eq_dec t' t); subst.
          + rewrite TMap.grs, Hu, rfind_remove_eq, Hnone. reflexivity.
          + rewrite TMap.gro; auto. rewrite <- Heq, Hu0, Hu, rfind_remove_neq; auto.
        - econstructor; [constructor; exact H0 | apply rt_refl].
      Qed.

      Lemma ready_linr t f r :
        TMap.find t c = Some (Build_ThreadState f (Ret r) None) ->
        forall ρ π, Δ0 ρ π -> TMap.find t π = Some (ls_linr f r).
      Proof.
        intros Hfind ρ π H0.
        destruct (nd_sub _ _ _ _ _ N ρ π H0) as [πe [Hlr Hu]].
        assert (Hr : rfind c t = Some (ls_linr f r)) by (unfold rfind; rewrite Hfind; reflexivity).
        rewrite Hu, Hr.
        rewrite (ready_lin_none _ _ _ _ _ _ _ _ (nd_run _ _ _ _ _ N) (nd_strip _ _ _ _ _ N) Hr Hlr).
        reflexivity.
      Qed.

      (* A step that changes no ready thread leaves the candidate set as is. *)
      Lemma same_lift c' :
        (forall t, rfind c' t = rfind c t) ->
        forall ρ π, Dset e c' ρ π -> pt_in (ac_steps Δ0) ρ π.
      Proof.
        intros Hsame ρ π [πe [Hlr Hu]].
        destruct (nd_D0 _ _ _ _ _ N ρ π) as [π2 [Heq H0]].
        { exists πe. split; auto. intros t. rewrite Hu, Hsame. reflexivity. }
        exists π2. split; auto. exact (ac_steps_refl Δ0 ρ π2 H0).
      Qed.
    End Lift.

    (** * One concrete step preserves the invariant *)

    Section Step.
      Variables (e : Trace F) (ce : @ThreadPoolState E F) (σ : State VE)
                (c : @ThreadPoolState E F) (Δ0 : AbstractConfig VF).
      Hypothesis Hcl : CompLin M σ0 ρ0.
      Hypothesis N : Node e ce σ c Δ0.

      Lemma Inv_next_inv_notready t f ts :
        TMap.find t c = None -> ready ts = None ->
        run (e ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil) σ (TMap.add t ts ce) ->
        Inv σ (TMap.add t ts c) (ac_inv Δ0 t f).
      Proof.
        intros Hfind Hready Hrun1.
        assert (Hr : rfind c t = None) by (unfold rfind; rewrite Hfind; reflexivity).
        destruct (classic (exists g, lin_err (e ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil) g))
          as [[g Herr] | Hnoerr].
        { left. exact (inv_lift_err _ _ _ _ _ N t f g Hfind Herr). }
        right. exists (e ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil), (TMap.add t ts ce).
        split; [exact Hrun1 |]. split.
        - intros t'. destruct (Pos.eq_dec t' t); subst.
          + rewrite rfind_add_eq, Hready, !TMap.gss. reflexivity.
          + rewrite rfind_add_neq, !TMap.gso; auto. exact (nd_strip _ _ _ _ _ N t').
        - split.
          + apply NoErr_snoc; [exact (nd_noerr _ _ _ _ _ N) |].
            intros g Hg. apply Hnoerr. eauto.
          + intros ρ' π' [πe' [Hlr Hu]].
            destruct (inv_lift _ _ _ _ _ N t f ρ' πe' Hfind Hlr) as [π2' [Hu' Hst]].
            exists π2'. split; auto.
            intros t'. rewrite Hu, Hu'. destruct (Pos.eq_dec t' t); subst.
            * rewrite rfind_add_eq, Hready, Hr. reflexivity.
            * rewrite rfind_add_neq; auto.
      Qed.

      Lemma Inv_next_inv_ready t f v :
        TMap.find t c = None ->
        run (e ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil) σ
          (TMap.add t (Build_ThreadState f (Ret v) None) ce) ->
        Inv σ (TMap.add t (Build_ThreadState f (Ret v) None) c) (ac_inv Δ0 t f).
      Proof.
        intros Hfind Hrun1.
        assert (Hrun2 : run ((e ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil)
                               ++ TEvent (Build_ThreadEvent t (ResEv f v)) :: nil) σ
                          (TMap.remove t (TMap.add t (Build_ThreadState f (Ret v) None) ce))).
        { eapply run_step; [exact Hrun1 |]. apply TraceStepRet.
          apply RetStep; [apply TMap.gss | reflexivity]. }
        destruct (classic (exists g, lin_err (e ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil) g))
          as [[g Herr] | Hnoerr1].
        { left. exact (inv_lift_err _ _ _ _ _ N t f g Hfind Herr). }
        destruct (classic (exists g, lin_err ((e ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil)
                                                ++ TEvent (Build_ThreadEvent t (ResEv f v)) :: nil) g))
          as [[g Herr] | Hnoerr2].
        { left. exact (invret_lift_err _ _ _ _ _ N t f v g Hfind Herr). }
        right.
        exists ((e ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil)
                  ++ TEvent (Build_ThreadEvent t (ResEv f v)) :: nil),
               (TMap.remove t (TMap.add t (Build_ThreadState f (Ret v) None) ce)).
        split; [exact Hrun2 |]. split.
        - intros t'. destruct (Pos.eq_dec t' t); subst.
          + rewrite rfind_add_eq, TMap.grs. reflexivity.
          + rewrite rfind_add_neq, TMap.gro, !TMap.gso; auto. exact (nd_strip _ _ _ _ _ N t').
        - split.
          + apply NoErr_snoc.
            * apply NoErr_snoc; [exact (nd_noerr _ _ _ _ _ N) |].
              intros g Hg. apply Hnoerr1. eauto.
            * intros g Hg. apply Hnoerr2. eauto.
          + intros ρ' π' [πe' [Hlr Hu]].
            destruct (invret_lift _ _ _ _ _ N t f v ρ' πe' Hfind Hlr) as [π2' [Hu' Hst]].
            exists π2'. split; auto. exact (is_union_pt_eq _ _ _ _ Hu Hu').
      Qed.

      Lemma Inv_next_inv t f c' :
        invstep M t f c c' -> Inv σ c' (ac_inv Δ0 t f).
      Proof.
        intros Hstep. inversion Hstep as [Hfind Hupd]. subst c'.
        assert (Hr : rfind c t = None) by (unfold rfind; rewrite Hfind; reflexivity).
        assert (Hrun1 : run (e ++ TEvent (Build_ThreadEvent t (InvEv f)) :: nil) σ
                          (TMap.add t (Build_ThreadState f (M f t) None) ce)).
        { eapply run_step; [exact (nd_run _ _ _ _ _ N) |]. apply TraceStepInv.
          apply InvStep; [| reflexivity].
          rewrite (strip_rel_not_ready _ _ _ (nd_strip _ _ _ _ _ N) Hr). exact Hfind. }
        destruct (M f t) as [op k | v | p] eqn:HM; try rewrite HM in Hrun1.
        - apply Inv_next_inv_notready; auto.
        - apply Inv_next_inv_ready; auto.
        - apply Inv_next_inv_notready; auto.
      Qed.

      (* A silent step of thread [t] (library or [Tau]): if the thread
         becomes ready, the eager trace returns it. *)
      Lemma Inv_next_pool t ts2 σ' :
        rfind c t = None ->
        trace_step M (mkTraceConfig e σ ce) (mkTraceConfig e σ' (TMap.add t ts2 ce)) ->
        Inv σ' (TMap.add t ts2 c) Δ0.
      Proof.
        intros Hr Hstep.
        assert (Hrun1 : run e σ' (TMap.add t ts2 ce))
          by (eapply run_step; [exact (nd_run _ _ _ _ _ N) | exact Hstep]).
        destruct (ready ts2) as [ls|] eqn:Hready.
        - destruct (ready_some _ _ Hready) as (f & r & Hls & Hts). subst ls ts2.
          assert (Hrun2 : run (e ++ TEvent (Build_ThreadEvent t (ResEv f r)) :: nil) σ'
                            (TMap.remove t (TMap.add t (Build_ThreadState f (Ret r) None) ce))).
          { eapply run_step; [exact Hrun1 |]. apply TraceStepRet.
            apply RetStep; [apply TMap.gss | reflexivity]. }
          destruct (classic (exists g, lin_err (e ++ TEvent (Build_ThreadEvent t (ResEv f r)) :: nil) g))
            as [[g Herr] | Hnoerr1].
          { left. exact (ret_lift_err _ _ _ _ _ N t f r _ g Hr Hready Herr). }
          right.
          exists (e ++ TEvent (Build_ThreadEvent t (ResEv f r)) :: nil),
                 (TMap.remove t (TMap.add t (Build_ThreadState f (Ret r) None) ce)).
          split; [exact Hrun2 |]. split.
          + intros t'. destruct (Pos.eq_dec t' t); subst.
            * rewrite rfind_add_eq, TMap.grs. reflexivity.
            * rewrite rfind_add_neq, TMap.gro, !TMap.gso; auto. exact (nd_strip _ _ _ _ _ N t').
          + split.
            * apply NoErr_snoc; [exact (nd_noerr _ _ _ _ _ N) |].
              intros g Hg. apply Hnoerr1. eauto.
            * intros ρ' π' [πe' [Hlr Hu]].
              destruct (ret_lift _ _ _ _ _ N t f r _ ρ' πe' Hr Hready Hlr) as [π2' [Hu' Hst]].
              exists π2'. split; auto. exact (is_union_pt_eq _ _ _ _ Hu Hu').
        - right. exists e, (TMap.add t ts2 ce). split; [exact Hrun1 |]. split.
          + intros t'. destruct (Pos.eq_dec t' t); subst.
            * rewrite rfind_add_eq, Hready, !TMap.gss. reflexivity.
            * rewrite rfind_add_neq, !TMap.gso; auto. exact (nd_strip _ _ _ _ _ N t').
          + split; [exact (nd_noerr _ _ _ _ _ N) |].
            apply (same_lift _ _ _ _ _ N). intros t'. destruct (Pos.eq_dec t' t); subst.
            * rewrite rfind_add_eq, Hready, Hr. reflexivity.
            * rewrite rfind_add_neq; auto.
      Qed.

      Lemma Inv_next_u ev σ' c' :
        ustep ev σ c σ' c' -> Inv σ' c' Δ0.
      Proof.
        intros Hstep. inversion Hstep as [f ts1 ts2 Hfind Hstep0 Hupd]. subst c'.
        assert (Hr : rfind c (te_tid ev) = None).
        { unfold rfind. rewrite Hfind. inversion Hstep0; subst; reflexivity. }
        apply Inv_next_pool; [exact Hr |].
        apply (TraceStepU M e σ ce ev σ' (TMap.add (te_tid ev) ts2 ce)).
        eapply UStep; [| exact Hstep0 | reflexivity].
        rewrite (strip_rel_not_ready _ _ _ (nd_strip _ _ _ _ _ N) Hr). exact Hfind.
      Qed.

      Lemma Inv_next_tau t c' :
        taustep t c c' -> Inv σ c' Δ0.
      Proof.
        intros Hstep. inversion Hstep as [ts1 ts2 Hfind Hstep0 Hupd]. subst c'.
        assert (Hr : rfind c t = None).
        { unfold rfind. rewrite Hfind. inversion Hstep0; subst; reflexivity. }
        apply Inv_next_pool; [exact Hr |].
        apply (TraceStepTau M e σ ce t (TMap.add t ts2 ce)).
        eapply TauStep; [| exact Hstep0 | reflexivity].
        rewrite (strip_rel_not_ready _ _ _ (nd_strip _ _ _ _ _ N) Hr). exact Hfind.
      Qed.

      Lemma Inv_next_ret t f ret c' :
        retstep t f ret c c' ->
        (forall ρ π, Δ0 ρ π -> TMap.find t π = Some (ls_linr f ret)) /\
        Inv σ c' (ac_res Δ0 t).
      Proof.
        intros Hstep. inversion Hstep as [Hfind Hupd]. subst c'.
        assert (Hr : rfind c t = Some (ls_linr f ret))
          by (unfold rfind; rewrite Hfind; reflexivity).
        split; [exact (ready_linr _ _ _ _ _ N t f ret Hfind) |].
        right. exists e, ce. split; [exact (nd_run _ _ _ _ _ N) |]. split.
        - intros t'. destruct (Pos.eq_dec t' t); subst.
          + rewrite rfind_remove_eq, TMap.grs.
            eapply strip_rel_ready; [exact (nd_strip _ _ _ _ _ N) | exact Hr].
          + rewrite rfind_remove_neq, TMap.gro; auto. exact (nd_strip _ _ _ _ _ N t').
        - split; [exact (nd_noerr _ _ _ _ _ N) |].
          intros ρ' π' Hd. exact (res_lift _ _ _ _ _ N t _ ρ' π' Hr Hd).
      Qed.

      (* A concrete error would be an error of [M] on the eager trace,
         which the criterion forbids as long as [idImpl] cannot error on
         any prefix of it. *)
      Lemma Inv_noerror ev : ~ uerror ev σ c.
      Proof.
        intros Huerr. inversion Huerr as [f ts Hfind Herror].
        inversion Herror as [tt op s' k Hvf]; subst. simpl in Hfind.
        assert (Hr : rfind c tt = None) by (unfold rfind; rewrite Hfind; reflexivity).
        apply (NoErr_no_TErr e f Hcl (nd_noerr _ _ _ _ _ N)).
        eapply run_ImplTraces. eapply run_step; [exact (nd_run _ _ _ _ _ N) |].
        eapply (TraceStepError M e σ ce f (Build_ThreadEvent tt (InvEv op))
                  (Build_ThreadState f (Vis op k) None)).
        - simpl. rewrite (strip_rel_not_ready _ _ _ (nd_strip _ _ _ _ _ N) Hr). exact Hfind.
        - constructor. exact Hvf.
      Qed.
    End Step.

    (** * The simulation *)

    (* Selecting the candidate set at a node: restrict the speculative
       closure of [Δ] to [Dset e c] (nonempty by the criterion, since no
       prefix of [e] errors), then either it errors or it is a [Node]. *)
    Lemma node_setup (Hcl : CompLin M σ0 ρ0) e ce σ c Δ :
      run e σ ce -> strip_rel c ce -> NoErr e ->
      (forall ρ π, Dset e c ρ π -> pt_in (ac_steps Δ) ρ π) ->
      exists Δ0, AbstractUpdateSteps Δ Δ0 /\ (ErrorCore Δ0 \/ Node e ce σ c Δ0).
    Proof.
      intros Hrun Hs Hne HD.
      destruct (NoErr_lin_reach e Hcl Hne (run_ImplTraces _ _ _ Hrun)) as (ρw & πw & Hlrw).
      destruct (Dset_nonempty e c ρw πw Hlrw) as [πd Hd].
      destruct (HD _ _ Hd) as [πd2 [Heqd Hd2]].
      assert (Hne0 : exists ρ π, ac_steps Δ ρ π /\ Dset e c ρ π)
        by (exists ρw, πd2; split; auto; eapply Dset_pt_eq; eauto).
      set (Δ0 := ac_restrict (ac_steps Δ) (Dset e c) Hne0).
      assert (Hsub : (Δ0 ⊆ ac_steps Δ)%AbstractConfig) by (intros ρ π [H _]; exact H).
      exists Δ0. split; [econstructor; [exact Hsub | constructor] |].
      destruct (classic (ErrorCore Δ0)) as [Herr0 | Hnoerr0]; [left; exact Herr0 | right].
      constructor; auto.
      - intros ρ π H. destruct (HD _ _ H) as [π2 [Heq H2]].
        exists π2. split; auto. split; auto. eapply Dset_pt_eq; eauto.
      - intros ρ π [_ H]. exact H.
    Qed.

    Lemma Inv_TPSimulation (Hcl : CompLin M σ0 ρ0) :
      forall σ c Δ, Inv σ c Δ -> TPSimulation M σ c Δ.
    Proof.
      cofix CH. intros σ c Δ HInv.
      destruct HInv as [Herr | (e & ce & Hrun & Hs & Hne & HD) ].
      { apply TPSimRoll with (Δ' := Δ); [constructor | left; exact Herr]. }
      destruct (node_setup Hcl e ce σ c Δ Hrun Hs Hne HD) as [Δ0 [Hupd [Herr0 | N]]].
      { apply TPSimRoll with (Δ' := Δ0); [exact Hupd | left; exact Herr0]. }
      apply TPSimRoll with (Δ' := Δ0); [exact Hupd |].
      right. constructor.
      - intros t f c' Hstep. apply CH. exact (Inv_next_inv _ _ _ _ _ N t f c' Hstep).
      - intros t f ret c' Hstep. split.
        + exact (proj1 (Inv_next_ret _ _ _ _ _ N t f ret c' Hstep)).
        + apply CH. exact (proj2 (Inv_next_ret _ _ _ _ _ N t f ret c' Hstep)).
      - intros ev σ' c' Hstep. exists Δ0. split; [exact (ac_steps_refl Δ0) |].
        apply CH. exact (Inv_next_u _ _ _ _ _ N ev σ' c' Hstep).
      - intros t c' Hstep. apply CH. exact (Inv_next_tau _ _ _ _ _ N t c' Hstep).
      - exact (Inv_noerror _ _ _ _ _ Hcl N).
    Qed.

    (* Lemma 5.3 (complete direction): Compositional Linearizability
       (Definition 4.1, [CompLin.CompLin]) implies the Threadpool Simulation
       (Definition 5.2, [TPSimulationSet.cal]). *)
    Theorem CompLin_to_cal : CompLin M σ0 ρ0 -> cal M σ0 ρ0.
    Proof.
      intros Hcl. apply Inv_TPSimulation; [exact Hcl |]. right.
      exists nil, (TMap.empty _). split; [apply rt_refl |]. split.
      - intros t. unfold rfind. rewrite !TMap.gempty. reflexivity.
      - split; [apply NoErr_nil |].
        intros ρ π [πe [Hlr Hu]]. apply lin_reach_nil in Hlr. destruct Hlr as [Hρ Hn]. subst ρ.
        exists (TMap.empty _). split.
        + intros t. rewrite Hu, Hn, TMap.gempty. unfold rfind. rewrite TMap.gempty. reflexivity.
        + exact (ac_steps_refl (ac_init ρ0) ρ0 (TMap.empty _) (ACSingle _ _)).
    Qed.

  End Completeness.

  (* Lemma 5.3: the Threadpool Simulation and Compositional Linearizability
     coincide. *)
  Theorem cal_iff_CompLin {E F : Op.t} {VE : @LTS E} {VF : @LTS F}
      (M : ModuleImpl E F) (σ0 : State VE) (ρ0 : State VF) :
    cal M σ0 ρ0 <-> CompLin.CompLin M σ0 ρ0.
  Proof.
    split.
    - apply CompLinSound.cal_to_CompLin.
    - apply CompLin_to_cal.
  Qed.

  (* Corollary: any compositionally linearizable layer implementation is
     verified against the Threadpool Simulation; the converse of
     [CompLinSound.LISim2LILin]. *)
  Theorem layer_implementation_cal {L L' : layer_interface}
      (LI : layer_implementation_linearizability L L') :
    cal (li_impl LI) (li_init L) (li_init L').
  Proof. apply CompLin_to_cal. exact (li_correct LI). Qed.

  Definition LILin2LISim {L L' : layer_interface}
      (LI : layer_implementation_linearizability L L') :
      layer_implementation_simulation L L' :=
  {|
    TPSimulation.li_impl := li_impl LI;
    TPSimulation.li_correct := layer_implementation_cal LI;
  |}.

End CompLinComplete.
