Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.
Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.Program.Equality.
Require Import Classical.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import SeparationAlgebra.
Require Import LTSLocality.
Require Import Assertion.
Require Import TPSimulationSet.
Require Import RGISimulationSet.
Require Import RGILogicSet.
Require Import CompLin.
Require Import CompLinSound.
Require Import CompLinComplete.
Require Import CompLinAux.
Require Import RGILogicSetComplete.

(** Completeness of the thread-local reasoning for Compositional
    Linearizability, modulo auxiliary state.

    Given [CompLin M σ0 ρ0], the canonical thread-pool simulation of
    [CompLinComplete] is cut into rely/guarantee/invariant triples over the
    auxiliary interfaces of [CompLinAux]: the invariant [I] says that the
    abstract configuration is (up to pending speculation) the candidate set
    of some eager trace whose pool replays the recorded underlay history
    ([thread_run]); each guarantee [G t] is the shape of the moves thread
    [t] makes; the relies are the other threads' guarantees. Every method
    body is then method-simulated from its invocation states, and the
    logic's completeness ([RGILogicSetComplete]) turns that into a proof in
    the program logic. The auxiliary state is what makes two canonical
    witnesses of the same proof state agree on every thread's continuation
    up to silent steps ([thread_run_det]), which is what thread [t] needs
    to stay consistent with the environment's moves. *)
Module CompLinRGComplete.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import TPSimulationSet.TPSimulation.
  Import CompLin.CompLin.
  Import CompLinComplete.CompLinComplete.
  Import CompLinAux.CompLinAux.

  Section Bookkeeping.
    Context {E F : Op.t}.
    Context (M : ModuleImpl E F).

    (** * Per-thread views of traces and histories *)

    (* The operations thread [u] has invoked along an overlay trace. *)
    Definition tops_item (u : tid) (l : list (Sig.op F)) (x : TraceItem F) : list (Sig.op F) :=
      match x with
      | TEvent ev =>
          match te_ev ev with
          | InvEv f => if Pos.eq_dec (te_tid ev) u then l ++ f :: nil else l
          | ResEv _ _ => l
          end
      | TErr _ => l
      end.

    Definition tops (e : Trace F) (u : tid) : list (Sig.op F) :=
      fold_left (tops_item u) e nil.

    Lemma tops_snoc e x u : tops (e ++ x :: nil) u = tops_item u (tops e u) x.
    Proof. unfold tops. rewrite fold_left_app. reflexivity. Qed.

    (* The underlay events of thread [u] in a history. *)
    Definition hist_u (h : list (@ThreadEvent E)) (u : tid) : list (@Event E) :=
      map te_ev (filter (fun ev => if Pos.eq_dec (te_tid ev) u then true else false) h).

    Lemma hist_u_snoc h ev u :
      hist_u (h ++ ev :: nil) u =
      if Pos.eq_dec (te_tid ev) u then hist_u h u ++ te_ev ev :: nil else hist_u h u.
    Proof.
      unfold hist_u. rewrite filter_app, map_app. simpl.
      destruct (Pos.eq_dec (te_tid ev) u); simpl; [reflexivity | rewrite app_nil_r; reflexivity].
    Qed.

    (** * Replaying one thread *)

    (* Silent steps as a relation between programs. *)
    Definition tau_eq {A} (p q : Prog E A) : Prop :=
      exists i j r, p = taus i r /\ q = taus j r.

    Lemma tau_eq_refl {A} (p : Prog E A) : tau_eq p p.
    Proof. exists O, O, p. auto. Qed.

    Lemma tau_eq_sym {A} (p q : Prog E A) : tau_eq p q -> tau_eq q p.
    Proof. intros (i & j & r & H1 & H2). exists j, i, r. auto. Qed.

    Lemma taus_vis_inv {A} i (r : Prog E A) op k :
      taus i r = Vis op k -> i = O /\ r = Vis op k.
    Proof. destruct i; simpl; intros H; [auto | discriminate]. Qed.

    Lemma taus_ret_inv {A} i (r : Prog E A) a :
      taus i r = Ret a -> i = O /\ r = Ret a.
    Proof. destruct i; simpl; intros H; [auto | discriminate]. Qed.

    Lemma taus_tau_inv {A} i (r : Prog E A) p :
      taus i r = Tau p -> (i = O /\ r = Tau p) \/ (exists i', i = S i' /\ taus i' r = p).
    Proof.
      destruct i; simpl; intros H; [left; auto | right]. exists i. injection H. auto.
    Qed.

    Lemma taus_plus {A} i j (r : Prog E A) : taus i (taus j r) = taus (i + j) r.
    Proof. induction i; simpl; [reflexivity | rewrite IHi; reflexivity]. Qed.

    Lemma tau_eq_trans {A} (p q s : Prog E A) : tau_eq p q -> tau_eq q s -> tau_eq p s.
    Proof.
      intros (i & j & r & -> & ->) (i' & j' & r' & Hr & ->).
      revert i' r' Hr. induction j as [ | j IHj]; intros i' r' Hr; simpl in Hr.
      - subst r. exists (Nat.add i i'), j', r'. split; [apply taus_plus | reflexivity].
      - destruct i' as [ | i']; simpl in Hr.
        + subst r'. exists i, (Nat.add j' (S j)), r. split; [reflexivity |].
          change (Tau (taus j r)) with (taus (S j) r). apply taus_plus.
        + injection Hr. intros Hr'.
          destruct (IHj i' r' Hr') as (a & c & q & Hq1 & Hq2). exists a, c, q. auto.
    Qed.

    Lemma tau_eq_vis {A} (op op' : Sig.op E) (k : Sig.ar op -> Prog E A) k' :
      tau_eq (Vis op k) (Vis op' k') -> Vis op k = Vis op' k'.
    Proof.
      intros (i & j & r & H1 & H2). symmetry in H1. symmetry in H2.
      apply taus_vis_inv in H1. apply taus_vis_inv in H2.
      destruct H1 as [_ H1]. destruct H2 as [_ H2]. subst r. exact H2.
    Qed.

    Lemma tau_eq_ret_vis {A} (a : A) op k :
      tau_eq (Ret a) (Vis op k) -> False.
    Proof.
      intros (i & j & r & H1 & H2). symmetry in H1. symmetry in H2.
      apply taus_ret_inv in H1. apply taus_vis_inv in H2.
      destruct H1 as [_ H1]. destruct H2 as [_ H2]. subst. discriminate.
    Qed.

    Lemma tau_eq_ret {A} (a a' : A) :
      tau_eq (@Ret E A a) (@Ret E A a') -> a = a'.
    Proof.
      intros (i & j & r & H1 & H2). symmetry in H1. symmetry in H2.
      apply taus_ret_inv in H1. apply taus_ret_inv in H2.
      destruct H1 as [_ H1]. destruct H2 as [_ H2]. subst. injection H2. auto.
    Qed.

    Lemma tau_eq_tau_l {A} (p q : Prog E A) : tau_eq (Tau p) q -> tau_eq p q.
    Proof.
      intros (i & j & r & H1 & H2). symmetry in H1.
      destruct (taus_tau_inv _ _ _ H1) as [[Hi Hr] | [i' [Hi Hp]]].
      - destruct Hi; subst r. exists O, (S j), p. split; [reflexivity |].
        rewrite H2. simpl. apply taus_tau.
      - subst. exists i', j, r. auto.
    Qed.

    Lemma tau_eq_tau_l' {A} (p q : Prog E A) : tau_eq p q -> tau_eq (Tau p) q.
    Proof.
      intros (i & j & r & H1 & H2). exists (S i), j, r. simpl. subst. auto.
    Qed.

    Lemma tau_eq_taus {A} k (p : Prog E A) : tau_eq (taus k p) p.
    Proof. exists k, O, p. auto. Qed.

    (* The states an instance of [f] on thread [u] can be in after
       consuming a sequence of underlay events, up to silent steps. *)
    Inductive inst (u : tid) (f : Sig.op F) :
        list (@Event E) -> Prog E (Sig.ar f) -> option (Sig.op E) -> Prop :=
    | inst_start : inst u f nil (M f u) None
    | inst_tau evs p b :
        inst u f evs (Tau p) b -> inst u f evs p b
    | inst_inv evs op k :
        inst u f evs (Vis op k) None ->
        inst u f (evs ++ InvEv op :: nil) (Vis op k) (Some op)
    | inst_res evs op k ret :
        inst u f evs (Vis op k) (Some op) ->
        inst u f (evs ++ ResEv op ret :: nil) (k ret) None.

    Lemma inst_nil_inv u f p b : inst u f nil p b -> tau_eq p (M f u) /\ b = None.
    Proof.
      intros H. remember nil as evs. induction H; subst.
      - split; [apply tau_eq_refl | reflexivity].
      - destruct (IHinst eq_refl) as [Hp Hb]. split; [apply tau_eq_tau_l; exact Hp | exact Hb].
      - exfalso. symmetry in Heqevs. eapply app_cons_not_nil; eauto.
      - exfalso. symmetry in Heqevs. eapply app_cons_not_nil; eauto.
    Qed.

    Lemma inst_snoc_inv u f evs x p b :
      inst u f (evs ++ x :: nil) p b ->
      exists p0 b0 p1 b1, inst u f evs p0 b0 /\ tau_eq p p1 /\ b = b1 /\
        ((exists op k, x = InvEv op /\ tau_eq p0 (Vis op k) /\ b0 = None /\
                       p1 = Vis op k /\ b1 = Some op) \/
         (exists op k ret, x = ResEv op ret /\ tau_eq p0 (Vis op k) /\ b0 = Some op /\
                           p1 = k ret /\ b1 = None)).
    Proof.
      intros H. remember (evs ++ x :: nil) as evs' eqn:Heq.
      revert evs x Heq. induction H as [ | evs0 p b H IH | evs0 op k H IH | evs0 op k ret H IH];
        intros evs x Heq.
      - exfalso. symmetry in Heq. eapply app_cons_not_nil; eauto.
      - destruct (IH evs x Heq) as (p0 & b0 & p1 & b1 & Hi & Heq1 & Hb & Hx).
        exists p0, b0, p1, b1. split; auto. split; auto. apply tau_eq_tau_l. exact Heq1.
      - apply app_inj_tail in Heq. destruct Heq as [Heqe Heqx]. subst.
        exists (Vis op k), None, (Vis op k), (Some op).
        split; [exact H |]. split; [apply tau_eq_refl |]. split; [reflexivity |].
        left. exists op, k. repeat split. apply tau_eq_refl.
      - apply app_inj_tail in Heq. destruct Heq as [Heqe Heqx]. subst.
        exists (Vis op k), (Some op), (k ret), None.
        split; [exact H |]. split; [apply tau_eq_refl |]. split; [reflexivity |].
        right. exists op, k, ret. repeat split. apply tau_eq_refl.
    Qed.

    Lemma vis_inj (op : Sig.op E) {A} (k k' : Sig.ar op -> Prog E A) :
      Vis op k = Vis op k' -> k = k'.
    Proof.
      intros H. injection H. intros H'.
      apply Eqdep.EqdepTheory.inj_pair2 in H'. exact H'.
    Qed.

    (* Replaying an instance is deterministic up to silent steps. *)
    Lemma inst_det u f evs : forall p1 b1 p2 b2,
      inst u f evs p1 b1 -> inst u f evs p2 b2 -> tau_eq p1 p2 /\ b1 = b2.
    Proof.
      induction evs as [ | x evs IH] using rev_ind; intros p1 b1 p2 b2 H1 H2.
      - apply inst_nil_inv in H1. apply inst_nil_inv in H2.
        destruct H1 as [H1 ->]. destruct H2 as [H2 ->].
        split; [ | reflexivity]. eapply tau_eq_trans; [exact H1 | apply tau_eq_sym; exact H2].
      - apply inst_snoc_inv in H1. apply inst_snoc_inv in H2.
        destruct H1 as (p0 & b0 & q1 & c1 & Hi1 & Heq1 & Hb1 & Hx1).
        destruct H2 as (p0' & b0' & q2 & c2 & Hi2 & Heq2 & Hb2 & Hx2). subst b1 b2.
        destruct (IH _ _ _ _ Hi1 Hi2) as [Heq0 Hb0].
        assert (Hq : q1 = q2 /\ c1 = c2).
        { destruct Hx1 as [ (op & k & Hx1 & Hv1 & Hb01 & Hq1 & Hc1)
                          | (op & k & ret & Hx1 & Hv1 & Hb01 & Hq1 & Hc1) ];
            destruct Hx2 as [ (op' & k' & Hx2 & Hv2 & Hb02 & Hq2 & Hc2)
                            | (op' & k' & ret' & Hx2 & Hv2 & Hb02 & Hq2 & Hc2) ];
            subst; try discriminate.
          - injection Hx2. intros Hop. subst op'.
            assert (Hvv : tau_eq (Vis op k) (Vis op k')).
            { eapply tau_eq_trans; [apply tau_eq_sym; exact Hv1 |].
              eapply tau_eq_trans; [exact Heq0 | exact Hv2]. }
            apply tau_eq_vis in Hvv. apply vis_inj in Hvv. subst. auto.
          - injection Hx2. intros Hret Hop. subst op'.
            apply Eqdep.EqdepTheory.inj_pair2 in Hret. subst ret'.
            assert (Hvv : tau_eq (Vis op k) (Vis op k')).
            { eapply tau_eq_trans; [apply tau_eq_sym; exact Hv1 |].
              eapply tau_eq_trans; [exact Heq0 | exact Hv2]. }
            apply tau_eq_vis in Hvv. apply vis_inj in Hvv. subst. auto. }
        destruct Hq as [Hq1 Hq2]. subst q2 c2. split; [ | reflexivity].
        eapply tau_eq_trans; [exact Heq1 | apply tau_eq_sym; exact Heq2].
    Qed.

    (* An instance that has reached a value consumes no further event. *)
    Lemma inst_ready_no_event u f evs r x evs' p b :
      inst u f evs (Ret r) None -> inst u f (evs ++ x :: evs') p b -> False.
    Proof.
      revert x p b. induction evs' as [ | y evs' IH] using rev_ind; intros x p b H1 H2.
      - apply inst_snoc_inv in H2. destruct H2 as (p0 & b0 & p1 & b1 & Hi & _ & _ & Hx).
        destruct (inst_det _ _ _ _ _ _ _ H1 Hi) as [Heq _].
        destruct Hx as [ (op & k & _ & Hv & _) | (op & k & ret & _ & Hv & _) ];
          eapply tau_eq_ret_vis; eapply tau_eq_trans; eauto.
      - rewrite app_comm_cons, app_assoc in H2.
        apply inst_snoc_inv in H2. destruct H2 as (p0 & b0 & p1 & b1 & Hi & _).
        eapply IH; eauto.
    Qed.

    (* The thread states of [u] after a sequence of operations and a
       sequence of underlay events. *)
    Inductive thread_run (u : tid) :
        list (Sig.op F) -> list (@Event E) -> option (@ThreadState E F) -> Prop :=
    | tr_nil : thread_run u nil nil None
    | tr_inst ops evs f evsf p b :
        thread_run u ops evs None -> inst u f evsf p b ->
        thread_run u (ops ++ f :: nil) (evs ++ evsf) (Some (Build_ThreadState f p b))
    | tr_ret ops evs f r :
        thread_run u ops evs (Some (Build_ThreadState f (Ret r) None)) ->
        thread_run u ops evs None.

    Lemma thread_run_some_inv u ops evs f p b :
      thread_run u ops evs (Some (Build_ThreadState f p b)) ->
      exists ops0 evs0 evsf, ops = ops0 ++ f :: nil /\ evs = evs0 ++ evsf /\
        thread_run u ops0 evs0 None /\ inst u f evsf p b.
    Proof.
      intros H. inversion H as [ | ops0 evs0 f0 evsf p0 b0 H0 Hi |]; subst.
      repeat match goal with
             | Hts : Build_ThreadState _ _ _ = Build_ThreadState _ _ _ |- _ =>
                 inversion Hts; subst; clear Hts
             | H' : existT _ _ _ = existT _ _ _ |- _ =>
                 apply Eqdep.EqdepTheory.inj_pair2 in H'; subst
             end.
      exists ops0, evs0, evsf. auto.
    Qed.

    Lemma thread_run_nil_inv u evs ots : thread_run u nil evs ots -> evs = nil /\ ots = None.
    Proof.
      intros H. remember nil as ops. induction H; subst.
      - auto.
      - exfalso. symmetry in Heqops. eapply app_cons_not_nil; eauto.
      - destruct (IHthread_run eq_refl) as [_ H']. discriminate.
    Qed.

    Lemma prefix_comparable {A} (l1 r1 l2 r2 : list A) :
      l1 ++ r1 = l2 ++ r2 -> (exists r, l2 = l1 ++ r) \/ (exists r, l1 = l2 ++ r).
    Proof.
      revert l2. induction l1 as [ | a l1 IH]; intros l2 H.
      - left. exists l2. reflexivity.
      - destruct l2 as [ | b l2].
        + right. exists (a :: l1). reflexivity.
        + simpl in H. injection H. intros H' ->.
          destruct (IH l2 H') as [[r Hr] | [r Hr]].
          * left. exists r. simpl. rewrite Hr. reflexivity.
          * right. exists r. simpl. rewrite Hr. reflexivity.
    Qed.

    (* A thread that has returned has consumed a determined number of
       events. *)
    Lemma thread_run_none_det u ops : forall evs1 evs2,
      thread_run u ops evs1 None -> thread_run u ops evs2 None ->
      ((exists r, evs2 = evs1 ++ r) \/ (exists r, evs1 = evs2 ++ r)) ->
      evs1 = evs2.
    Proof.
      induction ops as [ | g ops IH] using rev_ind; intros evs1 evs2 H1 H2 Hpre.
      - apply thread_run_nil_inv in H1. apply thread_run_nil_inv in H2.
        destruct H1 as [-> _]. destruct H2 as [-> _]. reflexivity.
      - inversion H1 as [ | | ops1 evs1' f1 r1 H1']; subst.
        { exfalso.
          match goal with
          | H : nil = _ ++ _ :: _ |- _ => exact (app_cons_not_nil _ _ _ H)
          | H : _ ++ _ :: _ = nil |- _ => exact (app_cons_not_nil _ _ _ (eq_sym H))
          end. }
        inversion H2 as [ | | ops2 evs2' f2 r2 H2']; subst.
        { exfalso.
          match goal with
          | H : nil = _ ++ _ :: _ |- _ => exact (app_cons_not_nil _ _ _ H)
          | H : _ ++ _ :: _ = nil |- _ => exact (app_cons_not_nil _ _ _ (eq_sym H))
          end. }
        apply thread_run_some_inv in H1'. apply thread_run_some_inv in H2'.
        destruct H1' as (o1 & e1 & ef1 & Ho1 & He1 & Hr1 & Hi1).
        destruct H2' as (o2 & e2 & ef2 & Ho2 & He2 & Hr2 & Hi2). subst evs1 evs2.
        apply app_inj_tail in Ho1. apply app_inj_tail in Ho2.
        destruct Ho1 as [Ho1 Hf1]. destruct Ho2 as [Ho2 Hf2]. subst o1 o2 f1 f2.
        assert (He : e1 = e2).
        { apply (IH e1 e2 Hr1 Hr2).
          destruct Hpre as [[r Hr] | [r Hr]].
          - rewrite <- app_assoc in Hr. eapply prefix_comparable. symmetry. exact Hr.
          - rewrite <- app_assoc in Hr. destruct (prefix_comparable _ _ _ _ Hr) as [H' | H']; auto. }
        subst e2. f_equal.
        destruct Hpre as [[r Hr] | [r Hr]].
        + rewrite <- app_assoc in Hr. apply app_inv_head in Hr.
          destruct r as [ | x r]; [rewrite app_nil_r in Hr; symmetry; exact Hr |].
          exfalso. rewrite Hr in Hi2. exact (inst_ready_no_event _ _ _ _ _ _ _ _ Hi1 Hi2).
        + rewrite <- app_assoc in Hr. apply app_inv_head in Hr.
          destruct r as [ | x r]; [rewrite app_nil_r in Hr; exact Hr |].
          exfalso. rewrite Hr in Hi1. exact (inst_ready_no_event _ _ _ _ _ _ _ _ Hi2 Hi1).
    Qed.

    (* Replaying a thread is deterministic up to silent steps. *)
    Lemma thread_run_det u ops evs f p1 b1 p2 b2 :
      thread_run u ops evs (Some (Build_ThreadState f p1 b1)) ->
      thread_run u ops evs (Some (Build_ThreadState f p2 b2)) ->
      tau_eq p1 p2 /\ b1 = b2.
    Proof.
      intros H1 H2.
      apply thread_run_some_inv in H1. apply thread_run_some_inv in H2.
      destruct H1 as (o1 & e1 & ef1 & Ho1 & He1 & Hr1 & Hi1).
      destruct H2 as (o2 & e2 & ef2 & Ho2 & He2 & Hr2 & Hi2).
      subst ops. apply app_inj_tail in Ho2. destruct Ho2 as [Ho2 _]. subst o1.
      assert (He : e1 = e2).
      { apply (thread_run_none_det u o2 e1 e2 Hr1 Hr2).
        rewrite He2 in He1. eapply prefix_comparable. exact (eq_sym He1). }
      subst e2. rewrite He2 in He1. apply app_inv_head in He1. subst ef2.
      eapply inst_det; eauto.
    Qed.

    Lemma thread_run_op u ops evs f p b :
      thread_run u ops evs (Some (Build_ThreadState f p b)) ->
      exists ops0, ops = ops0 ++ f :: nil.
    Proof.
      intros H. apply thread_run_some_inv in H. destruct H as (o & _ & _ & Ho & _). eauto.
    Qed.

    (** Steps of a thread, on the replay. *)

    Lemma thread_run_invoke u ops evs f :
      thread_run u ops evs None ->
      thread_run u (ops ++ f :: nil) evs (Some (Build_ThreadState f (M f u) None)).
    Proof.
      intros H. rewrite <- (app_nil_r evs). apply tr_inst; [exact H | constructor].
    Qed.

    Lemma thread_run_tau u ops evs f p b :
      thread_run u ops evs (Some (Build_ThreadState f (Tau p) b)) ->
      thread_run u ops evs (Some (Build_ThreadState f p b)).
    Proof.
      intros H. apply thread_run_some_inv in H.
      destruct H as (o & e & ef & Ho & He & Hr & Hi). subst.
      apply tr_inst; [exact Hr | apply inst_tau; exact Hi].
    Qed.

    Lemma thread_run_taus u ops evs f k p b :
      thread_run u ops evs (Some (Build_ThreadState f (taus k p) b)) ->
      thread_run u ops evs (Some (Build_ThreadState f p b)).
    Proof.
      induction k as [ | k IH]; intros H; [exact H |].
      apply IH. apply thread_run_tau. exact H.
    Qed.

    Lemma thread_run_uinv u ops evs f op k :
      thread_run u ops evs (Some (Build_ThreadState f (Vis op k) None)) ->
      thread_run u ops (evs ++ InvEv op :: nil) (Some (Build_ThreadState f (Vis op k) (Some op))).
    Proof.
      intros H. apply thread_run_some_inv in H.
      destruct H as (o & e & ef & Ho & He & Hr & Hi). subst.
      rewrite <- app_assoc. apply tr_inst; [exact Hr | apply inst_inv; exact Hi].
    Qed.

    Lemma thread_run_ures u ops evs f op k ret :
      thread_run u ops evs (Some (Build_ThreadState f (Vis op k) (Some op))) ->
      thread_run u ops (evs ++ ResEv op ret :: nil) (Some (Build_ThreadState f (k ret) None)).
    Proof.
      intros H. apply thread_run_some_inv in H.
      destruct H as (o & e & ef & Ho & He & Hr & Hi). subst.
      rewrite <- app_assoc. apply tr_inst; [exact Hr | apply inst_res; exact Hi].
    Qed.

    Lemma thread_run_return u ops evs f r :
      thread_run u ops evs (Some (Build_ThreadState f (Ret r) None)) ->
      thread_run u ops evs None.
    Proof. intros H. eapply tr_ret. exact H. Qed.

  End Bookkeeping.
  (** * The construction *)

  Section Construction.
    Import AssertionsSet.
    Import RGISimulationSet.RGISimulation.
    Import RGILogicSet.RGILogic.
    Open Scope assertion_scope.

    Context {E F : Op.t} {VE : @LTS E} {VF : @LTS F}.
    Context (M : ModuleImpl E F) (σ0 : State VE) (ρ0 : State VF).
    Hypothesis Hcl : CompLin M σ0 ρ0.

    Notation VE' := (hist_lts VE).
    Notation VF' := (ops_lts VF).
    Definition σ0' : State VE' := pair σ0 nil.
    Definition ρ0' : State VF' := pair ρ0 (fun _ => nil).
    Notation rd := (@ready_tc E F).
    Notation Hrd := (@ready_tc_ok E F).
    Notation PS := (@ProofState E F VE' VF').

    Lemma Hcl' : CompLin M σ0' ρ0'.
    Proof. exact (CompLin_aux M σ0 ρ0 Hcl). Qed.

    (** ** Operation lists carried by the possibilities *)

    Definition inv_ops (ρ' : State VF') (π : tmap (@LinState F)) (u : tid) : list (Sig.op F) :=
      snd ρ' u ++ match TMap.find u π with Some (ls_inv f) => f :: nil | _ => nil end.

    Definition ops_at (Δ : AbstractConfig VF') (u : tid) (l : list (Sig.op F)) : Prop :=
      forall ρ' π, Δ ρ' π -> inv_ops ρ' π u = l.

    Definition ops_uniform (Δ : AbstractConfig VF') : Prop :=
      forall u, exists l, ops_at Δ u l.

    Lemma poss_step_ops (ρ ρ' : State VF') π π' :
      poss_step (PossOk ρ π) (PossOk ρ' π') -> forall u, inv_ops ρ' π' u = inv_ops ρ π u.
    Proof.
      intros Hstep u. unfold inv_ops.
      inversion Hstep as [tt ff s1 s2 pp Hvf Hlin | tt ff rr s1 s2 pp Hvf Hlin |]; subst;
        simpl in Hvf; destruct Hvf as [_ Hops]; rewrite Hops; unfold ops_add; simpl.
      - destruct (Pos.eq_dec u tt); subst.
        + rewrite TMap.gss, Hlin. rewrite app_nil_r. reflexivity.
        + rewrite TMap.gso; auto.
      - destruct (Pos.eq_dec u tt); subst.
        + rewrite TMap.gss, Hlin. reflexivity.
        + rewrite TMap.gso; auto.
    Qed.

    Lemma poss_steps_ops_gen : forall (p q : @Poss F VF'), poss_steps p q ->
      forall ρ π ρ' π', p = PossOk ρ π -> q = PossOk ρ' π' ->
      forall u, inv_ops ρ' π' u = inv_ops ρ π u.
    Proof.
      intros p q H. induction H; intros ρ π ρ' π' Hp Hq u; subst.
      - eapply poss_step_ops; eauto.
      - inversion Hq; subst. reflexivity.
      - destruct y as [ρm πm |].
        + rewrite (IHclos_refl_trans2 ρm πm ρ' π' eq_refl eq_refl u).
          apply (IHclos_refl_trans1 ρ π ρm πm eq_refl eq_refl u).
        + exfalso. eapply CompLinSound.poss_steps_from_error in H0; [discriminate | reflexivity].
    Qed.

    Lemma poss_steps_ops (ρ ρ' : State VF') π π' :
      poss_steps (PossOk ρ π) (PossOk ρ' π') -> forall u, inv_ops ρ' π' u = inv_ops ρ π u.
    Proof. intros H. eapply poss_steps_ops_gen; eauto. Qed.

    Lemma ops_at_steps (Δ Δ' : AbstractConfig VF') u l :
      (Δ' ⊆ ac_steps Δ)%AbstractConfig -> ops_at Δ u l -> ops_at Δ' u l.
    Proof.
      intros Hsub Hl ρ' π' H. apply Hsub in H.
      inversion H as [ρ π ρ'' π'' Hposs Hsteps]; subst.
      rewrite (poss_steps_ops _ _ _ _ Hsteps). apply Hl. exact Hposs.
    Qed.

    Lemma ops_uniform_steps (Δ Δ' : AbstractConfig VF') :
      (Δ' ⊆ ac_steps Δ)%AbstractConfig -> ops_uniform Δ -> ops_uniform Δ'.
    Proof. intros Hsub Hu u. destruct (Hu u) as [l Hl]. exists l. eapply ops_at_steps; eauto. Qed.

    Lemma ops_at_unique (Δ : AbstractConfig VF') u l l' :
      ops_at Δ u l -> ops_at Δ u l' -> l = l'.
    Proof.
      intros H1 H2. destruct (ac_nonempty Δ) as [ρ [π Hposs]].
      rewrite <- (H1 _ _ Hposs). apply H2. exact Hposs.
    Qed.

    Lemma inv_ops_inv (ρ' : State VF') π t f u :
      inv_ops ρ' (TMap.add t (ls_inv f) π) u =
      if Pos.eq_dec u t then snd ρ' t ++ f :: nil else inv_ops ρ' π u.
    Proof.
      unfold inv_ops. destruct (Pos.eq_dec u t); subst.
      - rewrite TMap.gss. reflexivity.
      - rewrite TMap.gso; auto.
    Qed.

    Lemma inv_ops_res (ρ' : State VF') π t u :
      inv_ops ρ' (TMap.remove t π) u =
      if Pos.eq_dec u t then snd ρ' t else inv_ops ρ' π u.
    Proof.
      unfold inv_ops. destruct (Pos.eq_dec u t); subst.
      - rewrite TMap.grs, app_nil_r. reflexivity.
      - rewrite TMap.gro; auto.
    Qed.

    Lemma ops_at_ac_inv_t (Δ : AbstractConfig VF') t f l :
      ops_at Δ t l -> (forall ρ' π, Δ ρ' π -> TMap.find t π = None) ->
      ops_at (ac_inv Δ t f) t (l ++ f :: nil).
    Proof.
      intros Hl Hnone ρ' π H. inversion H as [ρ'' π'' Hposs]; subst.
      rewrite inv_ops_inv. destruct (Pos.eq_dec t t); [ | congruence].
      rewrite <- (Hl _ _ Hposs). unfold inv_ops. rewrite (Hnone _ _ Hposs), app_nil_r. reflexivity.
    Qed.

    Lemma ops_at_ac_inv_o (Δ : AbstractConfig VF') t f u l :
      u <> t -> ops_at Δ u l -> ops_at (ac_inv Δ t f) u l.
    Proof.
      intros Hne Hl ρ' π H. inversion H as [ρ'' π'' Hposs]; subst.
      rewrite inv_ops_inv. destruct (Pos.eq_dec u t); [congruence |]. apply Hl. exact Hposs.
    Qed.

    Lemma ops_at_ac_res_t (Δ : AbstractConfig VF') t f r l :
      ops_at Δ t l -> (forall ρ' π, Δ ρ' π -> TMap.find t π = Some (ls_linr f r)) ->
      ops_at (ac_res Δ t) t l.
    Proof.
      intros Hl Hlin ρ' π H. inversion H as [ρ'' π'' Hposs]; subst.
      rewrite inv_ops_res. destruct (Pos.eq_dec t t); [ | congruence].
      rewrite <- (Hl _ _ Hposs). unfold inv_ops. rewrite (Hlin _ _ Hposs), app_nil_r. reflexivity.
    Qed.

    Lemma ops_at_ac_res_o (Δ : AbstractConfig VF') t u l :
      u <> t -> ops_at Δ u l -> ops_at (ac_res Δ t) u l.
    Proof.
      intros Hne Hl ρ' π H. inversion H as [ρ'' π'' Hposs]; subst.
      rewrite inv_ops_res. destruct (Pos.eq_dec u t); [congruence |]. apply Hl. exact Hposs.
    Qed.

    Lemma ops_uniform_ac_inv (Δ : AbstractConfig VF') t f :
      ops_uniform Δ -> (forall ρ' π, Δ ρ' π -> TMap.find t π = None) ->
      ops_uniform (ac_inv Δ t f).
    Proof.
      intros Hu Hnone u. destruct (Hu u) as [l Hl]. destruct (Pos.eq_dec u t); subst.
      - exists (l ++ f :: nil). apply ops_at_ac_inv_t; auto.
      - exists l. apply ops_at_ac_inv_o; auto.
    Qed.

    Lemma ops_uniform_ac_res (Δ : AbstractConfig VF') t f r :
      ops_uniform Δ -> (forall ρ' π, Δ ρ' π -> TMap.find t π = Some (ls_linr f r)) ->
      ops_uniform (ac_res Δ t).
    Proof.
      intros Hu Hlin u. destruct (Hu u) as [l Hl]. destruct (Pos.eq_dec u t); subst.
      - exists l. eapply ops_at_ac_res_t; eauto.
      - exists l. apply ops_at_ac_res_o; auto.
    Qed.

    (* On the possibilities of the identity implementation, the operation
       lists are those of the trace. *)
    Lemma lin_reach_ops e (ρ' : State VF') π :
      lin_reach ρ0' e ρ' π -> forall u, inv_ops ρ' π u = tops e u.
    Proof.
      induction 1 as [ | s ρ π tt ff Hlr IH Hnone | s ρ π tt ff rr Hlr IH Hlin
                      | s ρ π ρ' π' Hlr IH Hstep]; intros u.
      - unfold inv_ops, tops. simpl. rewrite TMap.gempty. reflexivity.
      - rewrite tops_snoc. simpl. rewrite inv_ops_inv.
        destruct (Pos.eq_dec u tt); subst.
        + destruct (Pos.eq_dec tt tt); [ | congruence].
          rewrite <- (IH tt). unfold inv_ops. rewrite Hnone, app_nil_r. reflexivity.
        + destruct (Pos.eq_dec tt u); [congruence |]. apply IH.
      - rewrite tops_snoc. simpl. rewrite inv_ops_res.
        destruct (Pos.eq_dec u tt); subst.
        + rewrite <- (IH tt). unfold inv_ops. rewrite Hlin, app_nil_r. reflexivity.
        + apply IH.
      - rewrite (poss_step_ops _ _ _ _ Hstep). apply IH.
    Qed.

    Lemma Dset_ops e c (ρ' : State VF') π :
      Dset ρ0' rd e c ρ' π -> forall u, inv_ops ρ' π u = tops e u.
    Proof.
      intros [πe [Hlr Hu]] u. rewrite <- (lin_reach_ops _ _ _ Hlr u).
      unfold inv_ops. rewrite Hu. unfold rfind.
      destruct (TMap.find u c) as [ts|] eqn:Hc; [ | simpl; destruct (TMap.find u πe); reflexivity].
      destruct (rd ts) as [ls|] eqn:Hr; [ | simpl; destruct (TMap.find u πe); reflexivity].
      destruct (ready_some _ Hrd _ _ Hr) as (f & r & k & -> & _).
      simpl. destruct (TMap.find u πe) as [l|]; reflexivity.
    Qed.

    (** ** Histories *)

    Definition hist (σ' : State VE') : list (@ThreadEvent E) := snd σ'.

    Definition consistent (σ' : State VE') (Δ : AbstractConfig VF')
        (c : @ThreadPoolState E F) : Prop :=
      forall u l, ops_at Δ u l -> thread_run M u l (hist_u (hist σ') u) (TMap.find u c).

    (** ** The invariant *)

    Definition IW (s : PS) e c ce : Prop :=
      run M σ0' e (σ s) ce /\ strip_rel rd c ce /\ NoErr ρ0' e /\
      (forall ρ' π, Dset ρ0' rd e c ρ' π -> pt_in (ac_steps (Δ s)) ρ' π) /\
      ops_uniform (Δ s) /\ consistent (σ s) (Δ s) c.

    Definition I (s : PS) : Prop := APError s \/ exists e c ce, IW s e c ce.

    Lemma IW_Inv s e c ce : IW s e c ce -> Inv M σ0' ρ0' rd (σ s) c (Δ s).
    Proof. intros (Hrun & Hs & Hne & HD & _ & _). right. exists e, ce. auto. Qed.

    Lemma apperror_errorcore (σ' : State VE') (Δ' : AbstractConfig VF') :
      APError (σ', Δ') <-> ErrorCore Δ'.
    Proof.
      split.
      - intros H. inversion H as [s ρ π Hposs Hsteps]; subst. exists ρ, π. auto.
      - intros [ρ [π [Hposs Hsteps]]]. eapply APErrorSome with (ρ := ρ) (π := π); simpl; assumption.
    Qed.

    (* Any possibility of an [IW] state has the trace's operation lists
       and the pool's domain. *)
    Lemma IW_Dset_nonempty s e c ce : IW s e c ce -> exists ρ' π, Dset ρ0' rd e c ρ' π.
    Proof.
      intros (Hrun & Hs & Hne & HD & _ & _).
      destruct (NoErr_lin_reach M σ0' ρ0' e Hcl' Hne (run_ImplTraces _ _ _ _ _ Hrun)) as (ρw & πw & Hlrw).
      destruct (Dset_nonempty ρ0' rd e c ρw πw Hlrw) as [πd Hd]. eauto.
    Qed.

    Lemma IW_ops_at s e c ce u : IW s e c ce -> ops_at (Δ s) u (tops e u).
    Proof.
      intros HW. pose proof HW as (Hrun & Hs & Hne & HD & Hu & _).
      destruct (IW_Dset_nonempty _ _ _ _ HW) as (ρd & πd & Hd).
      destruct (HD _ _ Hd) as [π2 [Heq Hst]].
      inversion Hst as [ρ1 π1 ρ2 π2' Hposs Hsteps]; subst.
      destruct (Hu u) as [l Hl].
      intros ρ' π H. rewrite (Hl _ _ H).
      rewrite <- (Hl _ _ Hposs). rewrite <- (poss_steps_ops _ _ _ _ Hsteps u).
      rewrite <- (Dset_ops _ _ _ _ Hd u). unfold inv_ops. rewrite Heq. reflexivity.
    Qed.

    Lemma IW_dom s e c ce ρ' π u :
      IW s e c ce -> Δ s ρ' π -> (TMap.find u π = None <-> TMap.find u c = None).
    Proof.
      intros HW Hposs. pose proof HW as (Hrun & Hs & Hne & HD & Hu & _).
      destruct (IW_Dset_nonempty _ _ _ _ HW) as (ρd & πd & Hd).
      destruct (HD _ _ Hd) as [π2 [Heq Hst]].
      inversion Hst as [ρ1 π1 ρ2 π2' Hposs1 Hsteps]; subst.
      rewrite (ac_find_none_equiv (Δ s) ρ' π ρ1 π1 Hposs Hposs1 u).
      pose proof (poss_steps_domain _ _ _ _ Hsteps u) as Hdom. unfold map_domain in Hdom.
      assert (Hn : TMap.find u π1 = None <-> TMap.find u π2 = None).
      { destruct (TMap.find u π1) as [x|] eqn:H1; destruct (TMap.find u π2) as [y|] eqn:H2.
        - split; discriminate.
        - exfalso. destruct (proj1 Hdom (ex_intro _ x eq_refl)) as [z Hz]. discriminate.
        - exfalso. destruct (proj2 Hdom (ex_intro _ y eq_refl)) as [z Hz]. discriminate.
        - tauto. }
      rewrite Hn, <- Heq.
      destruct Hd as [πe [Hlr Hun]].
      pose proof (Hun u) as Hπ. unfold rfind in Hπ.
      pose proof (lin_reach_dom _ _ _ _ Hlr u) as Hpe.
      pose proof (run_dom _ _ _ _ _ Hrun u) as Hrd. pose proof (Hs u) as Hsu. unfold rfind in Hsu.
      destruct (TMap.find u c) as [ts|] eqn:Hc; try rewrite Hc in Hπ; try rewrite Hc in Hsu.
      - destruct (rd ts) as [ls|] eqn:Hr; try rewrite Hr in Hπ; try rewrite Hr in Hsu.
        + rewrite Hπ. unfold pt_union.
          split; [intros H; destruct (TMap.find u πe); discriminate | discriminate].
        + rewrite Hsu in Hrd.
          assert (Hpe' : TMap.find u πe <> None).
          { intros Hn0. apply Hpe in Hn0. apply Hrd in Hn0. discriminate. }
          rewrite Hπ. unfold pt_union. destruct (TMap.find u πe); [split; discriminate | congruence].
      - rewrite Hsu in Hrd.
        assert (Hpe' : TMap.find u πe = None) by (apply Hpe; apply Hrd; reflexivity).
        rewrite Hπ, Hpe'. simpl. tauto.
    Qed.

    (** ** Guarantees and relies *)

    Inductive Gbase (t : tid) : PS -> PS -> Prop :=
    | gb_id s : Gbase t s s
    | gb_inv s s' f : Ginv t f s s' -> Gbase t s s'
    | gb_ret s s' f r : Gret t f r s s' -> Gbase t s s'
    | gb_upd s s' :
        σ s = σ s' -> (Δ s' ⊆ ac_steps (Δ s))%AbstractConfig ->
        (APError s -> Δ s' = Δ s) -> Gbase t s s'
    | gb_step s s' ev :
        te_tid ev = t -> Step VE' ev (σ s) (σ s') ->
        (Δ s' ⊆ ac_steps (Δ s))%AbstractConfig ->
        (APError s -> Δ s' = Δ s) -> Gbase t s s'.

    Definition G (t : tid) : @RGRelation E F VE' VF' := clos_trans _ (Gbase t).

    Definition R (t : tid) : @RGRelation E F VE' VF' :=
      fun s s' => I s /\ exists t', t' <> t /\ G t' s s'.

    (* Errors are frozen. *)
    Lemma poss_steps_error_add (ρ : State VF') π t f :
      TMap.find t π = None -> poss_steps (PossOk ρ π) PossError ->
      poss_steps (PossOk ρ (TMap.add t (ls_inv f) π)) PossError.
    Proof.
      intros Hnone Hsteps.
      destruct (CompLinSound.poss_steps_error_last _ _ Hsteps) as (t0 & f0 & ρ1 & π1 & Hs & Herr & Hlin).
      set (X := fun u => if Pos.eq_dec u t then Some (ls_inv f) else None).
      assert (Hu : is_union π X (TMap.add t (ls_inv f) π)).
      { intros u. unfold X. destruct (Pos.eq_dec u t); subst.
        - rewrite TMap.gss, Hnone. reflexivity.
        - rewrite TMap.gso; auto. unfold pt_union. destruct (TMap.find u π); reflexivity. }
      destruct (poss_steps_union _ _ _ _ _ _ Hu Hs) as [π2 [Hu2 Hs2]].
      eapply rt_trans; [exact Hs2 |]. apply rt_step.
      eapply poss_error_union; [exact Hu2 |]. eapply ps_error; [exact Herr | exact Hlin].
    Qed.

    Lemma apperror_ac_inv (σ' : State VE') (Δ' : AbstractConfig VF') t f :
      (forall ρ π, Δ' ρ π -> TMap.find t π = None) ->
      APError (σ', Δ') -> APError (σ', ac_inv Δ' t f).
    Proof.
      intros Hnone H. inversion H as [s ρ π Hposs Hsteps]; subst. simpl in *.
      eapply APErrorSome with (ρ := ρ) (π := TMap.add t (ls_inv f) π); simpl.
      - constructor. exact Hposs.
      - apply poss_steps_error_add; [exact (Hnone _ _ Hposs) | exact Hsteps].
    Qed.

    Lemma Gbase_apperror t s s' : Gbase t s s' -> APError s -> APError s'.
    Proof.
      intros Hg Herr. destruct Hg as [s | s s' f [Hσ [Hnone Heq]] | s s' f r [Hσ [Hlin Heq]]
                                     | s s' Hσ Hsub Hfr | s s' ev Ht Hst Hsub Hfr].
      - exact Herr.
      - apply AbstractConfig_ext in Heq. destruct s as [σ1 Δ1]. destruct s' as [σ2 Δ2].
        simpl in *. subst. apply apperror_ac_inv; auto.
      - apply AbstractConfig_ext in Heq. destruct s as [σ1 Δ1]. destruct s' as [σ2 Δ2].
        simpl in *. subst. exact (RGILogicComplete.apperror_res _ _ _ f r Herr Hlin).
      - specialize (Hfr Herr). destruct s as [σ1 Δ1]. destruct s' as [σ2 Δ2]. simpl in *. subst.
        exact Herr.
      - specialize (Hfr Herr). destruct s as [σ1 Δ1]. destruct s' as [σ2 Δ2]. simpl in *. subst.
        eapply RGILogicComplete.apperror_state. exact Herr.
    Qed.

    Lemma G_apperror t s s' : G t s s' -> APError s -> APError s'.
    Proof.
      intros Hg. induction Hg as [s s' Hb | s s' s'' H1 IH1 H2 IH2].
      - exact (Gbase_apperror t s s' Hb).
      - intros H. apply IH2. apply IH1. exact H.
    Qed.

    (* Linearized entries of other threads are preserved. *)
    Lemma poss_step_linr (ρ ρ' : State VF') π π' t f r :
      poss_step (PossOk ρ π) (PossOk ρ' π') ->
      TMap.find t π = Some (ls_linr f r) -> TMap.find t π' = Some (ls_linr f r).
    Proof.
      intros Hstep Hlin.
      inversion Hstep as [tt ff s1 s2 pp Hvf Hlin0 | tt ff rr s1 s2 pp Hvf Hlin0 |]; subst;
        (destruct (Pos.eq_dec t tt); subst; [rewrite Hlin in Hlin0; discriminate | rewrite TMap.gso; auto]).
    Qed.

    Lemma poss_steps_linr_gen : forall (p q : @Poss F VF'), poss_steps p q ->
      forall ρ π ρ' π' t f r, p = PossOk ρ π -> q = PossOk ρ' π' ->
      TMap.find t π = Some (ls_linr f r) -> TMap.find t π' = Some (ls_linr f r).
    Proof.
      intros p q H. induction H; intros ρ π ρ' π' t f r Hp Hq Hlin; subst.
      - eapply poss_step_linr; eauto.
      - inversion Hq; subst. exact Hlin.
      - destruct y as [ρm πm |].
        + eapply IHclos_refl_trans2; eauto.
        + exfalso. eapply CompLinSound.poss_steps_from_error in H0; [discriminate | reflexivity].
    Qed.

    Lemma steps_linr (Δ Δ' : AbstractConfig VF') t f r :
      (Δ' ⊆ ac_steps Δ)%AbstractConfig ->
      (forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_linr f r)) ->
      (forall ρ π, Δ' ρ π -> TMap.find t π = Some (ls_linr f r)).
    Proof.
      intros Hsub Hlin ρ' π' H. apply Hsub in H.
      inversion H as [ρ π ρ'' π'' Hposs Hsteps]; subst.
      eapply poss_steps_linr_gen; eauto.
    Qed.

    Lemma Gbase_linr t t' s s' f r :
      t' <> t -> Gbase t' s s' -> ALin t (ls_linr f r) s -> ALin t (ls_linr f r) s'.
    Proof.
      intros Hne Hg Hlin.
      assert (Hne' : t <> t') by (intros Heq'; apply Hne; symmetry; exact Heq').
      destruct Hg as [s | s s' g [Hσ [Hnone Heq]] | s s' g r' [Hσ [Hlin' Heq]]
                     | s s' Hσ Hsub Hfr | s s' ev Ht Hst Hsub Hfr].
      - exact Hlin.
      - apply AbstractConfig_ext in Heq. intros ρ π H. rewrite Heq in H.
        inversion H as [ρ' π' Hposs]; subst. rewrite TMap.gso; [exact (Hlin _ _ Hposs) | exact Hne'].
      - apply AbstractConfig_ext in Heq. intros ρ π H. rewrite Heq in H.
        inversion H as [ρ' π' Hposs]; subst. rewrite TMap.gro; [exact (Hlin _ _ Hposs) | exact Hne'].
      - intros ρ π H. eapply steps_linr; eauto.
      - intros ρ π H. eapply steps_linr; eauto.
    Qed.

    Lemma G_linr t t' s s' f r :
      t' <> t -> G t' s s' -> ALin t (ls_linr f r) s -> ALin t (ls_linr f r) s'.
    Proof.
      intros Hne Hg. induction Hg as [s s' Hb | s s' s'' H1 IH1 H2 IH2].
      - exact (Gbase_linr t t' s s' f r Hne Hb).
      - intros H. apply IH2. apply IH1. exact H.
    Qed.

    (* The domain, seen by other threads. *)
    Lemma steps_none (Δ Δ' : AbstractConfig VF') t :
      (Δ' ⊆ ac_steps Δ)%AbstractConfig ->
      ((forall ρ π, Δ ρ π -> TMap.find t π = None) <->
       (forall ρ π, Δ' ρ π -> TMap.find t π = None)).
    Proof.
      intros Hsub. split.
      - intros Hn ρ' π' H. apply Hsub in H. inversion H as [ρ π ρ'' π'' Hposs Hsteps]; subst.
        pose proof (poss_steps_domain _ _ _ _ Hsteps t) as Hd. unfold map_domain in Hd.
        specialize (Hn _ _ Hposs).
        destruct (TMap.find t π') as [x|] eqn:Hx; [ | reflexivity].
        exfalso. destruct (proj2 Hd (ex_intro _ x eq_refl)) as [y Hy]. rewrite Hn in Hy. discriminate.
      - intros Hn ρ π Hposs. destruct (ac_nonempty Δ') as [ρ' [π' Hposs']].
        pose proof (Hn _ _ Hposs') as Hn'. pose proof Hposs' as H. apply Hsub in H.
        inversion H as [ρ1 π1 ρ2 π2 Hposs1 Hsteps]; subst.
        pose proof (poss_steps_domain _ _ _ _ Hsteps t) as Hd. unfold map_domain in Hd.
        assert (Hn1 : TMap.find t π1 = None).
        { destruct (TMap.find t π1) as [x|] eqn:Hx; [ | reflexivity].
          exfalso. destruct (proj1 Hd (ex_intro _ x eq_refl)) as [y Hy]. rewrite Hn' in Hy. discriminate. }
        exact (ac_find_none_same Δ ρ1 π1 ρ π t Hposs1 Hposs Hn1).
    Qed.

    Lemma Gbase_none t t' s s' :
      t' <> t -> Gbase t' s s' ->
      ((forall ρ π, Δ s ρ π -> TMap.find t π = None) <->
       (forall ρ π, Δ s' ρ π -> TMap.find t π = None)).
    Proof.
      intros Hne Hg.
      assert (Hne' : t <> t') by (intros Heq'; apply Hne; symmetry; exact Heq').
      destruct Hg as [s | s s' g [Hσ [Hnone Heq]] | s s' g r' [Hσ [Hlin' Heq]]
                     | s s' Hσ Hsub Hfr | s s' ev Ht Hst Hsub Hfr].
      - reflexivity.
      - apply AbstractConfig_ext in Heq. rewrite Heq. split.
        + intros Hn ρ π H. inversion H as [ρ' π' Hposs]; subst.
          rewrite TMap.gso; [exact (Hn _ _ Hposs) | exact Hne'].
        + intros Hn ρ π Hposs.
          assert (H' : ac_inv (Δ s) t' g ρ (TMap.add t' (ls_inv g) π)) by (constructor; exact Hposs).
          specialize (Hn _ _ H'). rewrite TMap.gso in Hn; [exact Hn | exact Hne'].
      - apply AbstractConfig_ext in Heq. rewrite Heq. split.
        + intros Hn ρ π H. inversion H as [ρ' π' Hposs]; subst.
          rewrite TMap.gro; [exact (Hn _ _ Hposs) | exact Hne'].
        + intros Hn ρ π Hposs.
          assert (H' : ac_res (Δ s) t' ρ (TMap.remove t' π)) by (constructor; exact Hposs).
          specialize (Hn _ _ H'). rewrite TMap.gro in Hn; [exact Hn | exact Hne'].
      - apply steps_none. exact Hsub.
      - apply steps_none. exact Hsub.
    Qed.

    Lemma G_none t t' s s' :
      t' <> t -> G t' s s' ->
      ((forall ρ π, Δ s ρ π -> TMap.find t π = None) <->
       (forall ρ π, Δ s' ρ π -> TMap.find t π = None)).
    Proof.
      intros Hne Hg. induction Hg as [s s' Hb | s s' s'' H1 IH1 H2 IH2].
      - exact (Gbase_none t t' s s' Hne Hb).
      - rewrite IH1. exact IH2.
    Qed.

    Lemma Gbase_ops t t' s s' l :
      t' <> t -> Gbase t' s s' -> ops_at (Δ s) t l -> ops_at (Δ s') t l.
    Proof.
      intros Hne Hg Hl.
      assert (Hne' : t <> t') by (intros Heq'; apply Hne; symmetry; exact Heq').
      destruct Hg as [s | s s' g [Hσ [Hnone Heq]] | s s' g r' [Hσ [Hlin' Heq]]
                     | s s' Hσ Hsub Hfr | s s' ev Ht Hst Hsub Hfr].
      - exact Hl.
      - apply AbstractConfig_ext in Heq. rewrite Heq. apply ops_at_ac_inv_o; auto.
      - apply AbstractConfig_ext in Heq. rewrite Heq. apply ops_at_ac_res_o; auto.
      - eapply ops_at_steps; eauto.
      - eapply ops_at_steps; eauto.
    Qed.

    Lemma G_ops t t' s s' l :
      t' <> t -> G t' s s' -> ops_at (Δ s) t l -> ops_at (Δ s') t l.
    Proof.
      intros Hne Hg. induction Hg as [s s' Hb | s s' s'' H1 IH1 H2 IH2].
      - exact (Gbase_ops t t' s s' l Hne Hb).
      - intros H. apply IH2. apply IH1. exact H.
    Qed.

    Lemma Gbase_hist t t' s s' :
      t' <> t -> Gbase t' s s' -> hist_u (hist (σ s')) t = hist_u (hist (σ s)) t.
    Proof.
      intros Hne Hg. destruct Hg as [s | s s' g [Hσ _] | s s' g r' [Hσ _]
                                    | s s' Hσ Hsub Hfr | s s' ev Ht Hst Hsub Hfr].
      - reflexivity.
      - rewrite Hσ. reflexivity.
      - rewrite Hσ. reflexivity.
      - rewrite Hσ. reflexivity.
      - simpl in Hst. destruct Hst as [_ Hh]. unfold hist. rewrite Hh, hist_u_snoc.
        destruct (Pos.eq_dec (te_tid ev) t); [congruence | reflexivity].
    Qed.

    Lemma G_hist t t' s s' :
      t' <> t -> G t' s s' -> hist_u (hist (σ s')) t = hist_u (hist (σ s)) t.
    Proof.
      intros Hne Hg. induction Hg as [s s' Hb | s s' s'' H1 IH1 H2 IH2].
      - exact (Gbase_hist t t' s s' Hne Hb).
      - rewrite IH2. exact IH1.
    Qed.

    Lemma R_apperror t s s' : R t s s' -> APError s -> APError s'.
    Proof. intros [_ [t' [_ Hg]]]. exact (G_apperror t' s s' Hg). Qed.

    Lemma R_linr t s s' f r : R t s s' -> ALin t (ls_linr f r) s -> ALin t (ls_linr f r) s'.
    Proof. intros [_ [t' [Hne Hg]]]. exact (G_linr t t' s s' f r Hne Hg). Qed.

    Lemma R_none t s s' :
      R t s s' ->
      ((forall ρ π, Δ s ρ π -> TMap.find t π = None) <->
       (forall ρ π, Δ s' ρ π -> TMap.find t π = None)).
    Proof. intros [_ [t' [Hne Hg]]]. exact (G_none t t' s s' Hne Hg). Qed.

    Lemma R_ops t s s' l : R t s s' -> ops_at (Δ s) t l -> ops_at (Δ s') t l.
    Proof. intros [_ [t' [Hne Hg]]]. exact (G_ops t t' s s' l Hne Hg). Qed.

    Lemma R_hist t s s' : R t s s' -> hist_u (hist (σ s')) t = hist_u (hist (σ s)) t.
    Proof. intros [_ [t' [Hne Hg]]]. exact (G_hist t t' s s' Hne Hg). Qed.

    Lemma ValidRGI_RG t : ValidRGI (R t) (G t) I t.
    Proof. constructor. intros s s' HR _. apply R_none. exact HR. Qed.

    Lemma HRG_RG t1 t2 :
      t1 <> t2 -> (I ⊓ (G t1 ∪ ((GINV t1 ∪ GRET t1) ∪ GId)) ⊆ R t2)%RGRelation.
    Proof.
      intros Hne s s' [Hg HI]. split; [exact HI |]. exists t1. split; [exact Hne |].
      destruct Hg as [Hg | [ [ [f Hg] | [f [r Hg] ] ] | Hg] ].
      - exact Hg.
      - apply t_step. eapply gb_inv. exact Hg.
      - apply t_step. eapply gb_ret. exact Hg.
      - unfold GId in Hg. subst. apply t_step. apply gb_id.
    Qed.

    Lemma G_refl t s : G t s s.
    Proof. apply t_step. apply gb_id. Qed.

    Lemma G_trans t s1 s2 s3 : G t s1 s2 -> G t s2 s3 -> G t s1 s3.
    Proof. intros. eapply t_trans; eauto. Qed.

    Lemma G_err t (σ1 : State VE') (Δ1 : AbstractConfig VF') σ2 ev :
      te_tid ev = t -> Step VE' ev σ1 σ2 -> APError (σ1, Δ1) -> G t (σ1, Δ1) (σ2, Δ1).
    Proof.
      intros Ht Hst Herr. apply t_step. apply gb_step with (ev := ev); simpl; auto.
      apply ac_steps_refl.
    Qed.

    Lemma I_err : ⊨ APError ==>> I.
    Proof. intros s H. left. exact H. Qed.

    (** ** Moving the canonical witness *)

    Lemma aus_subset (Δ Δ0 : AbstractConfig VF') :
      AbstractUpdateSteps Δ Δ0 -> (Δ0 ⊆ ac_steps Δ)%AbstractConfig.
    Proof.
      intros H. induction H as [Δ | Δ Δ' Δ'' Hsub H IH].
      - apply ac_steps_refl.
      - eapply ac_steps_subset_trans; [exact Hsub | exact IH].
    Qed.

    Lemma errorcore_sub (Δ Δ0 : AbstractConfig VF') :
      (Δ0 ⊆ ac_steps Δ)%AbstractConfig -> ErrorCore Δ0 -> ErrorCore Δ.
    Proof.
      intros Hsub [ρ [π [Hposs Hst]]]. apply Hsub in Hposs.
      inversion Hposs as [ρ1 π1 ρ2 π2 Hposs1 Hsteps]; subst.
      exists ρ1, π1. split; [exact Hposs1 |]. eapply rt_trans; eauto.
    Qed.

    Lemma pt_eq_union (π π2 : tmap (@LinState F)) : pt_eq π π2 -> is_union π (fun _ => None) π2.
    Proof. intros H t. rewrite H. unfold pt_union. destruct (TMap.find t π2); reflexivity. Qed.

    Lemma union_pt_eq (π π2 : tmap (@LinState F)) : is_union π (fun _ => None) π2 -> pt_eq π π2.
    Proof. intros H t. rewrite H. unfold pt_union. destruct (TMap.find t π); reflexivity. Qed.

    Lemma poss_error_pt (ρ : State VF') π π2 :
      pt_eq π π2 -> poss_steps (PossOk ρ π) PossError -> poss_steps (PossOk ρ π2) PossError.
    Proof.
      intros Heq Hsteps.
      destruct (CompLinSound.poss_steps_error_last _ _ Hsteps) as (t0 & f0 & ρ1 & π1 & Hs & Herr & Hlin).
      destruct (poss_steps_union _ _ _ _ _ _ (pt_eq_union _ _ Heq) Hs) as [π2' [Hu2 Hs2]].
      eapply rt_trans; [exact Hs2 |]. apply rt_step.
      eapply poss_error_union; [exact Hu2 |]. eapply ps_error; eauto.
    Qed.

    Lemma pt_in_steps (Δ : AbstractConfig VF') ρ π ρ' π' :
      pt_in (ac_steps Δ) ρ π -> poss_steps (PossOk ρ π) (PossOk ρ' π') -> pt_in (ac_steps Δ) ρ' π'.
    Proof.
      intros [π2 [Heq Hst]] Hsteps.
      destruct (poss_steps_union _ _ _ _ _ _ (pt_eq_union _ _ Heq) Hsteps) as [π2' [Hu2 Hs2]].
      exists π2'. split; [apply union_pt_eq; exact Hu2 |]. eapply ac_steps_poss; eauto.
    Qed.

    Lemma ac_steps_pt_mono (Δa Δb : AbstractConfig VF') :
      (forall ρ π, Δa ρ π -> pt_in (ac_steps Δb) ρ π) ->
      forall ρ π, ac_steps Δa ρ π -> pt_in (ac_steps Δb) ρ π.
    Proof.
      intros H ρ π Hst. inversion Hst as [ρ1 π1 ρ2 π2 Hposs Hsteps]; subst.
      eapply pt_in_steps; [apply H; exact Hposs | exact Hsteps].
    Qed.

    Lemma Inv_mono_pt (σ' : State VE') c (Δa Δb : AbstractConfig VF') :
      Inv M σ0' ρ0' rd σ' c Δa ->
      (forall ρ π, Δa ρ π -> pt_in (ac_steps Δb) ρ π) ->
      Inv M σ0' ρ0' rd σ' c Δb.
    Proof.
      intros [Herr | (e & ce & Hrun & Hs & Hne & HD) ] Hab.
      - left. destruct Herr as [ρ [π [Hposs Hsteps]]].
        destruct (Hab _ _ Hposs) as [π2 [Heq Hst]].
        inversion Hst as [ρ1 π1 ρ2 π2' Hposs1 Hsteps1]; subst.
        exists ρ1, π1. split; [exact Hposs1 |].
        eapply rt_trans; [exact Hsteps1 |]. eapply poss_error_pt; eauto.
      - right. exists e, ce. split; [exact Hrun |]. split; [exact Hs |]. split; [exact Hne |].
        intros ρ π Hd. destruct (HD _ _ Hd) as [π2 [Heq Hst]].
        destruct (ac_steps_pt_mono _ _ Hab _ _ Hst) as [π3 [Heq3 Hst3]].
        exists π3. split; [ | exact Hst3]. intros u. rewrite Heq. apply Heq3.
    Qed.

    Lemma Inv_sub (σ' : State VE') c (Δa Δb : AbstractConfig VF') :
      Inv M σ0' ρ0' rd σ' c Δa -> (Δa ⊆ ac_steps Δb)%AbstractConfig ->
      Inv M σ0' ρ0' rd σ' c Δb.
    Proof.
      intros HI Hsub. eapply Inv_mono_pt; [exact HI |].
      intros ρ π H. exists π. split; [intros u; reflexivity | apply Hsub; exact H].
    Qed.

    (* Silent steps of the witness until thread [t]'s body is [q]. *)
    Lemma Inv_catchup (σ' : State VE') (Δ' : AbstractConfig VF') t f b : forall k q c,
      Inv M σ0' ρ0' rd σ' c Δ' ->
      TMap.find t c = Some (Build_ThreadState f (taus k q) b) ->
      exists c', Inv M σ0' ρ0' rd σ' c' Δ' /\
        TMap.find t c' = Some (Build_ThreadState f q b) /\
        (forall u, u <> t -> TMap.find u c' = TMap.find u c).
    Proof.
      induction k as [ | k IH]; intros q c HI Hfind.
      - exists c. auto.
      - simpl in Hfind.
        destruct HI as [Herr | (e & ce & Hrun & Hs & Hne & HD) ].
        { exists (TMap.add t (Build_ThreadState f q b) c). split; [left; exact Herr |].
          split; [apply TMap.gss | intros u Hne'; rewrite TMap.gso; auto]. }
        destruct (node_setup M σ0' ρ0' rd Hcl' e ce σ' c Δ' Hrun Hs Hne HD) as [Δ0 [Hupd [Herr0 | N]]].
        { exists (TMap.add t (Build_ThreadState f q b) c).
          split; [left; eapply errorcore_sub; [apply (aus_subset _ _ Hupd) | exact Herr0] |].
          split; [apply TMap.gss | intros u Hne'; rewrite TMap.gso; auto]. }
        assert (Htau : taustep t c (TMap.add t (Build_ThreadState f (taus k q) b) c)).
        { eapply TauStep; [exact Hfind | constructor | reflexivity]. }
        pose proof (Inv_next_tau M σ0' ρ0' rd Hrd e ce σ' c Δ0 N t _ Htau) as HI1.
        apply (Inv_sub _ _ Δ0 Δ') in HI1; [ | apply (aus_subset _ _ Hupd) ].
        destruct (IH q _ HI1 (TMap.gss _ _ _)) as [c' [HI' [Hf' Hoth]]].
        exists c'. split; [exact HI' |]. split; [exact Hf' |].
        intros u Hne'. rewrite Hoth; auto. rewrite TMap.gso; auto.
    Qed.

    (* Readiness is invariant under silent steps. *)
    Lemma taus_ready_inv {A} i (r : Prog E A) k (v : A) :
      taus i r = taus k (Ret v) -> exists k', r = taus k' (Ret v).
    Proof.
      revert k. induction i as [ | i IH]; intros k H; simpl in H.
      - exists k. exact H.
      - destruct k as [ | k]; simpl in H; [discriminate |].
        injection H. intros H'. exact (IH k H').
    Qed.

    Lemma ready_tc_tau_eq f (p p' : Prog E (Sig.ar f)) b :
      tau_eq p p' -> rd (Build_ThreadState f p b) = rd (Build_ThreadState f p' b).
    Proof.
      intros (i & j & r & Hp & Hp'). subst p p'. destruct b as [op|]; [reflexivity |].
      destruct (rd (Build_ThreadState f r None)) as [ls|] eqn:Hr.
      - destruct (ready_tc_some _ _ _ Hr) as [v [k [_ Hrv]]]. subst r.
        rewrite !taus_plus, !ready_tc_intro. reflexivity.
      - destruct (rd (Build_ThreadState f (taus i r) None)) as [ls1|] eqn:H1.
        + exfalso. destruct (ready_tc_some _ _ _ H1) as [v [k [_ Hp]]].
          destruct (taus_ready_inv _ _ _ _ Hp) as [k' Hr']. subst r.
          rewrite ready_tc_intro in Hr. discriminate.
        + destruct (rd (Build_ThreadState f (taus j r) None)) as [ls2|] eqn:H2; [ | reflexivity].
          exfalso. destruct (ready_tc_some _ _ _ H2) as [v [k [_ Hp]]].
          destruct (taus_ready_inv _ _ _ _ Hp) as [k' Hr']. subst r.
          rewrite ready_tc_intro in Hr. discriminate.
    Qed.

    (* Removing an entry that is never stepped. *)
    Lemma poss_steps_mask_gen t f r : forall (p q : @Poss F VF'), poss_steps p q ->
      forall ρ π ρ' π' (π2 : tmap (@LinState F)),
        p = PossOk ρ π -> q = PossOk ρ' π' ->
        TMap.find t π = Some (ls_linr f r) ->
        (forall u, u <> t -> TMap.find u π2 = TMap.find u π) -> TMap.find t π2 = None ->
        exists π2', poss_steps (PossOk ρ π2) (PossOk ρ' π2') /\
          (forall u, u <> t -> TMap.find u π2' = TMap.find u π') /\ TMap.find t π2' = None.
    Proof.
      intros p q H. induction H; intros ρ π ρ' π' π2 Hp Hq Hlin Hagree Hnone; subst.
      - inversion H as [t0 f0 s1 s2 π0 Hstep Hlin0 | t0 f0 ret s1 s2 π0 Hstep Hlin0 |]; subst.
        + assert (Hne : t0 <> t) by (intros ->; rewrite Hlin in Hlin0; discriminate).
          exists (TMap.add t0 (ls_lini f0) π2). split; [ | split].
          * apply rt_step. eapply ps_inv; [exact Hstep | rewrite Hagree; auto].
          * intros u Hne'. destruct (Pos.eq_dec u t0); subst; [rewrite !TMap.gss; reflexivity | rewrite !TMap.gso; auto].
          * rewrite TMap.gso; auto.
        + assert (Hne : t0 <> t) by (intros ->; rewrite Hlin in Hlin0; discriminate).
          exists (TMap.add t0 (ls_linr f0 ret) π2). split; [ | split].
          * apply rt_step. eapply ps_ret; [exact Hstep | rewrite Hagree; auto].
          * intros u Hne'. destruct (Pos.eq_dec u t0); subst; [rewrite !TMap.gss; reflexivity | rewrite !TMap.gso; auto].
          * rewrite TMap.gso; auto.
      - inversion Hq; subst. exists π2. split; [apply rt_refl | auto].
      - destruct y as [ρm πm |].
        + destruct (IHclos_refl_trans1 _ _ _ _ π2 eq_refl eq_refl Hlin Hagree Hnone) as [πm2 [Hs1 [Ha1 Hn1]]].
          assert (Hlinm : TMap.find t πm = Some (ls_linr f r))
            by (exact (poss_steps_linr_gen _ _ H _ _ _ _ t f r eq_refl eq_refl Hlin)).
          destruct (IHclos_refl_trans2 _ _ _ _ πm2 eq_refl eq_refl Hlinm Ha1 Hn1) as [π2' [Hs2 [Ha2 Hn2]]].
          exists π2'. split; [eapply rt_trans; eauto | auto].
        + exfalso. eapply CompLinSound.poss_steps_from_error in H0; [discriminate | reflexivity].
    Qed.

    Lemma ac_res_steps_pt (Δ Δ0 : AbstractConfig VF') t f r :
      (forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_linr f r)) ->
      (Δ0 ⊆ ac_steps Δ)%AbstractConfig ->
      forall ρ π, ac_res Δ0 t ρ π -> pt_in (ac_steps (ac_res Δ t)) ρ π.
    Proof.
      intros Hlin Hsub ρ π H. inversion H as [ρ' π0 Hposs]; subst.
      apply Hsub in Hposs. inversion Hposs as [ρ1 π1 ρ2 π2 Hposs1 Hsteps]; subst.
      destruct (poss_steps_mask_gen t f r _ _ Hsteps _ _ _ _ (TMap.remove t π1)
                  eq_refl eq_refl (Hlin _ _ Hposs1)) as [π2' [Hs' [Hoth Ht]]];
        [intros u Hne; apply TMap.gro; auto | apply TMap.grs |].
      exists π2'. split.
      - intros u. destruct (Pos.eq_dec u t); subst.
        + rewrite TMap.grs, Ht. reflexivity.
        + rewrite TMap.gro; auto. symmetry. apply Hoth; auto.
      - econstructor; [constructor; exact Hposs1 | exact Hs'].
    Qed.

    Lemma ac_inv_steps_pt (Δ Δ0 : AbstractConfig VF') t f :
      (forall ρ π, Δ ρ π -> TMap.find t π = None) ->
      (Δ0 ⊆ ac_steps Δ)%AbstractConfig ->
      forall ρ π, ac_inv Δ0 t f ρ π -> pt_in (ac_steps (ac_inv Δ t f)) ρ π.
    Proof.
      intros Hnone Hsub ρ π H. inversion H as [ρ' π0 Hposs]; subst.
      apply Hsub in Hposs. inversion Hposs as [ρ1 π1 ρ2 π2 Hposs1 Hsteps]; subst.
      set (Xe := fun u => if Pos.eq_dec u t then Some (ls_inv f) else None).
      assert (Hu : is_union π1 Xe (TMap.add t (ls_inv f) π1)).
      { intros u. unfold Xe. destruct (Pos.eq_dec u t); subst.
        - rewrite TMap.gss, (Hnone _ _ Hposs1). reflexivity.
        - rewrite TMap.gso; auto. unfold pt_union. destruct (TMap.find u π1); reflexivity. }
      destruct (poss_steps_union _ _ _ _ _ _ Hu Hsteps) as [π2' [Hu2 Hs2]].
      assert (Hn0 : TMap.find t π0 = None).
      { pose proof (poss_steps_domain _ _ _ _ Hsteps t) as Hd. unfold map_domain in Hd.
        destruct (TMap.find t π0) as [x|] eqn:Hx; [ | reflexivity].
        exfalso. destruct (proj2 Hd (ex_intro _ x eq_refl)) as [y Hy].
        rewrite (Hnone _ _ Hposs1) in Hy. discriminate. }
      exists π2'. split.
      - intros u. rewrite Hu2. unfold Xe. destruct (Pos.eq_dec u t); subst.
        + rewrite TMap.gss, Hn0. reflexivity.
        + rewrite TMap.gso; auto. unfold pt_union. destruct (TMap.find u π0); reflexivity.
      - econstructor; [constructor; exact Hposs1 | exact Hs2].
    Qed.

    Definition mkps (σ' : State VE') (Δ' : AbstractConfig VF') : PS := (σ', Δ').

    (** ** The thread-local relation *)

    Definition own_lin t f (p : Prog E (Sig.ar f)) b (Δ : AbstractConfig VF') : Prop :=
      forall ls, rd (Build_ThreadState f p b) = Some ls ->
      forall ρ' π, Δ ρ' π -> TMap.find t π = Some ls.

    Definition X t f (n : nat) (σ' : State VE') (p : Prog E (Sig.ar f))
        (b : option (Sig.op E)) (Δ : AbstractConfig VF') : Prop :=
      I (σ', Δ) /\
      (~ APError (σ', Δ) ->
        (forall ρ' π, Δ ρ' π -> TMap.find t π <> None) /\
        (exists l, ops_at Δ t l /\
                   thread_run M t l (hist_u (hist σ') t) (Some (Build_ThreadState f p b))) /\
        (n = O -> own_lin t f p b Δ)) /\
      (n = O \/ n = S O).

    Lemma X_rely t f n (σ' : State VE') p b (Δ : AbstractConfig VF') σ'' Δ' :
      X t f n σ' p b Δ -> R t (σ', Δ) (σ'', Δ') -> I (σ'', Δ') -> X t f n σ'' p b Δ'.
    Proof.
      intros [HI [Hfacts Hn]] HR HI'. split; [exact HI' |]. split; [ | exact Hn].
      intros Hnoerr'.
      assert (Hnoerr : ~ APError (σ', Δ)) by (intros H; apply Hnoerr'; eapply R_apperror; eauto).
      destruct (Hfacts Hnoerr) as [Hact [[l [Hl Htr]] Hown]].
      split; [ | split].
      - intros ρ' π Hposs Hnone.
        assert (Hall' : forall ρ1 π1, Δ' ρ1 π1 -> TMap.find t π1 = None)
          by (intros ρ1 π1 H1; exact (ac_find_none_same Δ' ρ' π ρ1 π1 t Hposs H1 Hnone)).
        pose proof (R_none t _ _ HR) as Hiff. simpl in Hiff.
        destruct (ac_nonempty Δ) as [ρ2 [π2 H2]]. apply (Hact _ _ H2).
        exact (proj2 Hiff Hall' _ _ H2).
      - exists l. split; [exact (R_ops t _ _ l HR Hl) |].
        change (hist σ'') with (hist (σ (σ'', Δ'))). rewrite (R_hist t _ _ HR). exact Htr.
      - intros Hn0. specialize (Hown Hn0). intros ls Hready ρ' π Hposs.
        destruct (ready_some _ Hrd _ _ Hready) as (g & r & k & Hls & _). subst ls.
        exact (R_linr t _ _ g r HR (Hown _ Hready) _ _ Hposs).
    Qed.

    (* Facts about an [IW] state restricted to a canonical set. *)
    Lemma IW_node s e c ce Δ0 :
      IW s e c ce -> Node M σ0' ρ0' rd e ce (σ s) c Δ0 -> (Δ0 ⊆ ac_steps (Δ s))%AbstractConfig ->
      IW (σ s, Δ0) e c ce.
    Proof.
      intros HW N Hsub. pose proof HW as (Hrun & Hs & Hne & HD & Hu & Hcons).
      split; [exact Hrun |]. split; [exact Hs |]. split; [exact Hne |]. split.
      - intros ρ π Hd. destruct (nd_D0 _ _ _ _ _ _ _ _ _ N _ _ Hd) as [π2 [Heq H0]].
        exists π2. split; [exact Heq | exact (ac_steps_refl Δ0 ρ π2 H0) ].
      - split; [eapply ops_uniform_steps; eauto |].
        intros u l Hl. simpl in Hl.
        pose proof (ops_at_steps _ _ u _ Hsub (IW_ops_at _ _ _ _ u HW)) as Hl'.
        rewrite (ops_at_unique _ _ _ _ Hl Hl'). apply Hcons. exact (IW_ops_at _ _ _ _ u HW).
    Qed.


    (* Consistency of a pool after one of its threads moved. *)
    Lemma consistent_update (σ' σ'' : State VE') (Δ Δ' : AbstractConfig VF') c c' t :
      consistent σ' Δ c -> ops_uniform Δ ->
      (forall u, u <> t -> TMap.find u c' = TMap.find u c) ->
      (forall u, u <> t -> hist_u (hist σ'') u = hist_u (hist σ') u) ->
      (forall u l, u <> t -> ops_at Δ' u l -> ops_at Δ u l) ->
      (forall l, ops_at Δ' t l -> thread_run M t l (hist_u (hist σ'') t) (TMap.find t c')) ->
      consistent σ'' Δ' c'.
    Proof.
      intros Hcons Hu Hc Hh Hops Ht u l Hl. destruct (Pos.eq_dec u t); subst.
      - apply Ht. exact Hl.
      - rewrite (Hc u n), (Hh u n). apply Hcons. apply Hops; auto.
    Qed.

    Lemma ops_at_back (Δ Δ' : AbstractConfig VF') u l :
      ops_uniform Δ -> (Δ' ⊆ ac_steps Δ)%AbstractConfig -> ops_at Δ' u l -> ops_at Δ u l.
    Proof.
      intros Hu Hsub Hl. destruct (Hu u) as [l' Hl'].
      rewrite (ops_at_unique _ _ _ _ Hl (ops_at_steps _ _ _ _ Hsub Hl')). exact Hl'.
    Qed.

    Lemma hist_step (σ' σ'' : State VE') ev :
      Step VE' ev σ' σ'' ->
      forall u, hist_u (hist σ'') u =
        if Pos.eq_dec (te_tid ev) u then hist_u (hist σ') u ++ te_ev ev :: nil else hist_u (hist σ') u.
    Proof.
      intros [_ Hh] u. unfold hist. rewrite Hh. apply hist_u_snoc.
    Qed.

    Lemma active_steps (Δ Δ' : AbstractConfig VF') t :
      (Δ' ⊆ ac_steps Δ)%AbstractConfig ->
      (forall ρ π, Δ ρ π -> TMap.find t π <> None) ->
      (forall ρ π, Δ' ρ π -> TMap.find t π <> None).
    Proof.
      intros Hsub Hact ρ' π' H Hn. apply Hsub in H.
      inversion H as [ρ π ρ'' π'' Hposs Hsteps]; subst.
      apply (Hact _ _ Hposs).
      pose proof (poss_steps_domain _ _ _ _ Hsteps t) as Hd. unfold map_domain in Hd.
      destruct (TMap.find t π) as [x|] eqn:Hx; [ | reflexivity].
      exfalso. destruct (proj1 Hd (ex_intro _ x eq_refl)) as [y Hy]. rewrite Hn in Hy. discriminate.
    Qed.

    (* The core of the method simulation at a rank-zero state. *)
    Lemma core_at t f (σ' : State VE') p b (Δ : AbstractConfig VF') :
      X t f O σ' p b Δ -> MethodCore (R t) (G t) I t f (X t f) σ' p b Δ.
    Proof.
      intros HX. pose proof HX as [HI [Hfacts _]].
      destruct (classic (APError (σ', Δ))) as [Herr | Hnoerr].
      { inversion Herr as [s ρ π Hposs Hsteps]; subst. simpl in *.
        eapply MCore_Error; [exact HI | exact Hposs | exact Hsteps]. }
      destruct HI as [Herr | (e & c & ce & HW) ]; [contradiction |].
      destruct (Hfacts Hnoerr) as [Hact [[l [Hl Htr]] Hown]]. specialize (Hown eq_refl).
      pose proof (IW_ops_at _ _ _ _ t HW) as Hl'. simpl in Hl'.
      rewrite (ops_at_unique _ _ _ _ Hl Hl') in Htr. clear l Hl.
      pose proof HW as (Hrun & Hs & Hne & HD & Hu & Hcons). simpl in *.
      assert (Hnoerrc : ~ ErrorCore Δ) by (intros H; apply Hnoerr; apply apperror_errorcore; exact H).
      (* the witness's entry for [t] is the thread's state up to silent steps *)
      assert (Hct : exists i j q b', TMap.find t c = Some (Build_ThreadState f (taus i q) b') /\
                                     p = taus j q /\ b' = b).
      { destruct (TMap.find t c) as [[f' p' b']|] eqn:Hc.
        - pose proof (Hcons t _ Hl') as Htr'. rewrite Hc in Htr'.
          assert (Ho1 := Htr'); apply thread_run_op in Ho1; destruct Ho1 as [o1 Ho1].
          assert (Ho2 := Htr); apply thread_run_op in Ho2; destruct Ho2 as [o2 Ho2].
          rewrite Ho1 in Ho2. apply app_inj_tail in Ho2. destruct Ho2 as [_ Hf]. subst f'.
          destruct (thread_run_det (E := E) (F := F) M _ _ _ _ _ _ _ _ Htr' Htr) as [ (i & j & q & Hp' & Hp) Hbe]. subst.
          exists i, j, q, b. auto.
        - exfalso. destruct (ac_nonempty Δ) as [ρ1 [π1 H1]]. apply (Hact _ _ H1).
          apply (IW_dom _ _ _ _ _ _ t HW H1). exact Hc. }
      destruct Hct as (i & j & q & b' & Hc & Hp & Hb'). subst p b'.
      pose proof (IW_Inv _ _ _ _ HW) as HInv. simpl in HInv.
      (* catch up: the witness with [t] at [q] *)
      destruct (Inv_catchup σ' Δ t f b i q c HInv Hc) as [c1 [HI1 [Hc1 Hoth1]]].
      destruct HI1 as [Herr1 | (e1 & ce1 & Hrun1 & Hs1 & Hne1 & HD1) ]; [contradiction |].
      destruct (node_setup M σ0' ρ0' rd Hcl' e1 ce1 σ' c1 Δ Hrun1 Hs1 Hne1 HD1) as [Δ0 [Hupd [Herr0 | N]]].
      { exfalso. apply Hnoerrc. eapply errorcore_sub; [apply (aus_subset _ _ Hupd) | exact Herr0]. }
      pose proof (aus_subset _ _ Hupd) as Hsub0.
      (* the next invariant, from the step lemmas *)
      assert (Hnext : forall σ'' c' (Δ' : AbstractConfig VF'),
                Inv M σ0' ρ0' rd σ'' c' Δ' -> ops_uniform Δ' -> consistent σ'' Δ' c' -> I (σ'', Δ')).
      { intros σ'' c' Δ' [Herr' | (e' & ce' & Hrun' & Hs' & Hne' & HD') ] Hu' Hcons'.
        - left. apply apperror_errorcore. exact Herr'.
        - right. exists e', c', ce'. simpl. split; [exact Hrun' |]. split; [exact Hs' |].
          split; [exact Hne' |]. split; [exact HD' |]. split; [exact Hu' | exact Hcons']. }
      apply MCore_Continue.
      - (* a library step of [t] *)
        intros ev σ'' p2 b2 Hstep.
        destruct j as [ | j]; simpl in Hstep; [ | inversion Hstep].
        simpl in Htr.
        assert (Hvis : exists op k, q = Vis op k /\ Step VE' (Build_ThreadEvent t ev) σ' σ'' /\
                  ((ev = InvEv op /\ b = None /\ p2 = Vis op k /\ b2 = Some op) \/
                   (exists ret, ev = ResEv op ret /\ b = Some op /\ p2 = k ret /\ b2 = None))).
        { inversion Hstep as [tt op k s1 s2 Hvf | tt op rr k s1 s2 Hvf]; subst;
            repeat match goal with
                   | H : existT _ _ _ = existT _ _ _ |- _ =>
                       apply Eqdep.EqdepTheory.inj_pair2 in H; subst
                   end.
          - exists op, k. split; [reflexivity |]. split; [exact Hvf |]. left. auto.
          - exists op, k. split; [reflexivity |]. split; [exact Hvf |]. right. exists rr. auto. }
        destruct Hvis as (op & k & Hq & Hvf & Hcase). subst q.
        assert (Hu1 : @ustep E F VE' (Build_ThreadEvent t ev) σ' c1 σ''
                        (TMap.add t (Build_ThreadState f p2 b2) c1)).
        { eapply UStep; [exact Hc1 | exact Hstep | reflexivity]. }
        pose proof (Inv_next_u M σ0' ρ0' rd Hrd e1 ce1 σ' c1 Δ0 N _ _ _ Hu1) as HInv'.
        exists Δ0. split; [exact Hsub0 |]. split.
        { apply t_step. apply gb_step with (ev := Build_ThreadEvent t ev); simpl; auto. intros H; contradiction. }
        exists (S O).
        assert (Hcons' : consistent σ'' Δ0 (TMap.add t (Build_ThreadState f p2 b2) c1)).
        { eapply consistent_update with (Δ := Δ) (c := c) (σ' := σ') (t := t); auto.
          - intros u Hne'. rewrite TMap.gso; auto.
          - intros u Hne'. rewrite (hist_step _ _ _ Hvf u). simpl.
            destruct (Pos.eq_dec t u); [congruence | reflexivity].
          - intros u l Hne' Hl. eapply ops_at_back; eauto.
          - intros l Hl. rewrite TMap.gss.
            rewrite (ops_at_unique _ _ _ _ Hl (ops_at_steps _ _ _ _ Hsub0 Hl')).
            rewrite (hist_step _ _ _ Hvf t). simpl. destruct (Pos.eq_dec t t); [ | congruence].
            destruct Hcase as [ (-> & -> & -> & ->) | (ret & -> & -> & -> & ->) ].
            + apply thread_run_uinv. exact Htr.
            + apply thread_run_ures. exact Htr. }
        split; [apply (Hnext _ _ _ HInv'); [eapply ops_uniform_steps; eauto | exact Hcons'] |].
        split; [ | right; reflexivity].
        intros _. split; [ | split].
        + eapply active_steps; eauto.
        + exists (tops e t). split; [eapply ops_at_steps; eauto |].
          pose proof (Hcons' t (tops e t) (ops_at_steps _ _ _ _ Hsub0 Hl')) as Htr2.
          rewrite TMap.gss in Htr2. exact Htr2.
        + intros H. discriminate H.
      - (* the return *)
        intros ret [Hp Hb]. subst b.
        destruct j as [ | j]; simpl in Hp; [ | discriminate]. subst q. simpl in Htr.
        split; [intros s1 s2 Hg; apply t_step; eapply gb_ret; exact Hg |].
        assert (Hlinr : forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_linr f ret)).
        { intros ρ π Hposs. exact (Hown (ls_linr f ret) (ready_ret _ Hrd f ret) ρ π Hposs). }
        split; [ | exact Hlinr].
        assert (Hret1 : retstep t f ret c1 (TMap.remove t c1)) by (eapply RetStep; [exact Hc1 | reflexivity]).
        destruct (Inv_next_ret M σ0' ρ0' rd Hrd e1 ce1 σ' c1 Δ0 N t f ret _ Hret1) as [_ HInv'].
        apply (Inv_mono_pt _ _ _ (ac_res Δ t)) in HInv'; [ | apply ac_res_steps_pt with (f := f) (r := ret); auto].
        apply (Hnext _ _ _ HInv').
        + eapply ops_uniform_ac_res; eauto.
        + eapply consistent_update with (Δ := Δ) (c := c) (σ' := σ') (t := t); auto.
          * intros u Hne'. rewrite TMap.gro; auto.
          * intros u l Hne' Hl.
            destruct (Hu u) as [l0 Hl0].
            rewrite (ops_at_unique _ _ _ _ Hl (ops_at_ac_res_o _ _ _ _ Hne' Hl0)). exact Hl0.
          * intros l Hl. rewrite TMap.grs.
            rewrite (ops_at_unique _ _ _ _ Hl (ops_at_ac_res_t _ _ _ _ _ Hl' Hlinr)).
            eapply thread_run_return. exact Htr.
      - (* a silent step *)
        intros p2 b2 Hstep.
        inversion Hstep as [f0 p0 b0]; subst;
          repeat match goal with
                 | H : existT _ _ _ = existT _ _ _ |- _ =>
                     apply Eqdep.EqdepTheory.inj_pair2 in H
                 end.
        exists (S O). split; [right; exists e, c, ce; exact HW |]. split; [ | right; reflexivity].
        intros _. split; [exact Hact |]. split; [ | intros H; discriminate H].
        exists (tops e t). split; [exact Hl' |].
        apply thread_run_tau.
        match goal with
        | H : taus _ _ = Tau _ |- _ => rewrite <- H; exact Htr
        | H : Tau _ = taus _ _ |- _ => rewrite H; exact Htr
        end.
      - (* the invariant *)
        right. exists e, c, ce. exact HW.
      - (* stability *)
        intros σ'' Δ' HR HI'. exact (X_rely t f O σ' _ b Δ σ'' Δ' HX HR HI').
      - (* no concrete error *)
        intros ev Herror.
        inversion Herror as [tt op s1 k Hvf]; subst;
          repeat match goal with
                 | H : existT _ _ _ = existT _ _ _ |- _ =>
                     apply Eqdep.EqdepTheory.inj_pair2 in H
                 end.
        match goal with
        | H : taus ?j q = Vis _ _ |- _ => destruct j; simpl in H; [subst q | discriminate]
        | H : Vis _ _ = taus ?j q |- _ => destruct j; simpl in H; [subst q | discriminate]
        end.
        apply (Inv_noerror M σ0' ρ0' rd Hrd e1 ce1 σ' c1 Δ0 Hcl' N (Build_ThreadEvent t (InvEv op))).
        eapply UError; [exact Hc1 |]. constructor. exact Hvf.
    Qed.


    (* The ranked view: rank one updates to the canonical restricted set,
       rank zero is a core. *)
    Lemma X_view t f : forall n (σ' : State VE') p b (Δ : AbstractConfig VF'),
      X t f n σ' p b Δ -> MethodViewRanked (R t) (G t) I t f (X t f) n σ' p b Δ.
    Proof.
      intros n σ' p b Δ HX. pose proof HX as [HI [Hfacts Hn]].
      destruct Hn as [Hn | Hn]; subst n.
      - exists Δ. split; [constructor |]. split; [apply core_at; exact HX |].
        intros σ'' Δ' HR HI'. exists O. split; [auto |]. eapply X_rely; eauto.
      - destruct (classic (APError (σ', Δ))) as [Herr | Hnoerr].
        + exists Δ. split.
          { eapply MethodUpdatesStep; [apply ac_steps_refl | apply G_refl | exact HI | constructor]. }
          split.
          { inversion Herr as [s ρ π Hposs Hsteps]; subst. simpl in *.
            eapply MCore_Error; [exact HI | exact Hposs | exact Hsteps]. }
          intros σ'' Δ' HR HI'. exists (S O). split; [auto |]. eapply X_rely; eauto.
        + destruct HI as [Herr | (e & c & ce & HW) ]; [contradiction |].
          pose proof HW as (Hrun & Hs & Hne & HD & Hu & Hcons). simpl in *.
          destruct (node_setup M σ0' ρ0' rd Hcl' e ce σ' c Δ Hrun Hs Hne HD) as [Δ0 [Hupd [Herr0 | N] ] ].
          { exfalso. apply Hnoerr. apply apperror_errorcore.
            eapply errorcore_sub; [apply (aus_subset _ _ Hupd) | exact Herr0]. }
          pose proof (aus_subset _ _ Hupd) as Hsub0.
          destruct (Hfacts Hnoerr) as [Hact [[l [Hl Htr] ] _] ].
          pose proof (IW_ops_at _ _ _ _ t HW) as Hl'. simpl in Hl'.
          rewrite (ops_at_unique _ _ _ _ Hl Hl') in Htr. clear l Hl.
          exists Δ0. split.
          { eapply MethodUpdatesStep; [exact Hsub0 | | right; exists e, c, ce; exact HW | constructor].
            apply t_step. apply gb_upd; simpl; auto. intros H; contradiction. }
          split.
          { apply core_at. split; [right; exists e, c, ce; exact (IW_node _ _ _ _ _ HW N Hsub0) |].
            split; [ | left; reflexivity].
            intros _. split; [eapply active_steps; eauto |]. split.
            - exists (tops e t). split; [eapply ops_at_steps; eauto | exact Htr].
            - intros _ ls Hready ρ π Hposs.
              (* the witness's entry for [t] is ready with the same value *)
              assert (Hct : exists p' b', TMap.find t c = Some (Build_ThreadState f p' b') /\ tau_eq p' p /\ b' = b).
              { destruct (TMap.find t c) as [[f' p' b']|] eqn:Hc.
                - pose proof (Hcons t _ Hl') as Htr'. rewrite Hc in Htr'.
                  assert (Ho1 := Htr'); apply thread_run_op in Ho1; destruct Ho1 as [o1 Ho1].
                  assert (Ho2 := Htr); apply thread_run_op in Ho2; destruct Ho2 as [o2 Ho2].
                  rewrite Ho1 in Ho2. apply app_inj_tail in Ho2. destruct Ho2 as [_ Hf]. subst f'.
                  destruct (thread_run_det (E := E) (F := F) M _ _ _ _ _ _ _ _ Htr' Htr) as [Hpe Hbe]. subst b'. eauto.
                - exfalso. destruct (ac_nonempty Δ) as [ρ1 [π1 H1] ]. apply (Hact _ _ H1).
                  apply (IW_dom _ _ _ _ _ _ t HW H1). exact Hc. }
              destruct Hct as (p' & b' & Hc & Hpe & Hbe). subst b'.
              assert (Hr : rfind rd c t = Some ls).
              { unfold rfind. rewrite Hc. rewrite (ready_tc_tau_eq f p' p b Hpe). exact Hready. }
              destruct (nd_sub _ _ _ _ _ _ _ _ _ N _ _ Hposs) as [πe [Hlr Hun] ].
              rewrite Hun, Hr.
              rewrite (ready_lin_none M σ0' ρ0' rd e σ' c ce ρ πe t ls Hrun Hs Hr Hlr). reflexivity. }
          intros σ'' Δ' HR HI'. exists (S O). split; [auto |]. eapply X_rely; eauto.
    Qed.

    (* Every invocation state is method-simulated. *)
    Lemma method_sim t f (s : PS) :
      (Ginv t f ⊚ I) s -> MethodSimulation (R t) (G t) I t f (σ s) (M f t) None (Δ s).
    Proof.
      intros [s' [HI' [Hσ [Hnone Heq] ] ] ]. apply AbstractConfig_ext in Heq.
      destruct s as [σ1 Δ1]. destruct s' as [σ1' Δ1']. simpl in *. subst σ1' Δ1.
      exists (S O). eapply MethodSimulation_coinduction_ranked with (X := X t f); [apply X_view |].
      assert (Hstate :
        I (mkps σ1 (ac_inv Δ1' t f)) /\
        (~ APError (mkps σ1 (ac_inv Δ1' t f)) ->
          exists l, ops_at (ac_inv Δ1' t f) t l /\
            thread_run M t l (hist_u (hist σ1) t) (Some (Build_ThreadState f (M f t) None)))).
      { destruct HI' as [Herr | (e & c & ce & HW) ].
        { split; [left; apply apperror_ac_inv; auto |]. intros Hno. exfalso. apply Hno.
          apply apperror_ac_inv; auto. }
        pose proof HW as (Hrun & Hs & Hne & HD & Hu & Hcons). simpl in *.
        assert (Hc : TMap.find t c = None).
        { destruct (ac_nonempty Δ1') as [ρ1 [π1 H1] ]. apply (IW_dom _ _ _ _ _ _ t HW H1). exact (Hnone _ _ H1). }
        pose proof (IW_ops_at _ _ _ _ t HW) as Hl'. simpl in Hl'.
        pose proof (Hcons t _ Hl') as Htr. rewrite Hc in Htr.
        assert (Hl1 : ops_at (ac_inv Δ1' t f) t (tops e t ++ f :: nil)) by (apply ops_at_ac_inv_t; auto).
        assert (Hfacts : exists l, ops_at (ac_inv Δ1' t f) t l /\
            thread_run M t l (hist_u (hist σ1) t) (Some (Build_ThreadState f (M f t) None))).
        { exists (tops e t ++ f :: nil). split; [exact Hl1 | apply thread_run_invoke; exact Htr]. }
        split; [ | intros _; exact Hfacts].
        destruct (node_setup M σ0' ρ0' rd Hcl' e ce σ1 c Δ1' Hrun Hs Hne HD) as [Δ0 [Hupd [Herr0 | N] ] ].
        { left. apply apperror_ac_inv; auto. apply apperror_errorcore.
          eapply errorcore_sub; [apply (aus_subset _ _ Hupd) | exact Herr0]. }
        assert (Hinv : invstep M t f c (TMap.add t (Build_ThreadState f (M f t) None) c))
          by (eapply InvStep; [exact Hc | reflexivity]).
        pose proof (Inv_next_inv M σ0' ρ0' rd Hrd e ce σ1 c Δ0 N t f _ Hinv) as HInv'.
        apply (Inv_mono_pt _ _ _ (ac_inv Δ1' t f)) in HInv';
          [ | apply ac_inv_steps_pt; [exact Hnone | apply (aus_subset _ _ Hupd) ] ].
        destruct HInv' as [Herr' | (e' & ce' & Hrun' & Hs' & Hne' & HD') ].
        { left. apply apperror_errorcore. exact Herr'. }
        right. exists e', (TMap.add t (Build_ThreadState f (M f t) None) c), ce'. simpl.
        split; [exact Hrun' |]. split; [exact Hs' |]. split; [exact Hne' |]. split; [exact HD' |].
        split; [apply ops_uniform_ac_inv; auto |].
        eapply consistent_update with (Δ := Δ1') (c := c) (σ' := σ1) (t := t); auto.
        - intros u Hneu. rewrite TMap.gso; auto.
        - intros u l Hneu Hl. destruct (Hu u) as [l0 Hl0].
          rewrite (ops_at_unique _ _ _ _ Hl (ops_at_ac_inv_o _ _ _ _ _ Hneu Hl0)). exact Hl0.
        - intros l Hl. rewrite TMap.gss. rewrite (ops_at_unique _ _ _ _ Hl Hl1).
          apply thread_run_invoke. exact Htr. }
      destruct Hstate as [HIs Hfs].
      split; [exact HIs |]. split; [ | right; reflexivity].
      intros Hno. split; [ | split; [exact (Hfs Hno) | intros H; discriminate H] ].
      intros ρ π Hposs. inversion Hposs as [ρ' π' Hposs']; subst. rewrite TMap.gss. discriminate.
    Qed.

    (** ** Assembly *)

    Theorem RG_complete :
      (forall t, ValidRGI (R t) (G t) I t) /\
      (forall t1 t2, t1 <> t2 -> (I ⊓ (G t1 ∪ ((GINV t1 ∪ GRET t1) ∪ GId)) ⊆ R t2)%RGRelation) /\
      (forall t f, exists P Q, MethodProvable VE' VF' M (R t) (G t) I t f P Q) /\
      I (σ0', ρ0', TMap.empty _).
    Proof.
      split; [exact ValidRGI_RG |]. split; [exact HRG_RG |]. split.
      - intros t f. do 2 eexists.
        apply (RGILogicComplete.msim_MethodProvable M (R t) (G t) I t
                 (G_refl t) (G_trans t) (G_err t) (R_apperror t) I_err (R_linr t) f).
        intros s Hs. exact (method_sim t f s Hs).
      - right. exists nil, (TMap.empty _), (TMap.empty _). simpl.
        split; [apply rt_refl |]. split.
        { intros t. unfold rfind. rewrite !TMap.gempty. reflexivity. }
        split; [apply NoErr_nil |]. split.
        { intros ρ π [πe [Hlr Hu] ]. apply lin_reach_nil in Hlr. destruct Hlr as [Hρ Hn]. subst ρ.
          exists (TMap.empty _). split.
          - intros t. rewrite Hu, Hn, TMap.gempty. unfold rfind. rewrite TMap.gempty. reflexivity.
          - exact (ac_steps_refl (ac_init ρ0') ρ0' (TMap.empty _) (ACSingle _ _)). }
        split.
        { intros u. exists nil. intros ρ π H. inversion H; subst. unfold inv_ops. simpl.
          rewrite TMap.gempty. reflexivity. }
        intros u l Hl. simpl.
        assert (Hl0 : l = nil).
        { rewrite <- (Hl ρ0' (TMap.empty _) (ACSingle _ _)). unfold inv_ops. simpl.
          rewrite TMap.gempty. reflexivity. }
        subst l. rewrite TMap.gempty. constructor.
    Qed.

    (* The round trip: the logic proves what compositional linearizability
       states, and conversely. *)
    Theorem CompLin_via_logic : cal M σ0' ρ0'.
    Proof.
      destruct RG_complete as (Hv & Hrg & Hp & Hi).
      eapply soundness; eauto.
    Qed.

    Theorem CompLin_roundtrip : CompLin M σ0 ρ0.
    Proof.
      apply (CompLin_unaux M σ0 ρ0).
      apply CompLinSound.cal_to_CompLin. exact CompLin_via_logic.
    Qed.


  End Construction.

End CompLinRGComplete.
