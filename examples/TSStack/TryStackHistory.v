Require Import FMapPositive.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Logic.Classical_Prop.
Require Import QArith Qcanon Psatz.

Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.ListPoolSpec.
Require Import examples.TSStack.TryStackAuxSpec.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.

(** Abstract histories for the TryStack layer (Appendix A.4, rewritten
    version, Fig. 31 and Lemma A.1).

    Positions are pairs [(gap, rank)] ordered lexicographically.  Ranks are
    canonical rationals, so that inserting an event between two existing
    ones never renumbers anything; see the verification plan, departure 1.

    Clock conventions: the TryStackAux specification stamps an event with
    the clock value of its pre-state, so the event stamped [u] is the
    [(u+1)]-th event.  Gap [u] is the gap after the events stamped [< u]
    and before the event stamped [u]; the current gap of [s] is
    [tsa_now s]. *)
Module TryStackHistory.
  Import LTSSpec.
  Import LinCCALBase.
  Import ListPoolSpec.
  Import TryStackAuxSpec.
  Import TPSimulationSet.TPSimulation.

  Open Scope Qc_scope.

  (** * Positions *)

  Definition Pos : Type := (nat * Qc)%type.
  Definition gap (p : Pos) : nat := fst p.
  Definition rank (p : Pos) : Qc := snd p.

  Definition plt (p q : Pos) : Prop :=
    (gap p < gap q)%nat \/ (gap p = gap q /\ rank p < rank q).
  Definition ple (p q : Pos) : Prop := plt p q \/ p = q.

  Lemma pos_eta (p : Pos) : p = (gap p, rank p).
  Proof. destruct p; reflexivity. Qed.

  Lemma pos_ext (p q : Pos) : gap p = gap q -> rank p = rank q -> p = q.
  Proof. destruct p, q. unfold gap, rank. simpl. congruence. Qed.

  Lemma plt_irrefl p : ~ plt p p.
  Proof.
    intros [H|[_ H]]; [lia|]. exact (Qclt_not_eq _ _ H eq_refl).
  Qed.

  Lemma plt_trans p q r : plt p q -> plt q r -> plt p r.
  Proof.
    unfold plt. intros [H1|[H1 H1']] [H2|[H2 H2']].
    - left; lia.
    - left; lia.
    - left; lia.
    - right. split; [congruence|]. eapply Qclt_trans; eauto.
  Qed.

  Lemma plt_asym p q : plt p q -> plt q p -> False.
  Proof. intros H1 H2. apply (plt_irrefl p). eapply plt_trans; eauto. Qed.

  Lemma plt_trichotomy p q : plt p q \/ p = q \/ plt q p.
  Proof.
    unfold plt. destruct p as [u a], q as [v b]. unfold gap, rank. simpl.
    destruct (Nat.lt_trichotomy u v) as [H|[H|H]].
    - left. left. exact H.
    - subst v. destruct (Qc_dec a b) as [[Hab|Hab]|Hab].
      + left. right. auto.
      + right. right. right. auto.
      + subst b. right. left. reflexivity.
    - right. right. left. exact H.
  Qed.

  Lemma plt_dec p q : {plt p q} + {~ plt p q}.
  Proof.
    unfold plt. destruct (lt_dec (gap p) (gap q)) as [H|H].
    - left; auto.
    - destruct (Nat.eq_dec (gap p) (gap q)) as [He|He].
      + destruct (Qclt_le_dec (rank p) (rank q)) as [Hq|Hq].
        * left; auto.
        * right. intros [Hc|[_ Hc]]; [contradiction|].
          exact (Qcle_not_lt _ _ Hq Hc).
      + right. intros [Hc|[Hc _]]; contradiction.
  Qed.

  Lemma ple_refl p : ple p p.
  Proof. right; reflexivity. Qed.

  Lemma plt_ple_trans p q r : plt p q -> ple q r -> plt p r.
  Proof. intros H1 [H2| ->]; [eapply plt_trans; eauto|exact H1]. Qed.

  Lemma ple_plt_trans p q r : ple p q -> plt q r -> plt p r.
  Proof. intros [H1| ->] H2; [eapply plt_trans; eauto|exact H2]. Qed.

  Lemma ple_trans p q r : ple p q -> ple q r -> ple p r.
  Proof.
    intros [H1| ->] H2; [|exact H2]. left. eapply plt_ple_trans; eauto.
  Qed.

  Lemma not_plt_ple p q : ~ plt p q -> ple q p.
  Proof.
    intros H. destruct (plt_trichotomy p q) as [Hc|[Hc|Hc]].
    - contradiction.
    - subst. apply ple_refl.
    - left. exact Hc.
  Qed.

  Lemma plt_gap_lt p q : (gap p < gap q)%nat -> plt p q.
  Proof. left. exact H. Qed.

  Lemma plt_gap_le p q : plt p q -> (gap p <= gap q)%nat.
  Proof. intros [H|[H _]]; lia. Qed.

  Lemma ple_gap_le p q : ple p q -> (gap p <= gap q)%nat.
  Proof. intros [H| ->]; [apply plt_gap_le; exact H|lia]. Qed.

  Lemma plt_same_gap u a b : a < b -> plt (u, a) (u, b).
  Proof. intros H. right. split; [reflexivity|exact H]. Qed.

  Lemma plt_same_gap_inv u a b : plt (u, a) (u, b) -> a < b.
  Proof. intros [H|[_ H]]; [simpl in H; lia|exact H]. Qed.

  (** * Rational helpers *)

  Ltac qc_to_q :=
    unfold Qclt, Qcle, Qcdiv, Qcmult, Qcplus, Qcminus, Qcopp, Qcinv in *;
    cbn [this Q2Qc] in *;
    repeat rewrite Qred_correct in *.

  Definition half : Qc := Q2Qc (1 # 2).

  Lemma mid_between (a b : Qc) :
    a < b -> a < (a + b) * half /\ (a + b) * half < b.
  Proof. intros H. unfold half. qc_to_q. split; lra. Qed.

  Lemma lt_plus_1 (a : Qc) : a < a + 1.
  Proof. qc_to_q. lra. Qed.

  Lemma lt_minus_1 (a : Qc) : a + (-(1)) < a.
  Proof. qc_to_q. lra. Qed.

  Lemma Qcle_lt_dec' (a b : Qc) : a <= b \/ b < a.
  Proof.
    destruct (Qclt_le_dec b a) as [H|H]; [right|left]; assumption.
  Qed.

  Definition natq (n : nat) : Qc := Q2Qc (inject_Z (Z.of_nat n)).

  (** The rank [q + d * (i+1)/(K+2)] used for the pushes postponed behind
      a new pop: strictly between [q] and [q + d], increasing in [i]. *)
  Definition frac_rank (q d : Qc) (K i : nat) : Qc :=
    q + d * (natq (i + 1) / natq (K + 2)).

  Lemma frac_rank_bounds (q d : Qc) (K i : nat) :
    0 < d -> (i <= K)%nat ->
    q < frac_rank q d K i /\ frac_rank q d K i < q + d.
  Proof.
    intros Hd HiK. unfold frac_rank, natq. qc_to_q.
    set (I := inject_Z (Z.of_nat (i + 1))).
    set (KK := inject_Z (Z.of_nat (K + 2))).
    assert (HI : (0 < I)%Q). { unfold I, Qlt, inject_Z; simpl; lia. }
    assert (HIK : (I < KK)%Q). { unfold I, KK, Qlt, inject_Z; simpl; lia. }
    assert (HK : (0 < KK)%Q) by lra.
    assert (H0 : (0 < I / KK)%Q).
    { apply Qlt_shift_div_l; [exact HK|lra]. }
    assert (H1 : (I / KK < 1)%Q).
    { apply Qlt_shift_div_r; [exact HK|lra]. }
    unfold Qdiv in *. split; nra.
  Qed.

  Lemma frac_rank_mono (q d : Qc) (K i j : nat) :
    0 < d -> (i < j)%nat ->
    frac_rank q d K i < frac_rank q d K j.
  Proof.
    intros Hd Hij. unfold frac_rank, natq. qc_to_q.
    set (I := inject_Z (Z.of_nat (i + 1))).
    set (J := inject_Z (Z.of_nat (j + 1))).
    set (KK := inject_Z (Z.of_nat (K + 2))).
    assert (HIJ : (I < J)%Q). { unfold I, J, Qlt, inject_Z; simpl; lia. }
    assert (HK : (0 < KK)%Q). { unfold KK, Qlt, inject_Z; simpl; lia. }
    assert (H1 : (I / KK < J / KK)%Q).
    { apply Qlt_shift_div_l; [exact HK|].
      rewrite Qmult_comm, Qmult_div_r; [exact HIJ|].
      intro Hc. rewrite Hc in HK. apply (Qlt_irrefl 0 HK). }
    unfold Qdiv in *. nra.
  Qed.

  Lemma frac_rank_inj (q d : Qc) (K i j : nat) :
    0 < d -> frac_rank q d K i = frac_rank q d K j -> i = j.
  Proof.
    intros Hd Heq.
    destruct (Nat.lt_trichotomy i j) as [H|[H|H]]; [|exact H|].
    - exfalso. pose proof (frac_rank_mono q d K i j Hd H) as Hlt.
      rewrite Heq in Hlt. exact (Qclt_not_eq _ _ Hlt eq_refl).
    - exfalso. pose proof (frac_rank_mono q d K j i Hd H) as Hlt.
      rewrite Heq in Hlt. exact (Qclt_not_eq _ _ Hlt eq_refl).
  Qed.

  (** A rank strictly above every member of a finite list, and a rank
      strictly between a finite list of ranks below [q0] and [q0]. *)
  Lemma rank_above (R : list Qc) : exists q, forall r, In r R -> r < q.
  Proof.
    induction R as [|r R IH].
    - exists 0. intros ? [].
    - destruct IH as [q Hq].
      destruct (Qclt_le_dec r q) as [Hrq|Hqr].
      + exists q. intros r' [->|Hin]; [exact Hrq|now apply Hq].
      + exists (r + 1). intros r' [->|Hin]; [apply lt_plus_1|].
        eapply Qclt_le_trans; [now apply Hq|].
        eapply Qcle_trans; [exact Hqr|apply Qclt_le_weak, lt_plus_1].
  Qed.

  Lemma rank_below (R : list Qc) (q0 : Qc) :
    (forall r, In r R -> r < q0) ->
    exists q, q < q0 /\ forall r, In r R -> r < q.
  Proof.
    induction R as [|r R IH]; intros Hall.
    - exists (q0 + (-(1))). split; [apply lt_minus_1|intros ? []].
    - destruct IH as [q [Hq Hall']].
      { intros r' Hin. apply Hall. now right. }
      assert (Hr : r < q0) by (apply Hall; now left).
      destruct (Qclt_le_dec r q) as [Hrq|Hqr].
      + exists q. split; [exact Hq|].
        intros r' [->|Hin]; [exact Hrq|now apply Hall'].
      + destruct (mid_between r q0 Hr) as [Hm1 Hm2].
        exists ((r + q0) * half). split; [exact Hm2|].
        intros r' [->|Hin]; [exact Hm1|].
        eapply Qclt_le_trans; [now apply Hall'|].
        eapply Qcle_trans; [exact Hqr|apply Qclt_le_weak; exact Hm1].
  Qed.

  (** * Finite selection lemmas *)

  Lemma list_min_pos (L : list LPNodeId) (f : LPNodeId -> option Pos)
      (Pr : LPNodeId -> Prop) :
    (exists x p, In x L /\ Pr x /\ f x = Some p) ->
    exists x0 p0, In x0 L /\ Pr x0 /\ f x0 = Some p0 /\
      forall x p, In x L -> Pr x -> f x = Some p -> ple p0 p.
  Proof.
    induction L as [|y L IH]; intros (x & p & Hin & Hx & Hf).
    - contradiction.
    - destruct (classic (exists x p, In x L /\ Pr x /\ f x = Some p))
        as [Hrest|Hnone].
      + destruct (IH Hrest) as (x0 & p0 & Hin0 & Hx0 & Hf0 & Hmin).
        destruct (classic (Pr y /\ exists py, f y = Some py))
          as [[Hy [py Hfy]]|Hny].
        * destruct (plt_dec py p0) as [Hlt|Hnlt].
          -- exists y, py. split; [now left|]. split; [exact Hy|].
             split; [exact Hfy|].
             intros x' p' [->|Hin'] Hx' Hf'.
             ++ rewrite Hfy in Hf'. injection Hf' as ->. apply ple_refl.
             ++ left. eapply plt_ple_trans; [exact Hlt|].
                eapply Hmin; eauto.
          -- exists x0, p0. split; [now right|]. split; [exact Hx0|].
             split; [exact Hf0|].
             intros x' p' [->|Hin'] Hx' Hf'.
             ++ rewrite Hfy in Hf'. injection Hf' as ->.
                apply not_plt_ple. exact Hnlt.
             ++ eapply Hmin; eauto.
        * exists x0, p0. split; [now right|]. split; [exact Hx0|].
          split; [exact Hf0|].
          intros x' p' [->|Hin'] Hx' Hf'.
          -- exfalso. apply Hny. split; [exact Hx'|]. eauto.
          -- eapply Hmin; eauto.
      + destruct Hin as [->|Hin].
        * exists x, p. split; [now left|]. split; [exact Hx|].
          split; [exact Hf|].
          intros x' p' [->|Hin'] Hx' Hf'.
          -- rewrite Hf in Hf'. injection Hf' as ->. apply ple_refl.
          -- exfalso. apply Hnone. eauto.
        * exfalso. apply Hnone. eauto.
  Qed.

  Section WithValues.
    Context {A : Type}.

    Implicit Types (s : @TryStackAuxState A).

    (** * Histories *)

    Record history : Type := {
      h_inv : LPNodeId -> option Pos;
      h_pop : LPNodeId -> option (Pos * tid);
    }.

    Implicit Types (h H : history).

    Definition placed h x : Prop := h_inv h x <> None.
    Definition popped h x : Prop := h_pop h x <> None.

    (** [x →_h y]: [y]'s push completed before the abstract push-inv of
        [x]. *)
    Definition above s h x y : Prop :=
      exists p ry, h_inv h x = Some p /\ tsa_node_ret s y = Some ry /\
        (ry < gap p)%nat.

    Definition above_dec s h x y : {above s h x y} + {~ above s h x y}.
    Proof.
      unfold above.
      destruct (h_inv h x) as [p|] eqn:Hp.
      - destruct (tsa_node_ret s y) as [ry|] eqn:Hr.
        + destruct (lt_dec ry (gap p)) as [Hlt|Hge].
          * left. exists p, ry. auto.
          * right. intros (p' & ry' & Hp' & Hr' & Hlt).
            injection Hp' as <-. injection Hr' as <-. contradiction.
        + right. intros (p' & ry' & _ & Hr' & _). discriminate.
      - right. intros (p' & _ & Hp' & _). discriminate.
    Defined.

    Definition completed s x : Prop := tsa_node_ret s x <> None.

    (** * Legality (Fig. 31), with the Coq clock conventions *)

    Record legal s h : Prop := {
      lg_inv : forall x p, h_inv h x = Some p ->
        (gap p <= tsa_now s)%nat /\
        (exists i, tsa_node_inv s x = Some i /\ (i < gap p)%nat) /\
        (forall ry, tsa_node_ret s x = Some ry -> (gap p <= ry)%nat);
      lg_inv_all : forall x, completed s x -> placed h x;
      lg_pop : forall n p β, h_pop h n = Some (p, β) ->
        (gap p <= tsa_now s)%nat /\
        (exists q, h_inv h n = Some q /\ plt q p) /\
        ((exists st rt, tsa_removals s n = Some (β, st, rt) /\
            (st < gap p)%nat /\ (gap p <= rt)%nat) \/
         (tsa_removals s n = None /\
          exists st N, TMap.find β (tsa_snap_time s) = Some st /\
            TMap.find β (tsa_snapshots s) = Some N /\ N n /\
            (st < gap p)%nat));
      lg_pop_all : forall n, tsa_removals s n <> None -> popped h n;
      lg_spec : forall n m p q β,
        h_pop h n = Some (p, β) -> h_pop h m = Some (q, β) ->
        tsa_removals s n = None -> tsa_removals s m = None -> n = m;
      lg_top : forall n p β x q,
        h_pop h n = Some (p, β) -> h_inv h x = Some q -> plt q p ->
        above s h x n ->
        exists p' β', h_pop h x = Some (p', β') /\ plt p' p;
      lg_dist_inv : forall x y p,
        h_inv h x = Some p -> h_inv h y = Some p -> x = y;
      lg_dist_pop : forall x y p β β',
        h_pop h x = Some (p, β) -> h_pop h y = Some (p, β') -> x = y;
      lg_dist_mix : forall x y p β,
        h_inv h x = Some p -> h_pop h y = Some (p, β) -> False;
    }.

    (** No-needless-delay. *)
    Definition NND s H : Prop :=
      forall x m, h_pop H x = None -> above s H x m -> ~ tsa_edges s x m ->
        exists p β q, h_pop H m = Some (p, β) /\ h_inv H x = Some q /\ plt p q.

    Definition places_all s H : Prop :=
      forall x, tsa_is_vertex s x -> placed H x.

    Definition no_spec s H : Prop :=
      forall n, popped H n -> tsa_removals s n <> None.

    Definition canonical s H : Prop :=
      legal s H /\ places_all s H /\ no_spec s H /\ NND s H.

    (** * Well-formedness of the ghost clock data *)

    Record ghost_wf s : Prop := {
      gw_inv_vertex : forall x u, tsa_node_inv s x = Some u ->
        tsa_is_vertex s x /\ (u < tsa_now s)%nat;
      gw_vertex_inv : forall x, tsa_is_vertex s x ->
        exists u, tsa_node_inv s x = Some u;
      gw_inv_inj : forall x y u,
        tsa_node_inv s x = Some u -> tsa_node_inv s y = Some u -> x = y;
      gw_ret : forall x u, tsa_node_ret s x = Some u ->
        exists i, tsa_node_inv s x = Some i /\ (i < u)%nat /\ (u < tsa_now s)%nat;
      gw_ret_pending : forall x, tsa_is_vertex s x ->
        (tsa_node_ret s x = None <-> tsa_is_pending s x);
      gw_snap : forall β N, TMap.find β (tsa_snapshots s) = Some N ->
        exists st, TMap.find β (tsa_snap_time s) = Some st /\
          (st < tsa_now s)%nat /\
          forall x, N x <-> exists i, tsa_node_inv s x = Some i /\ (i < st)%nat;
      gw_snap_time : forall β st, TMap.find β (tsa_snap_time s) = Some st ->
        exists N, TMap.find β (tsa_snapshots s) = Some N;
      gw_garbage : forall n, tsa_garbage s n <-> tsa_removals s n <> None;
      gw_removal : forall n β st rt, tsa_removals s n = Some (β, st, rt) ->
        (st < rt)%nat /\ (rt < tsa_now s)%nat /\
        exists i, tsa_node_inv s n = Some i /\ (i < st)%nat;
      gw_edge : forall x y, tsa_edges s x y <->
        exists i ry, tsa_node_inv s x = Some i /\ tsa_node_ret s y = Some ry /\
          (ry < i)%nat;
      gw_pending_vertex : forall β l,
        TMap.find β (tsa_pending_pushes s) = Some l -> tsa_is_vertex s (β, l);
      gw_finite : exists L : list LPNodeId,
        forall x, In x L <-> tsa_is_vertex s x;
    }.

    Lemma gw_ret_vertex s x u :
      ghost_wf s -> tsa_node_ret s x = Some u -> tsa_is_vertex s x.
    Proof.
      intros Hwf Hr. destruct (gw_ret s Hwf x u Hr) as (i & Hi & _).
      exact (proj1 (gw_inv_vertex s Hwf x i Hi)).
    Qed.

    Lemma gw_edge_vertices s x y :
      ghost_wf s -> tsa_edges s x y -> tsa_is_vertex s x /\ tsa_is_vertex s y.
    Proof.
      intros Hwf He. apply (gw_edge s Hwf) in He.
      destruct He as (i & ry & Hi & Hr & _). split.
      - exact (proj1 (gw_inv_vertex s Hwf x i Hi)).
      - eapply gw_ret_vertex; eauto.
    Qed.

    Lemma gw_snapshot_vertex s β N n :
      ghost_wf s -> TMap.find β (tsa_snapshots s) = Some N -> N n ->
      tsa_is_vertex s n.
    Proof.
      intros Hwf HN Hn. destruct (gw_snap s Hwf β N HN) as (st & _ & _ & Hmem).
      apply Hmem in Hn. destruct Hn as (i & Hi & _).
      exact (proj1 (gw_inv_vertex s Hwf n i Hi)).
    Qed.

    (** Legal histories place only vertices. *)
    Lemma legal_placed_vertex s h x :
      ghost_wf s -> legal s h -> placed h x -> tsa_is_vertex s x.
    Proof.
      intros Hwf Hl Hp. unfold placed in Hp.
      destruct (h_inv h x) as [p|] eqn:Hx; [|contradiction].
      destruct (lg_inv s h Hl x p Hx) as (_ & (i & Hi & _) & _).
      exact (proj1 (gw_inv_vertex s Hwf x i Hi)).
    Qed.

    Lemma legal_popped_placed s h n :
      legal s h -> popped h n -> placed h n.
    Proof.
      intros Hl Hp. unfold popped in Hp.
      destruct (h_pop h n) as [[p β]|] eqn:Hn; [|contradiction].
      destruct (lg_pop s h Hl n p β Hn) as (_ & (q & Hq & _) & _).
      unfold placed. rewrite Hq. discriminate.
    Qed.

    Lemma above_placed s h x y : above s h x y -> placed h x.
    Proof.
      intros (p & ry & Hp & _). unfold placed. rewrite Hp. discriminate.
    Qed.

    (** [x →_h y] implies that [y] is placed before [x] (and completed). *)
    Lemma above_before s h x y :
      legal s h -> above s h x y ->
      exists p q, h_inv h x = Some p /\ h_inv h y = Some q /\ plt q p.
    Proof.
      intros Hl (p & ry & Hp & Hr & Hlt).
      assert (Hpl : placed h y).
      { apply (lg_inv_all s h Hl). unfold completed. rewrite Hr. discriminate. }
      unfold placed in Hpl. destruct (h_inv h y) as [q|] eqn:Hq; [|contradiction].
      exists p, q. split; [exact Hp|]. split; [reflexivity|].
      destruct (lg_inv s h Hl y q Hq) as (_ & _ & Hret).
      specialize (Hret ry Hr). left. lia.
    Qed.

    Lemma above_not_self s h x : legal s h -> ~ above s h x x.
    Proof.
      intros Hl (p & rx & Hp & Hr & Hlt).
      destruct (lg_inv s h Hl x p Hp) as (_ & _ & Hret).
      specialize (Hret rx Hr). lia.
    Qed.


    (** * Facts about the concrete transformers *)

    Lemma tsa_sp_is_vertex s α l v x :
      tsa_is_vertex (tsa_start_push α l v s) x <->
      tsa_is_vertex s x \/ x = (α, l).
    Proof.
      unfold tsa_is_vertex. simpl.
      destruct (node_eq_dec x (α, l)) as [->|Hneq].
      - rewrite node_update_eq. split; [auto|discriminate].
      - rewrite node_update_neq by congruence. tauto.
    Qed.

    Lemma tsa_sp_pending s α l v x :
      TMap.find α (tsa_pending_pushes s) = None ->
      (tsa_is_pending (tsa_start_push α l v s) x <->
       tsa_is_pending s x \/ x = (α, l)).
    Proof.
      intros Hnone. unfold tsa_is_pending. simpl. destruct x as [β l']. simpl.
      destruct (Pos.eq_dec β α) as [->|Hneq].
      - rewrite TMap.gss, Hnone. split.
        + intros Heq. injection Heq as ->. now right.
        + intros [Hbad|Heq]; [discriminate|]. injection Heq as ->. reflexivity.
      - rewrite TMap.gso by congruence. split.
        + now left.
        + intros [H|H]; [exact H|]. injection H as -> _. contradiction.
    Qed.

    Lemma tsa_fp_pending s α x :
      tsa_is_pending (tsa_finish_push α s) x <->
      tsa_is_pending s x /\ fst x <> α.
    Proof.
      unfold tsa_is_pending. simpl. destruct x as [β l]. simpl.
      destruct (Pos.eq_dec β α) as [->|Hneq].
      - rewrite TMap.grs. split; [discriminate|intros [_ H]; contradiction].
      - rewrite TMap.gro by congruence. tauto.
    Qed.

    Lemma not_vertex_no_inv s x :
      ghost_wf s -> ~ tsa_is_vertex s x -> tsa_node_inv s x = None.
    Proof.
      intros Hwf Hnv. destruct (tsa_node_inv s x) as [u|] eqn:Hu; [|reflexivity].
      exfalso. apply Hnv. exact (proj1 (gw_inv_vertex s Hwf x u Hu)).
    Qed.

    Lemma not_vertex_no_ret s x :
      ghost_wf s -> ~ tsa_is_vertex s x -> tsa_node_ret s x = None.
    Proof.
      intros Hwf Hnv. destruct (tsa_node_ret s x) as [u|] eqn:Hu; [|reflexivity].
      exfalso. apply Hnv. eapply gw_ret_vertex; eauto.
    Qed.

    Lemma not_vertex_no_removal s x :
      ghost_wf s -> ~ tsa_is_vertex s x -> tsa_removals s x = None.
    Proof.
      intros Hwf Hnv. destruct (tsa_removals s x) as [[[β st] rt]|] eqn:Hu; [|reflexivity].
      exfalso. apply Hnv.
      destruct (gw_removal s Hwf x β st rt Hu) as (_ & _ & i & Hi & _).
      exact (proj1 (gw_inv_vertex s Hwf x i Hi)).
    Qed.

    Lemma completed_iff_ret_lt s x :
      ghost_wf s ->
      ((exists ry, tsa_node_ret s x = Some ry /\ (ry < tsa_now s)%nat) <->
       tsa_is_vertex s x /\ ~ tsa_is_pending s x).
    Proof.
      intros Hwf. split.
      - intros (ry & Hr & _).
        assert (Hv : tsa_is_vertex s x) by (eapply gw_ret_vertex; eauto).
        split; [exact Hv|]. intros Hp.
        apply (gw_ret_pending s Hwf x Hv) in Hp. congruence.
      - intros [Hv Hnp].
        destruct (tsa_node_ret s x) as [ry|] eqn:Hr.
        + exists ry. split; [reflexivity|].
          destruct (gw_ret s Hwf x ry Hr) as (_ & _ & _ & H). exact H.
        + exfalso. apply Hnp. apply (gw_ret_pending s Hwf x Hv). exact Hr.
    Qed.

    (** * Preservation of [ghost_wf] by every TryStackAux step *)

    Lemma ghost_wf_empty : ghost_wf (@empty_try_stack_aux_state A).
    Proof.
      constructor; simpl.
      - intros x u H. discriminate.
      - intros x H. exfalso. apply H. reflexivity.
      - intros x y u H. discriminate.
      - intros x u H. discriminate.
      - intros x H. exfalso. apply H. reflexivity.
      - intros β N H. rewrite TMap.gempty in H. discriminate.
      - intros β st H. rewrite TMap.gempty in H. discriminate.
      - intros n. unfold empty_node_set, empty_node_map. tauto.
      - intros n β st rt H. discriminate.
      - intros x y. unfold empty_edges, empty_node_map. split.
        + contradiction.
        + intros (i & ry & H & _). discriminate.
      - intros β l H. rewrite TMap.gempty in H. discriminate.
      - exists nil. intros x. simpl. unfold tsa_is_vertex, empty_node_map. simpl.
        split; [contradiction|]. intros H. apply H. reflexivity.
    Qed.

    Lemma ghost_wf_start_push s α l v :
      ghost_wf s ->
      TMap.find α (tsa_pending_pushes s) = None ->
      tsa_fresh_node s (α, l) ->
      ghost_wf (tsa_start_push α l v s).
    Proof.
      intros Hwf Hnone [Hfv Hfg].
      assert (Hnv : ~ tsa_is_vertex s (α, l)).
      { unfold tsa_is_vertex. rewrite Hfv. intro H. apply H. reflexivity. }
      pose proof (not_vertex_no_inv s (α, l) Hwf Hnv) as Hι.
      pose proof (not_vertex_no_ret s (α, l) Hwf Hnv) as Hr.
      pose proof (not_vertex_no_removal s (α, l) Hwf Hnv) as HM.
      set (s' := tsa_start_push α l v s).
      assert (Hnow : tsa_now s' = S (tsa_now s)) by reflexivity.
      assert (Hinv' : forall x, tsa_node_inv s' x =
        if node_eq_dec (α, l) x then Some (tsa_now s) else tsa_node_inv s x).
      { intros x. reflexivity. }
      constructor.
      - intros x u. rewrite Hinv'. destruct (node_eq_dec (α, l) x) as [<-|Hneq].
        + intros Heq. injection Heq as <-. split; [|unfold s'; cbn [tsa_now tsa_start_push tsa_finish_push tsa_start_snapshot tsa_clear_snapshot tsa_remove_node]; lia].
          apply tsa_sp_is_vertex. now right.
        + intros Hu. destruct (gw_inv_vertex s Hwf x u Hu) as [Hv Hlt].
          split; [apply tsa_sp_is_vertex; now left|unfold s'; cbn [tsa_now tsa_start_push tsa_finish_push tsa_start_snapshot tsa_clear_snapshot tsa_remove_node]; lia].
      - intros x Hv. apply tsa_sp_is_vertex in Hv. rewrite Hinv'.
        destruct (node_eq_dec (α, l) x) as [<-|Hneq]; [eauto|].
        destruct Hv as [Hv|Hv]; [|symmetry in Hv; contradiction].
        exact (gw_vertex_inv s Hwf x Hv).
      - intros x y u. rewrite !Hinv'.
        destruct (node_eq_dec (α, l) x) as [<-|Hx];
          destruct (node_eq_dec (α, l) y) as [<-|Hy].
        + reflexivity.
        + intros Heq Hy'. injection Heq as <-.
          destruct (gw_inv_vertex s Hwf y _ Hy') as [_ Hlt]. lia.
        + intros Hx' Heq. injection Heq as <-.
          destruct (gw_inv_vertex s Hwf x _ Hx') as [_ Hlt]. lia.
        + apply (gw_inv_inj s Hwf).
      - intros x u Hu. simpl in Hu.
        destruct (gw_ret s Hwf x u Hu) as (i & Hi & Hlt & Hlt').
        exists i. rewrite Hinv'. destruct (node_eq_dec (α, l) x) as [<-|Hneq].
        + congruence.
        + split; [exact Hi|]. unfold s'; cbn [tsa_now tsa_start_push tsa_finish_push tsa_start_snapshot tsa_clear_snapshot tsa_remove_node]; lia.
      - intros x Hv. unfold s'. rewrite tsa_sp_pending by exact Hnone.
        cbn [tsa_node_ret tsa_start_push]. apply tsa_sp_is_vertex in Hv.
        destruct (node_eq_dec x (α, l)) as [->|Hneq].
        + rewrite Hr. split; [intros _; now right|reflexivity].
        + destruct Hv as [Hv|Hv]; [|contradiction].
          rewrite (gw_ret_pending s Hwf x Hv). split.
          * intros H. now left.
          * intros [H|H]; [exact H|contradiction].
      - intros β N HN. simpl in HN.
        destruct (gw_snap s Hwf β N HN) as (st & Hst & Hlt & Hmem).
        exists st. split; [exact Hst|]. split; [unfold s'; cbn [tsa_now tsa_start_push tsa_finish_push tsa_start_snapshot tsa_clear_snapshot tsa_remove_node]; lia|].
        intros x. rewrite Hmem, Hinv'. destruct (node_eq_dec (α, l) x) as [<-|Hneq].
        + split.
          * intros (i & Hi & _). congruence.
          * intros (i & Hi & Hlt'). injection Hi as <-. lia.
        + reflexivity.
      - intros β st Hst. simpl in Hst. exact (gw_snap_time s Hwf β st Hst).
      - intros n. simpl. apply (gw_garbage s Hwf).
      - intros n β st rt HMn. simpl in HMn.
        destruct (gw_removal s Hwf n β st rt HMn) as (H1 & H2 & i & Hi & H3).
        split; [exact H1|]. split; [unfold s'; cbn [tsa_now tsa_start_push tsa_finish_push tsa_start_snapshot tsa_clear_snapshot tsa_remove_node]; lia|].
        exists i. rewrite Hinv'. destruct (node_eq_dec (α, l) n) as [<-|Hneq].
        + congruence.
        + split; assumption.
      - intros x y. rewrite Hinv'. unfold s'.
        cbn [tsa_edges tsa_node_ret tsa_start_push].
        destruct (node_eq_dec (α, l) x) as [<-|Hneq].
        + split.
          * intros [He|(_ & Hv & Hnp)].
            -- exfalso. apply (gw_edge s Hwf) in He.
               destruct He as (i & _ & Hi & _). congruence.
            -- destruct (proj2 (completed_iff_ret_lt s y Hwf) (conj Hv Hnp))
                 as (ry & Hry & Hlt).
               exists (tsa_now s), ry. auto.
          * intros (i & ry & Hi & Hry & Hlt). injection Hi as <-.
            right. split; [reflexivity|].
            apply (completed_iff_ret_lt s y Hwf). exists ry. auto.
        + rewrite (gw_edge s Hwf). split.
          * intros [He|(Heq & _)]; [exact He|symmetry in Heq; contradiction].
          * intros He. left. exact He.
      - intros β l' Hl'. simpl in Hl'. apply tsa_sp_is_vertex.
        destruct (Pos.eq_dec β α) as [->|Hneq].
        + rewrite TMap.gss in Hl'. injection Hl' as ->. now right.
        + rewrite TMap.gso in Hl' by congruence. left.
          exact (gw_pending_vertex s Hwf β l' Hl').
      - destruct (gw_finite s Hwf) as [L HL].
        exists ((α, l) :: L). intros x. cbn [In]. rewrite HL. unfold s'.
        rewrite tsa_sp_is_vertex. split; intros [H|H]; auto.
    Qed.

    Lemma ghost_wf_finish_push s α l :
      ghost_wf s ->
      TMap.find α (tsa_pending_pushes s) = Some l ->
      ghost_wf (tsa_finish_push α s).
    Proof.
      intros Hwf Hl.
      set (s' := tsa_finish_push α s).
      assert (Hnow : tsa_now s' = S (tsa_now s)) by reflexivity.
      assert (Hret' : forall x, tsa_node_ret s' x =
        if node_eq_dec (α, l) x then Some (tsa_now s) else tsa_node_ret s x).
      { intros x. unfold s', tsa_finish_push. simpl. rewrite Hl. reflexivity. }
      assert (Hvl : tsa_is_vertex s (α, l)) by (eapply gw_pending_vertex; eauto).
      assert (Hpl : tsa_is_pending s (α, l)) by exact Hl.
      assert (Hrl : tsa_node_ret s (α, l) = None).
      { apply (gw_ret_pending s Hwf _ Hvl). exact Hpl. }
      constructor.
      - intros x u Hu. simpl in Hu. destruct (gw_inv_vertex s Hwf x u Hu).
        split; [assumption|unfold s'; cbn [tsa_now tsa_start_push tsa_finish_push tsa_start_snapshot tsa_clear_snapshot tsa_remove_node]; lia].
      - intros x Hv. simpl in *. exact (gw_vertex_inv s Hwf x Hv).
      - intros x y u. simpl. apply (gw_inv_inj s Hwf).
      - intros x u. rewrite Hret'. destruct (node_eq_dec (α, l) x) as [<-|Hneq].
        + intros Heq. injection Heq as <-.
          destruct (gw_vertex_inv s Hwf _ Hvl) as [i Hi].
          destruct (gw_inv_vertex s Hwf _ i Hi) as [_ Hlt].
          exists i. simpl. split; [exact Hi|]. unfold s'; cbn [tsa_now tsa_start_push tsa_finish_push tsa_start_snapshot tsa_clear_snapshot tsa_remove_node]; lia.
        + intros Hu. destruct (gw_ret s Hwf x u Hu) as (i & Hi & H1 & H2).
          exists i. simpl. split; [exact Hi|]. unfold s'; cbn [tsa_now tsa_start_push tsa_finish_push tsa_start_snapshot tsa_clear_snapshot tsa_remove_node]; lia.
      - intros x Hv. simpl in Hv. rewrite Hret'. unfold s'. rewrite tsa_fp_pending.
        destruct (node_eq_dec (α, l) x) as [<-|Hneq].
        + split; [discriminate|]. intros [_ H]. exfalso. apply H. reflexivity.
        + rewrite (gw_ret_pending s Hwf x Hv). split.
          * intros Hp. split; [exact Hp|]. intro Heq.
            apply Hneq. destruct x as [β l']. simpl in Heq. subst β.
            unfold tsa_is_pending in Hp. simpl in Hp. rewrite Hl in Hp.
            injection Hp as ->. reflexivity.
          * intros [Hp _]. exact Hp.
      - intros β N HN. simpl in HN.
        destruct (gw_snap s Hwf β N HN) as (st & Hst & Hlt & Hmem).
        exists st. split; [exact Hst|]. split; [unfold s'; cbn [tsa_now tsa_start_push tsa_finish_push tsa_start_snapshot tsa_clear_snapshot tsa_remove_node]; lia|exact Hmem].
      - intros β st Hst. simpl in Hst. exact (gw_snap_time s Hwf β st Hst).
      - intros n. simpl. apply (gw_garbage s Hwf).
      - intros n β st rt HMn. simpl in HMn.
        destruct (gw_removal s Hwf n β st rt HMn) as (H1 & H2 & H3).
        split; [exact H1|]. split; [unfold s'; cbn [tsa_now tsa_start_push tsa_finish_push tsa_start_snapshot tsa_clear_snapshot tsa_remove_node]; lia|exact H3].
      - intros x y. simpl. rewrite (gw_edge s Hwf). rewrite Hret'.
        destruct (node_eq_dec (α, l) y) as [<-|Hneq].
        + split.
          * intros (i & ry & Hi & Hry & Hlt). congruence.
          * intros (i & ry & Hi & Hry & Hlt). injection Hry as <-.
            destruct (gw_inv_vertex s Hwf x i Hi) as [_ Hlt']. lia.
        + reflexivity.
      - intros β l' Hl'.
        assert (Hp : tsa_is_pending (tsa_finish_push α s) (β, l')) by exact Hl'.
        apply tsa_fp_pending in Hp. destruct Hp as [Hp _].
        exact (gw_pending_vertex s Hwf β l' Hp).
      - simpl. exact (gw_finite s Hwf).
    Qed.

    Lemma ghost_wf_start_snapshot s α :
      ghost_wf s ->
      TMap.find α (tsa_snapshots s) = None ->
      ghost_wf (tsa_start_snapshot α s).
    Proof.
      intros Hwf Hnone.
      set (s' := tsa_start_snapshot α s).
      assert (Hnow : tsa_now s' = S (tsa_now s)) by reflexivity.
      constructor; simpl.
      - intros x u Hu. destruct (gw_inv_vertex s Hwf x u Hu).
        split; [assumption|lia].
      - intros x Hv. exact (gw_vertex_inv s Hwf x Hv).
      - apply (gw_inv_inj s Hwf).
      - intros x u Hu. destruct (gw_ret s Hwf x u Hu) as (i & Hi & H1 & H2).
        exists i. split; [exact Hi|]. lia.
      - intros x Hv. exact (gw_ret_pending s Hwf x Hv).
      - intros β N. destruct (Pos.eq_dec β α) as [->|Hneq].
        + rewrite !TMap.gss. intros Heq. injection Heq as <-.
          exists (tsa_now s). split; [reflexivity|]. split; [lia|].
          intros x. split.
          * intros Hv. destruct (gw_vertex_inv s Hwf x Hv) as [i Hi].
            exists i. split; [exact Hi|].
            exact (proj2 (gw_inv_vertex s Hwf x i Hi)).
          * intros (i & Hi & _). exact (proj1 (gw_inv_vertex s Hwf x i Hi)).
        + rewrite !TMap.gso by congruence. intros HN.
          destruct (gw_snap s Hwf β N HN) as (st & Hst & Hlt & Hmem).
          exists st. split; [exact Hst|]. split; [lia|exact Hmem].
      - intros β st. destruct (Pos.eq_dec β α) as [->|Hneq].
        + rewrite !TMap.gss. intros _. eexists. reflexivity.
        + rewrite !TMap.gso by congruence. apply (gw_snap_time s Hwf).
      - apply (gw_garbage s Hwf).
      - intros n β st rt HMn.
        destruct (gw_removal s Hwf n β st rt HMn) as (H1 & H2 & H3).
        split; [exact H1|]. split; [lia|exact H3].
      - apply (gw_edge s Hwf).
      - apply (gw_pending_vertex s Hwf).
      - exact (gw_finite s Hwf).
    Qed.

    Lemma ghost_wf_clear_snapshot s α :
      ghost_wf s ->
      ghost_wf (tsa_clear_snapshot α s).
    Proof.
      intros Hwf.
      constructor; simpl.
      - intros x u Hu. destruct (gw_inv_vertex s Hwf x u Hu).
        split; [assumption|lia].
      - intros x Hv. exact (gw_vertex_inv s Hwf x Hv).
      - apply (gw_inv_inj s Hwf).
      - intros x u Hu. destruct (gw_ret s Hwf x u Hu) as (i & Hi & H1 & H2).
        exists i. split; [exact Hi|]. lia.
      - intros x Hv. exact (gw_ret_pending s Hwf x Hv).
      - intros β N. destruct (Pos.eq_dec β α) as [->|Hneq].
        + rewrite TMap.grs. discriminate.
        + rewrite !TMap.gro by congruence. intros HN.
          destruct (gw_snap s Hwf β N HN) as (st & Hst & Hlt & Hmem).
          exists st. split; [exact Hst|]. split; [lia|exact Hmem].
      - intros β st. destruct (Pos.eq_dec β α) as [->|Hneq].
        + rewrite TMap.grs. discriminate.
        + rewrite !TMap.gro by congruence. apply (gw_snap_time s Hwf).
      - apply (gw_garbage s Hwf).
      - intros n β st rt HMn.
        destruct (gw_removal s Hwf n β st rt HMn) as (H1 & H2 & H3).
        split; [exact H1|]. split; [lia|exact H3].
      - apply (gw_edge s Hwf).
      - apply (gw_pending_vertex s Hwf).
      - exact (gw_finite s Hwf).
    Qed.

    Lemma ghost_wf_remove_node s α N n :
      ghost_wf s ->
      TMap.find α (tsa_snapshots s) = Some N ->
      N n -> ~ tsa_garbage s n ->
      ghost_wf (tsa_remove_node α n s).
    Proof.
      intros Hwf HN Hn Hng.
      destruct (gw_snap s Hwf α N HN) as (st & Hst & Hstlt & Hmem).
      assert (HMn : tsa_removals s n = None).
      { destruct (tsa_removals s n) eqn:HM; [|reflexivity].
        exfalso. apply Hng. apply (gw_garbage s Hwf). congruence. }
      set (s' := tsa_remove_node α n s).
      assert (Hnow : tsa_now s' = S (tsa_now s)) by reflexivity.
      assert (Hrem' : forall m, tsa_removals s' m =
        if node_eq_dec n m then Some (α, st, tsa_now s) else tsa_removals s m).
      { intros m. unfold s', tsa_remove_node. simpl. rewrite Hst. reflexivity. }
      constructor.
      - intros x u Hu. simpl in Hu. destruct (gw_inv_vertex s Hwf x u Hu).
        split; [assumption|unfold s'; cbn [tsa_now tsa_start_push tsa_finish_push tsa_start_snapshot tsa_clear_snapshot tsa_remove_node]; lia].
      - intros x Hv. simpl in *. exact (gw_vertex_inv s Hwf x Hv).
      - simpl. apply (gw_inv_inj s Hwf).
      - intros x u Hu. simpl in Hu. destruct (gw_ret s Hwf x u Hu) as (i & Hi & H1 & H2).
        exists i. simpl. split; [exact Hi|]. unfold s'; cbn [tsa_now tsa_start_push tsa_finish_push tsa_start_snapshot tsa_clear_snapshot tsa_remove_node]; lia.
      - intros x Hv. simpl in *. exact (gw_ret_pending s Hwf x Hv).
      - intros β N' HN'. simpl in HN'. destruct (Pos.eq_dec β α) as [->|Hneq].
        + rewrite TMap.grs in HN'. discriminate.
        + rewrite TMap.gro in HN' by congruence.
          destruct (gw_snap s Hwf β N' HN') as (st' & Hst' & Hlt & Hmem').
          exists st'. simpl. rewrite TMap.gro by congruence.
          split; [exact Hst'|]. split; [unfold s'; cbn [tsa_now tsa_start_push tsa_finish_push tsa_start_snapshot tsa_clear_snapshot tsa_remove_node]; lia|exact Hmem'].
      - intros β st' Hst'. simpl in Hst'. destruct (Pos.eq_dec β α) as [->|Hneq].
        + rewrite TMap.grs in Hst'. discriminate.
        + rewrite TMap.gro in Hst' by congruence. simpl.
          rewrite TMap.gro by congruence. exact (gw_snap_time s Hwf β st' Hst').
      - intros m. rewrite Hrem'. simpl. unfold set_add.
        destruct (node_eq_dec n m) as [<-|Hneq].
        + split; [discriminate|]. intros _. now left.
        + rewrite (gw_garbage s Hwf). split.
          * intros [Heq|Hg]; [symmetry in Heq; contradiction|exact Hg].
          * intros Hg. now right.
      - intros m β st' rt. rewrite Hrem'. destruct (node_eq_dec n m) as [<-|Hneq].
        + intros Heq. injection Heq as <- <- <-.
          split; [exact Hstlt|]. split; [unfold s'; cbn [tsa_now tsa_start_push tsa_finish_push tsa_start_snapshot tsa_clear_snapshot tsa_remove_node]; lia|].
          apply Hmem in Hn. destruct Hn as (i & Hi & Hlt). exists i. simpl. auto.
        + intros HMm. destruct (gw_removal s Hwf m β st' rt HMm) as (H1 & H2 & H3).
          split; [exact H1|]. split; [unfold s'; cbn [tsa_now tsa_start_push tsa_finish_push tsa_start_snapshot tsa_clear_snapshot tsa_remove_node]; lia|exact H3].
      - simpl. apply (gw_edge s Hwf).
      - simpl. apply (gw_pending_vertex s Hwf).
      - simpl. exact (gw_finite s Hwf).
    Qed.


    (** * Lemma A.1: feasible and safe insertion of a committed pop *)

    Lemma Qc_sub_pos (a b : Qc) : a < b -> 0 < b - a.
    Proof. intros Hab. exact (proj1 (Qclt_minus_iff a b) Hab). Qed.

    Lemma Qc_add_sub (a b : Qc) : a + (b - a) = b.
    Proof. ring. Qed.

    (** The positions occupied by the events of a history. *)
    Definition hpos H (p : Pos) : Prop :=
      (exists x, h_inv H x = Some p) \/ (exists x β, h_pop H x = Some (p, β)).

    (** The ranks of the events of [H] placed in gap [u], over the vertex
        list [L]. *)
    Definition ranks_in_gap H (L : list LPNodeId) (u : nat) : list Qc :=
      flat_map (fun x =>
        (match h_inv H x with
         | Some p => if Nat.eq_dec (gap p) u then rank p :: nil else nil
         | None => nil
         end) ++
        (match h_pop H x with
         | Some (p, _) => if Nat.eq_dec (gap p) u then rank p :: nil else nil
         | None => nil
         end)) L.

    Lemma ranks_in_gap_complete H L u x p :
      In x L -> gap p = u ->
      (h_inv H x = Some p \/ exists β, h_pop H x = Some (p, β)) ->
      In (rank p) (ranks_in_gap H L u).
    Proof.
      intros Hin Hgap Hev. unfold ranks_in_gap. apply in_flat_map.
      exists x. split; [exact Hin|]. apply in_or_app.
      destruct Hev as [Hev|[β Hev]].
      - left. rewrite Hev. destruct (Nat.eq_dec (gap p) u); [now left|contradiction].
      - right. rewrite Hev. destruct (Nat.eq_dec (gap p) u); [now left|contradiction].
    Qed.

    Lemma ranks_in_gap_sound H L u r :
      In r (ranks_in_gap H L u) ->
      exists x p, In x L /\ gap p = u /\ rank p = r /\
        (h_inv H x = Some p \/ exists β, h_pop H x = Some (p, β)).
    Proof.
      unfold ranks_in_gap. intros Hin. apply in_flat_map in Hin.
      destruct Hin as [x [Hx Hin]]. apply in_app_or in Hin.
      destruct Hin as [Hin|Hin].
      - destruct (h_inv H x) as [p|] eqn:Hp; [|contradiction].
        destruct (Nat.eq_dec (gap p) u) as [Hgap|]; [|contradiction].
        destruct Hin as [<-|[]]. exists x, p.
        split; [exact Hx|]. split; [exact Hgap|]. split; [reflexivity|].
        left. exact Hp.
      - destruct (h_pop H x) as [[p β]|] eqn:Hp; [|contradiction].
        destruct (Nat.eq_dec (gap p) u) as [Hgap|]; [|contradiction].
        destruct Hin as [<-|[]]. exists x, p.
        split; [exact Hx|]. split; [exact Hgap|]. split; [reflexivity|].
        right. exists β. exact Hp.
    Qed.

    Section Insertion.
      Variable s : @TryStackAuxState A.
      Variable H : history.
      Variables (α : tid) (N : LPNodeSet) (st : nat) (n : LPNodeId).
      Hypothesis Hwf : ghost_wf s.
      Hypothesis Hcan : canonical s H.
      Hypothesis HN : TMap.find α (tsa_snapshots s) = Some N.
      Hypothesis Hst : TMap.find α (tsa_snap_time s) = Some st.
      Hypothesis Htop : lp_top (fun m => N m /\ ~ tsa_garbage s m) (tsa_edges s) n.

      Let Hleg : legal s H := proj1 Hcan.
      Let Hall : places_all s H := proj1 (proj2 Hcan).
      Let Hnospec : no_spec s H := proj1 (proj2 (proj2 Hcan)).
      Let Hnnd : NND s H := proj2 (proj2 (proj2 Hcan)).

      Local Notation t := (tsa_now s).

      Lemma ins_n_vertex : tsa_is_vertex s n.
      Proof. eapply gw_snapshot_vertex; eauto. exact (proj1 (proj1 Htop)). Qed.

      Lemma ins_n_not_garbage : ~ tsa_garbage s n.
      Proof. exact (proj2 (proj1 Htop)). Qed.

      Lemma ins_n_no_removal : tsa_removals s n = None.
      Proof.
        destruct (tsa_removals s n) eqn:HM; [|reflexivity].
        exfalso. apply ins_n_not_garbage. apply (gw_garbage s Hwf). congruence.
      Qed.

      Lemma ins_n_not_popped : h_pop H n = None.
      Proof.
        destruct (h_pop H n) eqn:Hp; [|reflexivity].
        exfalso. assert (Hpop : popped H n) by (unfold popped; congruence).
        apply Hnospec in Hpop. apply Hpop. exact ins_n_no_removal.
      Qed.

      Lemma ins_st_facts :
        (st < t)%nat /\
        forall x, N x <-> exists i, tsa_node_inv s x = Some i /\ (i < st)%nat.
      Proof.
        destruct (gw_snap s Hwf α N HN) as (st' & Hst' & Hlt & Hmem).
        rewrite Hst in Hst'. injection Hst' as <-. auto.
      Qed.

      Lemma ins_hpos_gap H0 p : legal s H0 -> hpos H0 p -> (gap p <= t)%nat.
      Proof.
        intros Hl [[x Hx]|[x [β Hx]]].
        - exact (proj1 (lg_inv s H0 Hl x p Hx)).
        - exact (proj1 (lg_pop s H0 Hl x p β Hx)).
      Qed.

      (** Garbage vertices are popped in [H]; unpopped vertices are live. *)
      Lemma ins_unpopped_not_garbage x : h_pop H x = None -> ~ tsa_garbage s x.
      Proof.
        intros Hp Hg. apply (gw_garbage s Hwf) in Hg.
        pose proof (lg_pop_all s H Hleg x Hg) as Hpop. unfold popped in Hpop.
        congruence.
      Qed.

      (** Newer unpopped vertices. *)
      Definition newer x : Prop := above s H x n.
      Definition U x : Prop := newer x /\ h_pop H x = None.

      Lemma U_edge x : U x -> tsa_edges s x n.
      Proof.
        intros [Hab Hp]. destruct (classic (tsa_edges s x n)) as [He|Hne]; [exact He|].
        exfalso. destruct (Hnnd x n Hp Hab Hne) as (p & β & q & Hpop & _).
        rewrite ins_n_not_popped in Hpop. discriminate.
      Qed.

      Lemma U_not_in_N x : U x -> ~ N x.
      Proof.
        intros HU HNx. pose proof (U_edge x HU) as He.
        apply (proj2 Htop x); [|exact He].
        split; [exact HNx|]. apply ins_unpopped_not_garbage. exact (proj2 HU).
      Qed.

      Lemma U_placed x : U x -> exists p i, h_inv H x = Some p /\
        tsa_node_inv s x = Some i /\ (st <= i)%nat /\ (i < gap p)%nat.
      Proof.
        intros HU. destruct HU as [Hab Hp]. pose proof Hab as (p & rn & Hx & Hr & Hlt).
        destruct (lg_inv s H Hleg x p Hx) as (_ & (i & Hi & Hig) & _).
        exists p, i. split; [exact Hx|]. split; [exact Hi|]. split; [|exact Hig].
        destruct (proj2 ins_st_facts x) as [_ Hback].
        destruct (le_lt_dec st i) as [Hle|Hlt']; [exact Hle|].
        exfalso. apply (U_not_in_N x (conj Hab Hp)). apply Hback. eauto.
      Qed.

      Lemma U_after_n x pn : U x -> h_inv H n = Some pn ->
        exists p, h_inv H x = Some p /\ plt pn p.
      Proof.
        intros [Hab _] Hn. destruct Hab as (p & rn & Hx & Hr & Hlt).
        exists p. split; [exact Hx|].
        destruct (lg_inv s H Hleg n pn Hn) as (_ & _ & Hret).
        specialize (Hret rn Hr). left. lia.
      Qed.

      (** Blockers of a position [Q]. *)
      Definition blocker (Q : Pos) x : Prop :=
        newer x /\ (exists p, h_inv H x = Some p /\ plt p Q) /\
        ~ (exists p β, h_pop H x = Some (p, β) /\ plt p Q).

      Definition blocker_dec (Q : Pos) x : {blocker Q x} + {~ blocker Q x}.
      Proof.
        unfold blocker, newer.
        destruct (above_dec s H x n) as [Hab|Hab].
        - destruct (h_inv H x) as [p|] eqn:Hp.
          + destruct (plt_dec p Q) as [HpQ|HpQ].
            * destruct (h_pop H x) as [[q β]|] eqn:Hq.
              -- destruct (plt_dec q Q) as [HqQ|HqQ].
                 ++ right. intros (_ & _ & Hc). apply Hc. exists q, β. auto.
                 ++ left. split; [exact Hab|]. split; [exists p; auto|].
                    intros (q' & β' & Hq' & Hlt). injection Hq' as <- <-. contradiction.
              -- left. split; [exact Hab|]. split; [exists p; auto|].
                 intros (q' & β' & Hq' & _). discriminate.
            * right. intros (_ & (p' & Hp' & Hlt) & _). injection Hp' as <-. contradiction.
          + right. intros (_ & (p' & Hp' & _) & _). discriminate.
        - right. intros (Hc & _). contradiction.
      Defined.

      Lemma blocker_not_n Q : ~ blocker Q n.
      Proof. intros (Hab & _). exact (above_not_self s H n Hleg Hab). Qed.

      Lemma blocker_inv Q x : blocker Q x ->
        exists p i, h_inv H x = Some p /\ plt p Q /\
          tsa_node_inv s x = Some i /\ (i < gap p)%nat /\ (i < t)%nat.
      Proof.
        intros (_ & (p & Hp & Hlt) & _).
        destruct (lg_inv s H Hleg x p Hp) as (_ & (i & Hi & Hig) & _).
        exists p, i. repeat split; try assumption.
        exact (proj2 (gw_inv_vertex s Hwf x i Hi)).
      Qed.

      Lemma hpos_vertex_in (L : list LPNodeId) p :
        (forall x, In x L <-> tsa_is_vertex s x) ->
        hpos H p ->
        exists x, In x L /\ (h_inv H x = Some p \/ exists β, h_pop H x = Some (p, β)).
      Proof.
        intros HL [[x Hx]|[x [β Hx]]]; exists x.
        - split; [|left; exact Hx]. apply HL.
          eapply legal_placed_vertex; eauto. unfold placed. congruence.
        - split; [|right; eauto]. apply HL.
          eapply legal_placed_vertex; eauto.
          eapply legal_popped_placed; eauto. unfold popped. congruence.
      Qed.

      (** The feasible and safe position: immediately before the earliest
          newer unpopped vertex, or the end of the current gap. *)
      Lemma slot_exists : exists Q Qend,
        plt Q Qend /\ gap Qend = gap Q /\
        (forall p, hpos H p -> plt p Q \/ ple Qend p) /\
        (st < gap Q)%nat /\ (gap Q <= t)%nat /\
        (forall q, h_inv H n = Some q -> plt q Q) /\
        (forall x, blocker Q x ->
          exists p β, h_pop H x = Some (p, β) /\ plt Q p) /\
        (forall x, blocker Q x ->
          tsa_node_ret s x = None \/
          exists rx, tsa_node_ret s x = Some rx /\ (gap Q <= rx)%nat) /\
        (forall x m p β, blocker Q x -> h_pop H m = Some (p, β) -> ~ plt p Q ->
          (exists q rm, h_inv H x = Some q /\ tsa_node_ret s m = Some rm /\
            (gap q <= rm)%nat /\ (rm < gap Q)%nat) ->
          exists p' β', h_pop H x = Some (p', β') /\ plt p' p).
      Proof.
        destruct (gw_finite s Hwf) as [L HL].
        destruct ins_st_facts as [Hstt _].
        destruct (classic (exists x, U x)) as [[x1 HU1]|HnoU].
        - (* some newer vertex is unpopped *)
          destruct (list_min_pos L (h_inv H) U) as (x0 & p0 & Hin0 & HU0 & Hp0 & Hmin).
          { destruct (U_placed x1 HU1) as (p1 & i1 & Hp1 & _).
            exists x1, p1. split; [|auto]. apply HL.
            eapply legal_placed_vertex; eauto. unfold placed. congruence. }
          set (u0 := gap p0). set (q0 := rank p0).
          set (R := filter (fun r => if Qclt_le_dec r q0 then true else false)
                      (ranks_in_gap H L u0)).
          assert (HR : forall r, In r R -> r < q0).
          { intros r Hr. unfold R in Hr. apply filter_In in Hr. destruct Hr as [_ Hr].
            destruct (Qclt_le_dec r q0); [assumption|discriminate]. }
          destruct (rank_below R q0 HR) as (q & Hq & Hbelow).
          set (Q := (u0, q)).
          assert (HQp0 : plt Q p0).
          { unfold Q, plt. right. unfold u0, q0 in *. simpl. auto. }
          assert (Hsplit : forall p, hpos H p -> plt p Q \/ ple p0 p).
          { intros p Hp.
            destruct (hpos_vertex_in L p HL Hp) as (x & Hx & Hev).
            destruct (Nat.lt_trichotomy (gap p) u0) as [Hlt|[Heq|Hgt]].
            - left. left. exact Hlt.
            - destruct (Qclt_le_dec (rank p) q0) as [Hr|Hr].
              + left. right. split; [exact Heq|]. apply Hbelow. unfold R.
                apply filter_In. split.
                * eapply ranks_in_gap_complete; eauto.
                * destruct (Qclt_le_dec (rank p) q0) as [|Hc]; [reflexivity|].
                  exfalso. exact (Qcle_not_lt _ _ Hc Hr).
              + right. destruct (Qcle_lt_or_eq _ _ Hr) as [Hlt|Heqr].
                * left. right. split; [symmetry; exact Heq|exact Hlt].
                * right. apply pos_ext; [symmetry; exact Heq|exact Heqr].
            - right. left. left. exact Hgt. }
          assert (Hbefore : forall p, hpos H p -> plt p p0 -> plt p Q).
          { intros p Hp Hlt. destruct (Hsplit p Hp) as [HpQ|Hge]; [exact HpQ|].
            exfalso. apply (plt_irrefl p). eapply plt_ple_trans; eauto. }
          assert (Hblocker_popped : forall x, blocker Q x ->
            exists p β, h_pop H x = Some (p, β) /\ plt Q p).
          { intros x (Hnew & (p & Hp & HpQ) & Hnotbefore).
            destruct (h_pop H x) as [[px βx]|] eqn:Hpx.
            - exists px, βx. split; [reflexivity|].
              assert (Hhp : hpos H px) by (right; eauto).
              destruct (Hsplit px Hhp) as [HpxQ|Hge].
              + exfalso. apply Hnotbefore. exists px, βx. auto.
              + eapply plt_ple_trans; eauto.
            - exfalso. assert (HU : U x) by (split; assumption).
              assert (HinL : In x L).
              { apply HL. eapply legal_placed_vertex; eauto. unfold placed. congruence. }
              specialize (Hmin x p HinL HU Hp).
              apply (plt_irrefl p). eapply plt_ple_trans; [|exact Hmin].
              eapply plt_trans; eauto. }
          (* a pop placed after Q and above which x0 sits contradicts (top) *)
          assert (Hx0_top : forall m p β, h_pop H m = Some (p, β) -> ~ plt p Q ->
            above s H x0 m -> False).
          { intros m p β Hm HnQ Hab.
            assert (Hhp : hpos H p) by (right; eauto).
            destruct (Hsplit p Hhp) as [HpQ|Hge]; [contradiction|].
            assert (Hlt : plt p0 p).
            { destruct Hge as [Hge|Heq]; [exact Hge|].
              subst p. exfalso. exact (lg_dist_mix s H Hleg x0 m p0 β Hp0 Hm). }
            destruct (lg_top s H Hleg m p β x0 p0 Hm Hp0 Hlt Hab) as (p' & β' & Hpop & _).
            destruct HU0 as [_ HU0]. congruence. }
          exists Q, p0.
          split; [exact HQp0|].
          split; [reflexivity|].
          split; [exact Hsplit|].
          split.
          { destruct (U_placed x0 HU0) as (p0' & i & Hp0' & Hi & Hle & Hlt).
            rewrite Hp0 in Hp0'. injection Hp0' as <-. unfold Q, gap. simpl. lia. }
          split.
          { destruct (lg_inv s H Hleg x0 p0 Hp0) as (Hle & _). exact Hle. }
          split.
          { intros pn Hn. apply Hbefore; [left; eauto|].
            destruct (U_after_n x0 pn HU0 Hn) as (p' & Hp' & Hlt).
            rewrite Hp0 in Hp'. injection Hp' as <-. exact Hlt. }
          split; [exact Hblocker_popped|].
          split.
          { intros x Hb. destruct (tsa_node_ret s x) as [rx|] eqn:Hrx; [|now left].
            right. exists rx. split; [reflexivity|].
            destruct (le_lt_dec (gap Q) rx) as [Hle|Hlt]; [exact Hle|].
            exfalso. destruct (Hblocker_popped x Hb) as (px & βx & Hpx & HQpx).
            apply (Hx0_top x px βx Hpx).
            - intros Hc. exact (plt_asym _ _ HQpx Hc).
            - exists p0, rx. split; [exact Hp0|]. split; [exact Hrx|exact Hlt]. }
          { intros x m p β Hb Hm HnQ (q' & rm & Hq' & Hrm & Hle & Hlt).
            exfalso. apply (Hx0_top m p β Hm HnQ).
            exists p0, rm. split; [exact Hp0|]. split; [exact Hrm|exact Hlt]. }
        - (* every newer vertex is popped: the end of the current gap *)
          destruct (rank_above (ranks_in_gap H L t)) as (qtop & Habove).
          set (Q := (t, qtop)).
          assert (Hbefore : forall p, hpos H p -> plt p Q).
          { intros p Hp. pose proof (ins_hpos_gap H p Hleg Hp) as Hgap.
            destruct (hpos_vertex_in L p HL Hp) as (x & Hx & Hev).
            destruct (Nat.eq_dec (gap p) t) as [Heq|Hneq].
            - right. split; [exact Heq|]. apply Habove.
              eapply ranks_in_gap_complete; eauto.
            - left. unfold Q, gap in *. simpl in *. lia. }
          assert (Hnoblocker : forall x, blocker Q x -> False).
          { intros x (Hnew & _ & Hnotbefore).
            destruct (h_pop H x) as [[px βx]|] eqn:Hpx.
            - apply Hnotbefore. exists px, βx. split; [reflexivity|].
              apply Hbefore. right. eauto.
            - apply HnoU. exists x. split; assumption. }
          exists Q, (t, qtop + 1).
          split; [right; split; [reflexivity|apply lt_plus_1]|].
          split; [reflexivity|].
          split; [intros p Hp; left; apply Hbefore; exact Hp|].
          split; [exact Hstt|].
          split; [apply Nat.le_refl|].
          split; [intros q Hn; apply Hbefore; left; eauto|].
          split; [intros x Hb; exfalso; exact (Hnoblocker x Hb)|].
          split; [intros x Hb; exfalso; exact (Hnoblocker x Hb)|].
          intros x m p β Hb. exfalso. exact (Hnoblocker x Hb).
      Qed.

      (** ** The insertion [ins(H, α, n, st)] at a feasible and safe slot *)

      Section Slot.
        Variables (Q Qend : Pos).
        Hypothesis HQQ : plt Q Qend.
        Hypothesis HQgap : gap Qend = gap Q.
        Hypothesis HF2 : forall p, hpos H p -> plt p Q \/ ple Qend p.
        Hypothesis HF4a : (st < gap Q)%nat.
        Hypothesis HF4b : (gap Q <= t)%nat.
        Hypothesis HF5 : forall q, h_inv H n = Some q -> plt q Q.
        Hypothesis HF6 : forall x, blocker Q x ->
          exists p β, h_pop H x = Some (p, β) /\ plt Q p.
        Hypothesis HF7 : forall x, blocker Q x ->
          tsa_node_ret s x = None \/
          exists rx, tsa_node_ret s x = Some rx /\ (gap Q <= rx)%nat.
        Hypothesis HF8 : forall x m p β, blocker Q x -> h_pop H m = Some (p, β) ->
          ~ plt p Q ->
          (exists q rm, h_inv H x = Some q /\ tsa_node_ret s m = Some rm /\
            (gap q <= rm)%nat /\ (rm < gap Q)%nat) ->
          exists p' β', h_pop H x = Some (p', β') /\ plt p' p.

        Local Notation s' := (tsa_remove_node α n s).
        Let d : Qc := rank Qend - rank Q.

        Definition moved_pos (i : nat) : Pos := (gap Q, frac_rank (rank Q) d t i).

        Definition new_inv x : option Pos :=
          match blocker_dec Q x with
          | left _ =>
              match tsa_node_inv s x with
              | Some i => Some (moved_pos i)
              | None => h_inv H x
              end
          | right _ => h_inv H x
          end.

        Definition new_pop m : option (Pos * tid) :=
          if node_eq_dec m n then Some (Q, α) else h_pop H m.

        Definition H' : history := {| h_inv := new_inv; h_pop := new_pop |}.

        Lemma Hd_pos : 0 < d.
        Proof.
          unfold d. apply Qc_sub_pos.
          destruct HQQ as [Hlt|[_ Hlt]]; [lia|exact Hlt].
        Qed.

        Lemma moved_pos_gap i : gap (moved_pos i) = gap Q.
        Proof. reflexivity. Qed.

        Lemma moved_pos_between i :
          (i <= t)%nat -> plt Q (moved_pos i) /\ plt (moved_pos i) Qend.
        Proof.
          intros Hi.
          destruct (frac_rank_bounds (rank Q) d t i Hd_pos Hi) as [H1 H2].
          unfold d in H2. rewrite Qc_add_sub in H2.
          split.
          - right. split; [reflexivity|exact H1].
          - right. split; [symmetry; exact HQgap|exact H2].
        Qed.

        Lemma moved_pos_fresh i p :
          (i <= t)%nat -> hpos H p -> p <> moved_pos i.
        Proof.
          intros Hi Hp Heq. subst p.
          destruct (moved_pos_between i Hi) as [H1 H2].
          destruct (HF2 _ Hp) as [Hc|Hc].
          - exact (plt_asym _ _ H1 Hc).
          - apply (plt_irrefl Qend). eapply ple_plt_trans; eauto.
        Qed.

        Lemma Q_fresh p : hpos H p -> p <> Q.
        Proof.
          intros Hp Heq. subst p. destruct (HF2 _ Hp) as [Hc|Hc].
          - exact (plt_irrefl _ Hc).
          - apply (plt_irrefl Qend). eapply ple_plt_trans; eauto.
        Qed.

        Lemma new_inv_blocker x :
          blocker Q x ->
          exists i, tsa_node_inv s x = Some i /\ (i <= t)%nat /\
            new_inv x = Some (moved_pos i).
        Proof.
          intros Hb. destruct (blocker_inv Q x Hb) as (p & i & Hp & HpQ & Hi & _ & Hit).
          exists i. split; [exact Hi|]. split; [lia|].
          unfold new_inv. destruct (blocker_dec Q x) as [_|Hc]; [|contradiction].
          rewrite Hi. reflexivity.
        Qed.

        Lemma new_inv_other x : ~ blocker Q x -> new_inv x = h_inv H x.
        Proof.
          intros Hnb. unfold new_inv.
          destruct (blocker_dec Q x) as [Hc|_]; [contradiction|reflexivity].
        Qed.

        Lemma new_inv_cases x p :
          new_inv x = Some p ->
          (blocker Q x /\ exists i, tsa_node_inv s x = Some i /\ (i <= t)%nat /\
             p = moved_pos i) \/
          (~ blocker Q x /\ h_inv H x = Some p).
        Proof.
          intros Hp. destruct (blocker_dec Q x) as [Hb|Hnb].
          - left. split; [exact Hb|].
            destruct (new_inv_blocker x Hb) as (i & Hi & Hit & Hni).
            rewrite Hni in Hp. injection Hp as <-. eauto.
          - right. split; [exact Hnb|]. rewrite <- (new_inv_other x Hnb). exact Hp.
        Qed.

        Lemma new_inv_placed x : placed H x -> placed H' x.
        Proof.
          intros Hp. unfold placed in *. simpl.
          destruct (blocker_dec Q x) as [Hb|Hnb].
          - destruct (new_inv_blocker x Hb) as (i & _ & _ & Hni). rewrite Hni. discriminate.
          - rewrite new_inv_other; assumption.
        Qed.

        Lemma new_pop_n : new_pop n = Some (Q, α).
        Proof. unfold new_pop. destruct (node_eq_dec n n); congruence. Qed.

        Lemma new_pop_other m : m <> n -> new_pop m = h_pop H m.
        Proof. intros Hm. unfold new_pop. destruct (node_eq_dec m n); congruence. Qed.

        Lemma blocker_pos_after x p :
          blocker Q x -> new_inv x = Some p -> plt Q p /\ plt p Qend.
        Proof.
          intros Hb Hp. destruct (new_inv_blocker x Hb) as (i & _ & Hit & Hni).
          rewrite Hni in Hp. injection Hp as <-. apply moved_pos_between. exact Hit.
        Qed.

        (** Facts about the post-state. *)
        Lemma s'_removals m :
          tsa_removals s' m = if node_eq_dec n m then Some (α, st, t) else tsa_removals s m.
        Proof. unfold tsa_remove_node. simpl. rewrite Hst. reflexivity. Qed.

        Lemma s'_now : tsa_now s' = S t.
        Proof. reflexivity. Qed.

        Lemma above_s' x m : above s' H' x m <-> above s H' x m.
        Proof. reflexivity. Qed.

        Lemma above_nonblocker x m :
          ~ blocker Q x -> (above s H' x m <-> above s H x m).
        Proof.
          intros Hnb. unfold above. simpl. rewrite new_inv_other by exact Hnb. reflexivity.
        Qed.

        Lemma above_blocker x m :
          blocker Q x ->
          (above s H' x m <-> exists rm, tsa_node_ret s m = Some rm /\ (rm < gap Q)%nat).
        Proof.
          intros Hb. destruct (new_inv_blocker x Hb) as (i & Hi & Hit & Hni).
          unfold above. simpl. rewrite Hni. split.
          - intros (p & rm & Hp & Hrm & Hlt). injection Hp as <-. eauto.
          - intros (rm & Hrm & Hlt). exists (moved_pos i), rm. auto.
        Qed.

        (** A vertex placed before [Q] in [H'] is not moved and keeps its
            position. *)
        Lemma before_Q_unmoved x q :
          new_inv x = Some q -> plt q Q -> ~ blocker Q x /\ h_inv H x = Some q.
        Proof.
          intros Hq HqQ. destruct (new_inv_cases x q Hq) as [[Hb _]|Hc]; [|exact Hc].
          exfalso. destruct (blocker_pos_after x q Hb Hq) as [HQq _].
          exact (plt_asym _ _ HQq HqQ).
        Qed.

        Lemma new_pop_committed m p β :
          new_pop m = Some (p, β) -> tsa_removals s' m <> None.
        Proof.
          intros Hm. rewrite s'_removals. destruct (node_eq_dec n m) as [<-|Hneq].
          - discriminate.
          - rewrite new_pop_other in Hm by congruence.
            apply Hnospec. unfold popped. congruence.
        Qed.

        Lemma ins_legal : legal s' H'.
        Proof.
          pose proof ins_n_not_popped as Hnpop.
          pose proof (blocker_not_n Q) as Hnb_n.
          constructor.
          - (* (inv) *)
            intros x p Hp. simpl in Hp.
            destruct (new_inv_cases x p Hp) as [(Hb & i & Hi & Hit & ->)|(Hnb & Hold)].
            + destruct (blocker_inv Q x Hb) as (q & i' & Hq & HqQ & Hi' & Hig & _).
              rewrite Hi in Hi'. injection Hi' as <-.
              split; [rewrite s'_now, moved_pos_gap; lia|].
              split.
              * exists i. split; [exact Hi|]. rewrite moved_pos_gap.
                pose proof (plt_gap_le _ _ HqQ). lia.
              * intros ry Hry. simpl in Hry. rewrite moved_pos_gap.
                destruct (HF7 x Hb) as [Hc|(rx & Hrx & Hle)]; [congruence|].
                rewrite Hrx in Hry. injection Hry as <-. exact Hle.
            + destruct (lg_inv s H Hleg x p Hold) as (Hgap & Hi & Hret).
              split; [rewrite s'_now; lia|]. split; [exact Hi|exact Hret].
          - (* every completed vertex is placed *)
            intros x Hc. apply new_inv_placed. apply (lg_inv_all s H Hleg). exact Hc.
          - (* (pop) *)
            intros m p β Hm. simpl in Hm. unfold new_pop in Hm.
            destruct (node_eq_dec m n) as [->|Hneq].
            + injection Hm as <- <-.
              split; [rewrite s'_now; lia|].
              split.
              * pose proof (Hall n ins_n_vertex) as Hpl. unfold placed in Hpl.
                destruct (h_inv H n) as [q|] eqn:Hq; [|contradiction].
                exists q. split; [|apply HF5; reflexivity].
                simpl. rewrite new_inv_other by exact Hnb_n. exact Hq.
              * left. exists st, t. rewrite s'_removals.
                destruct (node_eq_dec n n); [|contradiction]. auto.
            + destruct (lg_pop s H Hleg m p β Hm) as (Hgap & (q & Hq & Hqp) & Hcase).
              split; [rewrite s'_now; lia|].
              split.
              * destruct (blocker_dec Q m) as [Hb|Hnb].
                -- destruct (new_inv_blocker m Hb) as (i & Hi & Hit & Hni).
                   exists (moved_pos i). split; [exact Hni|].
                   destruct (HF6 m Hb) as (pm & βm & Hpm & HQpm).
                   rewrite Hm in Hpm. injection Hpm as <- <-.
                   assert (Hhp : hpos H p) by (right; eauto).
                   destruct (HF2 p Hhp) as [Hc|Hge]; [exfalso; exact (plt_asym _ _ HQpm Hc)|].
                   destruct (moved_pos_between i Hit) as [_ Hend].
                   eapply plt_ple_trans; eauto.
                -- exists q. split; [simpl; rewrite new_inv_other; assumption|exact Hqp].
              * destruct Hcase as [(st' & rt' & HM & Hlt & Hle)|(HM & _)].
                -- left. exists st', rt'. rewrite s'_removals.
                   destruct (node_eq_dec n m) as [<-|_]; [congruence|auto].
                -- exfalso. apply (Hnospec m); [unfold popped; congruence|exact HM].
          - (* every removed vertex is popped *)
            intros m HM. rewrite s'_removals in HM. unfold popped. simpl. unfold new_pop.
            destruct (node_eq_dec n m) as [<-|Hneq].
            + destruct (node_eq_dec n n); [discriminate|contradiction].
            + destruct (node_eq_dec m n) as [->|_]; [contradiction|].
              apply (lg_pop_all s H Hleg). exact HM.
          - (* (spec): no speculative pops *)
            intros m m' p q β Hm Hm' HM _. exfalso.
            apply (new_pop_committed m p β Hm). exact HM.
          - (* (top) *)
            intros m p β x q Hm Hq Hqp Hab. simpl in Hm, Hq.
            unfold new_pop in Hm. destruct (node_eq_dec m n) as [->|Hneq].
            + injection Hm as <- <-.
              destruct (before_Q_unmoved x q Hq Hqp) as [Hnb Hold].
              rewrite above_s', above_nonblocker in Hab by exact Hnb.
              assert (Hxn : x <> n).
              { intro Heq. subst x. exact (above_not_self s H n Hleg Hab). }
              destruct (classic (exists p' β', h_pop H x = Some (p', β') /\ plt p' Q))
                as [(p' & β' & Hp' & Hlt)|Hnone].
              * exists p', β'. split; [|exact Hlt].
                simpl. rewrite new_pop_other by exact Hxn. exact Hp'.
              * exfalso. apply Hnb. split; [exact Hab|]. split; [exists q; auto|exact Hnone].
            + destruct (blocker_dec Q x) as [Hb|Hnb].
              * (* a moved blocker above an old pop *)
                destruct (HF6 x Hb) as (px & βx & Hpx & HQpx).
                assert (Hxn : x <> n) by (intro; subst x; congruence).
                exists px, βx. split; [simpl; rewrite new_pop_other by exact Hxn; exact Hpx|].
                rewrite above_s', above_blocker in Hab by exact Hb.
                destruct Hab as (rm & Hrm & Hrm_lt).
                destruct (blocker_pos_after x q Hb Hq) as [HQq _].
                assert (HnpQ : ~ plt p Q).
                { intros Hc. apply (plt_irrefl Q). eapply plt_trans; [exact HQq|].
                  eapply plt_trans; eauto. }
                destruct (blocker_inv Q x Hb) as (qx & i & Hqx & HqxQ & _).
                destruct (lt_dec rm (gap qx)) as [Hlt|Hge].
                -- (* already above in H *)
                   assert (Hab0 : above s H x m) by (exists qx, rm; auto).
                   assert (Hqxp : plt qx p) by (eapply plt_trans; [exact HqxQ|eapply plt_trans; eauto]).
                   destruct (lg_top s H Hleg m p β x qx Hm Hqx Hqxp Hab0) as (p' & β' & Hp' & Hlt').
                   rewrite Hpx in Hp'. injection Hp' as <- <-. exact Hlt'.
                -- (* safety (iii) *)
                   destruct (HF8 x m p β Hb Hm HnpQ) as (p' & β' & Hp' & Hlt').
                   { exists qx, rm. split; [exact Hqx|]. split; [exact Hrm|]. split; lia. }
                   rewrite Hpx in Hp'. injection Hp' as <- <-. exact Hlt'.
              * rewrite new_inv_other in Hq by exact Hnb.
                rewrite above_s', above_nonblocker in Hab by exact Hnb.
                destruct (lg_top s H Hleg m p β x q Hm Hq Hqp Hab) as (p' & β' & Hp' & Hlt').
                assert (Hxn : x <> n) by (intro; subst x; congruence).
                exists p', β'. split; [|exact Hlt'].
                simpl. rewrite new_pop_other by exact Hxn. exact Hp'.
          - (* (dist) for push-invs *)
            intros x y p Hx Hy. simpl in Hx, Hy.
            destruct (new_inv_cases x p Hx) as [(Hbx & i & Hi & Hit & Hpi)|(Hnbx & Hox)];
              destruct (new_inv_cases y p Hy) as [(Hby & j & Hj & Hjt & Hpj)|(Hnby & Hoy)].
            + subst p. pose proof (f_equal rank Hpj) as Hfrac.
              unfold moved_pos, rank in Hfrac. cbn [snd] in Hfrac.
              pose proof (frac_rank_inj _ _ _ _ _ Hd_pos Hfrac) as <-.
              eapply (gw_inv_inj s Hwf); eauto.
            + exfalso. apply (moved_pos_fresh i p Hit); [left; eauto|exact Hpi].
            + exfalso. apply (moved_pos_fresh j p Hjt); [left; eauto|exact Hpj].
            + eapply (lg_dist_inv s H Hleg); eauto.
          - (* (dist) for pops *)
            intros x y p β β' Hx Hy. simpl in Hx, Hy. unfold new_pop in Hx, Hy.
            destruct (node_eq_dec x n) as [->|Hxn]; destruct (node_eq_dec y n) as [->|Hyn].
            + reflexivity.
            + injection Hx as <- _. exfalso. apply (Q_fresh Q); [right; eauto|reflexivity].
            + injection Hy as <- _. exfalso. apply (Q_fresh Q); [right; eauto|reflexivity].
            + eapply (lg_dist_pop s H Hleg); eauto.
          - (* (dist) mixed *)
            intros x y p β Hx Hy. simpl in Hx, Hy. unfold new_pop in Hy.
            destruct (node_eq_dec y n) as [->|Hyn].
            + injection Hy as <- _.
              destruct (new_inv_cases x Q Hx) as [(Hb & i & Hi & Hit & HQi)|(Hnb & Hold)].
              * destruct (moved_pos_between i Hit) as [HQm _]. rewrite <- HQi in HQm.
                exact (plt_irrefl _ HQm).
              * apply (Q_fresh Q); [left; eauto|reflexivity].
            + destruct (new_inv_cases x p Hx) as [(Hb & i & Hi & Hit & Hpi)|(Hnb & Hold)].
              * apply (moved_pos_fresh i p Hit); [right; eauto|exact Hpi].
              * eapply (lg_dist_mix s H Hleg); eauto.
        Qed.

        Lemma ins_places_all : places_all s' H'.
        Proof.
          intros x Hv. apply new_inv_placed. apply Hall. exact Hv.
        Qed.

        Lemma ins_no_spec : no_spec s' H'.
        Proof.
          intros m Hp. unfold popped in Hp. simpl in Hp.
          destruct (new_pop m) as [[p β]|] eqn:Hm; [|contradiction].
          eapply new_pop_committed; eauto.
        Qed.

        Lemma ins_NND : NND s' H'.
        Proof.
          intros x m Hx Hab Hne. simpl in Hx. unfold new_pop in Hx.
          destruct (node_eq_dec x n) as [->|Hxn]; [discriminate|].
          assert (Hnb : ~ blocker Q x).
          { intros Hb. destruct (HF6 x Hb) as (p & β & Hp & _). congruence. }
          rewrite above_s', above_nonblocker in Hab by exact Hnb.
          simpl in Hne.
          destruct (node_eq_dec m n) as [->|Hmn].
          - exfalso. apply Hne. apply U_edge. split; [exact Hab|exact Hx].
          - destruct (Hnnd x m Hx Hab Hne) as (p & β & q & Hm & Hq & Hlt).
            exists p, β, q. split; [simpl; rewrite new_pop_other by exact Hmn; exact Hm|].
            split; [simpl; rewrite new_inv_other by exact Hnb; exact Hq|exact Hlt].
        Qed.

        Lemma ins_canonical : canonical s' H'.
        Proof.
          split; [exact ins_legal|]. split; [exact ins_places_all|].
          split; [exact ins_no_spec|exact ins_NND].
        Qed.

        Lemma ins_pop_old m : tsa_removals s m <> None -> h_pop H' m = h_pop H m.
        Proof.
          intros HM. simpl. apply new_pop_other. intro Heq. subst m.
          apply HM. exact ins_n_no_removal.
        Qed.

        Lemma ins_inv_later x p :
          h_inv H x = Some p -> exists p', h_inv H' x = Some p' /\ ple p p'.
        Proof.
          intros Hp. simpl. destruct (blocker_dec Q x) as [Hb|Hnb].
          - destruct (new_inv_blocker x Hb) as (i & Hi & Hit & Hni).
            exists (moved_pos i). split; [exact Hni|].
            destruct (blocker_inv Q x Hb) as (q & i' & Hq & HqQ & _).
            rewrite Hp in Hq. injection Hq as <-.
            left. eapply plt_trans; [exact HqQ|]. apply moved_pos_between. exact Hit.
          - exists p. split; [rewrite new_inv_other; assumption|apply ple_refl].
        Qed.

        Lemma ins_pop_n : h_pop H' n = Some (Q, α).
        Proof. simpl. apply new_pop_n. Qed.

      End Slot.

      (** Lemma A.1. *)
      Theorem fs_insertion :
        exists H' P,
          canonical (tsa_remove_node α n s) H' /\
          (forall m, tsa_removals s m <> None -> h_pop H' m = h_pop H m) /\
          (forall x p, h_inv H x = Some p ->
            exists p', h_inv H' x = Some p' /\ ple p p') /\
          h_pop H' n = Some (P, α) /\
          (st < gap P)%nat /\ (gap P <= t)%nat.
      Proof.
        destruct slot_exists as (Q & Qend & HQQ & HQgap & HF2 & HF4a & HF4b & HF5 & HF6 & HF7 & HF8).
        exists (H' Q Qend), Q.
        split; [apply ins_canonical; assumption|].
        split; [apply ins_pop_old|].
        split; [apply ins_inv_later; assumption|].
        split; [apply ins_pop_n|].
        split; assumption.
      Qed.

    End Insertion.
  End WithValues.
End TryStackHistory.
