Require Import FMapPositive.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Lia.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.


(** The partial-order queue [POQueue] of the Herlihy--Wing queue
    development (docs/proof-details/HWQueueProofDetails.tex, Section 4).

    It is the queue analogue of [TryStackSpec]: the enqueued elements are
    the vertices of a DAG.  An enqueue is interval sequential; its
    invocation creates a vertex ordered after every vertex whose enqueue had
    already responded, and its response merely marks the vertex complete.
    Overlapping enqueues stay unordered.  A dequeue is atomic and removes
    any minimal complete live vertex.

    Vertices are natural numbers handed out in order; in the implementation
    the identifier of a vertex is its slot index. *)
Module POQueueSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import TPSimulationSet.TPSimulation.

  Definition VertexId : Type := nat.
  Definition VertexSet : Type := VertexId -> Prop.
  Definition Edges : Type := VertexId -> VertexId -> Prop.
  Definition VertexMap (A : Type) : Type := VertexId -> option A.

  Definition vertex_update {A}
      (n : VertexId) (v : A) (V : VertexMap A) : VertexMap A :=
    fun n' => if Nat.eq_dec n n' then Some v else V n'.

  Definition vertex_set_add (n : VertexId) (N : VertexSet) : VertexSet :=
    fun n' => n' = n \/ N n'.

  Definition empty_vertex_map {A} : VertexMap A := fun _ => None.
  Definition empty_vertex_set : VertexSet := fun _ => False.
  Definition empty_edges : Edges := fun _ _ => False.

  Lemma vertex_update_same {A} n (v : A) V :
    vertex_update n v V n = Some v.
  Proof.
    unfold vertex_update. destruct (Nat.eq_dec n n); congruence.
  Qed.

  Lemma vertex_update_other {A} n m (v : A) V :
    n <> m -> vertex_update n v V m = V m.
  Proof.
    intros Hne. unfold vertex_update. destruct (Nat.eq_dec n m); congruence.
  Qed.

  (** Facts about the pending map shared by the well-formedness proofs. *)
  Lemma find_add_inv (actor a : tid) (n m : nat) (P : TMap.t nat) :
    TMap.find a (TMap.add actor n P) = Some m ->
    (a = actor /\ m = n) \/ (a <> actor /\ TMap.find a P = Some m).
  Proof.
    intros H. destruct (Pos.eq_dec a actor) as [-> | Hne].
    - rewrite TMap.gss in H. inversion H. auto.
    - rewrite TMap.gso in H by exact Hne. auto.
  Qed.

  Lemma find_remove_inv (actor a : tid) (m : nat) (P : TMap.t nat) :
    TMap.find a (TMap.remove actor P) = Some m ->
    a <> actor /\ TMap.find a P = Some m.
  Proof.
    intros H. destruct (Pos.eq_dec a actor) as [-> | Hne].
    - rewrite TMap.grs in H. discriminate.
    - rewrite TMap.gro in H by exact Hne. auto.
  Qed.

  Section Spec.
    Context {A : Type}.

    Variant EPOQueue_op :=
    | poq_enq (v : A)
    | poq_deq.
    Arguments EPOQueue_op : clear implicits.

    Definition EPOQueue_ar (op : EPOQueue_op) : Type :=
      match op with
      | poq_enq _ => unit
      | poq_deq => A
      end.

    Canonical Structure EPOQueue :=
    {|
      Sig.op := EPOQueue_op;
      Sig.ar := EPOQueue_ar
    |}.

    (** The tuple [(V, E, P, g, nxt)] of Definition 4.1.  Removed vertices
        remain in [poq_vertices]; [poq_garbage] distinguishes them from the
        live ones.  An edge [poq_edges s n m] reads "[n] is after [m]". *)
    Record POQueueState : Type := {
      poq_vertices : VertexMap A;
      poq_edges : Edges;
      poq_pending : TMap.t VertexId;
      poq_garbage : VertexSet;
      poq_next : VertexId;
    }.

    Definition poq_is_vertex (s : POQueueState) (n : VertexId) : Prop :=
      poq_vertices s n <> None.

    Definition poq_pending_vertex (s : POQueueState) (n : VertexId) : Prop :=
      exists actor, TMap.find actor (poq_pending s) = Some n.

    Definition poq_live (s : POQueueState) (n : VertexId) : Prop :=
      poq_is_vertex s n /\ ~ poq_garbage s n.

    Definition poq_complete (s : POQueueState) (n : VertexId) : Prop :=
      poq_is_vertex s n /\ ~ poq_pending_vertex s n.

    Definition poq_minimal (s : POQueueState) (n : VertexId) : Prop :=
      poq_live s n /\ forall m, poq_edges s n m -> ~ poq_live s m.

    (** [enq-inv]: the new vertex [nxt] is ordered after every complete
        vertex, garbage included (the "garbage-independent edges" decision
        of the TryStack development). *)
    Definition poq_start_enq
        (actor : tid) (v : A) (s : POQueueState) : POQueueState :=
      let n := poq_next s in
      {|
        poq_vertices := vertex_update n v (poq_vertices s);
        poq_edges :=
          fun n1 n2 => poq_edges s n1 n2 \/ (n1 = n /\ poq_complete s n2);
        poq_pending := TMap.add actor n (poq_pending s);
        poq_garbage := poq_garbage s;
        poq_next := S n
      |}.

    (** [enq-ret] *)
    Definition poq_finish_enq
        (actor : tid) (s : POQueueState) : POQueueState :=
      {|
        poq_vertices := poq_vertices s;
        poq_edges := poq_edges s;
        poq_pending := TMap.remove actor (poq_pending s);
        poq_garbage := poq_garbage s;
        poq_next := poq_next s
      |}.

    (** [deq-res] *)
    Definition poq_mark_garbage
        (n : VertexId) (s : POQueueState) : POQueueState :=
      {|
        poq_vertices := poq_vertices s;
        poq_edges := poq_edges s;
        poq_pending := poq_pending s;
        poq_garbage := vertex_set_add n (poq_garbage s);
        poq_next := poq_next s
      |}.

    Definition empty_poqueue_state : POQueueState :=
      {|
        poq_vertices := empty_vertex_map;
        poq_edges := empty_edges;
        poq_pending := TMap.empty VertexId;
        poq_garbage := empty_vertex_set;
        poq_next := O
      |}.

    (** As in [TryStackSpec], a control state makes the dequeue atomic: in
        [POQAtomic] only the dequeuer's response is enabled, so its two
        observable events are adjacent in every trace.  Enqueues stay in
        [POQReady], permitting the interval overlap. *)
    Variant POQueueControl : Type :=
    | POQReady (s : POQueueState)
    | POQAtomic (s : POQueueState) (actor : tid) (op : EPOQueue_op).

    Definition poq_payload (c : POQueueControl) : POQueueState :=
      match c with
      | POQReady s => s
      | POQAtomic s _ _ => s
      end.

    (** Definition 4.2. *)
    Variant StepPOQueue :
      @ThreadEvent EPOQueue -> POQueueControl -> POQueueControl -> Prop :=

    | step_poq_enq_inv actor s v e
        (Hidle : TMap.find actor (poq_pending s) = None) :
        e = {| te_tid := actor; te_ev := InvEv (poq_enq v) |} ->
        StepPOQueue e
          (POQReady s)
          (POQReady (poq_start_enq actor v s))
    | step_poq_enq_res actor s v n e
        (Hpending : TMap.find actor (poq_pending s) = Some n) :
        e = {| te_tid := actor; te_ev := ResEv (poq_enq v) tt |} ->
        StepPOQueue e
          (POQReady s)
          (POQReady (poq_finish_enq actor s))

    | step_poq_deq_inv actor s e :
        e = {| te_tid := actor; te_ev := InvEv poq_deq |} ->
        StepPOQueue e
          (POQReady s)
          (POQAtomic s actor poq_deq)
    | step_poq_deq_res actor s n v e
        (Hminimal : poq_minimal s n)
        (Hcomplete : poq_complete s n)
        (Hvalue : poq_vertices s n = Some v) :
        e = {| te_tid := actor; te_ev := ResEv poq_deq v |} ->
        StepPOQueue e
          (POQAtomic s actor poq_deq)
          (POQReady (poq_mark_garbage n s)).

    Definition ErrorPOQueue :
        @ThreadEvent EPOQueue -> POQueueControl -> Prop :=
      NoError.

    Definition VPOQueue : @LTS EPOQueue :=
      {|
        State := POQueueControl;
        Step := StepPOQueue;
        Error := ErrorPOQueue
      |}.

    (** ** Well-formedness (Lemma 4.3)

        (W1)--(W5) are the paper's clauses.  They are not inductive on
        their own: preserving (W3)--(W5) across [enq-inv] needs the three
        membership clauses (W6)--(W8), which the paper's proof uses
        implicitly ("the new identifier is fresh"). *)
    Record poq_wf (s : POQueueState) : Prop := {
      (* W1 *)
      wf_vertex_iff_lt : forall n, poq_is_vertex s n <-> n < poq_next s;
      (* W2 *)
      wf_edge_lt : forall n m, poq_edges s n m -> m < n;
      (* W3 *)
      wf_pending_no_incoming :
        forall n m, poq_pending_vertex s m -> ~ poq_edges s n m;
      (* W4 *)
      wf_pending_not_garbage :
        forall n, poq_pending_vertex s n -> ~ poq_garbage s n;
      (* W5 *)
      wf_pending_unique :
        forall a b n,
          TMap.find a (poq_pending s) = Some n ->
          TMap.find b (poq_pending s) = Some n ->
          a = b;
      (* W6: edge sources are vertices *)
      wf_edge_source : forall n m, poq_edges s n m -> poq_is_vertex s n;
      (* W7: pending vertices are vertices *)
      wf_pending_vertex : forall n, poq_pending_vertex s n -> poq_is_vertex s n;
      (* W8: garbage vertices are vertices *)
      wf_garbage_vertex : forall n, poq_garbage s n -> poq_is_vertex s n;
    }.

    Lemma empty_poqueue_state_wf : poq_wf empty_poqueue_state.
    Proof.
      constructor; simpl;
        unfold poq_is_vertex, poq_pending_vertex,
          empty_vertex_map, empty_edges, empty_vertex_set; simpl.
      - intro n. split; [intro H; exfalso; exact (H eq_refl) | lia].
      - intros n m [].
      - intros n m _ [].
      - intros n _ [].
      - intros a b n H. rewrite TMap.gempty in H. discriminate.
      - intros n m [].
      - intros n [a H]. rewrite TMap.gempty in H. discriminate.
      - intros n [].
    Qed.

    Lemma poq_start_enq_is_vertex actor v s m :
      poq_is_vertex (poq_start_enq actor v s) m <->
      (m = poq_next s \/ poq_is_vertex s m).
    Proof.
      unfold poq_is_vertex, poq_start_enq, vertex_update; simpl.
      destruct (Nat.eq_dec (poq_next s) m) as [Heq | Hne].
      - split; [intro; left; auto | intro; discriminate].
      - split; [intro; right; auto |].
        intros [H | H]; [exfalso; apply Hne; auto | exact H].
    Qed.

    Lemma poq_start_enq_pending_vertex actor v s m :
      TMap.find actor (poq_pending s) = None ->
      (poq_pending_vertex (poq_start_enq actor v s) m <->
       (m = poq_next s \/ poq_pending_vertex s m)).
    Proof.
      intros Hidle. unfold poq_pending_vertex, poq_start_enq; simpl.
      split.
      - intros [a Ha]. apply find_add_inv in Ha.
        destruct Ha as [[_ ->] | [_ Ha]]; [left; reflexivity | right; eauto].
      - intros [-> | [a Ha]].
        + exists actor. apply TMap.gss.
        + exists a. rewrite TMap.gso; [exact Ha |].
          intros ->. congruence.
    Qed.

    Lemma poq_finish_enq_pending_vertex actor s m :
      poq_pending_vertex (poq_finish_enq actor s) m ->
      poq_pending_vertex s m.
    Proof.
      intros [a Ha]. unfold poq_finish_enq in Ha; simpl in Ha.
      apply find_remove_inv in Ha. destruct Ha as [_ Ha]. exists a. exact Ha.
    Qed.

    Lemma poq_start_enq_wf actor v s :
      poq_wf s ->
      TMap.find actor (poq_pending s) = None ->
      poq_wf (poq_start_enq actor v s).
    Proof.
      intros [W1 W2 W3 W4 W5 W6 W7 W8] Hidle.
      assert (Hfresh : ~ poq_is_vertex s (poq_next s)).
      { intro Hv. apply W1 in Hv. lia. }
      constructor.
      - (* W1 *)
        intro n. simpl. split.
        + intro H. apply poq_start_enq_is_vertex in H.
          destruct H as [-> | H]; [lia | apply W1 in H; lia].
        + intro H. apply poq_start_enq_is_vertex.
          destruct (Nat.eq_dec n (poq_next s)) as [-> | Hne];
            [left; reflexivity | right; apply W1; lia].
      - (* W2 *)
        intros n m [Hold | [-> [Hv _]]]; simpl.
        + apply W2. exact Hold.
        + apply W1. exact Hv.
      - (* W3 *)
        intros n m Hpm Hedge.
        apply poq_start_enq_pending_vertex in Hpm; [| exact Hidle].
        destruct Hedge as [Hold | [-> Hc]].
        + destruct Hpm as [-> | Hpm].
          * pose proof (W6 n _ Hold) as Hv. apply W1 in Hv.
            apply W2 in Hold. lia.
          * exact (W3 n m Hpm Hold).
        + destruct Hpm as [-> | Hpm].
          * exact (Hfresh (proj1 Hc)).
          * exact (proj2 Hc Hpm).
      - (* W4 *)
        intros n Hp Hg. simpl in Hg.
        apply poq_start_enq_pending_vertex in Hp; [| exact Hidle].
        destruct Hp as [-> | Hp].
        + exact (Hfresh (W8 _ Hg)).
        + exact (W4 n Hp Hg).
      - (* W5 *)
        intros a b n Ha Hb. simpl in Ha, Hb.
        apply find_add_inv in Ha. apply find_add_inv in Hb.
        destruct Ha as [[Ha1 Ha2] | [Hane Ha]];
          destruct Hb as [[Hb1 Hb2] | [Hbne Hb]].
        + congruence.
        + subst n. exfalso. apply Hfresh. apply W7. exists b. exact Hb.
        + subst n. exfalso. apply Hfresh. apply W7. exists a. exact Ha.
        + exact (W5 a b n Ha Hb).
      - (* W6 *)
        intros n m Hedge. apply poq_start_enq_is_vertex.
        destruct Hedge as [Hold | [-> _]].
        + right. exact (W6 n m Hold).
        + left. reflexivity.
      - (* W7 *)
        intros n Hp. apply poq_start_enq_is_vertex.
        apply poq_start_enq_pending_vertex in Hp; [| exact Hidle].
        destruct Hp as [-> | Hp]; [left; reflexivity | right; exact (W7 n Hp)].
      - (* W8 *)
        intros n Hg. simpl in Hg. apply poq_start_enq_is_vertex.
        right. exact (W8 n Hg).
    Qed.

    Lemma poq_finish_enq_wf actor s :
      poq_wf s ->
      poq_wf (poq_finish_enq actor s).
    Proof.
      intros [W1 W2 W3 W4 W5 W6 W7 W8].
      constructor; simpl; unfold poq_is_vertex; simpl.
      - exact W1.
      - exact W2.
      - intros n m Hp. apply poq_finish_enq_pending_vertex in Hp.
        exact (W3 n m Hp).
      - intros n Hp. apply poq_finish_enq_pending_vertex in Hp.
        exact (W4 n Hp).
      - intros a b n Ha Hb.
        apply find_remove_inv in Ha. apply find_remove_inv in Hb.
        exact (W5 a b n (proj2 Ha) (proj2 Hb)).
      - exact W6.
      - intros n Hp. apply poq_finish_enq_pending_vertex in Hp.
        exact (W7 n Hp).
      - exact W8.
    Qed.

    Lemma poq_mark_garbage_wf n s :
      poq_wf s ->
      poq_complete s n ->
      poq_wf (poq_mark_garbage n s).
    Proof.
      intros [W1 W2 W3 W4 W5 W6 W7 W8] [Hv Hnp].
      constructor; simpl; unfold poq_is_vertex, poq_pending_vertex; simpl.
      - exact W1.
      - exact W2.
      - exact W3.
      - intros m Hp [-> | Hg].
        + exact (Hnp Hp).
        + exact (W4 m Hp Hg).
      - exact W5.
      - exact W6.
      - exact W7.
      - intros m [-> | Hg]; [exact Hv | exact (W8 m Hg)].
    Qed.

    Lemma step_poq_wf e c c' :
      StepPOQueue e c c' ->
      poq_wf (poq_payload c) ->
      poq_wf (poq_payload c').
    Proof.
      intros Hstep Hwf. inversion Hstep; subst; simpl in *.
      - now apply poq_start_enq_wf.
      - now apply poq_finish_enq_wf.
      - exact Hwf.
      - now apply poq_mark_garbage_wf.
    Qed.

    (** ** Facts about the transformers

        Used by both layer proofs.  They say how each rule changes the
        derived predicates of Definition 4.1. *)

    Lemma poq_pending_vertex_unique s a b n :
      poq_wf s ->
      TMap.find a (poq_pending s) = Some n ->
      TMap.find b (poq_pending s) = Some n ->
      a = b.
    Proof. intros Hwf. apply (wf_pending_unique s Hwf). Qed.

    Lemma poq_pending_live s n :
      poq_wf s -> poq_pending_vertex s n -> poq_live s n.
    Proof.
      intros Hwf Hp. split.
      - exact (wf_pending_vertex s Hwf n Hp).
      - exact (wf_pending_not_garbage s Hwf n Hp).
    Qed.

    Lemma poq_vertex_lt s n :
      poq_wf s -> poq_is_vertex s n -> n < poq_next s.
    Proof. intros Hwf Hv. apply (wf_vertex_iff_lt s Hwf). exact Hv. Qed.

    Lemma poq_next_not_vertex s :
      poq_wf s -> ~ poq_is_vertex s (poq_next s).
    Proof. intros Hwf Hv. apply poq_vertex_lt in Hv; [lia | exact Hwf]. Qed.

    Lemma poq_vertex_some s n :
      poq_is_vertex s n -> exists v, poq_vertices s n = Some v.
    Proof.
      unfold poq_is_vertex. destruct (poq_vertices s n) as [v|]; [eauto | congruence].
    Qed.

    (** [enq-inv] *)

    Lemma poq_start_enq_vertices actor v s m :
      m <> poq_next s ->
      poq_vertices (poq_start_enq actor v s) m = poq_vertices s m.
    Proof.
      intros Hne. unfold poq_start_enq; simpl. apply vertex_update_other. auto.
    Qed.

    Lemma poq_start_enq_vertex_new actor v s :
      poq_vertices (poq_start_enq actor v s) (poq_next s) = Some v.
    Proof. unfold poq_start_enq; simpl. apply vertex_update_same. Qed.

    Lemma poq_start_enq_edges actor v s n m :
      poq_edges (poq_start_enq actor v s) n m <->
      (poq_edges s n m \/ (n = poq_next s /\ poq_complete s m)).
    Proof. reflexivity. Qed.

    Lemma poq_start_enq_live actor v s m :
      poq_wf s ->
      (poq_live (poq_start_enq actor v s) m <->
       (m = poq_next s \/ poq_live s m)).
    Proof.
      intros Hwf. unfold poq_live. rewrite poq_start_enq_is_vertex.
      change (poq_garbage (poq_start_enq actor v s)) with (poq_garbage s).
      split.
      - intros [[-> | Hv] Hg]; [left; reflexivity | right; split; assumption].
      - intros [-> | [Hv Hg]].
        + split; [left; reflexivity |].
          intro Hg. apply (poq_next_not_vertex s Hwf).
          exact (wf_garbage_vertex s Hwf _ Hg).
        + split; [right; exact Hv | exact Hg].
    Qed.

    Lemma poq_start_enq_complete actor v s m :
      TMap.find actor (poq_pending s) = None ->
      m <> poq_next s ->
      (poq_complete (poq_start_enq actor v s) m <-> poq_complete s m).
    Proof.
      intros Hidle Hne. unfold poq_complete.
      rewrite poq_start_enq_is_vertex.
      rewrite (poq_start_enq_pending_vertex actor v s m Hidle).
      split.
      - intros [[Heq | Hv] Hnp]; [congruence |].
        split; [exact Hv |]. intro Hp. apply Hnp. right. exact Hp.
      - intros [Hv Hnp]. split; [right; exact Hv |].
        intros [Heq | Hp]; [congruence | exact (Hnp Hp)].
    Qed.

    Lemma poq_start_enq_new_pending actor v s :
      TMap.find actor (poq_pending s) = None ->
      poq_pending_vertex (poq_start_enq actor v s) (poq_next s).
    Proof.
      intros Hidle. apply (poq_start_enq_pending_vertex actor v s _ Hidle).
      left. reflexivity.
    Qed.

    Lemma poq_start_enq_new_not_complete actor v s :
      TMap.find actor (poq_pending s) = None ->
      ~ poq_complete (poq_start_enq actor v s) (poq_next s).
    Proof.
      intros Hidle [_ Hnp]. apply Hnp. exact (poq_start_enq_new_pending actor v s Hidle).
    Qed.

    (** [enq-ret] *)

    Lemma poq_finish_enq_pending_vertex_iff actor s n m :
      poq_wf s ->
      TMap.find actor (poq_pending s) = Some n ->
      (poq_pending_vertex (poq_finish_enq actor s) m <->
       (poq_pending_vertex s m /\ m <> n)).
    Proof.
      intros Hwf Hfind. split.
      - intros Hp. pose proof (poq_finish_enq_pending_vertex actor s m Hp) as Hold.
        split; [exact Hold |].
        intros ->. destruct Hp as [a Ha]. unfold poq_finish_enq in Ha; simpl in Ha.
        apply find_remove_inv in Ha. destruct Ha as [Hne Ha].
        apply Hne. exact (poq_pending_vertex_unique s a actor n Hwf Ha Hfind).
      - intros [[a Ha] Hne]. exists a. unfold poq_finish_enq; simpl.
        rewrite TMap.gro; [exact Ha |]. intros ->. congruence.
    Qed.

    Lemma poq_finish_enq_complete actor s n m :
      poq_wf s ->
      TMap.find actor (poq_pending s) = Some n ->
      (poq_complete (poq_finish_enq actor s) m <->
       (poq_complete s m \/ m = n)).
    Proof.
      intros Hwf Hfind. unfold poq_complete.
      change (poq_is_vertex (poq_finish_enq actor s) m) with (poq_is_vertex s m).
      rewrite (poq_finish_enq_pending_vertex_iff actor s n m Hwf Hfind).
      split.
      - intros [Hv Hnp]. destruct (Nat.eq_dec m n) as [-> | Hne].
        + right. reflexivity.
        + left. split; [exact Hv |]. intro Hp. apply Hnp. split; assumption.
      - intros [[Hv Hnp] | ->].
        + split; [exact Hv |]. intros [Hp _]. exact (Hnp Hp).
        + split.
          * apply (wf_pending_vertex s Hwf). exists actor. exact Hfind.
          * intros [_ Hne]. exact (Hne eq_refl).
    Qed.

    (** [deq-res] *)

    Lemma poq_mark_garbage_live n s m :
      poq_live (poq_mark_garbage n s) m <-> (poq_live s m /\ m <> n).
    Proof.
      unfold poq_live, poq_mark_garbage, vertex_set_add; simpl. split.
      - intros [Hv Hg]. split; [split; [exact Hv |] |]; intro H; apply Hg; auto.
      - intros [[Hv Hg] Hne]. split; [exact Hv |]. intros [H | H]; auto.
    Qed.

    Lemma poq_mark_garbage_complete n s m :
      poq_complete (poq_mark_garbage n s) m <-> poq_complete s m.
    Proof. reflexivity. Qed.

  End Spec.

  Module POQueueLayer.
    Section Layer.
      Context {A : Type}.

      Definition L : layer_interface :=
        {|
          li_sig := @EPOQueue A;
          li_lts := @VPOQueue A;
          li_init := POQReady (@empty_poqueue_state A)
        |}.
    End Layer.
  End POQueueLayer.

End POQueueSpec.
