Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import PeanoNat.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.


Module TimestampSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import TPSimulationSet.TPSimulation.

  (* Interval timestamps used by the timestamped stack.  [TSTop] is the
     initial, not-yet-stamped value stored in a newly allocated node. *)
  Variant TS : Type :=
  | TSTop
  | TSInterval (lower upper : nat).

  (** Figure 14's strict timestamp order.  Intervals are ordered only when
      they do not overlap; every allocated interval precedes the sentinel
      timestamp [TSTop]. *)
  Definition timestamp_lt (older newer : TS) : Prop :=
    match older, newer with
    | TSInterval _ older_upper, TSInterval newer_lower _ =>
        older_upper < newer_lower
    | TSInterval _ _, TSTop => True
    | TSTop, _ => False
    end.

  Variant ETimestamp_op :=
  | newTS.
  Arguments ETimestamp_op : clear implicits.

  Definition ETimestamp_ar (m : ETimestamp_op) : Type :=
    match m with
    (** The paper writes [N * N].  We embed that pair as [TSInterval] so
        the result can be passed directly to node-memory [setTS]; the LTS
        below never returns [TSTop]. *)
    | newTS => TS
    end.

  Canonical Structure ETimestamp :=
  {|
    Sig.op := ETimestamp_op;
    Sig.ar := ETimestamp_ar
  |}.

  (** The state [(t,p)] from Appendix A.1.  [ts_clock] is [t], and a map
      entry [p[actor] = lower] records the clock observed by the actor's
      pending [newTS] invocation.  Absence from the map represents bottom. *)
  Record TimestampState : Type := {
    ts_clock : nat;
    ts_pending : TMap.t nat;
  }.

  Definition initial_timestamp_state : TimestampState :=
    {|
      ts_clock := 0;
      ts_pending := TMap.empty nat
    |}.

  Definition start_newTS
      (actor : tid) (s : TimestampState) : TimestampState :=
    {|
      ts_clock := ts_clock s;
      ts_pending := TMap.add actor (ts_clock s) (ts_pending s)
    |}.

  Definition finish_newTS
      (actor : tid) (upper : nat) (s : TimestampState) : TimestampState :=
    {|
      ts_clock := Nat.max (ts_clock s) (S upper);
      ts_pending := TMap.remove actor (ts_pending s)
    |}.

  (** The paper's state invariant:
      [p[actor] <> bottom -> p[actor] <= t]. *)
  Definition timestamp_state_valid (s : TimestampState) : Prop :=
    forall actor lower,
      TMap.find actor (ts_pending s) = Some lower ->
      lower <= ts_clock s.

  Variant StepTimestamp :
      @ThreadEvent ETimestamp -> TimestampState -> TimestampState -> Prop :=
  | step_newTS_inv actor s e :
      e = {| te_tid := actor; te_ev := InvEv newTS |} ->
      StepTimestamp e s (start_newTS actor s)
  | step_newTS_res actor s lower upper e :
      TMap.find actor (ts_pending s) = Some lower ->
      lower <= upper ->
      e = {| te_tid := actor;
             te_ev := ResEv newTS (TSInterval lower upper) |} ->
      StepTimestamp e s (finish_newTS actor upper s).

  Definition ErrorTimestamp :
      @ThreadEvent ETimestamp -> TimestampState -> Prop :=
    NoError.

  Definition VTimestamp : @LTS ETimestamp :=
    {|
      State := TimestampState;
      Step := StepTimestamp;
      Error := ErrorTimestamp
    |}.

  Lemma initial_timestamp_state_valid :
    timestamp_state_valid initial_timestamp_state.
  Proof.
    intros actor lower Hfind. rewrite TMap.gempty in Hfind. discriminate.
  Qed.

  Lemma start_newTS_valid actor s :
    timestamp_state_valid s ->
    timestamp_state_valid (start_newTS actor s).
  Proof.
    intros Hvalid observer lower Hfind.
    destruct (Pos.eq_dec observer actor) as [-> | Hneq].
    - unfold start_newTS in Hfind. simpl in Hfind.
      rewrite TMap.gss in Hfind. inversion Hfind. apply Nat.le_refl.
    - unfold start_newTS in Hfind. simpl in Hfind.
      rewrite TMap.gso in Hfind by exact Hneq.
      eapply Hvalid. exact Hfind.
  Qed.

  Lemma finish_newTS_valid actor upper s :
    timestamp_state_valid s ->
    timestamp_state_valid (finish_newTS actor upper s).
  Proof.
    intros Hvalid observer lower Hfind.
    destruct (Pos.eq_dec observer actor) as [-> | Hneq].
    - unfold finish_newTS in Hfind. simpl in Hfind.
      rewrite TMap.grs in Hfind. discriminate.
    - unfold finish_newTS in Hfind. simpl in Hfind.
      rewrite TMap.gro in Hfind by exact Hneq.
      eapply Nat.le_trans.
      + eapply Hvalid. exact Hfind.
      + apply Nat.le_max_l.
  Qed.

  Lemma step_timestamp_valid e s s' :
    StepTimestamp e s s' ->
    timestamp_state_valid s ->
    timestamp_state_valid s'.
  Proof.
    intros Hstep Hvalid. inversion Hstep; subst.
    - now apply start_newTS_valid.
    - now apply finish_newTS_valid.
  Qed.

  Module TimestampLayer.
    Definition L : layer_interface :=
      {|
        li_sig := ETimestamp;
        li_lts := VTimestamp;
        li_init := initial_timestamp_state
      |}.
  End TimestampLayer.

End TimestampSpec.
