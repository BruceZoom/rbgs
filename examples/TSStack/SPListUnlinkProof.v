Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import PeanoNat.
Require Import List.
Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import SeparationAlgebra.
Require Import Assertion.
Require Import TPSimulationSet.
Require Import RGISimulationSet.
Require Import RGILogicSet.
Require Import CompLinLayer.
Require Import CompLinProj.

Require Import examples.Common.AtomicLTS.
Require Import examples.Common.Heap.
Require Import examples.CAS.CASRegSpec.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.NodeMemUnlinkSpec.
Require Import examples.TSStack.SPListSpec.
Require Import examples.TSStack.SPListGhostSpec.
Require Import examples.TSStack.SPList.
Require Import examples.TSStack.SPListUnlink.


(** Verification of [SPListUnlinkImpl], the single-producer list that
    unlinks taken nodes.

    The proof follows [SPListProof] (same singleton-set facade, same
    two-possibility window for [getTop]), but its representation invariant
    is different.  [SPListProof] represents the list by the immutable
    successor chain from the top.  With unlinking, successor pointers
    change and taken nodes drop out of the chain, so the chain no longer
    records the insertion order, and that order is exactly what makes
    "every node between [x] and its successor is taken" a stable fact.
    The proof therefore works against [SPListGhostSpec], whose state carries
    the insertion log, and [CompLinProj] erases the log at the end, so the
    result is a proof against the unchanged [SPListSpec].

    The invariant [valid h top log] says: the log has no duplicates, the
    top pointer points into the log after a prefix of taken nodes, and
    every node's successor points into the suffix of the log after it,
    again after a prefix of taken nodes ([skips]).  Taken flags only ever
    flip to true, so [skips] facts are stable; the log only ever grows at
    its front, so facts about a suffix of the log are stable.  Traversals
    keep a split of the log into a prefix of dead nodes and a suffix that
    the cursor skips into. *)
Module SPListUnlinkProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSingle.
  Import TPSimulationSet.TPSimulation.
  Import AtomicLTS CASRegSpec TimestampSpec NodeMemUnlinkSpec SPListSpec
    SPListGhostSpec.
  Import ListNotations.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.
  Module SetLogic := RGILogicSet.RGILogic.
  Import SetLogic.

  Open Scope prog_scope.
  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  Section Proof.
    Context {A : Type}.
    Context {owner : tid}.

    Definition ENodeMemLayer : layer_interface :=
      @NodeMemUnlinkLayer.L A.

    Definition ECASLayer : layer_interface := SPListImpl.ECASLayer.

    Definition E : layer_interface := ENodeMemLayer ⊗ₗ ECASLayer.

    (** The ghost overlay: [SPListSpec] with the insertion log. *)
    Definition F : layer_interface :=
      {|
        li_sig := @ESPList A;
        li_lts := @VSPListGhost A owner;
        li_init := pair (Ready (@SPListImpl.empty_splist_state A)) nil
      |}.

    (** The intended overlay, literally the one of [SPListProof]. *)
    Definition FSpec : layer_interface := @SPListImpl.F A owner.

    Definition mem_control :=
      State (@NodeMemUnlinkSpec.VNodeMemU A).
    Definition cas_control :=
      State (@CASRegSpec.VCASReg (Ptr * nat)).
    Definition abstract_control :=
      State (@SPListSpec.VSPList A owner).

    Definition concrete_state := State (li_lts E).
    Definition abstract_state := State (li_lts F).
    Definition single_state :=
      @SinglePossState.ProofStateSingle _ _ (li_lts E) (li_lts F).
    Definition assertion := @Assertion single_state.
    Definition rg_relation :=
      @AssertionsSingle.A.RGRelation _ _ (li_lts E) (li_lts F).

    Definition mem_heap (mc : mem_control) : @Heap (@Node A) :=
      AtomicLTS.state mc.

    Definition cas_value (cc : cas_control) : Ptr * nat :=
      AtomicLTS.state cc.

    Definition node_live (n : @Node A) : bool :=
      negb (snd (fst n)).

    Definition live_at (h : @Heap (@Node A)) (l : Addr) : bool :=
      match h l with
      | Some n => node_live n
      | None => false
      end.

    Definition taken_at (h : @Heap (@Node A)) (l : Addr) : bool :=
      match h l with
      | Some n => snd (fst n)
      | None => false
      end.

    Fixpoint live_order (h : @Heap (@Node A)) (xs : list Addr) : list Addr :=
      match xs with
      | nil => nil
      | l :: xs' =>
          if live_at h l then l :: live_order h xs'
          else live_order h xs'
      end.

    Definition node_projection (n : @Node A) : A * TS :=
      fst (fst n).

    Definition abstract_nodes
        (h : @Heap (@Node A)) (xs : list Addr) : @Heap (A * TS) :=
      fun l =>
        if List.existsb (Nat.eqb l) xs then
          match h l with
          | Some n => Some (node_projection n)
          | None => None
          end
        else None.

    (** * The log structure *)

    (** [skips h xs p]: the pointer [p] points into the list [xs] after a
        prefix of taken nodes, or past its end when every node of [xs] is
        taken. *)
    Inductive skips (h : @Heap (@Node A)) : list Addr -> Ptr -> Prop :=
    | skips_nil : skips h nil None
    | skips_here y rest : skips h (y :: rest) (Some y)
    | skips_over z rest p :
        taken_at h z = true -> skips h rest p -> skips h (z :: rest) p.

    (** Every node's successor skips into the suffix after it. *)
    Fixpoint links_ok (h : @Heap (@Node A)) (xs : list Addr) : Prop :=
      match xs with
      | nil => True
      | x :: rest =>
          (exists n, h x = Some n /\ skips h rest (snd n)) /\ links_ok h rest
      end.

    Definition valid (h : @Heap (@Node A)) (top : Ptr) (xs : list Addr) : Prop :=
      NoDup xs /\ skips h xs top /\ links_ok h xs.

    Definition all_taken (h : @Heap (@Node A)) (xs : list Addr) : Prop :=
      List.Forall (fun z => taken_at h z = true) xs.

    Lemma skips_app_taken h a b p :
      all_taken h a -> skips h b p -> skips h (a ++ b) p.
    Proof.
      induction a as [|z a IH]; intros Ha Hb; simpl; [exact Hb|].
      inversion Ha; subst. apply skips_over; [assumption|]. apply IH; assumption.
    Qed.

    Lemma skips_none_taken h xs :
      skips h xs None -> all_taken h xs.
    Proof.
      intros H. remember None as p. induction H; subst; [constructor| discriminate|].
      constructor; [assumption|]. apply IHskips. reflexivity.
    Qed.

    Lemma skips_taken_none h xs :
      all_taken h xs -> skips h xs None.
    Proof.
      induction xs as [|z xs IH]; intros H; [constructor|].
      inversion H; subst. apply skips_over; [assumption|]. apply IH; assumption.
    Qed.

    Lemma skips_some_split h xs y :
      skips h xs (Some y) ->
      exists a b, xs = a ++ y :: b /\ all_taken h a.
    Proof.
      intros H. remember (Some y) as p. induction H; subst.
      - discriminate.
      - injection Heqp as ->. exists nil, rest. split; [reflexivity|constructor].
      - destruct (IHskips eq_refl) as (a & b & -> & Ha).
        exists (z :: a), b. split; [reflexivity|]. constructor; assumption.
    Qed.

    Lemma skips_in h xs y :
      skips h xs (Some y) -> In y xs.
    Proof.
      intros H. destruct (skips_some_split _ _ _ H) as (a & b & -> & _).
      apply in_or_app. right. now left.
    Qed.

    Lemma skips_mono h h' xs p :
      (forall z, taken_at h z = true -> taken_at h' z = true) ->
      skips h xs p -> skips h' xs p.
    Proof.
      intros Hmono H. induction H.
      - constructor.
      - constructor.
      - apply skips_over; [apply Hmono; assumption|assumption].
    Qed.

    Lemma all_taken_mono h h' xs :
      (forall z, taken_at h z = true -> taken_at h' z = true) ->
      all_taken h xs -> all_taken h' xs.
    Proof.
      intros Hmono H. induction H; constructor; auto.
    Qed.

    Lemma all_taken_app h a b :
      all_taken h a -> all_taken h b -> all_taken h (a ++ b).
    Proof. intros Ha Hb. apply Forall_app. split; assumption. Qed.

    Lemma all_taken_app_inv h a b :
      all_taken h (a ++ b) -> all_taken h a /\ all_taken h b.
    Proof. intros H. apply Forall_app in H. exact H. Qed.

    Lemma links_ok_app_r h a b :
      links_ok h (a ++ b) -> links_ok h b.
    Proof.
      induction a as [|x a IH]; intros H; [exact H|].
      simpl in H. apply IH. exact (proj2 H).
    Qed.

    Lemma links_ok_split h a x b :
      links_ok h (a ++ x :: b) ->
      exists n, h x = Some n /\ skips h b (snd n).
    Proof.
      intros H. apply links_ok_app_r in H. simpl in H. exact (proj1 H).
    Qed.

    Lemma links_ok_defined h xs x :
      links_ok h xs -> In x xs -> h x <> None.
    Proof.
      induction xs as [|y xs IH]; intros H Hin; [contradiction|].
      simpl in H, Hin. destruct Hin as [<-|Hin].
      - destruct H as [[n [Hn _]] _]. congruence.
      - apply IH; [exact (proj2 H)|exact Hin].
    Qed.

    (** Transfer of the structure to another heap that keeps every log
        node defined, keeps successors, and only takes nodes. *)
    Definition structure_evol (h h' : @Heap (@Node A)) : Prop :=
      (forall z, taken_at h z = true -> taken_at h' z = true) /\
      (forall x n, h x = Some n -> exists n', h' x = Some n' /\ snd n' = snd n).

    Lemma links_ok_evol h h' xs :
      structure_evol h h' -> links_ok h xs -> links_ok h' xs.
    Proof.
      intros [Htaken Hnext]. induction xs as [|x xs IH]; intros H; [exact I|].
      simpl in H |- *. destruct H as [[n [Hn Hsk]] Hrest].
      split; [|apply IH; exact Hrest].
      destruct (Hnext _ _ Hn) as [n' [Hn' Esnd]].
      exists n'. split; [exact Hn'|]. rewrite Esnd.
      eapply skips_mono; [exact Htaken|exact Hsk].
    Qed.

    Lemma valid_evol h h' top xs :
      structure_evol h h' -> valid h top xs -> valid h' top xs.
    Proof.
      intros Hev [Hnd [Hsk Hlk]]. split; [exact Hnd|]. split.
      - eapply skips_mono; [exact (proj1 Hev)|exact Hsk].
      - eapply links_ok_evol; [exact Hev|exact Hlk].
    Qed.

    Lemma structure_evol_refl h : structure_evol h h.
    Proof. split; [auto|]. intros x n Hn. exists n. auto. Qed.

    Lemma taken_at_update_other h l n q :
      l <> q -> taken_at (heap_update l n h) q = taken_at h q.
    Proof.
      intros Hneq. unfold taken_at. rewrite HeapUpdateOther by exact Hneq.
      reflexivity.
    Qed.

    Lemma live_at_update_other h l q n :
      l <> q -> live_at (heap_update l n h) q = live_at h q.
    Proof.
      intro Hneq. unfold live_at. rewrite HeapUpdateOther by exact Hneq.
      reflexivity.
    Qed.

    (** The heap updates performed by the implementation. *)
    Lemma structure_evol_setTS h l v old_ts taken next ts :
      h l = Some (pair (pair (pair v old_ts) taken) next) ->
      structure_evol h
        (heap_update l (pair (pair (pair v ts) taken) next) h).
    Proof.
      intros Hl. split.
      - intros z Hz. destruct (Nat.eq_dec l z) as [<-|Hneq].
        + unfold taken_at in *. rewrite HeapUpdateSelf. rewrite Hl in Hz. exact Hz.
        + rewrite taken_at_update_other by exact Hneq. exact Hz.
      - intros x n Hx. destruct (Nat.eq_dec l x) as [<-|Hneq].
        + rewrite HeapUpdateSelf. eexists. split; [reflexivity|].
          rewrite Hl in Hx. injection Hx as <-. reflexivity.
        + rewrite HeapUpdateOther by exact Hneq. exists n. auto.
    Qed.

    Lemma structure_evol_take h l v ts next :
      h l = Some (pair (pair (pair v ts) false) next) ->
      structure_evol h
        (heap_update l (pair (pair (pair v ts) true) next) h).
    Proof.
      intros Hl. split.
      - intros z Hz. destruct (Nat.eq_dec l z) as [<-|Hneq].
        + unfold taken_at in *. rewrite HeapUpdateSelf. reflexivity.
        + rewrite taken_at_update_other by exact Hneq. exact Hz.
      - intros x n Hx. destruct (Nat.eq_dec l x) as [<-|Hneq].
        + rewrite HeapUpdateSelf. eexists. split; [reflexivity|].
          rewrite Hl in Hx. injection Hx as <-. reflexivity.
        + rewrite HeapUpdateOther by exact Hneq. exists n. auto.
    Qed.

    Lemma structure_evol_alloc h l n :
      h l = None -> structure_evol h (heap_update l n h).
    Proof.
      intros Hl. split.
      - intros z Hz. destruct (Nat.eq_dec l z) as [<-|Hneq].
        + unfold taken_at in Hz. rewrite Hl in Hz. discriminate.
        + rewrite taken_at_update_other by exact Hneq. exact Hz.
      - intros x m Hx. destruct (Nat.eq_dec l x) as [<-|Hneq]; [congruence|].
        rewrite HeapUpdateOther by exact Hneq. exists m. auto.
    Qed.

    (** Rewriting a successor keeps the structure except at that node. *)
    Definition structure_evol_except (h h' : @Heap (@Node A)) (l : Addr) : Prop :=
      (forall z, taken_at h z = true -> taken_at h' z = true) /\
      (forall x n, x <> l -> h x = Some n -> exists n', h' x = Some n' /\ snd n' = snd n).

    Lemma links_ok_evol_except h h' l xs :
      ~ In l xs -> structure_evol_except h h' l -> links_ok h xs -> links_ok h' xs.
    Proof.
      intros Hnotin [Htaken Hnext]. induction xs as [|x xs IH]; intros H; [exact I|].
      simpl in H |- *. destruct H as [[n [Hn Hsk]] Hrest].
      assert (Hxl : x <> l) by (intro; subst; apply Hnotin; now left).
      split; [|apply IH; [intro Hin; apply Hnotin; now right|exact Hrest]].
      destruct (Hnext _ _ Hxl Hn) as [n' [Hn' Esnd]].
      exists n'. split; [exact Hn'|]. rewrite Esnd.
      eapply skips_mono; [exact Htaken|exact Hsk].
    Qed.

    Lemma structure_evol_next h l v ts taken old new :
      h l = Some (pair (pair (pair v ts) taken) old) ->
      structure_evol_except h
        (heap_update l (pair (pair (pair v ts) taken) new) h) l.
    Proof.
      intros Hl. split.
      - intros z Hz. destruct (Nat.eq_dec l z) as [<-|Hneq].
        + unfold taken_at in *. rewrite HeapUpdateSelf. rewrite Hl in Hz. exact Hz.
        + rewrite taken_at_update_other by exact Hneq. exact Hz.
      - intros x n Hxl Hx. rewrite HeapUpdateOther by (intro; subst; apply Hxl; reflexivity).
        exists n. auto.
    Qed.

    Lemma skips_update_next h l v ts taken old new xs p :
      h l = Some (pair (pair (pair v ts) taken) old) ->
      skips h xs p ->
      skips (heap_update l (pair (pair (pair v ts) taken) new) h) xs p.
    Proof.
      intros Hl H. eapply skips_mono; [|exact H].
      exact (proj1 (structure_evol_next h l v ts taken old new Hl)).
    Qed.

    Lemma links_ok_update_next h l v ts taken old new a b :
      NoDup (a ++ l :: b) ->
      h l = Some (pair (pair (pair v ts) taken) old) ->
      links_ok h (a ++ l :: b) ->
      skips h b new ->
      links_ok (heap_update l (pair (pair (pair v ts) taken) new) h)
        (a ++ l :: b).
    Proof.
      intros Hnd Hl Hlk Hnew.
      pose proof (NoDup_remove_2 _ _ _ Hnd) as Hnotin.
      assert (Hna : ~ In l a) by (intro Hin; apply Hnotin, in_or_app; now left).
      assert (Hnb : ~ In l b) by (intro Hin; apply Hnotin, in_or_app; now right).
      clear Hnd Hnotin.
      induction a as [|x a IH]; simpl in *.
      - destruct Hlk as [_ Hrest]. split.
        + eexists. split; [apply HeapUpdateSelf|]. simpl.
          eapply skips_update_next; [exact Hl|exact Hnew].
        + eapply links_ok_evol_except; [exact Hnb| |exact Hrest].
          eapply structure_evol_next; exact Hl.
      - destruct Hlk as [[n [Hn Hsk]] Hrest].
        assert (Hxl : l <> x) by (intro; subst; apply Hna; now left).
        split.
        + exists n. split; [rewrite HeapUpdateOther by exact Hxl; exact Hn|].
          eapply skips_update_next; [exact Hl|exact Hsk].
        + apply IH; [exact Hrest|intro Hin; apply Hna; now right].
    Qed.


    (** * Live order and abstract nodes *)

    Lemma live_order_ext h h' xs :
      (forall q, In q xs -> live_at h q = live_at h' q) ->
      live_order h xs = live_order h' xs.
    Proof.
      induction xs as [|q tl IH]; intro Heq; [reflexivity|].
      simpl. rewrite (Heq q) by now left.
      assert (Htail : live_order h tl = live_order h' tl).
      { apply IH. intros r Hr. apply Heq. now right. }
      destruct (live_at h' q); simpl; rewrite Htail; reflexivity.
    Qed.

    Lemma live_order_in h xs l :
      In l (live_order h xs) -> In l xs.
    Proof.
      induction xs as [|q tl IH]; simpl; [tauto|].
      destruct (live_at h q); simpl; intuition.
    Qed.

    Lemma live_order_spec h xs l :
      NoDup xs ->
      (In l (live_order h xs) <-> In l xs /\ live_at h l = true).
    Proof.
      intro Hnodup. induction xs as [|q tl IH]; simpl.
      - tauto.
      - inversion Hnodup as [|? ? Hfresh Hnodup']; subst.
        specialize (IH Hnodup'). destruct (live_at h q) eqn:Hq; simpl.
        + split.
          * intros [Heq|Hin].
            -- subst q. split; [now left|exact Hq].
            -- apply IH in Hin as [Hin Hlive]. split; [now right|exact Hlive].
          * intros [[Heq|Hin] Hlive].
            -- now left.
            -- right. apply IH. now split.
        + split.
          * intro Hin. apply IH in Hin as [Hin Hlive]. split; [now right|exact Hlive].
          * intros [[Heq|Hin] Hlive].
            -- subst q. rewrite Hq in Hlive. discriminate.
            -- apply IH. now split.
    Qed.

    Lemma live_order_app h a b :
      live_order h (a ++ b) = live_order h a ++ live_order h b.
    Proof.
      induction a as [|q a IH]; simpl; [reflexivity|].
      destruct (live_at h q); simpl; rewrite IH; reflexivity.
    Qed.

    Lemma live_order_all_dead h xs :
      (forall q, In q xs -> live_at h q = false) -> live_order h xs = nil.
    Proof.
      induction xs as [|q xs IH]; intros H; simpl; [reflexivity|].
      rewrite (H q) by now left. apply IH. intros r Hr. apply H. now right.
    Qed.

    Lemma taken_live_false h z :
      taken_at h z = true -> live_at h z = false.
    Proof.
      unfold taken_at, live_at, node_live. destruct (h z) as [n|]; [|discriminate].
      intros ->. reflexivity.
    Qed.

    Lemma live_false_taken h z :
      h z <> None -> live_at h z = false -> taken_at h z = true.
    Proof.
      unfold taken_at, live_at, node_live. destruct (h z) as [n|]; [|congruence].
      intros _. destruct (snd (fst n)); [reflexivity|discriminate].
    Qed.

    Lemma all_taken_dead h xs :
      all_taken h xs -> forall q, In q xs -> live_at h q = false.
    Proof.
      intros H q Hq. unfold all_taken in H. rewrite Forall_forall in H.
      apply taken_live_false. apply H, Hq.
    Qed.

    Lemma forall_live_order h xs :
      List.Forall (fun l => In l xs) (live_order h xs).
    Proof.
      induction xs as [|q tl IH]; simpl; [constructor|].
      destruct (live_at h q); simpl.
      - constructor; [now left|].
        eapply List.Forall_impl; [|exact IH]. intros l Hin. now right.
      - eapply List.Forall_impl; [|exact IH]. intros l Hin. now right.
    Qed.

    Lemma filter_live_order h xs :
      List.filter (live_at h) (live_order h xs) = live_order h xs.
    Proof.
      induction xs as [|q tl IH]; simpl; [reflexivity|].
      destruct (live_at h q) eqn:Hlive; simpl; rewrite ?Hlive, IH;
        reflexivity.
    Qed.

    Lemma live_order_filter h xs :
      live_order h xs = List.filter (live_at h) xs.
    Proof.
      induction xs as [|q tl IH]; simpl; [reflexivity|].
      destruct (live_at h q); simpl; rewrite IH; reflexivity.
    Qed.

    Lemma filter_strengthen (p q : Addr -> bool) xs :
      (forall l, In l xs -> q l = true -> p l = true) ->
      List.filter q xs = List.filter q (List.filter p xs).
    Proof.
      induction xs as [|l tl IH]; intro Himp; simpl; [reflexivity|].
      specialize (IH (fun r Hr => Himp r (or_intror Hr))).
      destruct (q l) eqn:Hq, (p l) eqn:Hp; simpl; rewrite ?Hq, ?Hp, IH;
        try reflexivity.
      exfalso. specialize (Himp l (or_introl eq_refl) Hq). congruence.
    Qed.

    Lemma filter_order_membership h chain saved :
      NoDup chain -> List.Forall (fun l => In l chain) saved ->
      List.filter
        (fun l => List.existsb (Nat.eqb l) (live_order h chain)) saved =
      List.filter (live_at h) saved.
    Proof.
      intros Hnodup Hsaved. induction Hsaved as [|l tl Hin Hforall IH];
        simpl; [reflexivity|].
      destruct (live_at h l) eqn:Hlive.
      - assert (Hord : In l (live_order h chain)).
        { apply live_order_spec; auto. }
        assert (Hex : List.existsb (Nat.eqb l) (live_order h chain) = true).
        { apply existsb_exists. exists l. split; [exact Hord|apply Nat.eqb_refl]. }
        now rewrite Hex, IH.
      - assert (Hord : ~ In l (live_order h chain)).
        { intro Hbad. apply live_order_spec in Hbad; auto.
          destruct Hbad as [_ Hbad]. congruence. }
        assert (Hex : List.existsb (Nat.eqb l) (live_order h chain) = false).
        { apply Bool.not_true_iff_false. intro Hexists. apply Hord.
          apply existsb_exists in Hexists as [r [Hrin Heq]].
          apply Nat.eqb_eq in Heq. now subst r. }
        now rewrite Hex, IH.
    Qed.

    Lemma remove_nat_not_in l xs :
      ~ In l xs -> List.remove Nat.eq_dec l xs = xs.
    Proof.
      induction xs as [|q tl IH]; simpl; intro Hnot; [reflexivity|].
      destruct (Nat.eq_dec l q) as [Heq|Hneq].
      - subst q. exfalso. apply Hnot. now left.
      - f_equal. apply IH. intro Hin. apply Hnot. now right.
    Qed.

    Lemma existsb_nat_eq l xs :
      List.existsb (Nat.eqb l) xs = true <-> In l xs.
    Proof.
      rewrite existsb_exists. split.
      - intros [q [Hin Heq]]. apply Nat.eqb_eq in Heq. subst; exact Hin.
      - intros Hin. exists l. split; [exact Hin|apply Nat.eqb_refl].
    Qed.

    Lemma existsb_nat_neq l xs :
      List.existsb (Nat.eqb l) xs = false <-> ~ In l xs.
    Proof.
      rewrite <- Bool.not_true_iff_false, existsb_nat_eq. tauto.
    Qed.

    Lemma abstract_nodes_in h xs l :
      In l xs -> abstract_nodes h xs l =
        match h l with
        | Some n => Some (node_projection n)
        | None => None
        end.
    Proof.
      intro Hin. unfold abstract_nodes.
      apply existsb_nat_eq in Hin. now rewrite Hin.
    Qed.

    Lemma abstract_nodes_notin h xs l :
      ~ In l xs -> abstract_nodes h xs l = None.
    Proof.
      intro Hnot. unfold abstract_nodes.
      apply existsb_nat_neq in Hnot. now rewrite Hnot.
    Qed.

    Lemma abstract_nodes_some_in h xs l a :
      abstract_nodes h xs l = Some a -> In l xs.
    Proof.
      unfold abstract_nodes.
      destruct (List.existsb (Nat.eqb l) xs) eqn:Hex; [|discriminate].
      intros _. apply existsb_nat_eq. exact Hex.
    Qed.

    Lemma abstract_nodes_update_existing h xs l n :
      In l xs ->
      abstract_nodes (heap_update l n h) xs =
        heap_update l (node_projection n) (abstract_nodes h xs).
    Proof.
      intro Hin. apply functional_extensionality. intro q.
      unfold abstract_nodes, heap_update.
      destruct (Nat.eqb l q) eqn:Elq.
      - apply Nat.eqb_eq in Elq. subst q.
        assert (Hex : List.existsb (Nat.eqb l) xs = true).
        { apply existsb_exists. exists l. split; auto using Nat.eqb_refl. }
        now rewrite Hex.
      - destruct (List.existsb (Nat.eqb q) xs); reflexivity.
    Qed.

    Lemma abstract_nodes_update_same_proj h xs l n n' :
      h l = Some n -> node_projection n' = node_projection n ->
      abstract_nodes (heap_update l n' h) xs = abstract_nodes h xs.
    Proof.
      intros Hl Hproj. apply functional_extensionality. intro q.
      unfold abstract_nodes.
      destruct (List.existsb (Nat.eqb q) xs); [|reflexivity].
      destruct (Nat.eq_dec l q) as [<-|Hneq].
      - rewrite HeapUpdateSelf, Hl, Hproj. reflexivity.
      - rewrite HeapUpdateOther by exact Hneq. reflexivity.
    Qed.

    Lemma abstract_nodes_update_fresh h xs l n :
      ~ In l xs ->
      abstract_nodes (heap_update l n h) xs = abstract_nodes h xs.
    Proof.
      intro Hnot. apply functional_extensionality. intro q.
      unfold abstract_nodes.
      destruct (List.existsb (Nat.eqb q) xs) eqn:Hex; [|reflexivity].
      apply existsb_nat_eq in Hex.
      rewrite HeapUpdateOther; [reflexivity|]. intro Heq. subst q. contradiction.
    Qed.

    Lemma abstract_nodes_cons h xs l n :
      h l = Some n ->
      abstract_nodes h (l :: xs) =
        heap_update l (node_projection n) (abstract_nodes h xs).
    Proof.
      intro Hl. apply functional_extensionality. intro q.
      unfold abstract_nodes, heap_update. simpl.
      destruct (Nat.eqb q l) eqn:Eql.
      - apply Nat.eqb_eq in Eql. subst q. rewrite Nat.eqb_refl. simpl.
        rewrite Hl. reflexivity.
      - assert (Elq : Nat.eqb l q = false).
        { apply Nat.eqb_neq. apply Nat.eqb_neq in Eql. congruence. }
        rewrite Elq. reflexivity.
    Qed.

    Lemma live_order_update_same_taken h xs l v old_ts taken next new_ts :
      NoDup xs -> In l xs ->
      h l = Some (pair (pair (pair v old_ts) taken) next) ->
      live_order
        (heap_update l (pair (pair (pair v new_ts) taken) next) h) xs =
      live_order h xs.
    Proof.
      intros Hnodup Hin Hlookup.
      apply live_order_ext. intros q Hq.
      destruct (Nat.eq_dec l q) as [<-|Hneq].
      - unfold live_at, node_live. rewrite HeapUpdateSelf, Hlookup. reflexivity.
      - apply live_at_update_other. exact Hneq.
    Qed.

    Lemma live_order_update_next h xs l v ts taken old new :
      h l = Some (pair (pair (pair v ts) taken) old) ->
      live_order
        (heap_update l (pair (pair (pair v ts) taken) new) h) xs =
      live_order h xs.
    Proof.
      intros Hlookup.
      apply live_order_ext. intros q Hq.
      destruct (Nat.eq_dec l q) as [<-|Hneq].
      - unfold live_at, node_live. rewrite HeapUpdateSelf, Hlookup. reflexivity.
      - apply live_at_update_other. exact Hneq.
    Qed.

    Lemma live_order_take_succ h xs l v ts next :
      NoDup xs -> In l xs ->
      h l = Some (pair (pair (pair v ts) false) next) ->
      live_order
        (heap_update l (pair (pair (pair v ts) true) next) h) xs =
      List.remove Nat.eq_dec l (live_order h xs).
    Proof.
      intros Hnodup Hin Hlookup.
      induction xs as [|hd tl IH]; [contradiction|].
      inversion Hnodup as [|? ? Hfresh Hnodup']; subst.
      simpl in Hin. destruct Hin as [Heq|Hin].
      - subst hd. simpl. unfold live_at, node_live.
        rewrite HeapUpdateSelf, Hlookup. simpl.
        destruct (Nat.eq_dec l l) as [_|Hbad]; [|contradiction].
        rewrite remove_nat_not_in.
        + apply live_order_ext. intros q Hq.
          apply live_at_update_other. intro Heq. subst q. contradiction.
        + intro Hbad. apply Hfresh. eapply live_order_in; exact Hbad.
      - assert (Hneq : l <> hd) by congruence.
        simpl. rewrite live_at_update_other by exact Hneq.
        specialize (IH Hnodup' Hin).
        destruct (live_at h hd) eqn:Hlive; simpl.
        + destruct (Nat.eq_dec l hd); [contradiction|]. now rewrite IH.
        + exact IH.
    Qed.

    Lemma abstract_nodes_take_same h xs l v ts taken next :
      In l xs ->
      h l = Some (pair (pair (pair v ts) taken) next) ->
      abstract_nodes
        (heap_update l (pair (pair (pair v ts) true) next) h) xs =
      abstract_nodes h xs.
    Proof.
      intros Hin Hlookup.
      eapply abstract_nodes_update_same_proj; [exact Hlookup|reflexivity].
    Qed.

    Lemma live_order_prepend_fresh h xs l v ts top :
      ~ In l xs -> h l = None ->
      live_order
        (heap_update l (pair (pair (pair v ts) false) top) h)
        (l :: xs) = l :: live_order h xs.
    Proof.
      intros Hnotin Hfresh. simpl. unfold live_at, node_live.
      rewrite HeapUpdateSelf. simpl. f_equal.
      apply live_order_ext. intros q Hin.
      apply live_at_update_other. intro Heq. subst q. contradiction.
    Qed.

    Lemma heap_update_same {V} (h : @Heap V) l v :
      h l = Some v -> heap_update l v h = h.
    Proof.
      intro Hlookup. apply functional_extensionality. intro q.
      destruct (Nat.eq_dec l q) as [->|Hneq].
      - now rewrite HeapUpdateSelf.
      - now rewrite HeapUpdateOther.
    Qed.

    (** * The representation *)

    Definition represents
        (h : @Heap (@Node A)) (top : Ptr) (count : nat)
        (s : @SPListState A) (log : list Addr) : Prop :=
      valid h top log /\
      counter s = count /\
      length log = count /\
      nodes s = abstract_nodes h log /\
      order s = live_order h log.

    Lemma represents_defined h top count s log l :
      represents h top count s log -> In l log -> h l <> None.
    Proof.
      intros (Hvalid & _) Hin. eapply links_ok_defined; [exact (proj2 (proj2 Hvalid))|exact Hin].
    Qed.

    Lemma represents_abstract_in h top count s log l :
      represents h top count s log -> In l log ->
      exists n, h l = Some n /\ nodes s l = Some (node_projection n).
    Proof.
      intros Hrep Hin. pose proof (represents_defined _ _ _ _ _ _ Hrep Hin) as Hdef.
      destruct Hrep as (_ & _ & _ & Hnodes & _).
      destruct (h l) as [n|] eqn:Hl; [|congruence].
      exists n. split; [reflexivity|]. rewrite Hnodes, abstract_nodes_in by exact Hin.
      rewrite Hl. reflexivity.
    Qed.

    Lemma represents_defined_in h top count s log l :
      represents h top count s log -> nodes s l <> None -> In l log.
    Proof.
      intros (_ & _ & _ & Hnodes & _) Hdef. rewrite Hnodes in Hdef.
      destruct (abstract_nodes h log l) as [a|] eqn:Ha; [|congruence].
      eapply abstract_nodes_some_in; exact Ha.
    Qed.

    Lemma represents_undefined_notin h top count s log l :
      represents h top count s log -> nodes s l = None -> ~ In l log.
    Proof.
      intros Hrep Hundef Hin.
      destruct (represents_abstract_in _ _ _ _ _ _ Hrep Hin) as [n [_ Hn]].
      congruence.
    Qed.

    Lemma represents_live_in_order h top count s log l :
      represents h top count s log -> In l log ->
      (In l (order s) <-> live_at h l = true).
    Proof.
      intros Hrep Hin. pose proof Hrep as (Hvalid & _ & _ & _ & Horder).
      rewrite Horder. rewrite live_order_spec by exact (proj1 Hvalid). tauto.
    Qed.

    Lemma represents_setTS h top count s log l v old_ts taken next ts :
      represents h top count s log ->
      In l log ->
      h l = Some (pair (pair (pair v old_ts) taken) next) ->
      represents
        (heap_update l
          (pair (pair (pair v
            (match old_ts with TSTop => ts | _ => old_ts end)) taken) next) h)
        top count (SPListSpec.setTS l ts s) log.
    Proof.
      intros Hrep Hin Hlookup.
      pose proof Hrep as (Hvalid & Hcount & Hlength & Hnodes & Horder).
      assert (Habstract : nodes s l = Some (pair v old_ts)).
      { rewrite Hnodes, abstract_nodes_in by exact Hin. rewrite Hlookup. reflexivity. }
      destruct old_ts as [|lower upper].
      - unfold SPListSpec.setTS. rewrite Habstract.
        split; [eapply valid_evol; [eapply structure_evol_setTS; exact Hlookup|exact Hvalid]|].
        split; [exact Hcount|]. split; [exact Hlength|]. split.
        + simpl. rewrite Hnodes. symmetry. apply abstract_nodes_update_existing. exact Hin.
        + simpl. rewrite Horder. symmetry. eapply live_order_update_same_taken; eauto.
          exact (proj1 Hvalid).
      - unfold SPListSpec.setTS. rewrite Habstract.
        rewrite heap_update_same by exact Hlookup. exact Hrep.
    Qed.

    Lemma represents_tryTake_succ h top count s log l v ts next :
      represents h top count s log ->
      In l log ->
      h l = Some (pair (pair (pair v ts) false) next) ->
      represents
        (heap_update l (pair (pair (pair v ts) true) next) h)
        top count (SPListSpec.remove l s) log.
    Proof.
      intros Hrep Hin Hlookup.
      pose proof Hrep as (Hvalid & Hcount & Hlength & Hnodes & Horder).
      split; [eapply valid_evol; [eapply structure_evol_take; exact Hlookup|exact Hvalid]|].
      split; [exact Hcount|]. split; [exact Hlength|]. split.
      - simpl. rewrite Hnodes. symmetry. eapply abstract_nodes_take_same; eauto.
      - simpl. rewrite Horder. symmetry. eapply live_order_take_succ; eauto.
        exact (proj1 Hvalid).
    Qed.

    Lemma represents_allocate h top count s log l n :
      represents h top count s log -> h l = None ->
      represents (heap_update l n h) top count s log.
    Proof.
      intros Hrep Hfresh.
      pose proof Hrep as (Hvalid & Hcount & Hlength & Hnodes & Horder).
      assert (Hnotin : ~ In l log).
      { intro Hin. eapply represents_defined; eauto. }
      split; [eapply valid_evol; [eapply structure_evol_alloc; exact Hfresh|exact Hvalid]|].
      split; [exact Hcount|]. split; [exact Hlength|]. split.
      - rewrite Hnodes. symmetry. apply abstract_nodes_update_fresh. exact Hnotin.
      - rewrite Horder. apply live_order_ext. intros q Hq. symmetry.
        apply live_at_update_other. intro Heq. subst q. contradiction.
    Qed.

    Lemma represents_publish h top count s log l v p :
      represents h top count s log ->
      nodes s l = None ->
      h l = Some (pair (pair (pair v TSTop) false) p) ->
      skips h log p ->
      represents h (Some l) (S count) (SPListSpec.insert v l s) (l :: log).
    Proof.
      intros Hrep Hundefined Hcell Hskips.
      pose proof Hrep as (Hvalid & Hcount & Hlength & Hnodes & Horder).
      pose proof (represents_undefined_notin _ _ _ _ _ _ Hrep Hundefined) as Hnotin.
      split.
      { split; [constructor; [exact Hnotin|exact (proj1 Hvalid) ]|].
        split; [constructor|].
        simpl. split; [|exact (proj2 (proj2 Hvalid)) ].
        eexists. split; [exact Hcell|]. exact Hskips. }
      split; [simpl; rewrite Hcount, Nat.add_1_r; reflexivity|].
      split; [simpl; now rewrite Hlength|].
      split.
      - simpl. rewrite Hnodes. symmetry. rewrite (abstract_nodes_cons h log l _ Hcell).
        reflexivity.
      - simpl. unfold live_at, node_live. rewrite Hcell. simpl. now rewrite Horder.
    Qed.

    Lemma represents_casNext_succ h top count s log a l b v ts taken old new :
      represents h top count s log ->
      log = a ++ l :: b ->
      h l = Some (pair (pair (pair v ts) taken) old) ->
      skips h b new ->
      represents
        (heap_update l (pair (pair (pair v ts) taken) new) h)
        top count s log.
    Proof.
      intros Hrep Hlog Hcell Hnew.
      pose proof Hrep as (Hvalid & Hcount & Hlength & Hnodes & Horder).
      destruct Hvalid as (Hnd & Hsk & Hlk).
      split.
      { split; [exact Hnd|]. split.
        - eapply skips_update_next; [exact Hcell|exact Hsk].
        - rewrite Hlog in Hnd, Hlk |- *.
          eapply links_ok_update_next; eauto. }
      split; [exact Hcount|]. split; [exact Hlength|]. split.
      - rewrite Hnodes. symmetry.
        eapply abstract_nodes_update_same_proj; [exact Hcell|reflexivity].
      - rewrite Horder. symmetry. eapply live_order_update_next; exact Hcell.
    Qed.

    Lemma represents_cas_top h top count s log l :
      represents h top count s log ->
      skips h log (Some l) ->
      represents h (Some l) count s log.
    Proof.
      intros (Hvalid & Hrest) Hsk. split; [|exact Hrest].
      destruct Hvalid as (Hnd & _ & Hlk). split; [exact Hnd|]. split; assumption.
    Qed.

    (** * The invariant *)

    Definition mem_control_ok (mc : mem_control) : Prop :=
      match mc with
      | Pending _ t (nmalloc _ _) => t = owner
      | Pending _ t (nmsetTS _ _) => t = owner
      | _ => True
      end.

    Definition cas_control_ok (cc : cas_control) : Prop :=
      match cc with
      | Pending _ t (set _) => t = owner
      | _ => True
      end.

    Definition snapshot_consistent
        (s : @SPListState A)
        (pi : tmap (@LinState (li_sig F))) : Prop :=
      forall t,
        (exists saved, TMap.find t (snapshot s) = Some saved) <->
        TMap.find t pi = Some (ls_lini (@lgetTop A)).

    Definition abstract_payload (c : abstract_control) : @SPListState A :=
      match c with
      | Ready s => s
      | AtomicPending s _ _ => s
      end.

    Definition ctrl_of (ρ : abstract_state) : abstract_control := fst ρ.
    Definition log_of_ctrl (ρ : abstract_state) : list Addr := snd ρ.

    Definition source_I : assertion :=
      fun w =>
        exists mc cc s log,
          SinglePossState.σ w = pair mc cc /\
          SinglePossState.ρ w = pair (Ready s) log /\
          mem_control_ok mc /\
          cas_control_ok cc /\
          represents (mem_heap mc) (fst (cas_value cc))
            (snd (cas_value cc)) s log /\
          snapshot_consistent s (SinglePossState.π w).

    Definition timestamp_evol (actor : tid) (old new : TS) : Prop :=
      old = new \/ (actor = owner /\ old = TSTop).

    (** Values never change, timestamps are set once by the owner, taken
        flags only flip to true.  Successors are unconstrained here: their
        structure is captured by the invariant on both sides. *)
    Definition node_evol (actor : tid) (old new : @Node A) : Prop :=
      fst (fst (fst old)) = fst (fst (fst new)) /\
      timestamp_evol actor (snd (fst (fst old))) (snd (fst (fst new))) /\
      (snd (fst old) = true -> snd (fst new) = true).

    Definition heap_evol (actor : tid)
        (h h' : @Heap (@Node A)) : Prop :=
      forall l,
        match h l with
        | None => h' l = None \/ actor = owner
        | Some old =>
            exists new, h' l = Some new /\ node_evol actor old new
        end.

    Lemma heap_evol_taken actor h h' :
      heap_evol actor h h' ->
      forall z, taken_at h z = true -> taken_at h' z = true.
    Proof.
      intros Hev z Hz. specialize (Hev z). unfold taken_at in *.
      destruct (h z) as [n|]; [|discriminate].
      destruct Hev as [n' [Hn' [_ [_ Htk]]]]. rewrite Hn'. apply Htk. exact Hz.
    Qed.

    Lemma heap_evol_live_imp actor h h' l :
      heap_evol actor h h' -> h l <> None ->
      live_at h' l = true -> live_at h l = true.
    Proof.
      intros Hev Hdef Hlive. specialize (Hev l).
      unfold live_at, node_live in *.
      destruct (h l) as [n|]; [|congruence].
      destruct Hev as [n' [Hn' [_ [_ Htk]]]]. rewrite Hn' in Hlive.
      destruct (snd (fst n)) eqn:Htaken; [|reflexivity].
      rewrite Htk in Hlive by reflexivity. discriminate.
    Qed.

    Lemma heap_evol_dead_imp actor h h' l :
      heap_evol actor h h' -> h l <> None ->
      live_at h l = false -> live_at h' l = false.
    Proof.
      intros Hev Hdef Hdead.
      destruct (live_at h' l) eqn:Hl'; [|reflexivity].
      rewrite (heap_evol_live_imp _ _ _ _ Hev Hdef Hl') in Hdead. discriminate.
    Qed.

    Lemma heap_evol_defined actor h h' l :
      heap_evol actor h h' -> h l <> None -> h' l <> None.
    Proof.
      intros Hev Hdef. specialize (Hev l). destruct (h l); [|congruence].
      destruct Hev as [n' [Hn' _]]. congruence.
    Qed.

    Lemma heap_evol_value actor h h' l v ts taken next :
      heap_evol actor h h' ->
      h l = Some (pair (pair (pair v ts) taken) next) ->
      exists ts' taken' next',
        h' l = Some (pair (pair (pair v ts') taken') next').
    Proof.
      intros Hev Hl. specialize (Hev l). rewrite Hl in Hev.
      destruct Hev as [[[[v' ts'] taken'] next'] [Hn' [Hv _]]]. simpl in Hv.
      subst v'. eauto.
    Qed.

    Lemma heap_evol_refl actor h : heap_evol actor h h.
    Proof.
      intros l. destruct (h l) as [n|] eqn:Hlookup.
      - exists n. split; [reflexivity|].
        unfold node_evol, timestamp_evol. repeat split; auto.
      - now left.
    Qed.

    Lemma heap_evol_setTS h l v old_ts taken next ts :
      h l = Some (pair (pair (pair v old_ts) taken) next) ->
      heap_evol owner h
        (heap_update l
          (pair (pair (pair v
            (match old_ts with TSTop => ts | _ => old_ts end)) taken) next) h).
    Proof.
      intros Hlookup q. destruct (Nat.eq_dec l q) as [->|Hneq].
      - rewrite Hlookup, HeapUpdateSelf. eexists. split; [reflexivity|].
        unfold node_evol, timestamp_evol. simpl. repeat split; auto.
        destruct old_ts; auto.
      - rewrite HeapUpdateOther by exact Hneq.
        destruct (h q) as [n|] eqn:Hq.
        + exists n. split; [reflexivity|].
          unfold node_evol, timestamp_evol. repeat split; auto.
        + now left.
    Qed.

    Lemma heap_evol_tryTake actor h l v ts next :
      h l = Some (pair (pair (pair v ts) false) next) ->
      heap_evol actor h
        (heap_update l (pair (pair (pair v ts) true) next) h).
    Proof.
      intros Hlookup q. destruct (Nat.eq_dec l q) as [Heq|Hneq].
      - subst q. rewrite Hlookup, HeapUpdateSelf. eexists. split; [reflexivity|].
        unfold node_evol, timestamp_evol. simpl. repeat split; auto.
      - rewrite HeapUpdateOther by exact Hneq.
        destruct (h q) as [n|] eqn:Hq.
        + exists n. split; [reflexivity|].
          unfold node_evol, timestamp_evol. repeat split; auto.
        + now left.
    Qed.

    Lemma heap_evol_casNext actor h l v ts taken old new :
      h l = Some (pair (pair (pair v ts) taken) old) ->
      heap_evol actor h
        (heap_update l (pair (pair (pair v ts) taken) new) h).
    Proof.
      intros Hlookup q. destruct (Nat.eq_dec l q) as [Heq|Hneq].
      - subst q. rewrite Hlookup, HeapUpdateSelf. eexists. split; [reflexivity|].
        unfold node_evol, timestamp_evol. simpl. repeat split; auto.
      - rewrite HeapUpdateOther by exact Hneq.
        destruct (h q) as [n|] eqn:Hq.
        + exists n. split; [reflexivity|].
          unfold node_evol, timestamp_evol. repeat split; auto.
        + now left.
    Qed.

    Lemma heap_evol_allocate h l n :
      h l = None ->
      heap_evol owner h (heap_update l n h).
    Proof.
      intros Hfresh q. destruct (Nat.eq_dec l q) as [Heq|Hneq].
      - subst q. rewrite Hfresh. right. reflexivity.
      - rewrite HeapUpdateOther by exact Hneq.
        destruct (h q) as [m|] eqn:Hq.
        + exists m. split; [reflexivity|].
          unfold node_evol, timestamp_evol. repeat split; auto.
        + now left.
    Qed.

    (** Other threads never change the insertion counter, and the log
        only grows at its front, by the owner. *)
    Definition cas_evol (actor : tid)
        (q : Ptr * nat) (ρ : abstract_state)
        (q' : Ptr * nat) (ρ' : abstract_state) : Prop :=
      (actor <> owner -> snd q' = snd q) /\
      exists extra,
        log_of_ctrl ρ' = extra ++ log_of_ctrl ρ /\
        (actor <> owner -> extra = nil).

    Definition source_G (actor : tid) : rg_relation :=
      fun w w' =>
        source_I w /\ source_I w' /\
        heap_evol actor
          (mem_heap (fst (SinglePossState.σ w)))
          (mem_heap (fst (SinglePossState.σ w'))) /\
        (forall l, actor <> owner ->
          nodes (abstract_payload (ctrl_of (SinglePossState.ρ w))) l = None ->
          mem_heap (fst (SinglePossState.σ w)) l =
          mem_heap (fst (SinglePossState.σ w')) l) /\
        cas_evol actor
          (cas_value (snd (SinglePossState.σ w))) (SinglePossState.ρ w)
          (cas_value (snd (SinglePossState.σ w'))) (SinglePossState.ρ w') /\
        (forall q, q <> actor ->
          TMap.find q
            (snapshot (abstract_payload (ctrl_of (SinglePossState.ρ w)))) =
          TMap.find q
            (snapshot (abstract_payload (ctrl_of (SinglePossState.ρ w'))))) /\
        (forall q, q <> actor ->
          TMap.find q (SinglePossState.π w) =
          TMap.find q (SinglePossState.π w')).

    Definition source_R (observer : tid) : rg_relation :=
      AssertionsSingle.GuaranteeGeneratedRely source_G observer.

    Definition token_eq (observer : tid) : rg_relation :=
      fun w w' =>
        TMap.find observer (SinglePossState.π w) =
        TMap.find observer (SinglePossState.π w').

    Definition payload_of (w : single_state) : @SPListState A :=
      abstract_payload (ctrl_of (SinglePossState.ρ w)).
    Definition log_of (w : single_state) : list Addr :=
      log_of_ctrl (SinglePossState.ρ w).
    Definition heap_of (w : single_state) : @Heap (@Node A) :=
      mem_heap (fst (SinglePossState.σ w)).
    Definition reg_of (w : single_state) : Ptr * nat :=
      cas_value (snd (SinglePossState.σ w)).

    Definition NodeDefined (l : Addr) : assertion :=
      fun w => exists a, nodes (payload_of w) l = Some a.

    Definition NodeUndefined (l : Addr) : assertion :=
      fun w => nodes (payload_of w) l = None.

    Definition CountIs (count : nat) : assertion :=
      fun w => snd (reg_of w) = count.

    Lemma source_I_rep w :
      source_I w ->
      represents (heap_of w) (fst (reg_of w)) (snd (reg_of w))
        (payload_of w) (log_of w).
    Proof.
      intros (mc & cc & s & log & Eσ & Eρ & _ & _ & Hrep & _).
      unfold heap_of, reg_of, payload_of, log_of, ctrl_of, log_of_ctrl.
      rewrite Eσ, Eρ. exact Hrep.
    Qed.

    Lemma source_I_ready w :
      source_I w ->
      SinglePossState.ρ w = pair (Ready (payload_of w)) (log_of w).
    Proof.
      intros (mc & cc & s & log & Eσ & Eρ & _).
      unfold payload_of, log_of, ctrl_of, log_of_ctrl. rewrite Eρ. reflexivity.
    Qed.

    Lemma source_G_log actor w w' :
      source_G actor w w' ->
      exists extra, log_of w' = extra ++ log_of w /\ (actor <> owner -> extra = nil).
    Proof.
      intros (_ & _ & _ & _ & [_ Hlog] & _). exact Hlog.
    Qed.

    Lemma source_G_heap actor w w' :
      source_G actor w w' -> heap_evol actor (heap_of w) (heap_of w').
    Proof. intros (_ & _ & Hheap & _). exact Hheap. Qed.

    Lemma source_G_preserves_defined actor w w' l :
      source_G actor w w' -> NodeDefined l w -> NodeDefined l w'.
    Proof.
      intros HG [a Hdefined].
      pose proof HG as (HI & HI' & Hheap & _).
      pose proof (source_I_rep _ HI) as Hrep.
      pose proof (source_I_rep _ HI') as Hrep'.
      destruct (source_G_log _ _ _ HG) as [extra [Hlog _]].
      assert (Hin : In l (log_of w)).
      { eapply represents_defined_in; [exact Hrep|congruence]. }
      assert (Hin' : In l (log_of w')).
      { rewrite Hlog. apply in_or_app. right. exact Hin. }
      destruct (represents_abstract_in _ _ _ _ _ _ Hrep' Hin') as [n [_ Hn]].
      exists (node_projection n). exact Hn.
    Qed.

    Lemma source_G_preserves_undefined_nonowner actor w w' l :
      actor <> owner -> source_G actor w w' ->
      NodeUndefined l w -> NodeUndefined l w'.
    Proof.
      intros Hactor HG Hundefined.
      pose proof HG as (HI & HI' & _).
      pose proof (source_I_rep _ HI) as Hrep.
      pose proof (source_I_rep _ HI') as Hrep'.
      destruct (source_G_log _ _ _ HG) as [extra [Hlog Hnil]].
      rewrite (Hnil Hactor) in Hlog. simpl in Hlog.
      pose proof (represents_undefined_notin _ _ _ _ _ _ Hrep Hundefined) as Hnotin.
      unfold NodeUndefined.
      destruct (nodes (payload_of w') l) as [a|] eqn:Hl; [|reflexivity].
      exfalso. apply Hnotin. rewrite <- Hlog.
      eapply represents_defined_in; [exact Hrep'|congruence].
    Qed.

    Lemma source_G_count_nonowner actor w w' :
      actor <> owner -> source_G actor w w' ->
      snd (reg_of w) = snd (reg_of w').
    Proof.
      intros Hactor (_ & _ & _ & _ & [Hcount _] & _).
      symmetry. apply Hcount. exact Hactor.
    Qed.

    Lemma source_R_owner_preserves_count w w' :
      source_R owner w w' -> snd (reg_of w) = snd (reg_of w').
    Proof.
      intros [[actor [Hneq HG]]|Hadmin].
      - eapply source_G_count_nonowner; eauto.
      - pose proof
          (AssertionsSingle.linearization_rely_observer_view owner _ _ Hadmin)
          as [Hσ [Hρ Htoken]].
        unfold reg_of. now rewrite Hσ.
    Qed.

    Lemma source_R_owner_preserves_log w w' :
      source_R owner w w' -> log_of w' = log_of w.
    Proof.
      intros [[actor [Hneq HG]]|Hadmin].
      - destruct (source_G_log _ _ _ HG) as [extra [Hlog Hnil]].
        rewrite (Hnil Hneq) in Hlog. exact Hlog.
      - pose proof
          (AssertionsSingle.linearization_rely_observer_view owner _ _ Hadmin)
          as [Hσ [Hρ Htoken]].
        unfold log_of, log_of_ctrl. now rewrite Hρ.
    Qed.

    Lemma source_R_owner_preserves_undefined w w' l :
      source_R owner w w' -> NodeUndefined l w -> NodeUndefined l w'.
    Proof.
      intros [[actor [Hneq HG]]|Hadmin] Hundefined.
      - eapply source_G_preserves_undefined_nonowner; eauto.
      - pose proof
          (AssertionsSingle.linearization_rely_observer_view owner _ _ Hadmin)
          as [Hσ [Hρ Htoken]].
        unfold NodeUndefined, payload_of, ctrl_of in *. now rewrite <- Hρ.
    Qed.

    Lemma source_R_owner_preserves_private w w' l :
      source_R owner w w' -> NodeUndefined l w ->
      heap_of w l = heap_of w' l.
    Proof.
      intros [[actor [Hneq HG]]|Hadmin] Hundefined.
      - destruct HG as
          [HI [HI' [Hheap [Hprivate [Hcas [Hsnap Htokens]]]]]].
        apply Hprivate; [exact Hneq|exact Hundefined].
      - pose proof
          (AssertionsSingle.linearization_rely_observer_view owner _ _ Hadmin)
          as [Hσ [Hρ Htoken]].
        unfold heap_of. now rewrite Hσ.
    Qed.

    Lemma source_I_defined_lookup w l :
      source_I w -> NodeDefined l w ->
      exists v ts taken next,
        heap_of w l = Some (pair (pair (pair v ts) taken) next).
    Proof.
      intros HI [a Hdefined].
      pose proof (source_I_rep _ HI) as Hrep.
      assert (Hin : In l (log_of w)).
      { eapply represents_defined_in; [exact Hrep|congruence]. }
      destruct (represents_abstract_in _ _ _ _ _ _ Hrep Hin)
        as [[[[v ts] taken] next] [Hn _]].
      eauto.
    Qed.

    Lemma source_I_defined_in_log w l :
      source_I w -> NodeDefined l w -> In l (log_of w).
    Proof.
      intros HI [a Hdefined].
      eapply represents_defined_in; [eapply source_I_rep; exact HI|congruence].
    Qed.

    Lemma source_I_in_log_defined w l :
      source_I w -> In l (log_of w) -> NodeDefined l w.
    Proof.
      intros HI Hin.
      destruct (represents_abstract_in _ _ _ _ _ _ (source_I_rep _ HI) Hin)
        as [n [_ Hn]].
      exists (node_projection n). exact Hn.
    Qed.

    Lemma source_G_token_other actor observer :
      actor <> observer ->
      (source_G actor ⊆ token_eq observer)%RGRelation.
    Proof.
      intros Hneq w w' [_ [_ [_ [_ [_ [_ Htokens]]]]]].
      apply Htokens. congruence.
    Qed.

    Lemma observer_view_token observer :
      (AssertionsSingle.ObserverViewEq observer ⊆
        token_eq observer)%RGRelation.
    Proof. intros w w' [_ [_ Htoken]]. exact Htoken. Qed.

    Lemma source_R_token observer :
      (source_R observer ⊆ token_eq observer)%RGRelation.
    Proof.
      eapply AssertionsSingle.guarantee_generated_rely_facts.
      - intros actor Hneq. apply source_G_token_other; exact Hneq.
      - apply observer_view_token.
    Qed.

    Definition defined_facts (l : Addr) : rg_relation :=
      fun w w' => NodeDefined l w -> NodeDefined l w'.

    Lemma observer_view_defined l observer :
      (AssertionsSingle.ObserverViewEq observer ⊆
        defined_facts l)%RGRelation.
    Proof.
      intros w w' [Hsigma [Hrho Htoken]] Hdefined.
      unfold NodeDefined, payload_of, ctrl_of in *. rewrite <- Hrho. exact Hdefined.
    Qed.

    Lemma source_R_preserves_defined observer l :
      (source_R observer ⊆ defined_facts l)%RGRelation.
    Proof.
      intros w w' HR Hdefined.
      destruct HR as [[actor [Hneq HG]]|Hadmin].
      - eapply source_G_preserves_defined; eauto.
      - eapply observer_view_defined; [|exact Hdefined].
        eapply AssertionsSingle.linearization_rely_observer_view.
        exact Hadmin.
    Qed.

    (** Facts that only mention the heap and the log, and survive the rely
        because taken flags are monotone and the log grows at the front. *)
    Lemma source_R_heap observer w w' :
      source_R observer w w' ->
      exists actor, heap_evol actor (heap_of w) (heap_of w').
    Proof.
      intros [[actor [Hneq HG]]|Hadmin].
      - exists actor. eapply source_G_heap; exact HG.
      - exists observer.
        pose proof
          (AssertionsSingle.linearization_rely_observer_view observer _ _ Hadmin)
          as [Hσ [Hρ Htoken]].
        unfold heap_of. rewrite Hσ. apply heap_evol_refl.
    Qed.

    Lemma source_R_log observer w w' :
      source_R observer w w' ->
      exists extra, log_of w' = extra ++ log_of w.
    Proof.
      intros [[actor [Hneq HG]]|Hadmin].
      - destruct (source_G_log _ _ _ HG) as [extra [Hlog _]]. exists extra. exact Hlog.
      - exists nil.
        pose proof
          (AssertionsSingle.linearization_rely_observer_view observer _ _ Hadmin)
          as [Hσ [Hρ Htoken]].
        unfold log_of, log_of_ctrl. rewrite Hρ. reflexivity.
    Qed.

    Lemma source_R_taken observer w w' :
      source_R observer w w' ->
      forall z, taken_at (heap_of w) z = true -> taken_at (heap_of w') z = true.
    Proof.
      intros HR. destruct (source_R_heap _ _ _ HR) as [actor Hev].
      eapply heap_evol_taken; exact Hev.
    Qed.

    Lemma source_R_dead observer w w' l :
      source_R observer w w' -> heap_of w l <> None ->
      live_at (heap_of w) l = false -> live_at (heap_of w') l = false.
    Proof.
      intros HR Hdef Hdead. destruct (source_R_heap _ _ _ HR) as [actor Hev].
      eapply heap_evol_dead_imp; eauto.
    Qed.

    Lemma source_R_live_imp observer w w' l :
      source_R observer w w' -> heap_of w l <> None ->
      live_at (heap_of w') l = true -> live_at (heap_of w) l = true.
    Proof.
      intros HR Hdef Hlive. destruct (source_R_heap _ _ _ HR) as [actor Hev].
      eapply heap_evol_live_imp; eauto.
    Qed.

    Lemma source_R_value observer w w' l v ts taken next :
      source_R observer w w' ->
      heap_of w l = Some (pair (pair (pair v ts) taken) next) ->
      exists ts' taken' next',
        heap_of w' l = Some (pair (pair (pair v ts') taken') next').
    Proof.
      intros HR Hl. destruct (source_R_heap _ _ _ HR) as [actor Hev].
      eapply heap_evol_value; eauto.
    Qed.

    Lemma source_valid_rg observer w w' :
      source_R observer w w' -> source_I w' ->
      TMap.find observer (SinglePossState.π w) = None <->
      TMap.find observer (SinglePossState.π w') = None.
    Proof.
      intros HR _. pose proof (source_R_token observer _ _ HR) as Heq.
      rewrite Heq. tauto.
    Qed.

    Lemma source_parallel_compatible actor observer :
      actor <> observer -> forall w w',
      (source_G actor w w' \/
       (AssertionsSingle.GINV actor w w' \/
        AssertionsSingle.GRET actor w w') \/
       AssertionsSingle.A.GId w w') ->
      source_R observer w w'.
    Proof.
      intros Hneq. eapply AssertionsSingle.guarantee_generated_parallel_compatible.
      exact Hneq.
    Qed.

    Lemma cas_evol_refl actor q ρ : cas_evol actor q ρ q ρ.
    Proof.
      split; [reflexivity|]. exists nil. split; reflexivity.
    Qed.

    Lemma source_G_refl actor w :
      source_I w -> source_G actor w w.
    Proof.
      intro HI. repeat split; auto using heap_evol_refl.
      exists nil. split; reflexivity.
    Qed.

    Lemma source_G_same_payload actor w w' :
      source_I w -> source_I w' ->
      heap_of w = heap_of w' ->
      reg_of w = reg_of w' ->
      log_of w = log_of w' ->
      snapshot (payload_of w) = snapshot (payload_of w') ->
      (forall q, q <> actor ->
        TMap.find q (SinglePossState.π w) =
        TMap.find q (SinglePossState.π w')) ->
      source_G actor w w'.
    Proof.
      intros HI HI' Hheap Hcas Hlog Hsnapshot Htokens.
      unfold heap_of, reg_of, log_of, payload_of in *.
      repeat split; auto.
      - rewrite <- Hheap. apply heap_evol_refl.
      - intros l Hactor Hundefined. now rewrite Hheap.
      - intros _. rewrite Hcas. reflexivity.
      - exists nil. split; [|reflexivity]. rewrite Hlog. reflexivity.
      - intros q Hq. rewrite <- Hsnapshot. reflexivity.
    Qed.

    Lemma source_I_change_controls w mc' cc' :
      source_I w ->
      mem_heap mc' = mem_heap (fst (SinglePossState.σ w)) ->
      cas_value cc' = cas_value (snd (SinglePossState.σ w)) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair mc' cc') (SinglePossState.ρ w) (SinglePossState.π w)).
    Proof.
      intros HI Hheap Hcas Hmc' Hcc'.
      destruct HI as
        (mc & cc & s & log & Hsigma & Hrho & Hmc & Hcc & Hrep & Hsnap).
      exists mc', cc', s, log. simpl. split; [reflexivity|].
      split; [exact Hrho|].
      split; [exact Hmc'|].
      split; [exact Hcc'|].
      split.
      - rewrite Hheap, Hcas, Hsigma. exact Hrep.
      - exact Hsnap.
    Qed.

    Lemma source_I_mem_control w :
      source_I w -> mem_control_ok (fst (SinglePossState.σ w)).
    Proof.
      intros (mc & cc & s & log & Hsigma & Hrho & Hmc & Hcc & Hrep & Hsnap).
      rewrite Hsigma. exact Hmc.
    Qed.

    Lemma source_I_cas_control w :
      source_I w -> cas_control_ok (snd (SinglePossState.σ w)).
    Proof.
      intros (mc & cc & s & log & Hsigma & Hrho & Hmc & Hcc & Hrep & Hsnap).
      rewrite Hsigma. exact Hcc.
    Qed.
    (** ** Slot-local replay of abstract steps

        Possibilities in a set differ only in per-thread "slots": a thread's
        snapshot entry and its linearization-map entry.  Abstract steps of
        a thread never inspect another thread's slot, so a sequence of
        steps can be replayed on a possibility that differs only in some
        other thread's slot. *)

    Definition payload_agree (q : tid) (s s' : @SPListState A) : Prop :=
      counter s = counter s' /\ nodes s = nodes s' /\ order s = order s' /\
      (forall r, r <> q ->
        TMap.find r (snapshot s) = TMap.find r (snapshot s')).

    Definition control_agree_ctrl (q : tid) (c c' : abstract_control) : Prop :=
      match c, c' with
      | Ready s, Ready s' => payload_agree q s s'
      | AtomicPending s t op, AtomicPending s' t' op' =>
          t = t' /\ op = op' /\ payload_agree q s s'
      | _, _ => False
      end.

    (** Agreement of ghost states: the controls agree off [q] and the logs
        are equal. *)
    Definition control_agree (q : tid) (c c' : abstract_state) : Prop :=
      control_agree_ctrl q (fst c) (fst c') /\ snd c = snd c'.

    Lemma payload_agree_refl q s : payload_agree q s s.
    Proof. repeat split; auto. Qed.

    Lemma payload_agree_sym q s s' :
      payload_agree q s s' -> payload_agree q s' s.
    Proof.
      intros (Hc & Hn & Ho & Hs). repeat split; auto.
      intros r Hr. symmetry. auto.
    Qed.

    Lemma actual_snapshot_agree q t s s' :
      t <> q -> payload_agree q s s' ->
      actual_snapshot t s = actual_snapshot t s'.
    Proof.
      intros Hneq (Hc & Hn & Ho & Hs).
      unfold actual_snapshot. rewrite (Hs t Hneq), Ho. reflexivity.
    Qed.

    Lemma payload_agree_start q t s s' :
      t <> q -> payload_agree q s s' ->
      payload_agree q (start_snapshot t s) (start_snapshot t s').
    Proof.
      intros Hneq (Hc & Hn & Ho & Hs).
      repeat split; simpl; auto.
      intros r Hr. destruct (PositiveMap.E.eq_dec r t) as [->|Hrt].
      - rewrite !TMap.gss, Ho, Hc. reflexivity.
      - rewrite !TMap.gso by exact Hrt. auto.
    Qed.

    Lemma payload_agree_clear q t s s' :
      payload_agree q s s' ->
      payload_agree q (clear_snapshot t s) (clear_snapshot t s').
    Proof.
      intros (Hc & Hn & Ho & Hs).
      repeat split; simpl; auto.
      intros r Hr. destruct (PositiveMap.E.eq_dec r t) as [->|Hrt].
      - rewrite !TMap.grs. reflexivity.
      - rewrite !TMap.gro by exact Hrt. auto.
    Qed.

    Lemma payload_agree_insert q v l s s' :
      payload_agree q s s' ->
      payload_agree q (insert v l s) (insert v l s').
    Proof.
      intros (Hc & Hn & Ho & Hs).
      repeat split; simpl; auto; congruence.
    Qed.

    Lemma payload_agree_setTS q l ts s s' :
      payload_agree q s s' ->
      payload_agree q (setTS l ts s) (setTS l ts s').
    Proof.
      intros Hagree. pose proof Hagree as (Hc & Hn & Ho & Hs).
      unfold setTS. rewrite <- Hn.
      destruct (nodes s l) as [[v [|lo hi]]|]; auto.
      repeat split; simpl; auto; congruence.
    Qed.

    Lemma payload_agree_remove q l s s' :
      payload_agree q s s' ->
      payload_agree q (remove l s) (remove l s').
    Proof.
      intros (Hc & Hn & Ho & Hs).
      repeat split; simpl; auto; congruence.
    Qed.

    Definition control_snapshot_ctrl (q : tid) (c : abstract_control) :=
      TMap.find q (snapshot (abstract_payload c)).

    Definition control_snapshot (q : tid) (c : abstract_state) :=
      TMap.find q (snapshot (abstract_payload (fst c))).

    Lemma step_replay_ctrl q ev c1 c2 c1' :
      te_tid ev <> q ->
      @StepSPList A owner ev c1 c2 ->
      control_agree_ctrl q c1 c1' ->
      exists c2',
        @StepSPList A owner ev c1' c2' /\ control_agree_ctrl q c2 c2' /\
        control_snapshot_ctrl q c2' = control_snapshot_ctrl q c1'.
    Proof.
      intros Hneq Hstep Hagree.
      inversion Hstep; subst; simpl in Hneq;
        destruct c1' as [s' | s' t' op']; simpl in Hagree; try contradiction;
        try (destruct Hagree as (<- & <- & Hagree));
        pose proof Hagree as (Hc & Hn & Ho & Hs).
      - (* getTop inv *)
        eexists. split; [|split].
        + constructor. rewrite <- (Hs _ Hneq). assumption.
        + apply payload_agree_start; auto.
        + unfold control_snapshot_ctrl. simpl.
          rewrite TMap.gso by congruence. reflexivity.
      - (* getTop nonEmpty *)
        eexists. split; [|split].
        + eapply step_getTop_nonEmpty.
          * rewrite <- (actual_snapshot_agree q _ s s' Hneq Hagree).
            eassumption.
          * rewrite <- Hn. eassumption.
        + apply payload_agree_clear; auto.
        + unfold control_snapshot_ctrl. simpl.
          rewrite TMap.gro by congruence. reflexivity.
      - (* getTop empty *)
        eexists. split; [|split].
        + eapply step_getTop_empty.
          rewrite <- (actual_snapshot_agree q _ s s' Hneq Hagree).
          eassumption.
        + apply payload_agree_clear; auto.
        + unfold control_snapshot_ctrl. simpl.
          rewrite TMap.gro by congruence. reflexivity.
      - (* linsert inv *)
        eexists. split; [|split].
        + constructor; auto.
        + simpl. repeat split; auto.
        + reflexivity.
      - (* linsert res *)
        eexists. split; [|split].
        + constructor. rewrite <- Hn. assumption.
        + apply payload_agree_insert; auto.
        + reflexivity.
      - (* setTS inv *)
        eexists. split; [|split].
        + constructor; auto.
        + simpl. repeat split; auto.
        + reflexivity.
      - (* setTS res *)
        eexists. split; [|split].
        + constructor.
        + apply payload_agree_setTS; auto.
        + unfold control_snapshot_ctrl. simpl. unfold setTS.
          destruct (nodes s' l) as [[? [|? ?]]|]; reflexivity.
      - (* getCounter inv *)
        eexists. split; [|split].
        + constructor.
        + simpl. repeat split; auto.
        + reflexivity.
      - (* getCounter res *)
        exists (Ready s'). split; [|split].
        + rewrite Hc. constructor.
        + assumption.
        + reflexivity.
      - (* tryRemove inv *)
        eexists. split; [|split].
        + constructor. rewrite <- Hn. assumption.
        + simpl. repeat split; auto.
        + reflexivity.
      - (* tryRemove succ *)
        eexists. split; [|split].
        + constructor; [rewrite <- Hn | rewrite <- Ho]; assumption.
        + apply payload_agree_remove; auto.
        + reflexivity.
      - (* tryRemove fail *)
        exists (Ready s'). split; [|split].
        + constructor; [rewrite <- Hn | rewrite <- Ho]; assumption.
        + assumption.
        + reflexivity.
    Qed.

    Lemma step_replay q ev c1 c2 c1' :
      te_tid ev <> q ->
      Step (li_lts F) ev c1 c2 ->
      control_agree q c1 c1' ->
      exists c2',
        Step (li_lts F) ev c1' c2' /\ control_agree q c2 c2' /\
        control_snapshot q c2' = control_snapshot q c1'.
    Proof.
      intros Hneq [Hstep Hlog] [Hagree Hlogeq].
      destruct (step_replay_ctrl q ev _ _ (fst c1') Hneq Hstep Hagree)
        as (cc2' & Hstep' & Hagree' & Hsnap').
      exists (pair cc2' (log_update ev (snd c1'))).
      split; [split; [exact Hstep'|reflexivity]|].
      split; [split; [exact Hagree'|simpl; rewrite Hlog, Hlogeq; reflexivity]|].
      unfold control_snapshot. simpl. exact Hsnap'.
    Qed.

    (** Linearization-map entries only ever advance, so a thread whose entry
        is unchanged across a step sequence took no step in it. *)
    Definition ls_rank (ls : option (@LinState (li_sig F))) : nat :=
      match ls with
      | None => O
      | Some (ls_inv _) => S O
      | Some (ls_lini _) => S (S O)
      | Some (ls_linr _ _) => S (S (S O))
      end.

    Lemma poss_step_rank q (ρ1 ρ2 : abstract_state) π1 π2 :
      @poss_step _ (li_lts F) (PossOk ρ1 π1) (PossOk ρ2 π2) ->
      Peano.le (ls_rank (TMap.find q π1)) (ls_rank (TMap.find q π2)) /\
      (TMap.find q π1 = TMap.find q π2 \/
       Peano.lt (ls_rank (TMap.find q π1)) (ls_rank (TMap.find q π2))).
    Proof.
      intros Hstep. inversion Hstep; subst;
        match goal with
        | Hlin : TMap.find ?tt π1 = Some _ |- _ =>
          destruct (PositiveMap.E.eq_dec q tt) as [->|Hqt];
          [ rewrite Hlin, TMap.gss; unfold ls_rank; simpl;
            split; [repeat constructor|right; repeat constructor]
          | rewrite TMap.gso by exact Hqt; split; [apply Nat.le_refl|left; reflexivity] ]
        end.
    Qed.

    Lemma poss_steps_from_error p :
      @poss_steps _ (li_lts F) PossError p -> p = PossError.
    Proof.
      intros H. apply clos_rt_rt1n in H.
      remember PossError as e. induction H; subst; [reflexivity|].
      inversion H.
    Qed.

    Lemma poss_steps_rank q (ρ1 ρ2 : abstract_state) π1 π2 :
      @poss_steps _ (li_lts F) (PossOk ρ1 π1) (PossOk ρ2 π2) ->
      Peano.le (ls_rank (TMap.find q π1)) (ls_rank (TMap.find q π2)).
    Proof.
      intros Hsteps.
      remember (PossOk ρ1 π1) as p1. remember (PossOk ρ2 π2) as p2.
      revert ρ1 π1 ρ2 π2 Heqp1 Heqp2.
      induction Hsteps as [p1 p2 Hstep | p | p1 p2 p3 H12 IH12 H23 IH23];
        intros ρ1 π1 ρ2 π2 E1 E2; subst.
      - apply (poss_step_rank q) in Hstep. tauto.
      - inversion E2; subst. apply Nat.le_refl.
      - destruct p2 as [ρm πm|].
        + etransitivity; [eapply IH12 | eapply IH23]; eauto.
        + apply poss_steps_from_error in H23. discriminate.
    Qed.

    Lemma poss_step_replay q ρx πx ρx' πx' ρy πy :
      @poss_step _ (li_lts F) (PossOk ρx πx) (PossOk ρx' πx') ->
      TMap.find q πx' = TMap.find q πx ->
      control_agree q ρx ρy ->
      (forall r, r <> q -> TMap.find r πx = TMap.find r πy) ->
      exists ρy' πy',
        @poss_step _ (li_lts F) (PossOk ρy πy) (PossOk ρy' πy') /\
        control_agree q ρx' ρy' /\
        control_snapshot q ρy' = control_snapshot q ρy /\
        (forall r, r <> q -> TMap.find r πx' = TMap.find r πy') /\
        TMap.find q πy' = TMap.find q πy.
    Proof.
      intros Hstep Hq Hagree Htok.
      inversion Hstep; subst.
      - (* inv step *)
        match goal with
        | Hlin : TMap.find ?tt πx = Some (ls_inv ?ff),
          Hs : Step (li_lts F) ?ev ρx ρx' |- _ =>
          assert (Htq : tt <> q)
            by (intros Heq; subst; rewrite TMap.gss, Hlin in Hq; discriminate);
          destruct (step_replay q ev _ _ ρy Htq Hs Hagree)
            as (ρy' & Hstep' & Hagree' & Hsnap');
          exists ρy', (TMap.add tt (ls_lini ff) πy);
          split; [|split; [exact Hagree'|split; [exact Hsnap'|split]]];
          [ eapply ps_inv; [exact Hstep' | rewrite <- Htok by exact Htq; exact Hlin]
          | intros r Hr; destruct (PositiveMap.E.eq_dec r tt) as [->|Hrt];
            [rewrite !TMap.gss; reflexivity
            |rewrite !TMap.gso by exact Hrt; auto]
          | rewrite TMap.gso by congruence; reflexivity ]
        end.
      - (* res step *)
        match goal with
        | Hlin : TMap.find ?tt πx = Some (ls_lini ?ff),
          Hs : Step (li_lts F) ?ev ρx ρx' |- _ =>
          assert (Htq : tt <> q)
            by (intros Heq; subst; rewrite TMap.gss, Hlin in Hq; discriminate);
          destruct (step_replay q ev _ _ ρy Htq Hs Hagree)
            as (ρy' & Hstep' & Hagree' & Hsnap');
          eexists ρy', (TMap.add tt (ls_linr ff _) πy);
          split; [|split; [exact Hagree'|split; [exact Hsnap'|split]]];
          [ eapply ps_ret; [exact Hstep' | rewrite <- Htok by exact Htq; exact Hlin]
          | intros r Hr; destruct (PositiveMap.E.eq_dec r tt) as [->|Hrt];
            [rewrite !TMap.gss; reflexivity
            |rewrite !TMap.gso by exact Hrt; auto]
          | rewrite TMap.gso by congruence; reflexivity ]
        end.
    Qed.

    Lemma poss_steps_replay q ρx πx ρx' πx' ρy πy :
      @poss_steps _ (li_lts F) (PossOk ρx πx) (PossOk ρx' πx') ->
      TMap.find q πx' = TMap.find q πx ->
      control_agree q ρx ρy ->
      (forall r, r <> q -> TMap.find r πx = TMap.find r πy) ->
      exists ρy' πy',
        @poss_steps _ (li_lts F) (PossOk ρy πy) (PossOk ρy' πy') /\
        control_agree q ρx' ρy' /\
        control_snapshot q ρy' = control_snapshot q ρy /\
        (forall r, r <> q -> TMap.find r πx' = TMap.find r πy') /\
        TMap.find q πy' = TMap.find q πy.
    Proof.
      intros Hsteps. apply clos_rt_rt1n in Hsteps.
      remember (PossOk ρx πx) as p1. remember (PossOk ρx' πx') as p2.
      revert ρx πx ρx' πx' ρy πy Heqp1 Heqp2.
      induction Hsteps as [p | p1 p2 p3 H12 H23 IH];
        intros ρx πx ρx' πx' ρy πy E1 E2 Hq Hagree Htok; subst.
      - inversion E2; subst. exists ρy, πy.
        split; [apply rt_refl|]. split; [exact Hagree|]. repeat split; auto.
      - destruct p2 as [ρm πm|].
        2:{ exfalso. apply clos_rt1n_rt, poss_steps_from_error in H23.
            discriminate. }
        assert (Hqm : TMap.find q πm = TMap.find q πx).
        { pose proof (poss_step_rank q _ _ _ _ H12)
            as [Hle [Heq|Hlt]]; [symmetry; exact Heq|].
          exfalso.
          pose proof (poss_steps_rank q _ _ _ _
            (clos_rt1n_rt _ _ _ _ H23)) as Hle'.
          rewrite Hq in Hle'.
          exact (Nat.lt_irrefl _ (Nat.lt_le_trans _ _ _ Hlt Hle')). }
        destruct (poss_step_replay q _ _ _ _ _ _ H12 Hqm Hagree Htok)
          as (ρy1 & πy1 & Hstep1 & Hagree1 & Hsnap1 & Htok1 & Hq1).
        destruct (IH _ _ _ _ ρy1 πy1 eq_refl eq_refl) as
          (ρy' & πy' & Hsteps' & Hagree' & Hsnap' & Htok' & Hq');
          [congruence | exact Hagree1 | exact Htok1 |].
        exists ρy', πy'. split; [|split; [exact Hagree'|repeat split; auto]].
        + eapply rt_trans; [apply rt_step; exact Hstep1 | exact Hsteps'].
        + congruence.
        + congruence.
    Qed.

    (** ** The payload of a possibility is determined by the concrete state *)

    Lemma represents_determined h top count s s' log :
      represents h top count s log -> represents h top count s' log ->
      counter s = counter s' /\ nodes s = nodes s' /\ order s = order s'.
    Proof.
      intros (_ & Hc & _ & Hn & Ho) (_ & Hc' & _ & Hn' & Ho').
      repeat split; congruence.
    Qed.

    Lemma source_I_payload_determined w w' :
      source_I w -> source_I w' ->
      SinglePossState.σ w = SinglePossState.σ w' ->
      log_of w = log_of w' ->
      counter (payload_of w) = counter (payload_of w') /\
      nodes (payload_of w) = nodes (payload_of w') /\
      order (payload_of w) = order (payload_of w').
    Proof.
      intros HI HI' Eσ Elog.
      pose proof (source_I_rep _ HI) as Hrep.
      pose proof (source_I_rep _ HI') as Hrep'.
      unfold heap_of, reg_of in Hrep, Hrep'. rewrite Eσ in Hrep. rewrite Elog in Hrep.
      eapply represents_determined; eauto.
    Qed.

    (** ** Pointwise possibility facade

        [SPListImpl.getTop_impl] reads a node's timestamp before its taken
        flag.  When the flag is read as [false], [getTop] linearizes at the
        earlier timestamp read, which cannot be known at that time.  The
        proof therefore keeps, between the two reads, both the possibility
        in which [getTop] has already returned and the one in which it is
        still scanning, and drops one of them at the flag read.

        Every assertion below holds pointwise on all possibilities of a
        set.  The rely/guarantee relations relate each new possibility back
        to an old one, and in addition preserve the "twin" structure that
        keeps both branches available for an observer [q]: for every
        possibility there is one that differs only in [q]'s slot (its
        snapshot entry and its linearization-map entry) and carries the
        other linearization kind. *)

    Definition set_state :=
      @SetPossState.ProofStateSet _ _ (li_lts E) (li_lts F).
    Definition set_assertion := @Assertion set_state.
    Definition set_relation :=
      @AssertionsSet.A.RGRelation _ _ (li_lts E) (li_lts F).

    Definition mk (σ : concrete_state) (ρ : abstract_state)
        (π : tmap (@LinState (li_sig F))) : single_state :=
      @SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
        σ ρ π.

    Definition mks (σ : concrete_state)
        (Δ : @AbstractConfig (li_sig F) (li_lts F)) : set_state :=
      @SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F) σ Δ.

    Definition slot_snapshot (q : tid) (w : single_state) :=
      TMap.find q (snapshot (payload_of w)).
    Definition slot_token (q : tid) (w : single_state) :=
      TMap.find q (SinglePossState.π w).

    (** Agreement everywhere except in [q]'s slot. *)
    Definition offslot_agree (q : tid) (x y : single_state) : Prop :=
      SinglePossState.σ x = SinglePossState.σ y /\
      log_of x = log_of y /\
      (forall r, r <> q -> slot_snapshot r x = slot_snapshot r y) /\
      (forall r, r <> q -> slot_token r x = slot_token r y).

    (** Agreement on the concrete state, the log, and [q]'s slot. *)
    Definition slot_agree (q : tid) (x y : single_state) : Prop :=
      SinglePossState.σ x = SinglePossState.σ y /\
      log_of x = log_of y /\
      slot_snapshot q x = slot_snapshot q y /\
      slot_token q x = slot_token q y.

    (** An assertion of thread [q] that only looks at the concrete state,
        the (concrete-state-determined) payload, and [q]'s own slot. *)
    Definition slot_local (q : tid) (P : assertion) : Prop :=
      forall x y, P x -> source_I y -> slot_agree q x y -> P y.

    Definition kind_lini (q : tid) (x : single_state) : Prop :=
      exists f, slot_token q x = Some (ls_lini f).
    Definition kind_linr (q : tid) (x : single_state) : Prop :=
      exists f ret, slot_token q x = Some (ls_linr f ret).

    Definition HasKind (K : tid -> single_state -> Prop) (q : tid)
        (s : set_state) : Prop :=
      forall ρ π, SetPossState.Δ s ρ π ->
        exists ρ' π', SetPossState.Δ s ρ' π' /\
          offslot_agree q (mk (SetPossState.σ s) ρ π)
            (mk (SetPossState.σ s) ρ' π') /\
          K q (mk (SetPossState.σ s) ρ' π').

    Definition twins_preserved (q : tid) (s s' : set_state) : Prop :=
      (HasKind kind_lini q s -> HasKind kind_lini q s') /\
      (HasKind kind_linr q s -> HasKind kind_linr q s').

    Definition lift_assert (P : assertion) : set_assertion :=
      fun s => forall ρ π, SetPossState.Δ s ρ π ->
        P (mk (SetPossState.σ s) ρ π).

    Definition lift_backward (Rs : rg_relation) (s s' : set_state) : Prop :=
      forall ρ' π', SetPossState.Δ s' ρ' π' ->
        exists ρ π, SetPossState.Δ s ρ π /\
          Rs (mk (SetPossState.σ s) ρ π) (mk (SetPossState.σ s') ρ' π').

    Definition lift_relation (actor : tid) (Rs : rg_relation) :
        set_relation :=
      fun s s' => lift_backward Rs s s' /\
        forall q, q <> actor -> twins_preserved q s s'.

    Definition SI : set_assertion := lift_assert source_I.
    Definition G (t : tid) : set_relation := lift_relation t (source_G t).
    Definition R (t : tid) : set_relation :=
      fun s s' => lift_backward (source_R t) s s' /\ twins_preserved t s s'.

    Lemma lift_impl (P Q : assertion) :
      (forall x, P x -> Q x) ->
      forall s, lift_assert P s -> lift_assert Q s.
    Proof. intros HPQ s HP ρ π Hposs. apply HPQ, HP, Hposs. Qed.

    Lemma lift_no_error ev (P : assertion) :
      (forall x, P x -> AssertionsSingle.A.ANoError ev x) ->
      forall s, lift_assert P s -> AssertionsSet.A.ANoError ev s.
    Proof.
      intros Hsafe s HP.
      destruct (ac_nonempty (SetPossState.Δ s)) as (ρ & π & Hposs).
      exact (Hsafe _ (HP _ _ Hposs)).
    Qed.

    Lemma lift_stable t (P : assertion) :
      AssertionsSingle.A.Stable (source_R t) source_I P ->
      AssertionsSet.A.Stable (R t) SI (lift_assert P).
    Proof.
      unfold AssertionsSingle.A.Stable, AssertionsSet.A.Stable,
        AssertionsSingle.A.ComposeA, AssertionsSet.A.ComposeA.
      intros Hstable s' [[s [HP [Hback _]]] HI] ρ' π' Hposs'.
      destruct (Hback _ _ Hposs') as (ρ & π & Hposs & HR).
      apply Hstable. split.
      - exists (mk (SetPossState.σ s) ρ π). split; [apply HP, Hposs | exact HR].
      - apply HI, Hposs'.
    Qed.

    Lemma lift_post_lin (P : assertion) t ls :
      (forall x, P x -> TMap.find t (SinglePossState.π x) = Some ls) ->
      forall s, lift_assert P s ->
      forall ρ π, SetPossState.Δ s ρ π -> TMap.find t π = Some ls.
    Proof. intros Hlin s HP ρ π Hposs. exact (Hlin _ (HP _ _ Hposs)). Qed.

    Lemma lift_initial (P : assertion) σ ρ π :
      P (mk σ ρ π) -> lift_assert P (mks σ (ac_singleton ρ π)).
    Proof.
      intros HP ρ' π' Hposs. inversion Hposs; subst. exact HP.
    Qed.

    Lemma kind_lini_token q x y :
      slot_token q x = slot_token q y -> kind_lini q x -> kind_lini q y.
    Proof. intros Heq [f Hf]. exists f. rewrite <- Heq. exact Hf. Qed.

    Lemma kind_linr_token q x y :
      slot_token q x = slot_token q y -> kind_linr q x -> kind_linr q y.
    Proof. intros Heq [f [ret Hf]]. exists f, ret. rewrite <- Heq. exact Hf. Qed.

    Lemma offslot_agree_change_σ q σ1 σ2 ρ π ρ' π' :
      offslot_agree q (mk σ1 ρ π) (mk σ1 ρ' π') ->
      offslot_agree q (mk σ2 ρ π) (mk σ2 ρ' π').
    Proof.
      intros [_ [Hl [Hs Ht]]]. split; [reflexivity|]. split; [exact Hl|].
      split; assumption.
    Qed.

    Lemma twins_preserved_refl q σ σ' Δ :
      twins_preserved q (mks σ Δ) (mks σ' Δ).
    Proof.
      assert (Hgen : forall K : tid -> single_state -> Prop,
        (forall σ1 σ2 ρ π, K q (mk σ1 ρ π) -> K q (mk σ2 ρ π)) ->
        HasKind K q (mks σ Δ) -> HasKind K q (mks σ' Δ)).
      { intros K Kσ HK ρ π Hposs.
        destruct (HK ρ π Hposs) as (ρ' & π' & Hposs' & Hoff & Hkind).
        exists ρ', π'. split; [exact Hposs'|]. split.
        - eapply offslot_agree_change_σ. exact Hoff.
        - eapply Kσ. exact Hkind. }
      split; apply Hgen; intros σ1 σ2 ρ π H; exact H.
    Qed.

    Lemma lift_valid_rgi t :
      RGISimulationSet.RGISimulation.ValidRGI (R t) (G t) SI t.
    Proof.
      constructor. intros s s' [Hback _] _. split.
      - intros Hnone ρ' π' Hposs'.
        destruct (Hback _ _ Hposs') as (ρ & π & Hposs & HR).
        pose proof (source_R_token t _ _ HR) as Htok.
        unfold token_eq in Htok. simpl in Htok.
        exact (eq_trans (eq_sym Htok) (Hnone _ _ Hposs)).
      - intros Hnone' ρ π Hposs.
        destruct (ac_nonempty (SetPossState.Δ s')) as (ρ' & π' & Hposs').
        destruct (Hback _ _ Hposs') as (ρ0 & π0 & Hposs0 & HR).
        pose proof (source_R_token t _ _ HR) as Htok.
        unfold token_eq in Htok. simpl in Htok.
        pose proof (eq_trans Htok (Hnone' _ _ Hposs')) as Hn0.
        eapply ac_find_none_same; eauto.
    Qed.

    Lemma lift_ginv_twins t1 t2 f σ Δ :
      t1 <> t2 ->
      twins_preserved t2 (mks σ Δ) (mks σ (ac_inv Δ t1 f)).
    Proof.
      intros Hneq. split; intros HK ρ' π' Hposs'; inversion Hposs'; subst;
        destruct (HK _ _ Hposs) as (ρy & πy & Hpossy & [Hσ [Hl [Hs Ht]]] & Hkind);
        exists ρy, (TMap.add t1 (ls_inv f) πy);
        (split; [constructor; exact Hpossy|]);
        (split; [split; [reflexivity|split; [exact Hl|split; [exact Hs|]]]|]).
      - intros r Hr. unfold slot_token. simpl.
        destruct (PositiveMap.E.eq_dec r t1) as [->|Hrt].
        + rewrite !TMap.gss. reflexivity.
        + rewrite !TMap.gso by exact Hrt. apply Ht, Hr.
      - eapply kind_lini_token; [|exact Hkind].
        unfold slot_token. simpl. rewrite TMap.gso by congruence. reflexivity.
      - intros r Hr. unfold slot_token. simpl.
        destruct (PositiveMap.E.eq_dec r t1) as [->|Hrt].
        + rewrite !TMap.gss. reflexivity.
        + rewrite !TMap.gso by exact Hrt. apply Ht, Hr.
      - eapply kind_linr_token; [|exact Hkind].
        unfold slot_token. simpl. rewrite TMap.gso by congruence. reflexivity.
    Qed.

    Lemma lift_gret_twins t1 t2 σ Δ :
      t1 <> t2 ->
      twins_preserved t2 (mks σ Δ) (mks σ (ac_res Δ t1)).
    Proof.
      intros Hneq. split; intros HK ρ' π' Hposs'; inversion Hposs'; subst;
        destruct (HK _ _ Hposs) as (ρy & πy & Hpossy & [Hσ [Hl [Hs Ht]]] & Hkind);
        exists ρy, (TMap.remove t1 πy);
        (split; [constructor; exact Hpossy|]);
        (split; [split; [reflexivity|split; [exact Hl|split; [exact Hs|]]]|]).
      - intros r Hr. unfold slot_token. simpl.
        destruct (PositiveMap.E.eq_dec r t1) as [->|Hrt].
        + rewrite !TMap.grs. reflexivity.
        + rewrite !TMap.gro by exact Hrt. apply Ht, Hr.
      - eapply kind_lini_token; [|exact Hkind].
        unfold slot_token. simpl. rewrite TMap.gro by congruence. reflexivity.
      - intros r Hr. unfold slot_token. simpl.
        destruct (PositiveMap.E.eq_dec r t1) as [->|Hrt].
        + rewrite !TMap.grs. reflexivity.
        + rewrite !TMap.gro by exact Hrt. apply Ht, Hr.
      - eapply kind_linr_token; [|exact Hkind].
        unfold slot_token. simpl. rewrite TMap.gro by congruence. reflexivity.
    Qed.

    Lemma twins_preserved_equiv q s s' s'' :
      SetPossState.σ s' = SetPossState.σ s'' ->
      ac_equiv (SetPossState.Δ s') (SetPossState.Δ s'') ->
      twins_preserved q s s' -> twins_preserved q s s''.
    Proof.
      intros Hσ Heq [H1 H2].
      assert (Hconv : forall K, HasKind K q s' -> HasKind K q s'').
      { intros K HK ρ π Hposs. apply Heq in Hposs.
        destruct (HK _ _ Hposs) as (ρ' & π' & Hposs' & Hoff & Hkind).
        exists ρ', π'. split; [apply Heq, Hposs'|].
        rewrite <- Hσ. split; assumption. }
      split; intros HK; apply Hconv; auto.
    Qed.

    Lemma lift_parallel_compat t1 t2 :
      t1 <> t2 -> forall s s',
        (G t1 s s' \/
         (AssertionsSet.GINV t1 s s' \/ AssertionsSet.GRET t1 s s') \/
         AssertionsSet.A.GId s s') /\ SI s ->
        R t2 s s'.
    Proof.
      intros Hneq s s' [Hrel HI].
      destruct Hrel as [[Hback Htwins] | [[[f Hinv] | [f [ret Hret]]] | Hid]].
      - split.
        + intros ρ' π' Hposs'.
          destruct (Hback _ _ Hposs') as (ρ & π & Hposs & HG).
          exists ρ, π. split; [exact Hposs|].
          apply (source_parallel_compatible t1 t2 Hneq). left. exact HG.
        + apply Htwins. congruence.
      - destruct Hinv as [Hσ [Hnone HΔ]]. split.
        + intros ρ' π' Hposs'. apply HΔ in Hposs'. inversion Hposs'; subst.
          eexists ρ', _. split; [exact Hposs|].
          apply (source_parallel_compatible t1 t2 Hneq).
          right. left. left. exists f.
          unfold AssertionsSingle.Ginv, AssertionsSingle.LiftRelation_π. simpl.
          split; [exact Hσ|]. split; [reflexivity|].
          split; [exact (Hnone _ _ Hposs)|reflexivity].
        + destruct s as [σ Δ], s' as [σ' Δ']. simpl in *. subst σ'.
          eapply twins_preserved_equiv with (s' := mks σ (ac_inv Δ t1 f)).
          * reflexivity.
          * intros ρ π. simpl. symmetry. apply HΔ.
          * apply lift_ginv_twins. exact Hneq.
      - destruct Hret as [Hσ [Hlin HΔ]]. split.
        + intros ρ' π' Hposs'. apply HΔ in Hposs'. inversion Hposs'; subst.
          eexists ρ', _. split; [exact Hposs|].
          apply (source_parallel_compatible t1 t2 Hneq).
          right. left. right. exists f, ret.
          unfold AssertionsSingle.Gret, AssertionsSingle.LiftRelation_π. simpl.
          split; [exact Hσ|]. split; [reflexivity|].
          split; [exact (Hlin _ _ Hposs)|reflexivity].
        + destruct s as [σ Δ], s' as [σ' Δ']. simpl in *. subst σ'.
          eapply twins_preserved_equiv with (s' := mks σ (ac_res Δ t1)).
          * reflexivity.
          * intros ρ π. simpl. symmetry. apply HΔ.
          * apply lift_gret_twins. exact Hneq.
      - unfold AssertionsSet.A.GId in Hid. subst s'. split.
        + intros ρ π Hposs. exists ρ, π. split; [exact Hposs|].
          apply (source_parallel_compatible t1 t2 Hneq).
          right. right. reflexivity.
        + destruct s as [σ Δ]. apply twins_preserved_refl.
    Qed.

    Lemma lift_ginv_compose t f (I P : assertion) :
      (forall x, AssertionsSingle.A.ComposeA I (AssertionsSingle.Ginv t f) x ->
        P x) ->
      forall s, AssertionsSet.A.ComposeA (lift_assert I)
        (AssertionsSet.Ginv t f) s -> lift_assert P s.
    Proof.
      intros Himpl s [s0 [HI [Hσ [Hnone HΔ]]]] ρ' π' Hposs'.
      apply HΔ in Hposs'. inversion Hposs'; subst.
      apply Himpl. eexists (mk (SetPossState.σ s0) ρ' _). split.
      - eapply HI. exact Hposs.
      - unfold AssertionsSingle.Ginv, AssertionsSingle.LiftRelation_π. simpl.
        split; [exact Hσ|]. split; [reflexivity|].
        split; [exact (Hnone _ _ Hposs)|reflexivity].
    Qed.

    Lemma lift_gret_compose t f ret (Q I : assertion) :
      (forall x, AssertionsSingle.A.ComposeA Q (AssertionsSingle.Gret t f ret) x ->
        I x) ->
      forall s, AssertionsSet.A.ComposeA (lift_assert Q)
        (AssertionsSet.Gret t f ret) s -> lift_assert I s.
    Proof.
      intros Himpl s [s0 [HQ [Hσ [Hlin HΔ]]]] ρ' π' Hposs'.
      apply HΔ in Hposs'. inversion Hposs'; subst.
      apply Himpl. eexists (mk (SetPossState.σ s0) ρ' _). split.
      - eapply HQ. exact Hposs.
      - unfold AssertionsSingle.Gret, AssertionsSingle.LiftRelation_π. simpl.
        split; [exact Hσ|]. split; [reflexivity|].
        split; [exact (Hlin _ _ Hposs)|reflexivity].
    Qed.

    (** *** Transfer of facts between twins *)

    Lemma offslot_control_agree q x y :
      source_I x -> source_I y -> offslot_agree q x y ->
      control_agree q (SinglePossState.ρ x) (SinglePossState.ρ y).
    Proof.
      intros HIx HIy [Hσ [Hl [Hs Ht]]].
      pose proof (source_I_payload_determined _ _ HIx HIy Hσ Hl) as (Hc & Hn & Ho).
      rewrite (source_I_ready _ HIx), (source_I_ready _ HIy). simpl.
      split; [|exact Hl]. simpl. repeat split; auto.
    Qed.

    Lemma control_agree_ready q c s' log' :
      control_agree q c (pair (Ready s') log') ->
      exists s, c = pair (Ready s) log' /\ payload_agree q s s'.
    Proof.
      destruct c as [[s | s t op] log]; simpl; intros [Hc Hl]; [|contradiction].
      simpl in Hl. subst. eauto.
    Qed.

    Lemma control_agree_ready' q s log c' :
      control_agree q (pair (Ready s) log) c' ->
      exists s', c' = pair (Ready s') log /\ payload_agree q s s'.
    Proof.
      destruct c' as [[s' | s' t op] log']; simpl; intros [Hc Hl]; [|contradiction].
      simpl in Hl. subst. eauto.
    Qed.

    Lemma control_agree_snapshot q c c' :
      control_agree q c c' ->
      forall r, r <> q ->
        TMap.find r (snapshot (abstract_payload (fst c))) =
        TMap.find r (snapshot (abstract_payload (fst c'))).
    Proof.
      intros [Hc _].
      destruct c as [[s | s t op] log], c' as [[s' | s' t' op'] log']; simpl in *;
        try contradiction.
      - destruct Hc as (_ & _ & _ & Hs). exact Hs.
      - destruct Hc as (_ & _ & (_ & _ & _ & Hs)). exact Hs.
    Qed.

    Lemma control_agree_log q c c' :
      control_agree q c c' -> snd c = snd c'.
    Proof. intros [_ Hl]. exact Hl. Qed.

    Lemma represents_payload_agree q h top count s s' log :
      payload_agree q s s' -> represents h top count s log ->
      represents h top count s' log.
    Proof.
      intros (Hc & Hn & Ho & _) (Hvalid & Hcount & Hlen & Hnodes & Horder).
      split; [exact Hvalid|]. repeat split; congruence.
    Qed.

    (** A replayed twin satisfies the invariant: its payload agrees with
        the original image off [q], and its [q] slot is the twin's. *)
    Lemma source_I_transfer q x' y y' :
      source_I x' -> source_I y ->
      SinglePossState.σ y' = SinglePossState.σ x' ->
      control_agree q (SinglePossState.ρ x') (SinglePossState.ρ y') ->
      (forall r, r <> q -> slot_token r x' = slot_token r y') ->
      control_snapshot q (SinglePossState.ρ y') = slot_snapshot q y ->
      slot_token q y' = slot_token q y ->
      source_I y'.
    Proof.
      intros HIx' HIy Hσ Hagree Htok Hsnap Hq.
      destruct HIx' as (mc & cc & sx & log & Eσ & Eρ & Hmc & Hcc & Hrep & Hcons).
      destruct HIy as (mcy & ccy & sy & logy & Eσy & Eρy & _ & _ & _ & Hconsy).
      rewrite Eρ in Hagree.
      destruct (control_agree_ready' _ _ _ _ Hagree) as (sy' & Eρ' & Hpay).
      exists mc, cc, sy', log. split; [exact (eq_trans Hσ Eσ)|]. split; [exact Eρ'|].
      split; [exact Hmc|]. split; [exact Hcc|]. split.
      - eapply represents_payload_agree; eauto.
      - intros r. destruct (PositiveMap.E.eq_dec r q) as [->|Hrq].
        + unfold control_snapshot, slot_snapshot, payload_of, ctrl_of in Hsnap.
          rewrite Eρ', Eρy in Hsnap. simpl in Hsnap.
          unfold slot_token in Hq.
          rewrite Hsnap, Hq. apply Hconsy.
        + destruct Hpay as (_ & _ & _ & Hs).
          rewrite <- (Hs r Hrq). unfold slot_token in Htok.
          rewrite <- (Htok r Hrq). apply Hcons.
    Qed.

    Lemma source_G_transfer t q x x' y y' :
      q <> t ->
      source_G t x x' ->
      source_I y -> source_I y' ->
      offslot_agree q x y ->
      SinglePossState.σ y' = SinglePossState.σ x' ->
      control_agree q (SinglePossState.ρ x') (SinglePossState.ρ y') ->
      (forall r, r <> q -> slot_token r x' = slot_token r y') ->
      control_snapshot q (SinglePossState.ρ y') = slot_snapshot q y ->
      slot_token q y' = slot_token q y ->
      source_G t y y'.
    Proof.
      intros Hqt HG HIy HIy' [Hσxy [Hlxy [Hsxy Htxy]]] Hσ Hagree Htok Hsnap Hq.
      destruct HG as (HIx & HIx' & Hheap & Hpriv & Hcas & Hsnaps & Htoks).
      pose proof (source_I_payload_determined _ _ HIx HIy Hσxy Hlxy)
        as (_ & Hnodes & _).
      pose proof (control_agree_snapshot _ _ _ Hagree) as Hs'.
      pose proof (control_agree_log _ _ _ Hagree) as Hl'.
      split; [exact HIy|]. split; [exact HIy'|].
      rewrite <- Hσxy, Hσ. split; [exact Hheap|].
      split.
      { intros l Hactor Hundef. apply Hpriv; [exact Hactor|].
        unfold payload_of in Hnodes. rewrite Hnodes. exact Hundef. }
      split.
      { destruct Hcas as [Hcount Hlog]. split; [exact Hcount|].
        unfold log_of, log_of_ctrl in Hlxy. unfold log_of_ctrl in *.
        rewrite <- Hl', <- Hlxy. exact Hlog. }
      split.
      - intros r Hr. unfold ctrl_of. destruct (PositiveMap.E.eq_dec r q) as [->|Hrq].
        + unfold control_snapshot, slot_snapshot, payload_of, ctrl_of in Hsnap.
          symmetry. exact Hsnap.
        + unfold slot_snapshot, payload_of, ctrl_of in Hsxy.
          rewrite <- (Hsxy r Hrq), <- (Hs' r Hrq). apply Hsnaps. exact Hr.
      - intros r Hr. destruct (PositiveMap.E.eq_dec r q) as [->|Hrq].
        + unfold slot_token in Hq. symmetry. exact Hq.
        + unfold slot_token in Htxy, Htok.
          rewrite <- (Htxy r Hrq), <- (Htok r Hrq). apply Htoks. exact Hr.
    Qed.

    Lemma map_domain_equiv_of_tokens q (π1 π2 π1' π2' : tmap (@LinState (li_sig F))) :
      domain_equiv (map_domain π1) (map_domain π2) ->
      (forall r, r <> q -> TMap.find r π1' = TMap.find r π2') ->
      TMap.find q π1' = TMap.find q π1 ->
      TMap.find q π2' = TMap.find q π2 ->
      domain_equiv (map_domain π1') (map_domain π2').
    Proof.
      intros Hdom Hoff H1 H2 r. unfold map_domain.
      destruct (PositiveMap.E.eq_dec r q) as [->|Hrq].
      - rewrite H1, H2. apply Hdom.
      - rewrite (Hoff r Hrq). reflexivity.
    Qed.

    (** *** Lifting a pointwise update

        The image of a possibility set under a thread's update.  Only
        images with the domain [D] are kept, which is what makes the result
        a well-formed configuration.  [D] is chosen as the domain of one
        witness image; every image has that domain anyway because the
        postcondition fixes the acting thread's slot. *)
    Definition image_prop (Δ : @AbstractConfig (li_sig F) (li_lts F))
        (σ σ' : concrete_state) (Q : assertion) (Gs : rg_relation)
        (D : ThreadDomain) : @AbstractConfigProp (li_sig F) (li_lts F) :=
      fun ρ' π' => exists ρ π, Δ ρ π /\
        @poss_steps _ (li_lts F) (PossOk ρ π) (PossOk ρ' π') /\
        Q (mk σ' ρ' π') /\ Gs (mk σ ρ π) (mk σ' ρ' π') /\
        domain_equiv (map_domain π') D.

    Definition image_config Δ σ σ' Q Gs D
        (Hne : exists ρ' π', image_prop Δ σ σ' Q Gs D ρ' π') :
        @AbstractConfig (li_sig F) (li_lts F) :=
      {| ac_active := D;
         ac_prop := image_prop Δ σ σ' Q Gs D;
         ac_nonempty := Hne;
         ac_domain := fun ρ' π' H =>
           match H with
           | ex_intro _ ρ (ex_intro _ π (conj _ (conj _ (conj _ (conj _ Hdom))))) =>
               Hdom
           end |}.

    Lemma lift_pupdate t ev (P Q : assertion) :
      (forall x, P x -> source_I x) ->
      (forall x, Q x -> source_I x) ->
      slot_local t Q ->
      AssertionsSingle.PUpdate (source_G t) ev P Q ->
      AssertionsSet.PUpdate (G t) ev (lift_assert P) (lift_assert Q).
    Proof.
      intros HPI HQI Hloc Hupd σ Δ HP σ' Hstep.
      destruct (ac_nonempty Δ) as (ρ0 & π0 & Hposs0).
      destruct (Hupd σ ρ0 π0 (HP _ _ Hposs0) σ' Hstep)
        as (ρ0' & π0' & Hsteps0 & HQ0 & HG0).
      assert (Hne : exists ρ' π',
        image_prop Δ σ σ' Q (source_G t) (map_domain π0') ρ' π').
      { exists ρ0', π0', ρ0, π0.
        split; [exact Hposs0|]. split; [exact Hsteps0|].
        split; [exact HQ0|]. split; [exact HG0|]. apply domain_equiv_refl. }
      exists (image_config Δ σ σ' Q (source_G t) (map_domain π0') Hne).
      split; [|split].
      - intros ρ' π' (ρ & π & Hposs & Hsteps & _). econstructor; eauto.
      - intros ρ' π' (ρ & π & _ & _ & HQ & _). exact HQ.
      - split.
        + intros ρ' π' (ρ & π & Hposs & _ & _ & HG & _).
          exists ρ, π. split; assumption.
        + intros q Hq.
          assert (Hgen : forall K : tid -> single_state -> Prop,
            (forall x y, slot_token q x = slot_token q y -> K q x -> K q y) ->
            HasKind K q (mks σ Δ) ->
            HasKind K q (mks σ'
              (image_config Δ σ σ' Q (source_G t) (map_domain π0') Hne))).
          { intros K Ktok HK ρ' π' (ρ & π & Hposs & Hsteps & HQ' & HG & Hdom).
            destruct (HK ρ π Hposs) as (ρy & πy & Hpossy & Hoff & Hkind).
            pose proof (HPI _ (HP _ _ Hposs)) as HIx.
            pose proof (HPI _ (HP _ _ Hpossy)) as HIy.
            pose proof HG as (_ & _ & _ & _ & _ & _ & Htoks).
            simpl in Htoks.
            pose proof (offslot_control_agree q _ _ HIx HIy Hoff) as Hagree.
            simpl in Hagree.
            pose proof Hoff as [_ [_ [Hsxy Htxy]]].
            destruct (poss_steps_replay q ρ π ρ' π' ρy πy Hsteps
              (eq_sym (Htoks q Hq)) Hagree Htxy)
              as (ρy' & πy' & Hstepsy & Hagree' & Hsnap' & Htok' & Hqy).
            assert (HIy' : source_I (mk σ' ρy' πy')).
            { apply (source_I_transfer q (mk σ' ρ' π') (mk σ ρy πy)
                (mk σ' ρy' πy')).
              - exact (HQI _ HQ').
              - exact HIy.
              - reflexivity.
              - exact Hagree'.
              - intros r Hr. exact (Htok' r Hr).
              - exact Hsnap'.
              - exact Hqy. }
            assert (Htq : t <> q) by (intros Heq; apply Hq; symmetry; exact Heq).
            assert (HQy' : Q (mk σ' ρy' πy')).
            { eapply Hloc; [exact HQ' | exact HIy' |].
              split; [reflexivity|].
              split; [exact (control_agree_log _ _ _ Hagree')|]. split.
              - unfold slot_snapshot, payload_of, ctrl_of. simpl.
                apply (control_agree_snapshot _ _ _ Hagree' t Htq).
              - exact (Htok' t Htq). }
            assert (HGy : source_G t (mk σ ρy πy) (mk σ' ρy' πy')).
            { apply (source_G_transfer t q (mk σ ρ π) (mk σ' ρ' π')
                (mk σ ρy πy) (mk σ' ρy' πy')).
              - exact Hq.
              - exact HG.
              - exact HIy.
              - exact HIy'.
              - exact Hoff.
              - reflexivity.
              - exact Hagree'.
              - intros r Hr. exact (Htok' r Hr).
              - exact Hsnap'.
              - exact Hqy. }
            exists ρy', πy'. split; [|split].
            - exists ρy, πy. split; [exact Hpossy|]. split; [exact Hstepsy|].
              split; [exact HQy'|]. split; [exact HGy|].
              eapply domain_equiv_trans; [|exact Hdom].
              apply (map_domain_equiv_of_tokens q πy π πy' π').
              + eapply domain_equiv_trans; [eapply ac_domain; exact Hpossy|].
                apply domain_equiv_symm. eapply ac_domain; exact Hposs.
              + intros r Hr. symmetry. apply Htok', Hr.
              + exact Hqy.
              + symmetry. exact (Htoks q Hq).
            - split; [reflexivity|].
              split; [exact (control_agree_log _ _ _ Hagree')|]. split.
              + intros r Hr. unfold slot_snapshot, payload_of, ctrl_of. simpl.
                apply (control_agree_snapshot _ _ _ Hagree' r Hr).
              + intros r Hr. exact (Htok' r Hr).
            - eapply Ktok; [|exact Hkind]. exact (eq_sym Hqy). }

          split.
          * intros HK. exact (Hgen kind_lini (kind_lini_token q) HK).
          * intros HK. exact (Hgen kind_linr (kind_linr_token q) HK).
    Qed.

    (** A concrete step that changes no possibility. *)
    Lemma lift_pupdate_pure t ev (P Q : assertion) :
      (forall x, P x -> forall σ',
        Step (li_lts E) ev (SinglePossState.σ x) σ' ->
        Q (mk σ' (SinglePossState.ρ x) (SinglePossState.π x)) /\
        source_G t x (mk σ' (SinglePossState.ρ x) (SinglePossState.π x))) ->
      AssertionsSet.PUpdate (G t) ev (lift_assert P) (lift_assert Q).
    Proof.
      intros Hupd σ Δ HP σ' Hstep. exists Δ. split; [apply ac_steps_refl|].
      split.
      - intros ρ π Hposs. exact (proj1 (Hupd _ (HP _ _ Hposs) _ Hstep)).
      - split.
        + intros ρ π Hposs. exists ρ, π. split; [exact Hposs|].
          exact (proj2 (Hupd _ (HP _ _ Hposs) _ Hstep)).
        + intros q _. apply twins_preserved_refl.
    Qed.

    (** *** Program rules with pointwise leaf obligations *)

    Lemma singleton_provable_vis_safe {X} t
        (P : assertion) (Q : X -> assertion)
        (m : Sig.op (li_sig E)) (k : Sig.ar m -> Prog (li_sig E) X)
        (P' : assertion) (Q' : Sig.ar m -> assertion) :
      (⊨ P ==>> AssertionsSingle.A.ANoError (Build_ThreadEvent t (InvEv m))) ->
      (⊨ P' ==>> source_I) ->
      (forall a, ⊨ Q' a ==>> source_I) ->
      AssertionsSingle.A.Stable (source_R t) source_I P' ->
      (forall a, AssertionsSingle.A.Stable (source_R t) source_I (Q' a)) ->
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (InvEv m)) P P' ->
      (forall ret, AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (ResEv m ret)) P' (Q' ret)) ->
      (forall ret,
        [li_lts E, li_lts F, R t, G t, SI, t] ⊢
          {{ lift_assert (Q' ret) }} k ret {{ fun a => lift_assert (Q a) }}) ->
      (⊨ P ==>> source_I) ->
      slot_local t P' ->
      (forall a, slot_local t (Q' a)) ->
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ lift_assert P }} Vis m k {{ fun a => lift_assert (Q a) }}.
    Proof.
      intros Herror HinvP HinvQ HstableP HstableQ Hpinv Hpret Hnext HPI
        HlocP HlocQ.
      eapply SetLogic.provable_vis_safe with
        (P' := lift_assert P') (Q' := fun a => lift_assert (Q' a)).
      - intros s HP. eapply lift_no_error; [exact Herror|exact HP].
      - intros s HP. eapply lift_impl; [exact HinvP|exact HP].
      - intros a s HQ. eapply lift_impl; [exact (HinvQ a)|exact HQ].
      - apply lift_stable; exact HstableP.
      - intros a. apply lift_stable; exact (HstableQ a).
      - apply lift_pupdate.
        + exact HPI.
        + exact HinvP.
        + exact HlocP.
        + exact Hpinv.
      - intros ret. apply lift_pupdate.
        + exact HinvP.
        + exact (HinvQ ret).
        + exact (HlocQ ret).
        + exact (Hpret ret).
      - exact Hnext.
    Qed.

    Lemma singleton_provable_ret_safe {X} t (a : X)
        (P : assertion) (Q : X -> assertion) :
      (⊨ P ==>> Q a) ->
      (⊨ Q a ==>> source_I) ->
      AssertionsSingle.A.Stable (source_R t) source_I (Q a) ->
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ lift_assert P }} Ret a {{ fun r => lift_assert (Q r) }}.
    Proof.
      intros HP Hinv Hstable.
      eapply SetLogic.provable_ret_safe.
      - intros s Hpre. eapply lift_impl; [exact HP|exact Hpre].
      - intros s Hpost. eapply lift_impl; [exact Hinv|exact Hpost].
      - apply lift_stable; exact Hstable.
    Qed.

    Ltac singleton_ret_safe := eapply singleton_provable_ret_safe.

    Lemma valid_rg observer :
      RGISimulationSet.RGISimulation.ValidRGI
        (R observer) (G observer) SI observer.
    Proof. apply lift_valid_rgi. Qed.

    Lemma parallel_compatible actor observer :
      actor <> observer -> forall w w',
      (G actor w w' \/
       (AssertionsSet.GINV actor w w' \/ AssertionsSet.GRET actor w w') \/
       AssertionsSet.A.GId w w') /\ SI w ->
      R observer w w'.
    Proof. apply lift_parallel_compat. Qed.


    (** * Method-level assertions *)

    Definition Active (t : tid) (m : Sig.op (li_sig F)) : assertion :=
      source_I //\\ ALin t (ls_inv m).

    Definition Completed (t : tid) (m : Sig.op (li_sig F))
        (ret : Sig.ar m) : assertion :=
      source_I //\\ ALin t (ls_linr m ret).

    Definition SActive t m := lift_assert (Active t m).
    Definition SCompleted t m ret := lift_assert (Completed t m ret).

    Definition ActiveOwned (t : tid) (m : Sig.op (li_sig F)) : assertion :=
      fun w => Active t m w /\ t = owner.

    Definition SActiveOwned t m := lift_assert (ActiveOwned t m).

    (** Pure facts about the heap and the log. *)
    Definition SkipsLog (p : Ptr) : assertion :=
      fun w => skips (heap_of w) (log_of w) p.

    Definition SkipsAfter (l : Addr) (p : Ptr) : assertion :=
      fun w => forall a b, log_of w = a ++ l :: b -> skips (heap_of w) b p.

    Definition NodeTaken (l : Addr) : assertion :=
      fun w => taken_at (heap_of w) l = true.

    Definition NodeVal (l : Addr) (v : A) : assertion :=
      fun w => exists ts taken nx,
        heap_of w l = Some (pair (pair (pair v ts) taken) nx).

    (** Insert: the owner has read the register, walked to [p], and
        allocated its private node. *)
    Definition InsertRead (t : tid) (v : A) (q : Ptr * nat) : assertion :=
      ActiveOwned t (linsert v) //\\ CountIs (snd q) //\\ SkipsLog (fst q).

    Definition InsertWalked (t : tid) (v : A) (q : Ptr * nat) (p : Ptr) :
        assertion :=
      InsertRead t v q //\\ SkipsLog p.

    Definition InsertAllocated (t : tid) (v : A) (q : Ptr * nat) (p : Ptr)
        (l : Addr) : assertion :=
      fun w => InsertWalked t v q p w /\ NodeUndefined l w /\
        heap_of w l = Some (pair (pair (pair v TSTop) false) p).

    (** TryRemove: the taker holds the successful response and knows a
        pointer that skips the suffix after its node. *)
    Definition TakerCore (t : tid) (l : Addr) : assertion :=
      Completed t (ltryRemove l) true //\\ NodeDefined l.

    Definition TakerAt (t : tid) (l : Addr) (p : Ptr) : assertion :=
      TakerCore t l //\\ SkipsAfter l p.

    (** Subsequences, used to relate the saved snapshot to the log. *)
    Inductive subseq : list Addr -> list Addr -> Prop :=
    | subseq_nil : subseq nil nil
    | subseq_keep x xs ys : subseq xs ys -> subseq (x :: xs) (x :: ys)
    | subseq_skip x xs ys : subseq xs ys -> subseq xs (x :: ys).

    Lemma subseq_in xs ys x : subseq xs ys -> In x xs -> In x ys.
    Proof.
      intros H. induction H; simpl; intros Hin; [contradiction| |].
      - destruct Hin as [<-|Hin]; [now left|right; auto].
      - right. auto.
    Qed.

    Lemma subseq_filter (f : Addr -> bool) ys : subseq (List.filter f ys) ys.
    Proof.
      induction ys as [|y ys IH]; simpl; [constructor|].
      destruct (f y); [apply subseq_keep|apply subseq_skip]; exact IH.
    Qed.

    Lemma subseq_app_split xs a b :
      subseq xs (a ++ b) ->
      exists xa xb, xs = xa ++ xb /\ subseq xa a /\ subseq xb b.
    Proof.
      revert xs. induction a as [|y a IH]; intros xs H; simpl in H.
      - exists nil, xs. split; [reflexivity|]. split; [constructor|exact H].
      - inversion H; subst.
        + destruct (IH _ H2) as (xa & xb & -> & Ha & Hb).
          exists (y :: xa), xb. split; [reflexivity|]. split; [constructor; exact Ha|exact Hb].
        + destruct (IH _ H2) as (xa & xb & -> & Ha & Hb).
          exists xa, xb. split; [reflexivity|]. split; [constructor; exact Ha|exact Hb].
    Qed.

    Lemma subseq_cons_inv x xs ys :
      subseq xs (x :: ys) ->
      (exists xs', xs = x :: xs' /\ subseq xs' ys) \/ subseq xs ys.
    Proof.
      intros H. inversion H; subst; [left; eauto|right; assumption].
    Qed.

    Lemma subseq_notin xs ys x :
      subseq xs ys -> ~ In x ys -> ~ In x xs.
    Proof. intros H Hn Hin. apply Hn. eapply subseq_in; eauto. Qed.

    (** Splitting a saved snapshot around a live node of the log: the
        saved nodes before it come from the (dead) prefix. *)
    Lemma subseq_around xs dead l tl :
      NoDup (dead ++ l :: tl) ->
      subseq xs (dead ++ l :: tl) -> In l xs ->
      exists s1 s2, xs = s1 ++ l :: s2 /\ (forall x, In x s1 -> In x dead).
    Proof.
      intros Hnd Hsub Hin.
      destruct (subseq_app_split _ _ _ Hsub) as (xa & xb & -> & Ha & Hb).
      pose proof (NoDup_remove_2 _ _ _ Hnd) as Hnotin.
      assert (Hla : ~ In l xa).
      { eapply subseq_notin; [exact Ha|]. intro H. apply Hnotin. apply in_or_app. now left. }
      destruct (subseq_cons_inv _ _ _ Hb) as [[xb' [-> Hb']] | Hb'].
      - exists xa, xb'. split; [reflexivity|]. intros x Hx. eapply subseq_in; eauto.
      - exfalso. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (Hla Hin)|].
        assert (Hltl : ~ In l tl).
        { intro H. apply Hnotin. apply in_or_app. now right. }
        apply Hltl. eapply subseq_in; eauto.
    Qed.

    Lemma split_unique (l : Addr) a b a' b' :
      NoDup (a ++ l :: b) -> a ++ l :: b = a' ++ l :: b' -> a = a' /\ b = b'.
    Proof.
      revert a'. induction a as [|x a IH]; intros a' Hnd Heq; simpl in *.
      - destruct a' as [|y a']; simpl in Heq.
        + inversion Heq; subst. auto.
        + inversion Heq; subst. inversion Hnd; subst.
          match goal with
          | H : ~ In _ _ |- _ => exfalso; apply H; apply in_or_app; right; now left
          end.
      - destruct a' as [|y a']; simpl in Heq.
        + inversion Heq; subst. inversion Hnd; subst.
          match goal with
          | H : ~ In _ _ |- _ => exfalso; apply H; apply in_or_app; right; now left
          end.
        + inversion Heq; subst. inversion Hnd; subst.
          match goal with
          | Hnd' : NoDup (?a0 ++ _ :: ?b0), Hrest : ?a0 ++ _ :: ?b0 = _ ++ _ :: _ |- _ =>
              destruct (IH _ Hnd' Hrest) as [-> ->]; auto
          end.
    Qed.

    (** The scan invariant of [getTop]: a snapshot [saved] of the live
        nodes at the snapshot time, taken over the log [logS] (a suffix of
        the current log of the recorded length), a prefix of [logS] whose
        nodes are all dead now, and a cursor that skips into the rest. *)
    Definition ScanCore (t : tid) (count : nat) (saved logS prefix suffix : list Addr)
        (p : Ptr) : assertion :=
      fun w =>
        source_I w /\
        ALin t (ls_lini (@lgetTop A)) w /\
        TMap.find t (snapshot (payload_of w)) = Some (pair saved count) /\
        logS = prefix ++ suffix /\
        (exists extra, log_of w = extra ++ logS) /\
        length logS = count /\
        (forall x, In x prefix -> live_at (heap_of w) x = false) /\
        skips (heap_of w) suffix p /\
        subseq saved logS /\
        (forall x, In x logS -> live_at (heap_of w) x = true -> In x saved).

    Definition GetTopScan (t : tid) (count : nat) (p : Ptr) : assertion :=
      fun w => exists saved logS prefix suffix,
        ScanCore t count saved logS prefix suffix p w.

    Definition SGetTopScan t count p := lift_assert (GetTopScan t count p).

    Definition GetTopLoop (t : tid) (count : nat) (p : Ptr) : assertion :=
      match p with
      | None => Completed t (@lgetTop A) (@inr (@LNode A) nat count)
      | Some _ => GetTopScan t count p
      end.

    Definition SGetTopLoop t count p := lift_assert (GetTopLoop t count p).

    (** What the final CAS of [getTop] needs: the returned node sits in a
        suffix [logS] of the log of the recorded length, after a prefix of
        dead nodes. *)
    Definition DoneData (count : nat) (l : Addr) : assertion :=
      fun w => exists logS prefix tl,
        logS = prefix ++ l :: tl /\
        (exists extra, log_of w = extra ++ logS) /\
        length logS = count /\
        (forall x, In x prefix -> live_at (heap_of w) x = false).

    Definition GetTopDone (t : tid) (count : nat) (l : Addr) (v : A) (ts : TS) :
        assertion :=
      Completed t (@lgetTop A) (@inl (@LNode A) nat (pair (pair v ts) l)) //\\
      DoneData count l.

    Definition GetTopResult (t : tid) (count : nat) (ret : @LNode A + nat) :
        assertion :=
      match ret with
      | inl (pair (pair v ts) l) => GetTopDone t count l v ts
      | inr c => Completed t (@lgetTop A) (@inr (@LNode A) nat c)
      end.

    Definition GetTopBodyPost (t : tid) (count : nat)
        (r : Ptr + (@LNode A + nat)) : assertion :=
      match r with
      | inl p => GetTopLoop t count p
      | inr ret => GetTopResult t count ret
      end.

    Lemma active_entails_I t m :
      ⊨ Active t m ==>> source_I.
    Proof. apply ConjLeftImpl. apply ImplRefl. Qed.

    Lemma completed_entails_I t m ret :
      ⊨ Completed t m ret ==>> source_I.
    Proof. apply ConjLeftImpl. apply ImplRefl. Qed.

    Lemma active_stable t m :
      AssertionsSingle.A.Stable (source_R t) source_I (Active t m).
    Proof.
      unfold AssertionsSingle.A.Stable, Active.
      intros out [[pre [[HIpre Hlin] HR]] HIout].
      split; [exact HIout|].
      unfold ALin in *. rewrite <- (source_R_token t _ _ HR).
      exact Hlin.
    Qed.

    Lemma completed_stable t m ret :
      AssertionsSingle.A.Stable (source_R t) source_I
        (Completed t m ret).
    Proof.
      unfold AssertionsSingle.A.Stable, Completed.
      intros out [[pre [[HIpre Hlin] HR]] HIout].
      split; [exact HIout|].
      unfold ALin in *. rewrite <- (source_R_token t _ _ HR).
      exact Hlin.
    Qed.

    Lemma active_owned_entails_I t m :
      ⊨ ActiveOwned t m ==>> source_I.
    Proof. intros w [Hactive Howner]. now apply active_entails_I in Hactive. Qed.

    Lemma active_owned_stable t m :
      AssertionsSingle.A.Stable (source_R t) source_I (ActiveOwned t m).
    Proof.
      unfold AssertionsSingle.A.Stable, ActiveOwned.
      intros out [[pre [[Hactive Howner] HR]] HIout].
      split; [|exact Howner].
      eapply active_stable. split; [exists pre; eauto|exact HIout].
    Qed.

    (** Stability of the pure facts. *)
    Lemma skips_log_stable_owner w w' p :
      source_R owner w w' -> SkipsLog p w -> SkipsLog p w'.
    Proof.
      intros HR H. unfold SkipsLog in *.
      rewrite (source_R_owner_preserves_log _ _ HR).
      eapply skips_mono; [|exact H]. eapply source_R_taken; exact HR.
    Qed.

    Lemma skips_after_stable t w w' l p :
      source_R t w w' -> source_I w' -> In l (log_of w) ->
      SkipsAfter l p w -> SkipsAfter l p w'.
    Proof.
      intros HR HI' Hin H a' b' Hlog'.
      destruct (source_R_log _ _ _ HR) as [extra Hlog].
      apply in_split in Hin. destruct Hin as [a [b Hab]].
      pose proof (H a b Hab) as Hsk.
      assert (Heq : (extra ++ a) ++ l :: b = a' ++ l :: b').
      { rewrite <- app_assoc, <- Hab, <- Hlog. exact Hlog'. }
      assert (Hnd : NoDup (log_of w')).
      { destruct (source_I_rep _ HI') as (Hvalid & _). exact (proj1 Hvalid). }
      rewrite Hlog' in Hnd. rewrite <- Heq in Hnd.
      destruct (split_unique _ _ _ _ _ Hnd Heq) as [_ <-].
      eapply skips_mono; [|exact Hsk]. eapply source_R_taken; exact HR.
    Qed.

    Lemma node_taken_stable t w w' l :
      source_R t w w' -> NodeTaken l w -> NodeTaken l w'.
    Proof.
      intros HR H. unfold NodeTaken in *. eapply source_R_taken; eauto.
    Qed.

    Lemma node_val_stable t w w' l v :
      source_R t w w' -> NodeVal l v w -> NodeVal l v w'.
    Proof.
      intros HR (ts & tk & nx & H).
      destruct (source_R_value _ _ _ _ _ _ _ _ HR H) as (ts' & tk' & nx' & H').
      exists ts', tk', nx'. exact H'.
    Qed.

    Lemma count_is_stable_owner w w' c :
      source_R owner w w' -> CountIs c w -> CountIs c w'.
    Proof.
      intros HR H. unfold CountIs in *.
      rewrite <- (source_R_owner_preserves_count _ _ HR). exact H.
    Qed.

    Lemma insert_read_entails_I t v q :
      ⊨ InsertRead t v q ==>> source_I.
    Proof. intros w [Howned _]. eapply active_owned_entails_I; eauto. Qed.

    Lemma insert_read_stable t v q :
      AssertionsSingle.A.Stable (source_R t) source_I (InsertRead t v q).
    Proof.
      unfold AssertionsSingle.A.Stable, InsertRead.
      intros out [[pre [[Howned [Hcount Hsk]] HR]] HIout].
      assert (Howner : t = owner) by exact (proj2 Howned).
      subst t. split; [|split].
      - eapply active_owned_stable. split; [exists pre; eauto|exact HIout].
      - eapply count_is_stable_owner; eauto.
      - eapply skips_log_stable_owner; eauto.
    Qed.

    Lemma insert_walked_entails_I t v q p :
      ⊨ InsertWalked t v q p ==>> source_I.
    Proof. intros w [Hread _]. eapply insert_read_entails_I; eauto. Qed.

    Lemma insert_walked_stable t v q p :
      AssertionsSingle.A.Stable (source_R t) source_I (InsertWalked t v q p).
    Proof.
      unfold AssertionsSingle.A.Stable, InsertWalked.
      intros out [[pre [[Hread Hsk] HR]] HIout].
      assert (Howner : t = owner) by exact (proj2 (proj1 Hread)).
      subst t. split.
      - eapply insert_read_stable. split; [exists pre; eauto|exact HIout].
      - eapply skips_log_stable_owner; eauto.
    Qed.

    Lemma insert_allocated_entails_I t v q p l :
      ⊨ InsertAllocated t v q p l ==>> source_I.
    Proof.
      intros w [Hwalked [Hundefined Hcell]].
      apply insert_walked_entails_I in Hwalked. exact Hwalked.
    Qed.

    Lemma insert_allocated_stable t v q p l :
      AssertionsSingle.A.Stable (source_R t) source_I
        (InsertAllocated t v q p l).
    Proof.
      unfold AssertionsSingle.A.Stable, InsertAllocated.
      intros out [[pre [[Hwalked [Hundefined Hcell]] HR]] HIout].
      assert (Howner : t = owner) by exact (proj2 (proj1 (proj1 Hwalked))).
      subst t. split.
      - eapply insert_walked_stable. split; [exists pre; eauto|exact HIout].
      - split.
        + eapply source_R_owner_preserves_undefined; eauto.
        + rewrite <- (source_R_owner_preserves_private _ _ l HR Hundefined).
          exact Hcell.
    Qed.

    Lemma taker_core_entails_I t l :
      ⊨ TakerCore t l ==>> source_I.
    Proof. intros w [[HI _] _]. exact HI. Qed.

    Lemma taker_core_stable t l :
      AssertionsSingle.A.Stable (source_R t) source_I (TakerCore t l).
    Proof.
      unfold AssertionsSingle.A.Stable, TakerCore.
      intros out [[pre [[Hcomp Hdef] HR]] HIout]. split.
      - eapply completed_stable. split; [exists pre; eauto|exact HIout].
      - eapply source_R_preserves_defined; eauto.
    Qed.

    Lemma taker_at_entails_I t l p :
      ⊨ TakerAt t l p ==>> source_I.
    Proof. intros w [Hcore _]. eapply taker_core_entails_I; eauto. Qed.

    Lemma taker_at_stable t l p :
      AssertionsSingle.A.Stable (source_R t) source_I (TakerAt t l p).
    Proof.
      unfold AssertionsSingle.A.Stable, TakerAt.
      intros out [[pre [[Hcore Hsk] HR]] HIout]. split.
      - eapply taker_core_stable. split; [exists pre; eauto|exact HIout].
      - eapply skips_after_stable; [exact HR|exact HIout| |exact Hsk].
        eapply source_I_defined_in_log; [exact (proj1 (proj1 Hcore))|exact (proj2 Hcore) ].
    Qed.

    Lemma scan_core_entails_I t count saved logS prefix suffix p :
      ⊨ ScanCore t count saved logS prefix suffix p ==>> source_I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma getTop_scan_entails_I t count p :
      ⊨ GetTopScan t count p ==>> source_I.
    Proof. intros w (saved & logS & prefix & suffix & HI & _). exact HI. Qed.

    Lemma scan_core_log_defined t count saved logS prefix suffix p w x :
      ScanCore t count saved logS prefix suffix p w -> In x logS ->
      heap_of w x <> None.
    Proof.
      intros (HI & _ & _ & _ & [extra Hlog] & _) Hin.
      eapply represents_defined; [eapply source_I_rep; exact HI|].
      rewrite Hlog. apply in_or_app. right. exact Hin.
    Qed.

    Lemma scan_core_stable t count saved logS prefix suffix p :
      AssertionsSingle.A.Stable (source_R t) source_I
        (ScanCore t count saved logS prefix suffix p).
    Proof.
      unfold AssertionsSingle.A.Stable.
      intros out [[pre [Hscan HR]] HIout].
      pose proof Hscan as
        (HIpre & Hlin & Hsnap & HlogS & [extra Hlog] & Hlen & Hdead & Hsk & Hsub & Hlive).
      split; [exact HIout|]. split.
      { pose proof (source_R_token t _ _ HR) as Htoken.
        unfold ALin in Hlin |- *.
        etransitivity; [symmetry; exact Htoken|exact Hlin]. }
      split.
      { destruct HR as [[actor [Hactor HG]]|Hadmin].
        - destruct HG as (_ & _ & _ & _ & _ & Hsnaps & _).
          unfold payload_of. rewrite <- (Hsnaps t (fun H => Hactor (eq_sym H))). exact Hsnap.
        - pose proof
            (AssertionsSingle.linearization_rely_observer_view t _ _ Hadmin)
            as [Hσ [Hρ Htoken]].
          unfold payload_of, ctrl_of in *. rewrite <- Hρ. exact Hsnap. }
      split; [exact HlogS|].
      split.
      { destruct (source_R_log _ _ _ HR) as [extra' Hlog'].
        exists (extra' ++ extra). rewrite Hlog', Hlog, app_assoc. reflexivity. }
      split; [exact Hlen|].
      split.
      { intros x Hx. eapply source_R_dead; [exact HR| |apply Hdead; exact Hx].
        eapply scan_core_log_defined; [exact Hscan|].
        rewrite HlogS. apply in_or_app. now left. }
      split.
      { eapply skips_mono; [|exact Hsk]. eapply source_R_taken; exact HR. }
      split; [exact Hsub|].
      intros x Hx Hlivex. apply Hlive; [exact Hx|].
      eapply source_R_live_imp; [exact HR| |exact Hlivex].
      eapply scan_core_log_defined; [exact Hscan|exact Hx].
    Qed.

    Lemma getTop_scan_stable t count p :
      AssertionsSingle.A.Stable (source_R t) source_I (GetTopScan t count p).
    Proof.
      unfold AssertionsSingle.A.Stable.
      intros out [[pre [ (saved & logS & prefix & suffix & Hscan) HR]] HIout].
      exists saved, logS, prefix, suffix.
      eapply scan_core_stable. split; [exists pre; eauto|exact HIout].
    Qed.

    Lemma getTop_loop_entails_I t count p :
      ⊨ GetTopLoop t count p ==>> source_I.
    Proof.
      destruct p; simpl.
      - apply getTop_scan_entails_I.
      - apply completed_entails_I.
    Qed.

    Lemma getTop_loop_stable t count p :
      AssertionsSingle.A.Stable (source_R t) source_I
        (GetTopLoop t count p).
    Proof.
      destruct p; simpl.
      - apply getTop_scan_stable.
      - apply completed_stable.
    Qed.

    Lemma done_data_stable t w w' count l :
      source_R t w w' -> source_I w -> DoneData count l w -> DoneData count l w'.
    Proof.
      intros HR HI (logS & prefix & tl & HlogS & [extra Hlog] & Hlen & Hdead).
      exists logS, prefix, tl. split; [exact HlogS|].
      destruct (source_R_log _ _ _ HR) as [extra' Hlog'].
      split; [exists (extra' ++ extra); rewrite Hlog', Hlog, app_assoc; reflexivity|].
      split; [exact Hlen|].
      intros x Hx. eapply source_R_dead; [exact HR| |apply Hdead; exact Hx].
      eapply represents_defined; [eapply source_I_rep; exact HI|].
      rewrite Hlog, HlogS. apply in_or_app. right. apply in_or_app. now left.
    Qed.

    Lemma getTop_done_entails_I t count l v ts :
      ⊨ GetTopDone t count l v ts ==>> source_I.
    Proof. intros w [[HI _] _]. exact HI. Qed.

    Lemma getTop_done_stable t count l v ts :
      AssertionsSingle.A.Stable (source_R t) source_I (GetTopDone t count l v ts).
    Proof.
      unfold AssertionsSingle.A.Stable, GetTopDone.
      intros out [[pre [[Hcomp Hdata] HR]] HIout]. split.
      - eapply completed_stable. split; [exists pre; eauto|exact HIout].
      - eapply done_data_stable; [exact HR|exact (proj1 Hcomp)|exact Hdata].
    Qed.

    Lemma getTop_result_entails_I t count ret :
      ⊨ GetTopResult t count ret ==>> source_I.
    Proof.
      destruct ret as [[[v ts] l]|c]; simpl.
      - apply getTop_done_entails_I.
      - apply completed_entails_I.
    Qed.

    Lemma getTop_result_stable t count ret :
      AssertionsSingle.A.Stable (source_R t) source_I (GetTopResult t count ret).
    Proof.
      destruct ret as [[[v ts] l]|c]; simpl.
      - apply getTop_done_stable.
      - apply completed_stable.
    Qed.

    Lemma getTop_body_post_entails_I t count r :
      ⊨ GetTopBodyPost t count r ==>> source_I.
    Proof.
      destruct r as [p|ret]; simpl.
      - apply getTop_loop_entails_I.
      - apply getTop_result_entails_I.
    Qed.

    Lemma getTop_body_post_stable t count r :
      AssertionsSingle.A.Stable (source_R t) source_I (GetTopBodyPost t count r).
    Proof.
      destruct r as [p|ret]; simpl.
      - apply getTop_loop_stable.
      - apply getTop_result_stable.
    Qed.

    (** The snapshot of the getTop: actual snapshot from the scan data. *)
    Definition ActiveDefined (t : tid) (m : Sig.op (li_sig F))
        (l : Addr) : assertion := Active t m //\\ NodeDefined l.

    Definition SActiveDefined t m l := lift_assert (ActiveDefined t m l).

    Lemma active_defined_entails_I t m l :
      ⊨ ActiveDefined t m l ==>> source_I.
    Proof. apply ConjLeftImpl, active_entails_I. Qed.

    Lemma active_defined_stable t m l :
      AssertionsSingle.A.Stable (source_R t) source_I
        (ActiveDefined t m l).
    Proof.
      unfold AssertionsSingle.A.Stable, ActiveDefined.
      intros out [[pre [[[HIpre Hlin] Hdefined] HR]] HIout].
      split.
      - split; [exact HIout|].
        unfold ALin in *. rewrite <- (source_R_token t _ _ HR). exact Hlin.
      - eapply source_R_preserves_defined; eauto.
    Qed.

    Definition ActiveOwnedDefined (t : tid) (m : Sig.op (li_sig F))
        (l : Addr) : assertion :=
      fun w => ActiveDefined t m l w /\ t = owner.

    Definition SActiveOwnedDefined t m l :=
      lift_assert (ActiveOwnedDefined t m l).

    Lemma active_owned_defined_entails_I t m l :
      ⊨ ActiveOwnedDefined t m l ==>> source_I.
    Proof. intros w [H _]. apply active_defined_entails_I in H. exact H. Qed.

    Lemma active_owned_defined_stable t m l :
      AssertionsSingle.A.Stable (source_R t) source_I
        (ActiveOwnedDefined t m l).
    Proof.
      unfold AssertionsSingle.A.Stable, ActiveOwnedDefined.
      intros out [[pre [[Hactive Howner] HR]] HIout].
      destruct Hactive as [[HIpre Hlin] Hdefined].
      split; [|exact Howner]. split.
      - split; [exact HIout|].
        unfold ALin in *. rewrite <- (source_R_token t _ _ HR). exact Hlin.
      - eapply source_R_preserves_defined; eauto.
    Qed.

    (** *** Slot locality of the method assertions *)

    Lemma slot_local_conj q (P Q : assertion) :
      slot_local q P -> slot_local q Q -> slot_local q (P //\\ Q).
    Proof.
      intros HP HQ x y [Hx1 Hx2] HI Hag. split; [eapply HP|eapply HQ]; eauto.
    Qed.

    Lemma slot_local_source_I q : slot_local q source_I.
    Proof. intros x y _ HI _. exact HI. Qed.

    Lemma slot_local_ALin q ls : slot_local q (ALin q ls).
    Proof.
      intros x y Hx HI [_ [_ [_ Ht]]]. unfold ALin in *. unfold slot_token in Ht.
      rewrite <- Ht. exact Hx.
    Qed.

    Lemma slot_local_active t m : slot_local t (Active t m).
    Proof.
      unfold Active. apply slot_local_conj;
        [apply slot_local_source_I | apply slot_local_ALin].
    Qed.

    Lemma slot_local_completed t m ret : slot_local t (Completed t m ret).
    Proof.
      unfold Completed. apply slot_local_conj;
        [apply slot_local_source_I | apply slot_local_ALin].
    Qed.

    Lemma slot_local_active_owned t m : slot_local t (ActiveOwned t m).
    Proof.
      intros x y [Hx Ho] HI Hag. split; [|exact Ho].
      eapply slot_local_active; eauto.
    Qed.

    Lemma slot_agree_nodes q x y :
      source_I x -> source_I y -> slot_agree q x y ->
      nodes (payload_of x) = nodes (payload_of y).
    Proof.
      intros HIx HIy [Hσ [Hl _]].
      exact (proj1 (proj2 (source_I_payload_determined _ _ HIx HIy Hσ Hl))).
    Qed.

    Lemma slot_agree_heap q x y :
      slot_agree q x y -> heap_of x = heap_of y.
    Proof. intros [Hσ _]. unfold heap_of. rewrite Hσ. reflexivity. Qed.

    Lemma slot_agree_reg q x y :
      slot_agree q x y -> reg_of x = reg_of y.
    Proof. intros [Hσ _]. unfold reg_of. rewrite Hσ. reflexivity. Qed.

    Lemma slot_agree_log q x y :
      slot_agree q x y -> log_of x = log_of y.
    Proof. intros [_ [Hl _]]. exact Hl. Qed.

    Lemma slot_local_active_defined t m l :
      slot_local t (ActiveDefined t m l).
    Proof.
      intros x y [Hact [a Hnode]] HI Hag.
      pose proof (proj1 Hact) as HIx.
      split; [eapply slot_local_active; eauto|].
      exists a. pose proof (slot_agree_nodes t x y HIx HI Hag) as Hn.
      rewrite <- Hn. exact Hnode.
    Qed.

    Lemma slot_local_active_owned_defined t m l :
      slot_local t (ActiveOwnedDefined t m l).
    Proof.
      intros x y [Hact Ho] HI Hag. split; [|exact Ho].
      eapply slot_local_active_defined; eauto.
    Qed.

    Lemma slot_local_count_is q c : slot_local q (CountIs c).
    Proof.
      intros x y Hx _ Hag. unfold CountIs in *. rewrite <- (slot_agree_reg q x y Hag).
      exact Hx.
    Qed.

    Lemma slot_local_skips_log q p : slot_local q (SkipsLog p).
    Proof.
      intros x y Hx _ Hag. unfold SkipsLog in *.
      rewrite <- (slot_agree_heap q x y Hag), <- (slot_agree_log q x y Hag). exact Hx.
    Qed.

    Lemma slot_local_skips_after q l p : slot_local q (SkipsAfter l p).
    Proof.
      intros x y Hx _ Hag. unfold SkipsAfter in *.
      rewrite <- (slot_agree_heap q x y Hag), <- (slot_agree_log q x y Hag). exact Hx.
    Qed.

    Lemma slot_local_node_taken q l : slot_local q (NodeTaken l).
    Proof.
      intros x y Hx _ Hag. unfold NodeTaken in *.
      rewrite <- (slot_agree_heap q x y Hag). exact Hx.
    Qed.

    Lemma slot_local_node_val q l v : slot_local q (NodeVal l v).
    Proof.
      intros x y Hx _ Hag. unfold NodeVal in *.
      rewrite <- (slot_agree_heap q x y Hag). exact Hx.
    Qed.

    Lemma slot_local_insert_read t v q : slot_local t (InsertRead t v q).
    Proof.
      unfold InsertRead. apply slot_local_conj.
      - apply slot_local_active_owned.
      - apply slot_local_conj; [apply slot_local_count_is | apply slot_local_skips_log].
    Qed.

    Lemma slot_local_insert_walked t v q p : slot_local t (InsertWalked t v q p).
    Proof.
      unfold InsertWalked. apply slot_local_conj;
        [apply slot_local_insert_read | apply slot_local_skips_log].
    Qed.

    Lemma slot_local_insert_allocated t v q p l :
      slot_local t (InsertAllocated t v q p l).
    Proof.
      intros x y [Hwalked [Hundef Hcell]] HI Hag.
      pose proof (insert_walked_entails_I _ _ _ _ _ Hwalked) as HIx.
      split; [eapply slot_local_insert_walked; eauto|].
      split.
      - unfold NodeUndefined in *.
        pose proof (slot_agree_nodes t x y HIx HI Hag) as Hn.
        rewrite <- Hn. exact Hundef.
      - rewrite <- (slot_agree_heap t x y Hag). exact Hcell.
    Qed.

    Lemma slot_local_taker_core t l : slot_local t (TakerCore t l).
    Proof.
      intros x y [Hcomp [a Hnode]] HI Hag.
      pose proof (proj1 Hcomp) as HIx.
      split; [eapply slot_local_completed; eauto|].
      exists a. pose proof (slot_agree_nodes t x y HIx HI Hag) as Hn.
      rewrite <- Hn. exact Hnode.
    Qed.

    Lemma slot_local_taker_at t l p : slot_local t (TakerAt t l p).
    Proof.
      unfold TakerAt. apply slot_local_conj;
        [apply slot_local_taker_core | apply slot_local_skips_after].
    Qed.

    Lemma slot_local_scan_core t count saved logS prefix suffix p :
      slot_local t (ScanCore t count saved logS prefix suffix p).
    Proof.
      intros x y
        (HIx & Hlin & Hsnap & HlogS & Hlog & Hlen & Hdead & Hsk & Hsub & Hlive)
        HIy Hag.
      pose proof Hag as [Hσ [Hl [Hs Ht]]].
      pose proof (slot_agree_heap t x y Hag) as Hheap.
      split; [exact HIy|].
      split; [eapply slot_local_ALin; eauto|].
      split.
      { unfold slot_snapshot, payload_of in Hs. unfold payload_of.
        rewrite <- Hs. exact Hsnap. }
      split; [exact HlogS|].
      split; [rewrite <- Hl; exact Hlog|].
      split; [exact Hlen|].
      split; [rewrite <- Hheap; exact Hdead|].
      split; [rewrite <- Hheap; exact Hsk|].
      split; [exact Hsub|].
      rewrite <- Hheap. exact Hlive.
    Qed.

    Lemma slot_local_getTop_scan t count p :
      slot_local t (GetTopScan t count p).
    Proof.
      intros x y (saved & logS & prefix & suffix & Hscan) HI Hag.
      exists saved, logS, prefix, suffix.
      eapply slot_local_scan_core; eauto.
    Qed.

    Lemma slot_local_getTop_loop t count p :
      slot_local t (GetTopLoop t count p).
    Proof.
      destruct p; simpl;
        [apply slot_local_getTop_scan | apply slot_local_completed].
    Qed.

    Lemma slot_local_done_data q count l : slot_local q (DoneData count l).
    Proof.
      intros x y (logS & prefix & tl & HlogS & Hlog & Hlen & Hdead) _ Hag.
      exists logS, prefix, tl. split; [exact HlogS|].
      split; [rewrite <- (slot_agree_log q x y Hag); exact Hlog|].
      split; [exact Hlen|].
      rewrite <- (slot_agree_heap q x y Hag). exact Hdead.
    Qed.

    Lemma slot_local_getTop_done t count l v ts :
      slot_local t (GetTopDone t count l v ts).
    Proof.
      unfold GetTopDone. apply slot_local_conj;
        [apply slot_local_completed | apply slot_local_done_data].
    Qed.

    Lemma slot_local_getTop_result t count ret :
      slot_local t (GetTopResult t count ret).
    Proof.
      destruct ret as [[[v ts] l]|c]; simpl;
        [apply slot_local_getTop_done | apply slot_local_completed].
    Qed.

    Lemma slot_local_getTop_body_post t count r :
      slot_local t (GetTopBodyPost t count r).
    Proof.
      destruct r as [p|ret]; simpl;
        [apply slot_local_getTop_loop | apply slot_local_getTop_result].
    Qed.

    (** *** Snapshot consistency bookkeeping *)

    Lemma snapshot_consistent_add_inv s pi t m :
      snapshot_consistent s pi -> TMap.find t pi = None ->
      snapshot_consistent s (TMap.add t (ls_inv m) pi).
    Proof.
      intros Hconsistent Hnone q.
      destruct (PositiveMap.E.eq_dec q t) as [->|Hneq].
      - rewrite TMap.gss. split.
        + intros [saved Hsaved].
          pose proof
            (proj1 (Hconsistent t) (ex_intro _ saved Hsaved)) as Hbad.
          rewrite Hnone in Hbad. discriminate.
        + discriminate.
      - rewrite TMap.gso by exact Hneq. apply Hconsistent.
    Qed.

    Lemma snapshot_consistent_remove_linr s pi t m ret :
      snapshot_consistent s pi ->
      TMap.find t pi = Some (ls_linr m ret) ->
      snapshot_consistent s (TMap.remove t pi).
    Proof.
      intros Hconsistent Hlin q.
      destruct (PositiveMap.E.eq_dec q t) as [->|Hneq].
      - rewrite TMap.grs. split.
        + intros [saved Hsaved].
          pose proof (proj1 (Hconsistent t) (ex_intro _ saved Hsaved)) as Hbad.
          rewrite Hlin in Hbad. discriminate.
        + discriminate.
      - rewrite TMap.gro by exact Hneq. apply Hconsistent.
    Qed.

    Lemma snapshot_consistent_atomic s pi t m ret :
      snapshot_consistent s pi ->
      TMap.find t pi = Some (ls_inv m) ->
      snapshot_consistent s
        (TMap.add t (ls_linr m ret) (TMap.add t (ls_lini m) pi)).
    Proof.
      intros Hconsistent Hlin q.
      destruct (PositiveMap.E.eq_dec q t) as [->|Hneq].
      - repeat rewrite TMap.gss. split.
        + intros [saved Hsaved].
          pose proof
            (proj1 (Hconsistent t) (ex_intro _ saved Hsaved)) as Hbad.
          rewrite Hlin in Hbad. discriminate.
        + discriminate.
      - repeat rewrite TMap.gso by exact Hneq. apply Hconsistent.
    Qed.

    Lemma snapshot_consistent_getTop_inv s pi t :
      snapshot_consistent s pi ->
      TMap.find t pi = Some (ls_inv (@lgetTop A)) ->
      snapshot_consistent (start_snapshot t s)
        (TMap.add t (ls_lini (@lgetTop A)) pi).
    Proof.
      intros Hconsistent Hlin q.
      destruct (PositiveMap.E.eq_dec q t) as [->|Hneq].
      - simpl. rewrite TMap.gss, TMap.gss. split; [intros _; reflexivity|].
        intros _. eexists. reflexivity.
      - simpl. repeat rewrite TMap.gso by exact Hneq. apply Hconsistent.
    Qed.

    Lemma snapshot_consistent_getTop_res s pi t ret :
      snapshot_consistent s pi ->
      TMap.find t pi = Some (ls_lini (@lgetTop A)) ->
      snapshot_consistent (clear_snapshot t s)
        (TMap.add t (ls_linr (@lgetTop A) ret) pi).
    Proof.
      intros Hconsistent Hlin q.
      destruct (PositiveMap.E.eq_dec q t) as [->|Hneq].
      - simpl. rewrite TMap.grs, TMap.gss. split; [intros [? H]; discriminate|].
        discriminate.
      - simpl. rewrite TMap.gro, TMap.gso by exact Hneq. apply Hconsistent.
    Qed.

    Lemma snapshot_setTS_same (s : @SPListState A) l ts :
      snapshot (SPListSpec.setTS l ts s) = snapshot s.
    Proof.
      unfold SPListSpec.setTS.
      destruct (nodes s l) as [[v' old']|]; [destruct old'|]; reflexivity.
    Qed.

    Lemma source_I_change_pi w pi' :
      source_I w ->
      snapshot_consistent (payload_of w) pi' ->
      source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (SinglePossState.σ w) (SinglePossState.ρ w) pi').
    Proof.
      intros HI Hsnap'.
      destruct HI as
        (mc & cc & s & log & Hsigma & Hrho & Hmc & Hcc & Hrep & Hsnap).
      exists mc, cc, s, log. simpl.
      split; [exact Hsigma|].
      split; [exact Hrho|].
      split; [exact Hmc|].
      split; [exact Hcc|].
      split; [exact Hrep|].
      unfold payload_of, ctrl_of in Hsnap'. rewrite Hrho in Hsnap'. simpl in Hsnap'.
      exact Hsnap'.
    Qed.

    Lemma ginv_exposes_active t m :
      forall out,
        AssertionsSingle.A.ComposeA source_I
          (AssertionsSingle.Ginv t m) out ->
        Active t m out.
    Proof.
      intros out [pre [HI Hginv]].
      unfold AssertionsSingle.Ginv, AssertionsSingle.LiftRelation_π in Hginv.
      destruct Hginv as [Hsigma [Hrho [Hnone Hpi]]].
      destruct HI as
        (mc & cc & s & log & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      split.
      - exists mc, cc, s, log.
        split; [rewrite <- Hsigma; exact Eσ|].
        split; [rewrite <- Hrho; exact Eρ|].
        split; [exact Hmc|].
        split; [exact Hcc|].
        split; [exact Hrep|].
        rewrite Hpi. eapply snapshot_consistent_add_inv; eauto.
      - unfold ALin. rewrite Hpi, TMap.gss. reflexivity.
    Qed.

    Lemma gret_closes_completed t m ret :
      forall out,
        AssertionsSingle.A.ComposeA (Completed t m ret)
          (AssertionsSingle.Gret t m ret) out ->
        source_I out.
    Proof.
      intros out [pre [[HI Hlin] Hgret]].
      unfold AssertionsSingle.Gret, AssertionsSingle.LiftRelation_π in Hgret.
      destruct Hgret as [Hsigma [Hrho [Hfind Hpi]]].
      destruct HI as
        (mc & cc & s & log & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      exists mc, cc, s, log.
      split; [rewrite <- Hsigma; exact Eσ|].
      split; [rewrite <- Hrho; exact Eρ|].
      split; [exact Hmc|].
      split; [exact Hcc|].
      split; [exact Hrep|].
      rewrite Hpi. eapply snapshot_consistent_remove_linr; eauto.
    Qed.

    Lemma set_ginv_exposes_active t m :
      forall w,
        AssertionsSet.A.ComposeA SI (AssertionsSet.Ginv t m) w ->
        SActive t m w.
    Proof.
      eapply lift_ginv_compose. apply ginv_exposes_active.
    Qed.

    Lemma set_gret_closes_completed t m ret :
      forall w,
        AssertionsSet.A.ComposeA (SCompleted t m ret)
          (AssertionsSet.Gret t m ret) w -> SI w.
    Proof.
      eapply lift_gret_compose. apply gret_closes_completed.
    Qed.

    Lemma completed_has_return_token t m ret :
      forall w, SCompleted t m ret w ->
      forall rho pi, SetPossState.Δ w rho pi ->
        TMap.find t pi = Some (ls_linr m ret).
    Proof.
      eapply lift_post_lin.
      intros x [_ Hlin]. exact Hlin.
    Qed.


    (** * Method proofs *)

    Definition in_mem := @SPListUnlinkImpl.in_mem A.
    Definition in_cas := @SPListUnlinkImpl.in_cas A.

    (** Abstract steps of the ghost specification: the control steps as in
        [SPListSpec], the log by [log_update]. *)
    Ltac gstep_inv t op s2 :=
      eapply rt_trans;
        [apply rt_step; eapply (Semantics.ps_inv t op _ (s2 : abstract_state));
          [split; [simpl|reflexivity]|eauto]
        |].
    Ltac gstep_ret t op ret s2 :=
      eapply rt_trans;
        [apply rt_step; eapply (Semantics.ps_ret t op ret _ (s2 : abstract_state));
          [split; [simpl|reflexivity]
          |rewrite TMap.gss; reflexivity]
        |].

    Lemma source_I_build mc cc s log pi :
      mem_control_ok mc -> cas_control_ok cc ->
      represents (mem_heap mc) (fst (cas_value cc)) (snd (cas_value cc)) s log ->
      snapshot_consistent s pi ->
      source_I (mk (pair mc cc) (pair (Ready s) log) pi).
    Proof.
      intros Hmc Hcc Hrep Hsnap. exists mc, cc, s, log. simpl.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact Hmc|].
      split; [exact Hcc|]. split; [exact Hrep|exact Hsnap].
    Qed.

    (** ** getCounter *)

    Lemma getCounter_get_inv_update t :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@InvEv (li_sig E) (in_cas get)))
        (Active t lgetCounter) (Active t lgetCounter).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [HIpre Hlin].
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair s1 (Pending s4 t get)) ρ1 π1)).
      { eapply source_I_change_controls with
          (w := @SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F) (pair s1 (Idle s4)) ρ1 π1).
        - exact HIpre.
        - reflexivity.
        - reflexivity.
        - pose proof (source_I_mem_control _ HIpre) as Hok.
          simpl in Hok. exact Hok.
        - reflexivity. }
      pupdate_finish. split.
      - split; [exact HIpost|exact Hlin].
      - eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma getCounter_get_res_update t q :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (in_cas get) q))
        (Active t lgetCounter)
        (Completed t lgetCounter (snd q)).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [HIpre Hlin].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & log & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc.
      subst ρ1.
      pose proof Hrep as (Hvalid & Hcount & Hlength & Hnodes & Horder).
      simpl in Hcount.
      pupdate_start.
      gstep_inv t (@lgetCounter A) (pair (AtomicPending s t (@lgetCounter A)) log).
      { constructor. }
      gstep_ret t (@lgetCounter A) (snd q) (pair (Ready s) log).
      { rewrite <- Hcount. constructor. }
      apply rt_refl.
      assert (HIpost : source_I (mk (pair s1 (Idle q)) (pair (Ready s) log)
        (TMap.add t (ls_linr (@lgetCounter A) (snd q))
          (TMap.add t (ls_lini (@lgetCounter A)) π1)))).
      { apply source_I_build; [exact Hmc|reflexivity|exact Hrep|].
        eapply snapshot_consistent_atomic; eauto. }
      split.
      - split; [exact HIpost|].
        unfold ALin. simpl. rewrite TMap.gss. reflexivity.
      - eapply source_G_same_payload; simpl; eauto.
        intros r Hneq. simpl.
        repeat rewrite TMap.gso by exact Hneq. reflexivity.
    Qed.

    Lemma getCounter_triple t :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActive t lgetCounter }}
          (@SPListUnlinkImpl.getCounter_impl A t)
        {{ fun ret => SCompleted t lgetCounter ret }}.
    Proof.
      unfold SPListUnlinkImpl.getCounter_impl.
      eapply singleton_provable_vis_safe with
        (P' := Active t lgetCounter)
        (Q' := fun q => Completed t lgetCounter (snd q)).
      - intros w _ Herror.
        destruct (SinglePossState.σ w) as [mc cc]. simpl in Herror.
        dependent destruction Herror.
      - apply active_entails_I.
      - intros q. apply completed_entails_I.
      - apply active_stable.
      - intros q. apply completed_stable.
      - apply getCounter_get_inv_update.
      - intros q. apply getCounter_get_res_update.
      - intros q. singleton_ret_safe.
        + apply ImplRefl.
        + apply completed_entails_I.
        + apply completed_stable.
      - apply active_entails_I.
      - apply slot_local_active.
      - intros q. apply slot_local_completed.
    Qed.

    (** ** setTS *)

    Lemma setTS_inv_update t l ts :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@InvEv (li_sig E) (in_mem (nmsetTS l ts))))
        (ActiveOwnedDefined t (lsetTS l ts) l)
        (ActiveOwnedDefined t (lsetTS l ts) l).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[[HIpre Hlin] Hdefined] Howner].
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair (Pending s3 t0 (nmsetTS l0 ts0)) s2) ρ1 π1)).
      { eapply source_I_change_controls with
          (w := @SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F) (pair (Idle s3) s2) ρ1 π1).
        - exact HIpre.
        - reflexivity.
        - reflexivity.
        - simpl. exact Howner.
        - pose proof (source_I_cas_control _ HIpre) as Hok.
          simpl in Hok. exact Hok. }
      pupdate_finish. split.
      - repeat split; auto.
      - eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma setTS_res_update t l ts :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (in_mem (nmsetTS l ts)) tt))
        (ActiveOwnedDefined t (lsetTS l ts) l)
        (Completed t (lsetTS l ts) tt).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[[HIpre Hlin] Hdefined] Howner].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & log & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc. subst ρ1.
      simpl in Hrep.
      assert (Hin : In l0 log).
      { eapply represents_defined_in; [exact Hrep|].
        unfold NodeDefined, payload_of, ctrl_of in Hdefined. simpl in Hdefined.
        destruct Hdefined as [a Hdefined]. congruence. }
      assert (Hrep' : represents
        (heap_update l0
          (pair (pair (pair v
            (match old_ts with TSTop => ts0 | _ => old_ts end)) taken) next) s0)
        (fst (cas_value s2)) (snd (cas_value s2))
        (SPListSpec.setTS l0 ts0 s) log).
      { eapply represents_setTS; eauto. }
      pupdate_start.
      gstep_inv t0 (@lsetTS A l0 ts0) (pair (AtomicPending s t0 (@lsetTS A l0 ts0)) log).
      { constructor. exact Howner. }
      gstep_ret t0 (@lsetTS A l0 ts0) tt (pair (Ready (SPListSpec.setTS l0 ts0 s)) log).
      { constructor. }
      apply rt_refl.
      assert (HIpost : source_I
        (mk
          (pair
            (Idle
              (heap_update l0
                (pair (pair (pair v
                  (match old_ts with TSTop => ts0 | _ => old_ts end)) taken)
                  next) s0))
            s2)
          (pair (Ready (SPListSpec.setTS l0 ts0 s)) log)
          (TMap.add t0 (ls_linr (lsetTS l0 ts0) tt)
            (TMap.add t0 (ls_lini (lsetTS l0 ts0)) π1)))).
      { apply source_I_build; [reflexivity|exact Hcc|exact Hrep'|].
        eapply snapshot_consistent_atomic; [|exact Hlin].
        unfold snapshot_consistent. rewrite snapshot_setTS_same. exact Hsnap. }
      split.
      - split; [exact HIpost|].
        unfold ALin. simpl. rewrite TMap.gss. reflexivity.
      - unfold source_G. repeat split; auto.
        + simpl. rewrite Howner. eapply heap_evol_setTS; eauto.
        + intros q Hnotowner Hundefined. contradiction Hnotowner.
        + exists nil. split; [reflexivity|]. intros; reflexivity.
        + intros q Hneq. unfold ctrl_of. simpl. rewrite snapshot_setTS_same. reflexivity.
        + intros q Hneq. simpl.
          repeat rewrite TMap.gso by exact Hneq. reflexivity.
    Qed.

    Lemma setTS_valid_triple t l ts :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActiveOwnedDefined t (lsetTS l ts) l }}
          (@SPListUnlinkImpl.setTS_impl A l ts t)
        {{ fun ret => SCompleted t (lsetTS l ts) ret }}.
    Proof.
      unfold SPListUnlinkImpl.setTS_impl.
      eapply singleton_provable_vis_safe with
        (P' := ActiveOwnedDefined t (lsetTS l ts) l)
        (Q' := fun _ => Completed t (lsetTS l ts) tt).
      - intros w [[[HI Hlin] Hdefined] Howner] Herror.
        destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
        simpl in Herror. revert Howner. dependent destruction Herror.
        + intros Howner. destruct (source_I_defined_lookup _ _ HI Hdefined)
            as (v & old & taken & next & Hlookup).
          unfold heap_of in Hlookup. rewrite Eσ in Hlookup. simpl in Hlookup. congruence.
        + intros Howner. pose proof (source_I_mem_control _ HI) as Hok.
          rewrite Eσ in Hok. simpl in Hok. congruence.
      - apply active_owned_defined_entails_I.
      - intros []; apply completed_entails_I.
      - apply active_owned_defined_stable.
      - intros []; apply completed_stable.
      - apply setTS_inv_update.
      - intros []; apply setTS_res_update.
      - intros []. singleton_ret_safe.
        + apply ImplRefl.
        + apply completed_entails_I.
        + apply completed_stable.
      - apply active_owned_defined_entails_I.
      - apply slot_local_active_owned_defined.
      - intros []. apply slot_local_completed.
    Qed.

    (** Either some possibility has the node undefined, and the
        specification's error is reachable there, or every possibility has
        it defined. *)
    Lemma defined_everywhere_or_undefined_somewhere (w : set_state) l :
      (forall ρ π, SetPossState.Δ w ρ π ->
        NodeDefined l (mk (SetPossState.σ w) ρ π)) \/
      (exists ρ π, SetPossState.Δ w ρ π /\
        nodes (payload_of (mk (SetPossState.σ w) ρ π)) l = None).
    Proof.
      destruct (classic (exists ρ π, SetPossState.Δ w ρ π /\
          nodes (payload_of (mk (SetPossState.σ w) ρ π)) l = None))
        as [H | Hnone]; [right; exact H|left].
      intros ρ π Hposs.
      destruct (nodes (payload_of (mk (SetPossState.σ w) ρ π)) l) as [a|] eqn:Hnode.
      - exists a. exact Hnode.
      - exfalso. apply Hnone. exists ρ, π. split; assumption.
    Qed.

    Lemma setTS_active_valid_or_error t l ts :
      ⊨ SActive t (lsetTS l ts) ==>>
        SActiveOwnedDefined t (lsetTS l ts) l \\// AssertionsSet.APError.
    Proof.
      intros w Hall.
      destruct (PositiveMap.E.eq_dec t owner) as [Howner|Howner].
      - destruct (defined_everywhere_or_undefined_somewhere w l)
          as [Hdef | [ρ0 [π0 [Hposs0 Hnode]]]].
        + left. intros ρ π Hposs. pose proof (Hall _ _ Hposs) as [HI Hlin].
          split; [|exact Howner]. split; [split; assumption|].
          apply Hdef. exact Hposs.
        + right. pose proof (Hall _ _ Hposs0) as [HI0 Hlin0].
          destruct HI0 as (mc & cc & s & log & Eσ & Eρ & _).
          econstructor; [exact Hposs0|].
          apply rt_step. eapply ps_error; [|exact Hlin0].
          simpl in Eρ. rewrite Eρ. simpl.
          eapply (@error_setTS_undefined A owner t s l ts _); [|reflexivity].
          unfold payload_of, ctrl_of in Hnode. simpl in Hnode.
          rewrite Eρ in Hnode. simpl in Hnode. exact Hnode.
      - right.
        destruct (ac_nonempty (SetPossState.Δ w)) as (ρ0 & π0 & Hposs0).
        pose proof (Hall _ _ Hposs0) as [HI0 Hlin0].
        destruct HI0 as (mc & cc & s & log & Eσ & Eρ & _).
        econstructor; [exact Hposs0|].
        apply rt_step. eapply ps_error; [|exact Hlin0].
        simpl in Eρ. rewrite Eρ. simpl.
        eapply (@error_setTS_not_owner A owner t s l ts _); eauto.
    Qed.

    Lemma setTS_triple t l ts :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActive t (lsetTS l ts) }}
          (@SPListUnlinkImpl.setTS_impl A l ts t)
        {{ fun ret => SCompleted t (lsetTS l ts) ret }}.
    Proof.
      eapply SetLogic.provable_perror.
      - apply setTS_active_valid_or_error.
      - apply setTS_valid_triple.
    Qed.


    (** ** tryRemove: the take *)

    Lemma tryRemove_inv_update t l :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@InvEv (li_sig E) (in_mem (nmtryTake l))))
        (ActiveDefined t (ltryRemove l) l)
        (ActiveDefined t (ltryRemove l) l).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[HIpre Hlin] Hdefined].
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (pair (Pending s3 t0 (nmtryTake l0)) s2) ρ1 π1)).
      { eapply source_I_change_controls with
          (w := @SinglePossState.Build_ProofStateSingle _ _
            (li_lts E) (li_lts F) (pair (Idle s3) s2) ρ1 π1).
        - exact HIpre.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - pose proof (source_I_cas_control _ HIpre) as Hok.
          simpl in Hok. exact Hok. }
      pupdate_finish. split.
      - split; [split; [exact HIpost|exact Hlin]|exact Hdefined].
      - eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma tryRemove_succ_update t l :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (in_mem (nmtryTake l)) true))
        (ActiveDefined t (ltryRemove l) l)
        (TakerCore t l).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[HIpre Hlin] Hdefined].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & log & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc. subst ρ1.
      simpl in Hrep.
      match goal with H : s0 l0 = Some _ |- _ => rename H into Hconcrete end.
      assert (Hin : In l0 log).
      { eapply represents_defined_in; [exact Hrep|].
        unfold NodeDefined, payload_of, ctrl_of in Hdefined. simpl in Hdefined.
        destruct Hdefined as [a Hdefined]. congruence. }
      assert (Hnode_defined : nodes s l0 <> None).
      { unfold NodeDefined, payload_of, ctrl_of in Hdefined. simpl in Hdefined.
        destruct Hdefined as [a Hdefined]. congruence. }
      assert (Hlive : In l0 (order s)).
      { apply (represents_live_in_order _ _ _ _ _ _ Hrep Hin).
        unfold live_at, node_live. rewrite Hconcrete. reflexivity. }
      assert (Hrep' : represents
        (heap_update l0 (pair (pair (pair v ts) true) next) s0)
        (fst (cas_value s2)) (snd (cas_value s2))
        (SPListSpec.remove l0 s) log).
      { eapply represents_tryTake_succ; eauto. }
      pupdate_start.
      gstep_inv t0 (@ltryRemove A l0) (pair (AtomicPending s t0 (@ltryRemove A l0)) log).
      { constructor. exact Hnode_defined. }
      gstep_ret t0 (@ltryRemove A l0) true (pair (Ready (SPListSpec.remove l0 s)) log).
      { constructor; assumption. }
      apply rt_refl.
      assert (HIpost : source_I
        (mk
          (pair (Idle (heap_update l0 (pair (pair (pair v ts) true) next) s0)) s2)
          (pair (Ready (SPListSpec.remove l0 s)) log)
          (TMap.add t0 (ls_linr (ltryRemove l0) true)
            (TMap.add t0 (ls_lini (ltryRemove l0)) π1)))).
      { apply source_I_build; [reflexivity|exact Hcc|exact Hrep'|].
        eapply snapshot_consistent_atomic; [exact Hsnap|exact Hlin]. }
      split.
      - split; [split; [exact HIpost|]|].
        + unfold ALin. simpl. rewrite TMap.gss. reflexivity.
        + unfold NodeDefined. simpl.
          destruct (represents_abstract_in _ _ _ _ _ _ Hrep' Hin) as [n [_ Hn]].
          exists (node_projection n). exact Hn.
      - unfold source_G. repeat split; auto.
        + simpl. eapply heap_evol_tryTake; exact Hconcrete.
        + intros q Hnotowner Hundefined. simpl.
          destruct (Nat.eq_dec l0 q) as [Heq|Hneq].
          * subst q. exfalso. apply Hnode_defined. exact Hundefined.
          * symmetry. apply HeapUpdateOther. exact Hneq.
        + exists nil. split; [reflexivity|]. intros; reflexivity.
        + intros q Hneq. simpl.
          repeat rewrite TMap.gso by exact Hneq. reflexivity.
    Qed.

    Lemma tryRemove_fail_update t l :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (in_mem (nmtryTake l)) false))
        (ActiveDefined t (ltryRemove l) l)
        (Completed t (ltryRemove l) false).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[HIpre Hlin] Hdefined].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & log & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc. subst ρ1.
      simpl in Hrep.
      match goal with H : s3 l0 = Some _ |- _ => rename H into Hconcrete end.
      assert (Hin : In l0 log).
      { eapply represents_defined_in; [exact Hrep|].
        unfold NodeDefined, payload_of, ctrl_of in Hdefined. simpl in Hdefined.
        destruct Hdefined as [a Hdefined]. congruence. }
      assert (Hnode_defined : nodes s l0 <> None).
      { unfold NodeDefined, payload_of, ctrl_of in Hdefined. simpl in Hdefined.
        destruct Hdefined as [a Hdefined]. congruence. }
      assert (Hnotlive : ~ In l0 (order s)).
      { intro Hbad. apply (represents_live_in_order _ _ _ _ _ _ Hrep Hin) in Hbad.
        unfold live_at, node_live in Hbad. rewrite Hconcrete in Hbad. discriminate. }
      pupdate_start.
      gstep_inv t0 (@ltryRemove A l0) (pair (AtomicPending s t0 (@ltryRemove A l0)) log).
      { constructor. exact Hnode_defined. }
      gstep_ret t0 (@ltryRemove A l0) false (pair (Ready s) log).
      { constructor; assumption. }
      apply rt_refl.
      assert (HIpost : source_I
        (mk (pair (Idle s3) s2) (pair (Ready s) log)
          (TMap.add t0 (ls_linr (ltryRemove l0) false)
            (TMap.add t0 (ls_lini (ltryRemove l0)) π1)))).
      { apply source_I_build; [reflexivity|exact Hcc|exact Hrep|].
        eapply snapshot_consistent_atomic; [exact Hsnap|exact Hlin]. }
      split.
      - split; [exact HIpost|].
        unfold ALin. simpl. rewrite TMap.gss. reflexivity.
      - eapply source_G_same_payload; simpl; eauto.
        intros q Hneq. repeat rewrite TMap.gso by exact Hneq. reflexivity.
    Qed.


    (** ** The walk over taken nodes

        [skip_taken_impl] follows successors while the node is taken.  It
        is used by [insert] (from the register's pointer) and by
        [tryRemove] (from the taken node's successor), with different
        invariants; the proof is generic in a pointer-indexed assertion
        [P] closed under the hop over a taken node. *)

    Section Walk.
      Variable t : tid.
      Variable P : Ptr -> assertion.
      Hypothesis HP_I : forall p w, P p w -> source_I w.
      Hypothesis HP_stable :
        forall p, AssertionsSingle.A.Stable (source_R t) source_I (P p).
      Hypothesis HP_local : forall p, slot_local t (P p).
      Hypothesis HP_defined : forall x w, P (Some x) w -> NodeDefined x w.
      Hypothesis HP_controls : forall p σ ρ π mc' cc',
        P p (mk σ ρ π) ->
        mem_heap mc' = mem_heap (fst σ) -> cas_value cc' = cas_value (snd σ) ->
        mem_control_ok mc' -> cas_control_ok cc' ->
        P p (mk (pair mc' cc') ρ π).
      Hypothesis HP_hop : forall x w v ts nx,
        P (Some x) w ->
        heap_of w x = Some (pair (pair (pair v ts) true) nx) -> P nx w.

      Definition WalkTaken (x : Addr) : assertion := P (Some x) //\\ NodeTaken x.

      Definition WalkBodyPost (r : Ptr + Ptr) : assertion :=
        match r with
        | inl q => P q
        | inr q => P q
        end.

      Lemma walk_taken_entails_I x : ⊨ WalkTaken x ==>> source_I.
      Proof. intros w [Hp _]. eapply HP_I; exact Hp. Qed.

      Lemma walk_taken_stable x :
        AssertionsSingle.A.Stable (source_R t) source_I (WalkTaken x).
      Proof.
        unfold AssertionsSingle.A.Stable, WalkTaken.
        intros out [[pre [[Hp Htk] HR]] HIout]. split.
        - eapply HP_stable. split; [exists pre; eauto|exact HIout].
        - eapply node_taken_stable; eauto.
      Qed.

      Lemma slot_local_walk_taken x : slot_local t (WalkTaken x).
      Proof.
        unfold WalkTaken. apply slot_local_conj;
          [apply HP_local|apply slot_local_node_taken].
      Qed.

      Lemma walk_node_defined x w :
        P (Some x) w ->
        exists v ts tk nx, heap_of w x = Some (pair (pair (pair v ts) tk) nx).
      Proof.
        intros Hp. eapply source_I_defined_lookup;
          [eapply HP_I; exact Hp|eapply HP_defined; exact Hp].
      Qed.

      Lemma walk_getTaken_no_error x :
        ⊨ P (Some x) ==>>
          AssertionsSingle.A.ANoError
            (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetTaken x)))).
      Proof.
        intros w Hp Herror.
        destruct (walk_node_defined x w Hp) as (v & ts & tk & nx & Hcell).
        destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
        unfold heap_of in Hcell. rewrite Eσ in Hcell. simpl in Hcell.
        simpl in Herror. dependent destruction Herror. simpl in *. congruence.
      Qed.

      Lemma walk_getNext_no_error x :
        ⊨ WalkTaken x ==>>
          AssertionsSingle.A.ANoError
            (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetNext x)))).
      Proof.
        intros w [Hp _] Herror.
        destruct (walk_node_defined x w Hp) as (v & ts & tk & nx & Hcell).
        destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
        unfold heap_of in Hcell. rewrite Eσ in Hcell. simpl in Hcell.
        simpl in Herror. dependent destruction Herror. simpl in *. congruence.
      Qed.

      Lemma walk_getTaken_inv_update x :
        AssertionsSingle.PUpdate (source_G t)
          (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetTaken x))))
          (P (Some x)) (P (Some x)).
      Proof.
        pupdate_intros_atomic. pupdate_finish.
        pose proof (HP_I _ _ Hpre) as HIpre.
        pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
        split.
        - eapply HP_controls; [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc].
        - match goal with
          | |- source_G _ _ ?w2 =>
              assert (HIpost : source_I w2) by
                (eapply HP_I; eapply HP_controls;
                  [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc])
          end.
          eapply source_G_same_payload; simpl; eauto.
      Qed.

      Lemma walk_getTaken_res_update x b :
        AssertionsSingle.PUpdate (source_G t)
          (Build_ThreadEvent t (@ResEv (li_sig E) (in_mem (nmgetTaken x)) b))
          (P (Some x)) (if b then WalkTaken x else P (Some x)).
      Proof.
        pupdate_intros_atomic.
        match goal with H : _ _ = Some _ |- _ => rename H into Hconcrete end.
        pupdate_finish.
        pose proof (HP_I _ _ Hpre) as HIpre.
        pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
        split.
        - match goal with |- (if ?bb then _ else _) _ => destruct bb end.
          + split.
            * eapply HP_controls; [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc].
            * unfold NodeTaken, heap_of, taken_at. simpl. rewrite Hconcrete. reflexivity.
          + eapply HP_controls; [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc].
        - match goal with
          | |- source_G _ _ ?w2 =>
              assert (HIpost : source_I w2) by
                (eapply HP_I; eapply HP_controls;
                  [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc])
          end.
          eapply source_G_same_payload; simpl; eauto.
      Qed.

      Lemma walk_getNext_inv_update x :
        AssertionsSingle.PUpdate (source_G t)
          (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetNext x))))
          (WalkTaken x) (WalkTaken x).
      Proof.
        pupdate_intros_atomic. pupdate_finish.
        destruct Hpre as [Hp Htk].
        pose proof (HP_I _ _ Hp) as HIpre.
        pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
        split.
        - split.
          + eapply HP_controls; [exact Hp|reflexivity|reflexivity|exact I|exact Hcc].
          + exact Htk.
        - match goal with
          | |- source_G _ _ ?w2 =>
              assert (HIpost : source_I w2) by
                (eapply HP_I; eapply HP_controls;
                  [exact Hp|reflexivity|reflexivity|exact I|exact Hcc])
          end.
          eapply source_G_same_payload; simpl; eauto.
      Qed.

      Lemma walk_getNext_res_update x nx :
        AssertionsSingle.PUpdate (source_G t)
          (Build_ThreadEvent t (@ResEv (li_sig E) (in_mem (nmgetNext x)) nx))
          (WalkTaken x) (P nx).
      Proof.
        pupdate_intros_atomic.
        match goal with H : _ _ = Some _ |- _ => rename H into Hconcrete end.
        pupdate_finish.
        destruct Hpre as [Hp Htk].
        pose proof (HP_I _ _ Hp) as HIpre.
        pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
        unfold NodeTaken, heap_of, taken_at in Htk. simpl in Htk.
        rewrite Hconcrete in Htk. simpl in Htk. subst.
        pose proof (HP_hop _ _ _ _ _ Hp Hconcrete) as Hhop.
        split.
        - eapply HP_controls; [exact Hhop|reflexivity|reflexivity|exact I|exact Hcc].
        - match goal with
          | |- source_G _ _ ?w2 =>
              assert (HIpost : source_I w2) by
                (eapply HP_I; eapply HP_controls;
                  [exact Hhop|reflexivity|reflexivity|exact I|exact Hcc])
          end.
          eapply source_G_same_payload; simpl; eauto.
      Qed.

      Lemma walk_triple p0 :
        [li_lts E, li_lts F, R t, G t, SI, t] ⊢
          {{ lift_assert (P p0) }}
            (@SPListUnlinkImpl.skip_taken_impl A p0)
          {{ fun r => lift_assert (P r) }}.
      Proof.
        unfold SPListUnlinkImpl.skip_taken_impl.
        eapply SetLogic.provable_doloop_data with
          (Iloop := fun q => lift_assert (P q))
          (Q := fun r => lift_assert (P r)).
        - intros a w H. eapply lift_impl; [intros x Hx; eapply HP_I; exact Hx|exact H].
        - intros a. apply lift_stable. apply HP_stable.
        - intros q.
          eapply SetLogic.provable_conseq_weak_post with
            (Q' := fun r => lift_assert (WalkBodyPost r)).
          + intros [p|p]; unfold WalkBodyPost; simpl; intros w Hpost;
              eapply lift_impl; [intros x Hx; eapply HP_I; exact Hx|exact Hpost|
                                 intros x Hx; eapply HP_I; exact Hx|exact Hpost].
          + intros [p|p]; simpl; apply lift_stable; apply HP_stable.
          + intros [p|p]; unfold WalkBodyPost; simpl; intros w Hpost; exact Hpost.
          + destruct q as [x|].
            * eapply singleton_provable_vis_safe with
                (P' := P (Some x))
                (Q' := fun b : bool => if b then WalkTaken x else P (Some x)).
              -- apply walk_getTaken_no_error.
              -- intros w H; eapply HP_I; exact H.
              -- intros b; destruct b;
                   [apply walk_taken_entails_I|intros w H; eapply HP_I; exact H].
              -- apply HP_stable.
              -- intros b; destruct b; [apply walk_taken_stable|apply HP_stable].
              -- apply walk_getTaken_inv_update.
              -- intros b. apply walk_getTaken_res_update.
              -- intros b. destruct b.
                 ++ eapply singleton_provable_vis_safe with
                      (P' := WalkTaken x) (Q' := fun nx : Ptr => P nx).
                    ** apply walk_getNext_no_error.
                    ** apply walk_taken_entails_I.
                    ** intros nx w H; eapply HP_I; exact H.
                    ** apply walk_taken_stable.
                    ** intros nx; apply HP_stable.
                    ** apply walk_getNext_inv_update.
                    ** intros nx. apply walk_getNext_res_update.
                    ** intros nx. unfold WalkBodyPost. singleton_ret_safe.
                       --- intros w H; exact H.
                       --- intros w H; eapply HP_I; exact H.
                       --- apply HP_stable.
                    ** apply walk_taken_entails_I.
                    ** apply slot_local_walk_taken.
                    ** intros nx; apply HP_local.
                 ++ unfold WalkBodyPost. singleton_ret_safe.
                    ** intros w H; exact H.
                    ** intros w H; eapply HP_I; exact H.
                    ** apply HP_stable.
              -- intros w H; eapply HP_I; exact H.
              -- apply HP_local.
              -- intros b; destruct b; [apply slot_local_walk_taken|apply HP_local].
            * unfold WalkBodyPost. singleton_ret_safe.
              -- intros w H; exact H.
              -- intros w H; eapply HP_I; exact H.
              -- apply HP_stable.
      Qed.
    End Walk.


    (** ** Transfer across control changes with the same payload *)

    Lemma source_I_controls σ ρ π mc' cc' :
      source_I (mk σ ρ π) ->
      mem_heap mc' = mem_heap (fst σ) -> cas_value cc' = cas_value (snd σ) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      source_I (mk (pair mc' cc') ρ π).
    Proof.
      intros HI Hh Hc Hm Hcc.
      exact (source_I_change_controls (mk σ ρ π) mc' cc' HI Hh Hc Hm Hcc).
    Qed.

    Lemma completed_controls t m ret σ ρ π mc' cc' :
      Completed t m ret (mk σ ρ π) ->
      mem_heap mc' = mem_heap (fst σ) -> cas_value cc' = cas_value (snd σ) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      Completed t m ret (mk (pair mc' cc') ρ π).
    Proof.
      intros [HI Hlin] Hh Hc Hm Hcc. split; [eapply source_I_controls; eauto|exact Hlin].
    Qed.

    Lemma active_controls t m σ ρ π mc' cc' :
      Active t m (mk σ ρ π) ->
      mem_heap mc' = mem_heap (fst σ) -> cas_value cc' = cas_value (snd σ) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      Active t m (mk (pair mc' cc') ρ π).
    Proof.
      intros [HI Hlin] Hh Hc Hm Hcc. split; [eapply source_I_controls; eauto|exact Hlin].
    Qed.

    Lemma taker_core_controls t l σ ρ π mc' cc' :
      TakerCore t l (mk σ ρ π) ->
      mem_heap mc' = mem_heap (fst σ) -> cas_value cc' = cas_value (snd σ) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      TakerCore t l (mk (pair mc' cc') ρ π).
    Proof.
      intros [Hcomp Hdef] Hh Hc Hm Hcc. split; [eapply completed_controls; eauto|exact Hdef].
    Qed.

    Lemma taker_at_controls t l p σ ρ π mc' cc' :
      TakerAt t l p (mk σ ρ π) ->
      mem_heap mc' = mem_heap (fst σ) -> cas_value cc' = cas_value (snd σ) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      TakerAt t l p (mk (pair mc' cc') ρ π).
    Proof.
      intros [Hcore Hsk] Hh Hc Hm Hcc. split; [eapply taker_core_controls; eauto|].
      unfold SkipsAfter, heap_of, log_of in *. simpl in *. rewrite Hh. exact Hsk.
    Qed.

    Lemma insert_read_controls t v q σ ρ π mc' cc' :
      InsertRead t v q (mk σ ρ π) ->
      mem_heap mc' = mem_heap (fst σ) -> cas_value cc' = cas_value (snd σ) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      InsertRead t v q (mk (pair mc' cc') ρ π).
    Proof.
      intros [[Hact Howner] [Hcount Hsk]] Hh Hc Hm Hcc.
      split; [split; [eapply active_controls; eauto|exact Howner]|].
      split.
      - unfold CountIs, reg_of in *. simpl in *. rewrite Hc. exact Hcount.
      - unfold SkipsLog, heap_of, log_of in *. simpl in *. rewrite Hh. exact Hsk.
    Qed.

    Lemma insert_walked_controls t v q p σ ρ π mc' cc' :
      InsertWalked t v q p (mk σ ρ π) ->
      mem_heap mc' = mem_heap (fst σ) -> cas_value cc' = cas_value (snd σ) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      InsertWalked t v q p (mk (pair mc' cc') ρ π).
    Proof.
      intros [Hread Hsk] Hh Hc Hm Hcc.
      split; [eapply insert_read_controls; eauto|].
      unfold SkipsLog, heap_of, log_of in *. simpl in *. rewrite Hh. exact Hsk.
    Qed.

    Lemma insert_allocated_controls t v q p l σ ρ π mc' cc' :
      InsertAllocated t v q p l (mk σ ρ π) ->
      mem_heap mc' = mem_heap (fst σ) -> cas_value cc' = cas_value (snd σ) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      InsertAllocated t v q p l (mk (pair mc' cc') ρ π).
    Proof.
      intros [Hwalked [Hundef Hcell]] Hh Hc Hm Hcc.
      split; [eapply insert_walked_controls; eauto|].
      split; [exact Hundef|].
      unfold heap_of in *. simpl in *. rewrite Hh. exact Hcell.
    Qed.

    (** ** tryRemove: the unlink *)

    Lemma taker_at_defined t l x w :
      TakerAt t l (Some x) w -> NodeDefined x w.
    Proof.
      intros [[[HI Hlin] Hdef] Hsk].
      pose proof (source_I_defined_in_log _ _ HI Hdef) as Hin.
      apply in_split in Hin. destruct Hin as [a [b Hab]].
      pose proof (Hsk a b Hab) as Hsk'.
      apply skips_in in Hsk'.
      eapply source_I_in_log_defined; [exact HI|].
      rewrite Hab. apply in_or_app. right. now right.
    Qed.

    Lemma taker_at_hop t l x w v ts nx :
      TakerAt t l (Some x) w ->
      heap_of w x = Some (pair (pair (pair v ts) true) nx) ->
      TakerAt t l nx w.
    Proof.
      intros [Hcore Hsk] Hcell. split; [exact Hcore|].
      intros a b Hab. pose proof (Hsk a b Hab) as Hskb.
      destruct (skips_some_split _ _ _ Hskb) as (b1 & b2 & -> & Hb1).
      pose proof (source_I_rep _ (proj1 (proj1 Hcore))) as Hrep.
      destruct Hrep as ((_ & _ & Hlk) & _).
      rewrite Hab in Hlk.
      assert (Hlk' : links_ok (heap_of w) ((a ++ l :: b1) ++ x :: b2)).
      { rewrite <- app_assoc. simpl. exact Hlk. }
      destruct (links_ok_split _ _ _ _ Hlk') as [n [Hn Hskn]].
      rewrite Hcell in Hn. injection Hn as <-. simpl in Hskn.
      replace (b1 ++ x :: b2) with ((b1 ++ x :: nil) ++ b2)
        by (rewrite <- app_assoc; reflexivity).
      apply skips_app_taken; [|exact Hskn].
      apply all_taken_app; [exact Hb1|]. constructor; [|constructor].
      unfold taken_at. rewrite Hcell. reflexivity.
    Qed.

    Lemma taker_core_no_error_getNext t l :
      ⊨ TakerCore t l ==>>
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetNext l)))).
    Proof.
      intros w [[HI _] Hdef] Herror.
      destruct (source_I_defined_lookup _ _ HI Hdef) as (v & ts & tk & nx & Hcell).
      destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
      unfold heap_of in Hcell. rewrite Eσ in Hcell. simpl in Hcell.
      simpl in Herror. dependent destruction Herror. simpl in *. congruence.
    Qed.

    Lemma taker_at_no_error_casNext t l old p :
      ⊨ TakerAt t l p ==>>
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmcasNext l old p)))).
    Proof.
      intros w [[[HI _] Hdef] _] Herror.
      destruct (source_I_defined_lookup _ _ HI Hdef) as (v & ts & tk & nx & Hcell).
      destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
      unfold heap_of in Hcell. rewrite Eσ in Hcell. simpl in Hcell.
      simpl in Herror. dependent destruction Herror. simpl in *. congruence.
    Qed.

    Lemma tryRemove_getNext_inv_update t l :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetNext l))))
        (TakerCore t l) (TakerCore t l).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      pose proof (taker_core_entails_I _ _ _ Hpre) as HIpre.
      pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
      split.
      - eapply taker_core_controls; [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc].
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply taker_core_entails_I; eapply taker_core_controls;
                [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma tryRemove_getNext_res_update t l nx :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_mem (nmgetNext l)) nx))
        (TakerCore t l) (TakerAt t l nx).
    Proof.
      pupdate_intros_atomic.
      match goal with H : _ _ = Some _ |- _ => rename H into Hconcrete end.
      pupdate_finish.
      pose proof (taker_core_entails_I _ _ _ Hpre) as HIpre.
      pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
      match goal with
      | |- _ /\ source_G _ ?w1 _ =>
        match type of Hconcrete with
        | _ ?ll = Some (pair (pair (pair _ _) _) ?nn) =>
          assert (Hsk : SkipsAfter ll nn w1)
        end
      end.
      { intros a b Hab.
        pose proof (source_I_rep _ HIpre) as ((_ & _ & Hlk) & _).
        rewrite Hab in Hlk.
        destruct (links_ok_split _ _ _ _ Hlk) as [n [Hn Hskn]].
        unfold heap_of in Hn. simpl in Hn. rewrite Hconcrete in Hn.
        injection Hn as <-. simpl in Hskn. exact Hskn. }
      split.
      - split.
        + eapply taker_core_controls; [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc].
        + unfold SkipsAfter, heap_of, log_of in *. simpl in *. exact Hsk.
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply taker_core_entails_I; eapply taker_core_controls;
                [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma tryRemove_casNext_inv_update t l old p :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmcasNext l old p))))
        (TakerAt t l p) (TakerAt t l p).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      pose proof (taker_at_entails_I _ _ _ _ Hpre) as HIpre.
      pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
      split.
      - eapply taker_at_controls; [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc].
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply taker_at_entails_I; eapply taker_at_controls;
                [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma tryRemove_casNext_succ_update t l old p :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_mem (nmcasNext l old p)) true))
        (TakerAt t l p) (Completed t (ltryRemove l) true).
    Proof.
      pupdate_intros_atomic.
      match goal with H : _ _ = Some _ |- _ => rename H into Hconcrete end.
      pupdate_finish.
      destruct Hpre as [[[HIpre Hlin] Hdef] Hsk].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & log & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc. subst ρ1.
      simpl in Hrep.
      assert (Hin : In l0 log).
      { eapply represents_defined_in; [exact Hrep|].
        unfold NodeDefined, payload_of, ctrl_of in Hdef. simpl in Hdef.
        destruct Hdef as [a Ha]. rewrite Ha. discriminate. }
      apply in_split in Hin. destruct Hin as [a [b Hab]].
      pose proof (Hsk a b Hab) as Hskb. unfold heap_of in Hskb. simpl in Hskb.
      assert (HIpost : source_I
        (mk (pair (Idle (heap_update l0 (pair (pair (pair v ts) taken) new) s0)) s2)
            (pair (Ready s) log) π1)).
      { apply source_I_build; [exact I|exact Hcc| |exact Hsnap].
        eapply represents_casNext_succ; [exact Hrep|exact Hab|exact Hconcrete|exact Hskb]. }
      split.
      - split; [exact HIpost|exact Hlin].
      - unfold source_G. split; [exact HIpre0|]. split; [exact HIpost|].
        split.
        { simpl. eapply heap_evol_casNext; exact Hconcrete. }
        split.
        { intros q Hnotowner Hundef. simpl.
          match goal with
          | |- context [heap_update ?ll _ _] => destruct (Nat.eq_dec ll q) as [<-|Hneq]
          end.
          - exfalso. destruct Hdef as [a' Ha']. unfold payload_of, ctrl_of in Ha'.
            simpl in Ha', Hundef. congruence.
          - symmetry. apply HeapUpdateOther. exact Hneq. }
        split; [split; [intros _; reflexivity|exists nil; split; reflexivity]|].
        split; [intros q Hq; reflexivity|intros q Hq; reflexivity].
    Qed.

    Lemma tryRemove_casNext_fail_update t l old p :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_mem (nmcasNext l old p)) false))
        (TakerAt t l p) (Completed t (ltryRemove l) true).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      pose proof (taker_at_entails_I _ _ _ _ Hpre) as HIpre.
      pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
      destruct Hpre as [[Hcomp Hdef] Hsk].
      split.
      - eapply completed_controls; [exact Hcomp|reflexivity|reflexivity|exact I|exact Hcc].
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply completed_entails_I; eapply completed_controls;
                [exact Hcomp|reflexivity|reflexivity|exact I|exact Hcc])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma tryRemove_valid_triple t l :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActiveDefined t (ltryRemove l) l }}
          (@SPListUnlinkImpl.tryRemove_impl A l t)
        {{ fun ret => SCompleted t (ltryRemove l) ret }}.
    Proof.
      unfold SPListUnlinkImpl.tryRemove_impl.
      eapply singleton_provable_vis_safe with
        (P' := ActiveDefined t (ltryRemove l) l)
        (Q' := fun ret : bool =>
          if ret then TakerCore t l else Completed t (ltryRemove l) false).
      - intros w [[HI Hlin] Hdefined] Herror.
        destruct (source_I_defined_lookup _ _ HI Hdefined)
          as (v & ts & taken & next & Hlookup).
        destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
        unfold heap_of in Hlookup. rewrite Eσ in Hlookup. simpl in Hlookup.
        simpl in Herror. dependent destruction Herror. simpl in *. congruence.
      - apply active_defined_entails_I.
      - intros ret; destruct ret; [apply taker_core_entails_I|apply completed_entails_I].
      - apply active_defined_stable.
      - intros ret; destruct ret; [apply taker_core_stable|apply completed_stable].
      - apply tryRemove_inv_update.
      - intros ret. destruct ret.
        + apply tryRemove_succ_update.
        + apply tryRemove_fail_update.
      - intros ret. destruct ret.
        + eapply singleton_provable_vis_safe with
            (P' := TakerCore t l) (Q' := fun nx : Ptr => TakerAt t l nx).
          * apply taker_core_no_error_getNext.
          * apply taker_core_entails_I.
          * intros nx. apply taker_at_entails_I.
          * apply taker_core_stable.
          * intros nx. apply taker_at_stable.
          * apply tryRemove_getNext_inv_update.
          * intros nx. apply tryRemove_getNext_res_update.
          * intros nx.
            eapply SetLogic.provable_seq with
              (Q' := fun p => lift_assert (TakerAt t l p)).
            -- apply (walk_triple t (TakerAt t l)).
               ++ intros p w H. eapply taker_at_entails_I; exact H.
               ++ intros p. apply taker_at_stable.
               ++ intros p. apply slot_local_taker_at.
               ++ intros x w H. eapply taker_at_defined; exact H.
               ++ intros p σ ρ π mc' cc' H. eapply taker_at_controls; exact H.
               ++ intros x w v ts nx' H Hcell. eapply taker_at_hop; eauto.
            -- intros p.
               eapply singleton_provable_vis_safe with
                 (P' := TakerAt t l p)
                 (Q' := fun _ : bool => Completed t (ltryRemove l) true).
               ++ apply taker_at_no_error_casNext.
               ++ apply taker_at_entails_I.
               ++ intros _. apply completed_entails_I.
               ++ apply taker_at_stable.
               ++ intros _. apply completed_stable.
               ++ apply tryRemove_casNext_inv_update.
               ++ intros b. destruct b.
                  ** apply tryRemove_casNext_succ_update.
                  ** apply tryRemove_casNext_fail_update.
               ++ intros b. singleton_ret_safe.
                  ** apply ImplRefl.
                  ** apply completed_entails_I.
                  ** apply completed_stable.
               ++ apply taker_at_entails_I.
               ++ apply slot_local_taker_at.
               ++ intros _. apply slot_local_completed.
          * apply taker_core_entails_I.
          * apply slot_local_taker_core.
          * intros nx. apply slot_local_taker_at.
        + singleton_ret_safe.
          * apply ImplRefl.
          * apply completed_entails_I.
          * apply completed_stable.
      - apply active_defined_entails_I.
      - apply slot_local_active_defined.
      - intros ret; destruct ret; [apply slot_local_taker_core|apply slot_local_completed].
    Qed.

    Lemma tryRemove_active_valid_or_error t l :
      ⊨ SActive t (ltryRemove l) ==>>
        SActiveDefined t (ltryRemove l) l \\// AssertionsSet.APError.
    Proof.
      intros w Hall.
      destruct (defined_everywhere_or_undefined_somewhere w l)
        as [Hdef | [ρ0 [π0 [Hposs0 Hnode]]]].
      - left. intros ρ π Hposs. pose proof (Hall _ _ Hposs) as [HI Hlin].
        split; [split; assumption|]. apply Hdef. exact Hposs.
      - right. pose proof (Hall _ _ Hposs0) as [HI0 Hlin0].
        destruct HI0 as (mc & cc & s & log & Eσ & Eρ & _).
        econstructor; [exact Hposs0|].
        apply rt_step. eapply ps_error; [|exact Hlin0].
        simpl in Eρ. rewrite Eρ. simpl.
        eapply (@error_tryRemove_undefined A owner t s l _); [|reflexivity].
        unfold payload_of, ctrl_of in Hnode. simpl in Hnode.
        rewrite Eρ in Hnode. simpl in Hnode. exact Hnode.
    Qed.

    Lemma tryRemove_triple t l :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActive t (ltryRemove l) }}
          (@SPListUnlinkImpl.tryRemove_impl A l t)
        {{ fun ret => SCompleted t (ltryRemove l) ret }}.
    Proof.
      eapply SetLogic.provable_perror.
      - apply tryRemove_active_valid_or_error.
      - apply tryRemove_valid_triple.
    Qed.


    (** ** insert *)

    Lemma skips_alloc h l n xs p :
      h l = None -> skips h xs p -> skips (heap_update l n h) xs p.
    Proof.
      intros Hl H. eapply skips_mono; [|exact H].
      exact (proj1 (structure_evol_alloc h l n Hl)).
    Qed.

    Lemma insert_walked_defined t v q x w :
      InsertWalked t v q (Some x) w -> NodeDefined x w.
    Proof.
      intros [Hread Hsk]. pose proof (insert_read_entails_I _ _ _ _ Hread) as HI.
      eapply source_I_in_log_defined; [exact HI|]. eapply skips_in; exact Hsk.
    Qed.

    Lemma insert_walked_hop t v q x w v' ts nx :
      InsertWalked t v q (Some x) w ->
      heap_of w x = Some (pair (pair (pair v' ts) true) nx) ->
      InsertWalked t v q nx w.
    Proof.
      intros [Hread Hsk] Hcell. split; [exact Hread|].
      pose proof (insert_read_entails_I _ _ _ _ Hread) as HI.
      unfold SkipsLog in *.
      destruct (skips_some_split _ _ _ Hsk) as (a & b & Hab & Ha).
      pose proof (source_I_rep _ HI) as ((_ & _ & Hlk) & _).
      rewrite Hab in Hlk.
      destruct (links_ok_split _ _ _ _ Hlk) as [n [Hn Hskn]].
      rewrite Hcell in Hn. injection Hn as <-. simpl in Hskn.
      rewrite Hab.
      replace (a ++ x :: b) with ((a ++ x :: nil) ++ b)
        by (rewrite <- app_assoc; reflexivity).
      apply skips_app_taken; [|exact Hskn].
      apply all_taken_app; [exact Ha|]. constructor; [|constructor].
      unfold taken_at. rewrite Hcell. reflexivity.
    Qed.

    Lemma insert_get_inv_update t v :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (in_cas get)))
        (ActiveOwned t (linsert v)) (ActiveOwned t (linsert v)).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      destruct Hpre as [[HIpre Hlin] Howner].
      pose proof (source_I_mem_control _ HIpre) as Hmc. simpl in Hmc.
      split.
      - split; [split; [|exact Hlin]|exact Howner].
        eapply source_I_controls; [exact HIpre|reflexivity|reflexivity|exact Hmc|exact I].
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply source_I_controls; [exact HIpre|reflexivity|reflexivity|exact Hmc|exact I])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma insert_get_res_update t v q :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_cas get) q))
        (ActiveOwned t (linsert v)) (InsertRead t v q).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      destruct Hpre as [[HIpre Hlin] Howner].
      pose proof (source_I_mem_control _ HIpre) as Hmc. simpl in Hmc.
      pose proof (source_I_rep _ HIpre) as ((_ & Hsk & _) & _).
      unfold heap_of, reg_of, log_of in Hsk. simpl in Hsk.
      split.
      - split; [split; [split; [|exact Hlin]|exact Howner]|].
        + eapply source_I_controls; [exact HIpre|reflexivity|reflexivity|exact Hmc|exact I].
        + split.
          * unfold CountIs, reg_of. simpl. reflexivity.
          * unfold SkipsLog, heap_of, log_of. simpl. exact Hsk.
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply source_I_controls; [exact HIpre|reflexivity|reflexivity|exact Hmc|exact I])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma insert_malloc_inv_update t v q p :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmalloc v p))))
        (InsertWalked t v q p) (InsertWalked t v q p).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      pose proof (insert_walked_entails_I _ _ _ _ _ Hpre) as HIpre.
      pose proof (proj2 (proj1 (proj1 Hpre))) as Howner.
      pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
      split.
      - eapply insert_walked_controls; [exact Hpre|reflexivity|reflexivity|exact Howner|exact Hcc].
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply insert_walked_entails_I; eapply insert_walked_controls;
                [exact Hpre|reflexivity|reflexivity|exact Howner|exact Hcc])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma insert_malloc_res_update t v q p l :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_mem (nmalloc v p)) l))
        (InsertWalked t v q p) (InsertAllocated t v q p l).
    Proof.
      pupdate_intros_atomic.
      match goal with H : _ _ = None |- _ => rename H into Hfresh end.
      pupdate_finish.
      destruct Hpre as [[[[HIpre Hlin] Howner] [Hcount Hsk0]] Hsk].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & log & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc. subst ρ1.
      simpl in Hrep.
      pose proof Hrep as Hrep0.
      destruct Hrep as (Hvalid & Hcnt & Hlen & Hnodes & Horder).
      unfold CountIs, reg_of in Hcount. unfold SkipsLog, heap_of, log_of in Hsk0, Hsk.
      simpl in Hcount, Hsk0, Hsk.
      assert (Hnotin : ~ In l log).
      { intro Hin. eapply represents_defined; [exact Hrep0|exact Hin|exact Hfresh]. }
      match goal with
      | |- context [Idle (heap_update ?ll ?nn ?hh) ] =>
          assert (HIpost : source_I
            (mk (pair (Idle (heap_update ll nn hh)) s2) (pair (Ready s) log) π1))
      end.
      { apply source_I_build; [exact I|exact Hcc| |exact Hsnap].
        eapply represents_allocate; [exact Hrep0|exact Hfresh]. }
      split.
      - split; [|split].
        + split.
          * split; [split; [split; [exact HIpost|exact Hlin]|exact Howner]|].
            split.
            -- unfold CountIs, reg_of. simpl. exact Hcount.
            -- unfold SkipsLog, heap_of, log_of. simpl. apply skips_alloc; assumption.
          * unfold SkipsLog, heap_of, log_of. simpl. apply skips_alloc; assumption.
        + unfold NodeUndefined, payload_of, ctrl_of. simpl. rewrite Hnodes.
          apply abstract_nodes_notin. exact Hnotin.
        + unfold heap_of. simpl. apply HeapUpdateSelf.
      - unfold source_G. split; [exact HIpre0|]. split; [exact HIpost|].
        split; [simpl; rewrite Howner; eapply heap_evol_allocate; exact Hfresh|].
        split; [intros q' Hnotowner; exfalso; apply Hnotowner; exact Howner|].
        split; [split; [intros _; reflexivity|exists nil; split; reflexivity]|].
        split; intros; reflexivity.
    Qed.

    Lemma insert_set_inv_update t v q p l :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@InvEv (li_sig E) (in_cas (set (pair (Some l) (S (snd q)))))))
        (InsertAllocated t v q p l) (InsertAllocated t v q p l).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      pose proof (insert_allocated_entails_I _ _ _ _ _ _ Hpre) as HIpre.
      pose proof (proj2 (proj1 (proj1 (proj1 Hpre)))) as Howner.
      pose proof (source_I_mem_control _ HIpre) as Hmc. simpl in Hmc.
      split.
      - eapply insert_allocated_controls; [exact Hpre|reflexivity|reflexivity|exact Hmc|exact Howner].
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply insert_allocated_entails_I; eapply insert_allocated_controls;
                [exact Hpre|reflexivity|reflexivity|exact Hmc|exact Howner])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma insert_set_res_update t v q p l :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (in_cas (set (pair (Some l) (S (snd q))))) tt))
        (InsertAllocated t v q p l)
        (Completed t (linsert v) l).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [[[[[HIpre Hlin] Howner] [Hcount Hsk0]] Hsk] [Hundef Hcell]].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & log & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc. subst ρ1.
      simpl in Hrep.
      unfold CountIs, reg_of in Hcount. unfold SkipsLog, heap_of, log_of in Hsk.
      unfold NodeUndefined, payload_of, ctrl_of in Hundef. unfold heap_of in Hcell.
      simpl in Hcount, Hsk, Hundef, Hcell.
      pupdate_start.
      gstep_inv t (@linsert A v) (pair (AtomicPending s t (@linsert A v)) log).
      { constructor. exact Howner. }
      gstep_ret t (@linsert A v) l (pair (Ready (SPListSpec.insert v l s)) (l :: log)).
      { constructor. exact Hundef. }
      apply rt_refl.
      match goal with
      | |- context [Idle (pair (Some l) (S (snd q))) ] =>
          assert (HIpost : source_I
            (mk (pair s1 (Idle (pair (Some l) (S (snd q)))))
                (pair (Ready (SPListSpec.insert v l s)) (l :: log))
                (TMap.add t (ls_linr (linsert v) l)
                  (TMap.add t (ls_lini (linsert v)) π1))))
      end.
      { apply source_I_build; [exact Hmc|exact I| |].
        - simpl. rewrite <- Hcount.
          eapply represents_publish; [exact Hrep|exact Hundef|exact Hcell|exact Hsk].
        - eapply snapshot_consistent_atomic; [exact Hsnap|exact Hlin]. }
      split.
      - split; [exact HIpost|].
        unfold ALin. simpl. rewrite TMap.gss. reflexivity.
      - unfold source_G. split; [exact HIpre0|]. split; [exact HIpost|].
        split; [simpl; apply heap_evol_refl|].
        split; [intros q' Hnotowner; exfalso; apply Hnotowner; exact Howner|].
        split.
        { split; [intros Hno; exfalso; apply Hno; exact Howner|].
          exists (l :: nil). split; [reflexivity|].
          intros Hno; exfalso; apply Hno; exact Howner. }
        split; [intros r Hneq; simpl; reflexivity|].
        intros r Hneq. simpl. repeat rewrite TMap.gso by exact Hneq. reflexivity.
    Qed.

    Lemma insert_valid_triple t v :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ lift_assert (ActiveOwned t (linsert v)) }}
          (@SPListUnlinkImpl.insert_impl A v t)
        {{ fun l => SCompleted t (linsert v) l }}.
    Proof.
      unfold SPListUnlinkImpl.insert_impl.
      eapply singleton_provable_vis_safe with
        (P' := ActiveOwned t (linsert v))
        (Q' := fun q => InsertRead t v q).
      - intros w Hpre Herror.
        destruct (SinglePossState.σ w) as [mc cc]. simpl in Herror.
        dependent destruction Herror.
      - apply active_owned_entails_I.
      - intros q. apply insert_read_entails_I.
      - apply active_owned_stable.
      - intros q. apply insert_read_stable.
      - apply insert_get_inv_update.
      - intros q. apply insert_get_res_update.
      - intros q. destruct q as [top count]. simpl.
        eapply SetLogic.provable_seq with
          (Q' := fun p => lift_assert (InsertWalked t v (pair top count) p)).
        + eapply SetLogic.provable_conseq_weak_pre with
            (P' := lift_assert (InsertWalked t v (pair top count) top)).
          * intros w H ρ π Hposs. pose proof (H _ _ Hposs) as Hread.
            split; [exact Hread|]. exact (proj2 (proj2 Hread)).
          * apply (walk_triple t (InsertWalked t v (pair top count))).
            -- intros p w H. eapply insert_walked_entails_I; exact H.
            -- intros p. apply insert_walked_stable.
            -- intros p. apply slot_local_insert_walked.
            -- intros x w H. eapply insert_walked_defined; exact H.
            -- intros p σ ρ π mc' cc' H. eapply insert_walked_controls; exact H.
            -- intros x w v' ts nx H Hcell. eapply insert_walked_hop; eauto.
        + intros p.
          eapply singleton_provable_vis_safe with
            (P' := InsertWalked t v (pair top count) p)
            (Q' := fun l => InsertAllocated t v (pair top count) p l).
          * intros w Hpre Herror.
            destruct (SinglePossState.σ w) as [mc cc]. simpl in Herror.
            dependent destruction Herror.
          * apply insert_walked_entails_I.
          * intros l. apply insert_allocated_entails_I.
          * apply insert_walked_stable.
          * intros l. apply insert_allocated_stable.
          * apply insert_malloc_inv_update.
          * intros l. apply insert_malloc_res_update.
          * intros l.
            eapply singleton_provable_vis_safe with
              (P' := InsertAllocated t v (pair top count) p l)
              (Q' := fun _ : unit => Completed t (linsert v) l).
            -- intros w Hpre Herror.
               pose proof (proj2 (proj1 (proj1 (proj1 Hpre)))) as Howner.
               pose proof (insert_allocated_entails_I _ _ _ _ _ _ Hpre) as HI.
               destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
               simpl in Herror. dependent destruction Herror.
               pose proof (source_I_cas_control _ HI) as Hok.
               rewrite Eσ in Hok. simpl in Hok. congruence.
            -- apply insert_allocated_entails_I.
            -- intros []; apply completed_entails_I.
            -- apply insert_allocated_stable.
            -- intros []; apply completed_stable.
            -- apply insert_set_inv_update.
            -- intros []; apply insert_set_res_update.
            -- intros []. singleton_ret_safe.
               ++ apply ImplRefl.
               ++ apply completed_entails_I.
               ++ apply completed_stable.
            -- apply insert_allocated_entails_I.
            -- apply slot_local_insert_allocated.
            -- intros []. apply slot_local_completed.
          * apply insert_walked_entails_I.
          * apply slot_local_insert_walked.
          * intros l. apply slot_local_insert_allocated.
      - apply active_owned_entails_I.
      - apply slot_local_active_owned.
      - intros q. apply slot_local_insert_read.
    Qed.

    Lemma insert_active_valid_or_error t v :
      ⊨ SActive t (linsert v) ==>>
        lift_assert (ActiveOwned t (linsert v)) \\// AssertionsSet.APError.
    Proof.
      intros w Hall.
      destruct (ac_nonempty (SetPossState.Δ w)) as (ρ0 & π0 & Hposs0).
      pose proof (Hall _ _ Hposs0) as [HI0 Hlin0].
      destruct (PositiveMap.E.eq_dec t owner) as [Howner|Howner].
      - left. intros ρ π Hposs. split; [apply Hall, Hposs|exact Howner].
      - right. destruct HI0 as
          (mc & cc & s & log & Eσ & Eρ & _).
        econstructor; [exact Hposs0|].
        apply rt_step. eapply ps_error; [|exact Hlin0].
        simpl in Eρ. rewrite Eρ. simpl.
        eapply (@error_linsert_not_owner A owner t s v _); eauto.
    Qed.

    Lemma insert_triple t v :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActive t (linsert v) }}
          (@SPListUnlinkImpl.insert_impl A v t)
        {{ fun l => SCompleted t (linsert v) l }}.
    Proof.
      eapply SetLogic.provable_perror.
      - apply insert_active_valid_or_error.
      - apply insert_valid_triple.
    Qed.

    (** ** getTop: the register read *)

    Lemma represents_start_snapshot h top count s log t :
      represents h top count s log ->
      represents h top count (start_snapshot t s) log.
    Proof.
      intros (Hv & Hc & Hl & Hn & Ho). split; [exact Hv|].
      split; [exact Hc|]. split; [exact Hl|]. split; [exact Hn|exact Ho].
    Qed.

    Lemma represents_clear_snapshot h top count s log t :
      represents h top count s log ->
      represents h top count (clear_snapshot t s) log.
    Proof.
      intros (Hv & Hc & Hl & Hn & Ho). split; [exact Hv|].
      split; [exact Hc|]. split; [exact Hl|]. split; [exact Hn|exact Ho].
    Qed.

    Lemma getTop_get_inv_update t :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (in_cas get)))
        (Active t (@lgetTop A)) (Active t (@lgetTop A)).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      destruct Hpre as [HIpre Hlin].
      pose proof (source_I_mem_control _ HIpre) as Hmc. simpl in Hmc.
      split.
      - split; [|exact Hlin].
        eapply source_I_controls; [exact HIpre|reflexivity|reflexivity|exact Hmc|exact I].
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply source_I_controls; [exact HIpre|reflexivity|reflexivity|exact Hmc|exact I])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma getTop_get_res_update t q :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_cas get) q))
        (Active t (@lgetTop A))
        (GetTopLoop t (snd q) (fst q)).
    Proof.
      pupdate_intros_atomic.
      destruct Hpre as [HIpre Hlin]. pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & log & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc. subst ρ1.
      simpl in Hrep. pose proof Hrep as Hrep0.
      destruct Hrep as (Hvalid & Hcount & Hlength & Hnodes & Horder).
      assert (Hsnapshot_none : TMap.find t (snapshot s) = None).
      { destruct (TMap.find t (snapshot s)) as [saved|] eqn:Hfind;
          [|reflexivity].
        pose proof (proj1 (Hsnap t) (ex_intro _ saved Hfind)) as Hbad.
        unfold ALin in Hlin. simpl in Hlin. simpl in Hbad.
        pose proof (eq_trans (eq_sym Hlin) Hbad) as Habs. discriminate Habs. }
      destruct q as [top count]. simpl in *.
      destruct top as [l|].
      - pupdate_start.
        gstep_inv t (@lgetTop A) (pair (Ready (start_snapshot t s)) log).
        { constructor. exact Hsnapshot_none. }
        apply rt_refl.
        assert (HIpost : source_I
          (mk (pair s1 (Idle (pair (Some l) count)))
              (pair (Ready (start_snapshot t s)) log)
              (TMap.add t (ls_lini (@lgetTop A)) π1))).
        { apply source_I_build; [exact Hmc|exact I| |].
          - apply represents_start_snapshot. exact Hrep0.
          - eapply snapshot_consistent_getTop_inv; eauto. }
        split.
        + simpl. exists (order s), log, nil, log.
          split; [exact HIpost|].
          split; [unfold ALin; simpl; rewrite TMap.gss; reflexivity|].
          split.
          { unfold payload_of, ctrl_of. simpl. rewrite TMap.gss, Hcount. reflexivity. }
          split; [reflexivity|].
          split; [exists nil; reflexivity|].
          split; [exact Hlength|].
          split; [intros x Hx; contradiction|].
          split; [unfold heap_of; simpl; exact (proj1 (proj2 Hvalid))|].
          split; [rewrite Horder, live_order_filter; apply subseq_filter|].
          intros x Hx Hlive. rewrite Horder. apply live_order_spec; [exact (proj1 Hvalid)|].
          split; [exact Hx|]. unfold heap_of in Hlive. simpl in Hlive. exact Hlive.
        + unfold source_G. split; [exact HIpre0|]. split; [exact HIpost|].
          split; [simpl; apply heap_evol_refl|].
          split; [intros q' _ _; reflexivity|].
          split; [split; [intros _; reflexivity|exists nil; split; reflexivity]|].
          split.
          * intros r Hneq. unfold ctrl_of. simpl. rewrite TMap.gso by exact Hneq. reflexivity.
          * intros r Hneq. simpl. rewrite TMap.gso by exact Hneq. reflexivity.
      - assert (Horder_nil : order s = nil).
        { rewrite Horder. apply live_order_all_dead. apply all_taken_dead.
          apply skips_none_taken. exact (proj1 (proj2 Hvalid)). }
        pupdate_start.
        gstep_inv t (@lgetTop A) (pair (Ready (start_snapshot t s)) log).
        { constructor. exact Hsnapshot_none. }
        gstep_ret t (@lgetTop A) (@inr (@LNode A) nat count)
          (pair (Ready (clear_snapshot t (start_snapshot t s))) log).
        { constructor. unfold actual_snapshot. simpl. rewrite TMap.gss. simpl.
          rewrite Horder_nil, Hcount. reflexivity. }
        apply rt_refl.
        assert (HIpost : source_I
          (mk (pair s1 (Idle (pair None count)))
              (pair (Ready (clear_snapshot t (start_snapshot t s))) log)
              (TMap.add t (ls_linr (@lgetTop A) (@inr (@LNode A) nat count))
                (TMap.add t (ls_lini (@lgetTop A)) π1)))).
        { apply source_I_build; [exact Hmc|exact I| |].
          - apply represents_clear_snapshot, represents_start_snapshot. exact Hrep0.
          - eapply snapshot_consistent_getTop_res.
            + eapply snapshot_consistent_getTop_inv; eauto.
            + rewrite TMap.gss. reflexivity. }
        split.
        + simpl. split; [exact HIpost|].
          unfold ALin. simpl. rewrite TMap.gss. reflexivity.
        + unfold source_G. split; [exact HIpre0|]. split; [exact HIpost|].
          split; [simpl; apply heap_evol_refl|].
          split; [intros q' _ _; reflexivity|].
          split; [split; [intros _; reflexivity|exists nil; split; reflexivity]|].
          split.
          * intros r Hneq. unfold ctrl_of. simpl.
            rewrite TMap.gro, TMap.gso by exact Hneq. reflexivity.
          * intros r Hneq. simpl. repeat rewrite TMap.gso by exact Hneq. reflexivity.
    Qed.


    (** ** [getTop]: per-field reads and the two-possibility window

        As in [SPListProof]: the value is immutable, the timestamp is set
        once and the taken flag flipped once, so a node observed untaken
        after its timestamp was read was untaken, with that timestamp, at
        the timestamp read, which is the linearization point.  Between the
        two reads both the scanning and the returned possibility are kept.
        The successor read before the timestamp is remembered as a skip
        pointer into the suffix after the node, which stays valid when the
        node's remover rewrites the successor. *)

    Definition NodeValC (l : Addr) (v : A) (σ : concrete_state) : Prop :=
      exists ts taken nx,
        mem_heap (fst σ) l = Some (pair (pair (pair v ts) taken) nx).

    Definition GetTopScanVal (t : tid) (count : nat) (l : Addr) (v : A) :
        assertion :=
      GetTopScan t count (Some l) //\\ NodeVal l v.

    Definition GetTopScanAt (t : tid) (count : nat) (l : Addr) (v : A)
        (nx : Ptr) : assertion :=
      GetTopScan t count (Some l) //\\ NodeVal l v //\\ SkipsAfter l nx.

    Definition GetTopKind (t : tid) (count : nat) (l : Addr) (v : A)
        (nx : Ptr) (ts : TS) : assertion :=
      fun w => GetTopScanAt t count l v nx w \/ GetTopDone t count l v ts w.

    Definition GetTopWindow (t : tid) (count : nat) (l : Addr) (v : A)
        (nx : Ptr) (ts : TS) : set_assertion :=
      fun s =>
        lift_assert (GetTopKind t count l v nx ts) s /\
        NodeValC l v (SetPossState.σ s) /\
        HasKind kind_lini t s /\
        (live_at (mem_heap (fst (SetPossState.σ s))) l = true ->
          HasKind kind_linr t s).

    Definition GetTopTakenPost (t : tid) (count : nat) (l : Addr) (v : A)
        (nx : Ptr) (ts : TS) (b : bool) : assertion :=
      if b then GetTopLoop t count nx else GetTopDone t count l v ts.

    (** *** Normal form of a scan at a node *)

    Lemma scan_core_some_split t count saved logS prefix suffix l w :
      ScanCore t count saved logS prefix suffix (Some l) w ->
      exists tp tl, suffix = tp ++ l :: tl /\ all_taken (heap_of w) tp /\
        ScanCore t count saved logS (prefix ++ tp) (l :: tl) (Some l) w.
    Proof.
      intros (HI & Hlin & Hsnap & HlogS & Hlog & Hlen & Hdead & Hsk & Hsub & Hlive).
      destruct (skips_some_split _ _ _ Hsk) as (tp & tl & -> & Htp).
      exists tp, tl. split; [reflexivity|]. split; [exact Htp|].
      split; [exact HI|]. split; [exact Hlin|]. split; [exact Hsnap|].
      split; [rewrite HlogS, <- app_assoc; reflexivity|].
      split; [exact Hlog|]. split; [exact Hlen|].
      split.
      { intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx].
        - apply Hdead. exact Hx.
        - eapply all_taken_dead; [exact Htp|exact Hx]. }
      split; [constructor|]. split; [exact Hsub|]. exact Hlive.
    Qed.

    Lemma scan_core_in_log t count saved logS prefix suffix p w x :
      ScanCore t count saved logS prefix suffix p w -> In x logS -> In x (log_of w).
    Proof.
      intros (_ & _ & _ & _ & [extra Hlog] & _) Hx. rewrite Hlog.
      apply in_or_app. right. exact Hx.
    Qed.

    Lemma NoDup_app_right_part (a b : list Addr) : NoDup (a ++ b) -> NoDup b.
    Proof.
      induction a as [|x a IH]; intros H; [exact H|].
      simpl in H. inversion H; subst. apply IH. assumption.
    Qed.

    Lemma scan_core_nodup_logS t count saved logS prefix suffix p w :
      ScanCore t count saved logS prefix suffix p w -> NoDup logS.
    Proof.
      intros (HI & _ & _ & _ & [extra Hlog] & _).
      pose proof (source_I_rep _ HI) as ((Hnd & _) & _).
      rewrite Hlog in Hnd. eapply NoDup_app_right_part. exact Hnd.
    Qed.

    Lemma scan_core_saved_in_log t count saved logS prefix suffix p w :
      ScanCore t count saved logS prefix suffix p w ->
      List.Forall (fun x => In x (log_of w)) saved.
    Proof.
      intros Hscan. pose proof Hscan as (_ & _ & _ & _ & _ & _ & _ & _ & Hsub & _).
      apply Forall_forall. intros x Hx.
      eapply scan_core_in_log; [exact Hscan|]. eapply subseq_in; eauto.
    Qed.

    (** The actual snapshot of the scanning thread is the saved list
        filtered by liveness now. *)
    Lemma scan_core_actual_snapshot t count saved logS prefix suffix p σ s log π :
      ScanCore t count saved logS prefix suffix p (mk σ (pair (Ready s) log) π) ->
      actual_snapshot t s =
        Some (pair (List.filter (live_at (mem_heap (fst σ))) saved) count).
    Proof.
      intros Hscan. pose proof Hscan as (HI & _ & Hsnap & _).
      pose proof (source_I_rep _ HI) as Hrep.
      pose proof Hrep as ((Hnd & _) & _ & _ & _ & Horder).
      unfold payload_of, ctrl_of in Hsnap. simpl in Hsnap.
      unfold actual_snapshot. rewrite Hsnap.
      unfold heap_of, log_of, payload_of, ctrl_of in Horder. simpl in Horder.
      rewrite Horder.
      rewrite (filter_order_membership _ _ _ Hnd).
      - reflexivity.
      - pose proof (scan_core_saved_in_log _ _ _ _ _ _ _ _ Hscan) as Hall.
        unfold log_of in Hall. simpl in Hall. exact Hall.
    Qed.

    (** A scan positioned at a live node: the node heads the actual
        snapshot, and the data for the final CAS. *)
    Lemma scan_complete_facts t count saved logS prefix tl l v ts nx σ s log π :
      ScanCore t count saved logS prefix (l :: tl) (Some l) (mk σ (pair (Ready s) log) π) ->
      mem_heap (fst σ) l = Some (pair (pair (pair v ts) false) nx) ->
      (exists rest, actual_snapshot t s = Some (pair (l :: rest) count)) /\
      nodes s l = Some (pair v ts) /\
      TMap.find t π = Some (ls_lini (@lgetTop A)) /\
      DoneData count l (mk σ (pair (Ready s) log) π).
    Proof.
      intros Hscan Hcell.
      pose proof (scan_core_actual_snapshot _ _ _ _ _ _ _ _ _ _ _ Hscan) as Hactual.
      pose proof Hscan as (HI & Hlin & Hsnap & HlogS & Hlog & Hlen & Hdead & Hsk & Hsub & Hlive).
      pose proof (scan_core_nodup_logS _ _ _ _ _ _ _ _ Hscan) as HndS.
      assert (Hlivel : live_at (mem_heap (fst σ)) l = true).
      { unfold live_at, node_live. rewrite Hcell. reflexivity. }
      assert (Hinl : In l saved).
      { apply Hlive; [rewrite HlogS; apply in_or_app; right; now left|exact Hlivel]. }
      rewrite HlogS in HndS, Hsub.
      destruct (subseq_around _ _ _ _ HndS Hsub Hinl) as (s1 & s2 & -> & Hs1).
      split.
      { exists (List.filter (live_at (mem_heap (fst σ))) s2).
        rewrite Hactual. f_equal. f_equal.
        rewrite filter_app. cbn [List.filter]. rewrite Hlivel.
        replace (List.filter (live_at (mem_heap (fst σ))) s1) with (@nil Addr).
        - reflexivity.
        - symmetry. rewrite <- live_order_filter. apply live_order_all_dead.
          intros x Hx. apply Hdead. apply Hs1. exact Hx. }
      split.
      { pose proof (source_I_rep _ HI) as Hrep.
        assert (Hin : In l (log_of (mk σ (pair (Ready s) log) π))).
        { eapply scan_core_in_log; [exact Hscan|]. rewrite HlogS. apply in_or_app. right. now left. }
        destruct (represents_abstract_in _ _ _ _ _ _ Hrep Hin) as [n [Hn Hnode]].
        unfold heap_of in Hn. cbn [mk SinglePossState.σ] in Hn.
        rewrite Hcell in Hn. injection Hn as <-.
        unfold payload_of, ctrl_of in Hnode. simpl in Hnode. exact Hnode. }
      split; [unfold ALin in Hlin; simpl in Hlin; exact Hlin|].
      exists logS, prefix, tl. split; [exact HlogS|]. split; [exact Hlog|].
      split; [exact Hlen|]. exact Hdead.
    Qed.

    Lemma getTop_complete_step t count saved logS prefix tl l v ts nx σ s log π :
      ScanCore t count saved logS prefix (l :: tl) (Some l) (mk σ (pair (Ready s) log) π) ->
      mem_heap (fst σ) l = Some (pair (pair (pair v ts) false) nx) ->
      Step (li_lts F)
        (Build_ThreadEvent t
          (ResEv (@lgetTop A) (@inl (@LNode A) nat (pair (pair v ts) l))))
        (pair (Ready s) log) (pair (Ready (clear_snapshot t s)) log).
    Proof.
      intros Hscan Hcell.
      destruct (scan_complete_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hscan Hcell)
        as ([rest Hactual] & Hnode & _ & _).
      split; [|reflexivity]. simpl.
      eapply step_getTop_nonEmpty; [exact Hactual|exact Hnode].
    Qed.

    (** A scan at a taken node whose remembered successor is [None]: every
        saved node is dead. *)
    Lemma getTop_empty_step t count l v σ s log π :
      GetTopScanAt t count l v None (mk σ (pair (Ready s) log) π) ->
      taken_at (mem_heap (fst σ)) l = true ->
      Step (li_lts F)
        (Build_ThreadEvent t
          (ResEv (@lgetTop A) (@inr (@LNode A) nat count)))
        (pair (Ready s) log) (pair (Ready (clear_snapshot t s)) log).
    Proof.
      intros [ (saved & logS & prefix & suffix & Hscan0) [_ Hsk]] Htaken.
      destruct (scan_core_some_split _ _ _ _ _ _ _ _ Hscan0) as (tp & tl & -> & Htp & Hscan).
      pose proof (scan_core_actual_snapshot _ _ _ _ _ _ _ _ _ _ _ Hscan) as Hactual.
      pose proof Hscan as (HI & _ & _ & HlogS & [extra Hlog] & _ & Hdead & _ & Hsub & _).
      assert (Htl : all_taken (mem_heap (fst σ)) tl).
      { apply skips_none_taken.
        apply (Hsk (extra ++ prefix ++ tp) tl).
        unfold log_of. simpl. unfold log_of in Hlog. simpl in Hlog.
        rewrite Hlog, HlogS, !app_assoc. reflexivity. }
      assert (Hall : forall x, In x saved -> live_at (mem_heap (fst σ)) x = false).
      { intros x Hx. pose proof (subseq_in _ _ _ Hsub Hx) as Hx'.
        rewrite HlogS in Hx'. apply in_app_or in Hx'. destruct Hx' as [Hx'|Hx'].
        - apply Hdead. exact Hx'.
        - destruct Hx' as [<-|Hx'].
          + apply taken_live_false. exact Htaken.
          + eapply all_taken_dead; [exact Htl|exact Hx']. }
      split; [|reflexivity]. simpl.
      eapply step_getTop_empty. rewrite Hactual. f_equal. f_equal.
      rewrite <- live_order_filter. apply live_order_all_dead. exact Hall.
    Qed.

    (** A scan at a taken node moves on to the remembered successor. *)
    Lemma getTop_shift_scan t count l v l' w :
      GetTopScanAt t count l v (Some l') w ->
      taken_at (heap_of w) l = true ->
      GetTopScan t count (Some l') w.
    Proof.
      intros [ (saved & logS & prefix & suffix & Hscan0) [_ Hsk]] Htaken.
      destruct (scan_core_some_split _ _ _ _ _ _ _ _ Hscan0) as (tp & tl & -> & Htp & Hscan).
      pose proof Hscan as (HI & Hlin & Hsnap & HlogS & [extra Hlog] & Hlen & Hdead & _ & Hsub & Hlive).
      exists saved, logS, ((prefix ++ tp) ++ l :: nil), tl.
      split; [exact HI|]. split; [exact Hlin|]. split; [exact Hsnap|].
      split; [rewrite HlogS, <- !app_assoc; reflexivity|].
      split; [exists extra; exact Hlog|]. split; [exact Hlen|].
      split.
      { intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|[<-|[]]].
        - apply Hdead. exact Hx.
        - apply taken_live_false. exact Htaken. }
      split.
      { apply (Hsk (extra ++ prefix ++ tp) tl).
        rewrite Hlog, HlogS, !app_assoc. reflexivity. }
      split; [exact Hsub|]. exact Hlive.
    Qed.

    Lemma getTop_done_from_scan t count saved logS prefix tl l v ts nx w :
      ScanCore t count saved logS prefix (l :: tl) (Some l) w ->
      heap_of w l = Some (pair (pair (pair v ts) false) nx) ->
      DoneData count l w.
    Proof.
      intros (_ & _ & _ & HlogS & Hlog & Hlen & Hdead & _) _.
      exists logS, prefix, tl. split; [exact HlogS|]. split; [exact Hlog|].
      split; [exact Hlen|]. exact Hdead.
    Qed.

    (** *** Stability *)

    Lemma getTop_scan_val_entails_I t count l v :
      ⊨ GetTopScanVal t count l v ==>> source_I.
    Proof. intros w [H _]. eapply getTop_scan_entails_I; exact H. Qed.

    Lemma getTop_scan_at_entails_I t count l v nx :
      ⊨ GetTopScanAt t count l v nx ==>> source_I.
    Proof. intros w [H _]. eapply getTop_scan_entails_I; exact H. Qed.

    Lemma getTop_scan_val_stable t count l v :
      AssertionsSingle.A.Stable (source_R t) source_I
        (GetTopScanVal t count l v).
    Proof.
      unfold AssertionsSingle.A.Stable.
      intros out [[pre [[Hscan Hval] HR]] HIout]. split.
      - eapply getTop_scan_stable.
        split; [exists pre; split; [exact Hscan|exact HR] | exact HIout].
      - eapply node_val_stable; eauto.
    Qed.

    Lemma getTop_scan_in_log t count l w :
      GetTopScan t count (Some l) w -> In l (log_of w).
    Proof.
      intros (saved & logS & prefix & suffix & Hscan).
      pose proof Hscan as (_ & _ & _ & HlogS & _ & _ & _ & Hsk & _).
      eapply scan_core_in_log; [exact Hscan|].
      rewrite HlogS. apply in_or_app. right. eapply skips_in. exact Hsk.
    Qed.

    Lemma getTop_scan_at_stable t count l v nx :
      AssertionsSingle.A.Stable (source_R t) source_I
        (GetTopScanAt t count l v nx).
    Proof.
      unfold AssertionsSingle.A.Stable.
      intros out [[pre [[Hscan [Hval Hsk]] HR]] HIout].
      split; [|split].
      - eapply getTop_scan_stable.
        split; [exists pre; split; [exact Hscan|exact HR] | exact HIout].
      - eapply node_val_stable; eauto.
      - eapply skips_after_stable; [exact HR|exact HIout| |exact Hsk].
        eapply getTop_scan_in_log. exact Hscan.
    Qed.

    Lemma slot_local_getTop_scan_val t count l v :
      slot_local t (GetTopScanVal t count l v).
    Proof.
      unfold GetTopScanVal. apply slot_local_conj;
        [apply slot_local_getTop_scan | apply slot_local_node_val].
    Qed.

    Lemma slot_local_getTop_scan_at t count l v nx :
      slot_local t (GetTopScanAt t count l v nx).
    Proof.
      unfold GetTopScanAt. apply slot_local_conj; [apply slot_local_getTop_scan|].
      apply slot_local_conj; [apply slot_local_node_val | apply slot_local_skips_after].
    Qed.

    Lemma getTop_kind_entails_I t count l v nx ts :
      ⊨ GetTopKind t count l v nx ts ==>> source_I.
    Proof.
      intros w [HA | HB]; [eapply getTop_scan_at_entails_I; exact HA
                          | eapply getTop_done_entails_I; exact HB].
    Qed.

    Lemma getTop_window_entails_I t count l v nx ts :
      ⊨ GetTopWindow t count l v nx ts ==>> SI.
    Proof.
      intros s [Hkinds _] ρ π Hposs.
      eapply getTop_kind_entails_I. apply Hkinds, Hposs.
    Qed.

    Lemma node_valC_live_imp t l v x x' :
      source_R t x x' ->
      NodeValC l v (SinglePossState.σ x) ->
      live_at (mem_heap (fst (SinglePossState.σ x'))) l = true ->
      live_at (mem_heap (fst (SinglePossState.σ x))) l = true.
    Proof.
      intros HR (ts & tk & nx & Hcell) Hlive.
      eapply source_R_live_imp; [exact HR| |exact Hlive].
      unfold heap_of. rewrite Hcell. discriminate.
    Qed.

    Lemma getTop_window_stable t count l v nx ts :
      AssertionsSet.A.Stable (R t) SI (GetTopWindow t count l v nx ts).
    Proof.
      unfold AssertionsSet.A.Stable, AssertionsSet.A.ComposeA.
      intros s' [[s [[Hkinds [Hcell [Hlini Hlinr]]] [Hback Htwins]]] HI].
      destruct (ac_nonempty (SetPossState.Δ s')) as (ρ0 & π0 & Hposs0).
      destruct (Hback _ _ Hposs0) as (ρ1 & π1 & Hposs1 & HR0).
      split; [|split; [|split]].
      - intros ρ' π' Hposs'.
        destruct (Hback _ _ Hposs') as (ρ & π & Hposs & HR).
        pose proof (Hkinds _ _ Hposs) as Hk. pose proof (HI _ _ Hposs') as HI'.
        destruct Hk as [HA | HB].
        + left. eapply getTop_scan_at_stable.
          split; [exists (mk (SetPossState.σ s) ρ π); split;
            [exact HA|exact HR] | exact HI'].
        + right. eapply getTop_done_stable.
          split; [exists (mk (SetPossState.σ s) ρ π); split;
            [exact HB|exact HR] | exact HI'].
      - exact (node_val_stable t (mk (SetPossState.σ s) ρ1 π1)
          (mk (SetPossState.σ s') ρ0 π0) l v HR0 Hcell).
      - apply (proj1 Htwins). exact Hlini.
      - intros Hlive. apply (proj2 Htwins). apply Hlinr.
        exact (node_valC_live_imp t l v (mk (SetPossState.σ s) ρ1 π1)
          (mk (SetPossState.σ s') ρ0 π0) HR0 Hcell Hlive).
    Qed.

    Lemma getTop_taken_post_entails_I t count l v nx ts b :
      ⊨ GetTopTakenPost t count l v nx ts b ==>> source_I.
    Proof.
      destruct b; simpl;
        [apply getTop_loop_entails_I | apply getTop_done_entails_I].
    Qed.

    Lemma getTop_taken_post_stable t count l v nx ts b :
      AssertionsSingle.A.Stable (source_R t) source_I
        (GetTopTakenPost t count l v nx ts b).
    Proof.
      destruct b; simpl; [apply getTop_loop_stable | apply getTop_done_stable].
    Qed.

    (** *** Transfer across the controls (same heap, register and log) *)

    Lemma scan_core_controls t count saved logS prefix suffix p σ ρ π mc' cc' :
      ScanCore t count saved logS prefix suffix p (mk σ ρ π) ->
      mem_heap mc' = mem_heap (fst σ) -> cas_value cc' = cas_value (snd σ) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      ScanCore t count saved logS prefix suffix p (mk (pair mc' cc') ρ π).
    Proof.
      intros (HI & Hlin & Hsnap & HlogS & Hlog & Hlen & Hdead & Hsk & Hsub & Hlive)
        Hheap Hcas Hmc Hcc.
      split; [eapply source_I_controls; eauto|].
      split; [exact Hlin|]. split; [exact Hsnap|]. split; [exact HlogS|].
      split; [exact Hlog|]. split; [exact Hlen|].
      unfold heap_of in *. simpl in *. rewrite Hheap.
      split; [exact Hdead|]. split; [exact Hsk|]. split; [exact Hsub|]. exact Hlive.
    Qed.

    Lemma getTop_scan_controls t count p σ ρ π mc' cc' :
      GetTopScan t count p (mk σ ρ π) ->
      mem_heap mc' = mem_heap (fst σ) -> cas_value cc' = cas_value (snd σ) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      GetTopScan t count p (mk (pair mc' cc') ρ π).
    Proof.
      intros (saved & logS & prefix & suffix & Hscan) Hheap Hcas Hmc Hcc.
      exists saved, logS, prefix, suffix. eapply scan_core_controls; eauto.
    Qed.

    Lemma node_val_controls l v σ ρ π mc' cc' :
      NodeVal l v (mk σ ρ π) -> mem_heap mc' = mem_heap (fst σ) ->
      NodeVal l v (mk (pair mc' cc') ρ π).
    Proof.
      intros H Hheap. unfold NodeVal, heap_of in *. simpl in *. rewrite Hheap. exact H.
    Qed.

    Lemma skips_after_controls l p σ ρ π mc' cc' :
      SkipsAfter l p (mk σ ρ π) -> mem_heap mc' = mem_heap (fst σ) ->
      SkipsAfter l p (mk (pair mc' cc') ρ π).
    Proof.
      intros H Hheap. unfold SkipsAfter, heap_of, log_of in *. simpl in *.
      rewrite Hheap. exact H.
    Qed.

    Lemma done_data_controls count l σ ρ π mc' cc' :
      DoneData count l (mk σ ρ π) -> mem_heap mc' = mem_heap (fst σ) ->
      DoneData count l (mk (pair mc' cc') ρ π).
    Proof.
      intros (logS & prefix & tl & HlogS & Hlog & Hlen & Hdead) Hheap.
      exists logS, prefix, tl. split; [exact HlogS|]. split; [exact Hlog|].
      split; [exact Hlen|]. unfold heap_of in *. simpl in *. rewrite Hheap. exact Hdead.
    Qed.

    Lemma getTop_done_controls t count l v ts σ ρ π mc' cc' :
      GetTopDone t count l v ts (mk σ ρ π) ->
      mem_heap mc' = mem_heap (fst σ) -> cas_value cc' = cas_value (snd σ) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      GetTopDone t count l v ts (mk (pair mc' cc') ρ π).
    Proof.
      intros [Hcomp Hdata] Hheap Hcas Hmc Hcc.
      split; [eapply completed_controls; eauto|eapply done_data_controls; eauto].
    Qed.

    Lemma getTop_scan_at_controls t count l v nx σ ρ π mc' cc' :
      GetTopScanAt t count l v nx (mk σ ρ π) ->
      mem_heap mc' = mem_heap (fst σ) -> cas_value cc' = cas_value (snd σ) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      GetTopScanAt t count l v nx (mk (pair mc' cc') ρ π).
    Proof.
      intros [Hscan [Hval Hsk]] Hheap Hcas Hmc Hcc.
      split; [eapply getTop_scan_controls; eauto|].
      split; [eapply node_val_controls; eauto|eapply skips_after_controls; eauto].
    Qed.

    Lemma getTop_kind_controls t count l v nx ts σ ρ π mc' cc' :
      GetTopKind t count l v nx ts (mk σ ρ π) ->
      mem_heap mc' = mem_heap (fst σ) -> cas_value cc' = cas_value (snd σ) ->
      mem_control_ok mc' -> cas_control_ok cc' ->
      GetTopKind t count l v nx ts (mk (pair mc' cc') ρ π).
    Proof.
      intros [HA | HB] Hheap Hcas Hmc Hcc.
      - left. eapply getTop_scan_at_controls; eauto.
      - right. eapply getTop_done_controls; eauto.
    Qed.

    Lemma offslot_agree_refl q x : offslot_agree q x x.
    Proof. split; [reflexivity|]. split; [reflexivity|]. split; intros; reflexivity. Qed.

    Lemma offslot_agree_sym q x y :
      offslot_agree q x y -> offslot_agree q y x.
    Proof.
      intros [Hσ [Hl [Hs Ht]]]. split; [symmetry; exact Hσ|].
      split; [symmetry; exact Hl|].
      split; intros r Hr; symmetry; auto.
    Qed.

    Lemma HasKind_change_σ (K : tid -> single_state -> Prop) q σ1 σ2 Δ :
      (forall σ1 σ2 ρ π, K q (mk σ1 ρ π) -> K q (mk σ2 ρ π)) ->
      HasKind K q (mks σ1 Δ) -> HasKind K q (mks σ2 Δ).
    Proof.
      intros Kσ HK ρ π Hposs.
      destruct (HK ρ π Hposs) as (ρ' & π' & Hposs' & Hoff & Hkind).
      exists ρ', π'. split; [exact Hposs'|]. split.
      - eapply offslot_agree_change_σ. exact Hoff.
      - eapply Kσ. exact Hkind.
    Qed.

    Lemma kind_lini_σ q σ1 σ2 ρ π :
      kind_lini q (mk σ1 ρ π) -> kind_lini q (mk σ2 ρ π).
    Proof. intros H. exact H. Qed.

    Lemma kind_linr_σ q σ1 σ2 ρ π :
      kind_linr q (mk σ1 ρ π) -> kind_linr q (mk σ2 ρ π).
    Proof. intros H. exact H. Qed.

    (** *** The returning possibility *)

    Lemma getTop_ret_completed t ret σ s log π :
      source_I (mk σ (pair (Ready s) log) π) ->
      TMap.find t π = Some (ls_lini (@lgetTop A)) ->
      Completed t (@lgetTop A) ret
        (mk σ (pair (Ready (clear_snapshot t s)) log)
          (TMap.add t (ls_linr (@lgetTop A) ret) π)).
    Proof.
      intros HI Hlin.
      destruct HI as (mc & cc & s0 & log0 & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eρ. inversion Eρ; subst s0 log0.
      split.
      - exists mc, cc, (clear_snapshot t s), log. simpl.
        split; [exact Eσ|]. split; [reflexivity|].
        split; [exact Hmc|]. split; [exact Hcc|]. split.
        + apply represents_clear_snapshot. exact Hrep.
        + eapply snapshot_consistent_getTop_res; eauto.
      - unfold ALin. simpl. rewrite TMap.gss. reflexivity.
    Qed.

    Lemma getTop_ret_G t ret mc cc mc' cc' s log π :
      mem_heap mc' = mem_heap mc ->
      cas_value cc' = cas_value cc ->
      source_I (mk (pair mc cc) (pair (Ready s) log) π) ->
      source_I (mk (pair mc' cc') (pair (Ready (clear_snapshot t s)) log)
        (TMap.add t (ls_linr (@lgetTop A) ret) π)) ->
      source_G t (mk (pair mc cc) (pair (Ready s) log) π)
        (mk (pair mc' cc') (pair (Ready (clear_snapshot t s)) log)
          (TMap.add t (ls_linr (@lgetTop A) ret) π)).
    Proof.
      intros Hheap Hcas HI HI'.
      split; [exact HI|]. split; [exact HI'|].
      cbn [mk SinglePossState.σ SinglePossState.ρ SinglePossState.π fst snd].
      rewrite Hheap, Hcas.
      split; [apply heap_evol_refl|].
      split; [intros; reflexivity|].
      split; [split; [intros _; reflexivity|exists nil; split; reflexivity]|].
      split.
      - intros q Hq. unfold ctrl_of. simpl. rewrite TMap.gro by exact Hq. reflexivity.
      - intros q Hq. simpl. rewrite TMap.gso by exact Hq. reflexivity.
    Qed.

    (** *** Configurations built by the window steps *)

    Definition ret_image_prop (Δ : @AbstractConfig (li_sig F) (li_lts F))
        (t : tid) (ret : Sig.ar (@lgetTop A))
        (Sel : tmap (@LinState (li_sig F)) -> Prop) :
        @AbstractConfigProp (li_sig F) (li_lts F) :=
      fun ρ' π' => exists s log π, Δ (pair (Ready s) log) π /\ Sel π /\
        ρ' = pair (Ready (clear_snapshot t s)) log /\
        π' = TMap.add t (ls_linr (@lgetTop A) ret) π.

    Lemma ret_image_domain (Δ : @AbstractConfig (li_sig F) (li_lts F)) t ret
        (Sel : tmap (@LinState (li_sig F)) -> Prop) :
      (forall ρ π, Δ ρ π -> Sel π ->
        TMap.find t π = Some (ls_lini (@lgetTop A))) ->
      forall ρ' π', ret_image_prop Δ t ret Sel ρ' π' ->
        domain_equiv (map_domain π') (ac_active Δ).
    Proof.
      intros Hlini ρ' π' (s & log & π & Hposs & Hsel & _ & ->).
      eapply domain_equiv_trans; [|eapply ac_domain; exact Hposs].
      intros r. unfold map_domain.
      destruct (PositiveMap.E.eq_dec r t) as [->|Hrt].
      - rewrite TMap.gss, (Hlini _ _ Hposs Hsel).
        split; intros _; eexists; reflexivity.
      - rewrite TMap.gso by exact Hrt. reflexivity.
    Qed.

    Definition fork_prop (Δ : @AbstractConfig (li_sig F) (li_lts F)) t ret :
        @AbstractConfigProp (li_sig F) (li_lts F) :=
      fun ρ' π' => Δ ρ' π' \/ ret_image_prop Δ t ret (fun _ => True) ρ' π'.

    Lemma fork_nonempty (Δ : @AbstractConfig (li_sig F) (li_lts F)) t ret :
      exists ρ π, fork_prop Δ t ret ρ π.
    Proof.
      destruct (ac_nonempty Δ) as (ρ & π & H). exists ρ, π. left. exact H.
    Qed.

    Lemma fork_domain (Δ : @AbstractConfig (li_sig F) (li_lts F)) t ret
        (Hlini : forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_lini (@lgetTop A))) :
      forall ρ π, fork_prop Δ t ret ρ π ->
        domain_equiv (map_domain π) (ac_active Δ).
    Proof.
      intros ρ π [H | H]; [eapply ac_domain; exact H |].
      eapply ret_image_domain; [|exact H].
      intros ρ0 π0 Hposs _. exact (Hlini _ _ Hposs).
    Qed.

    Definition fork_config (Δ : @AbstractConfig (li_sig F) (li_lts F)) t ret Hlini :
        @AbstractConfig (li_sig F) (li_lts F) :=
      {| ac_active := ac_active Δ; ac_prop := fork_prop Δ t ret;
         ac_nonempty := fork_nonempty Δ t ret;
         ac_domain := fork_domain Δ t ret Hlini |}.

    Definition filter_prop (Δ : @AbstractConfig (li_sig F) (li_lts F))
        (Sel : tmap (@LinState (li_sig F)) -> Prop) :
        @AbstractConfigProp (li_sig F) (li_lts F) :=
      fun ρ π => Δ ρ π /\ Sel π.

    Lemma filter_domain (Δ : @AbstractConfig (li_sig F) (li_lts F))
        (Sel : tmap (@LinState (li_sig F)) -> Prop) :
      forall ρ π, filter_prop Δ Sel ρ π ->
        domain_equiv (map_domain π) (ac_active Δ).
    Proof. intros ρ π [H _]. eapply ac_domain; exact H. Qed.

    Definition filter_config (Δ : @AbstractConfig (li_sig F) (li_lts F))
        (Sel : tmap (@LinState (li_sig F)) -> Prop)
        (Hne : exists ρ π, filter_prop Δ Sel ρ π) :
        @AbstractConfig (li_sig F) (li_lts F) :=
      {| ac_active := ac_active Δ; ac_prop := filter_prop Δ Sel;
         ac_nonempty := Hne; ac_domain := filter_domain Δ Sel |}.

    Definition ret_image_config (Δ : @AbstractConfig (li_sig F) (li_lts F)) t ret
        (Sel : tmap (@LinState (li_sig F)) -> Prop) Hlini
        (Hne : exists ρ' π', ret_image_prop Δ t ret Sel ρ' π') :
        @AbstractConfig (li_sig F) (li_lts F) :=
      {| ac_active := ac_active Δ; ac_prop := ret_image_prop Δ t ret Sel;
         ac_nonempty := Hne; ac_domain := ret_image_domain Δ t ret Sel Hlini |}.

    Lemma ret_image_offslot q t ret σ s log π sy πy :
      q <> t ->
      offslot_agree q (mk σ (pair (Ready s) log) π) (mk σ (pair (Ready sy) log) πy) ->
      offslot_agree q
        (mk σ (pair (Ready (clear_snapshot t s)) log)
          (TMap.add t (ls_linr (@lgetTop A) ret) π))
        (mk σ (pair (Ready (clear_snapshot t sy)) log)
          (TMap.add t (ls_linr (@lgetTop A) ret) πy)).
    Proof.
      intros Hqt [_ [_ [Hs Ht]]]. split; [reflexivity|]. split; [reflexivity|]. split.
      - intros r Hr. unfold slot_snapshot, payload_of, ctrl_of. simpl.
        destruct (PositiveMap.E.eq_dec r t) as [->|Hrt].
        + rewrite !TMap.grs. reflexivity.
        + rewrite !TMap.gro by exact Hrt.
          unfold slot_snapshot, payload_of, ctrl_of in Hs. simpl in Hs. exact (Hs r Hr).
      - intros r Hr. unfold slot_token. simpl.
        destruct (PositiveMap.E.eq_dec r t) as [->|Hrt].
        + rewrite !TMap.gss. reflexivity.
        + rewrite !TMap.gso by exact Hrt. exact (Ht r Hr).
    Qed.

    Lemma ret_image_offslot_orig t ret σ s log π :
      offslot_agree t
        (mk σ (pair (Ready (clear_snapshot t s)) log)
          (TMap.add t (ls_linr (@lgetTop A) ret) π))
        (mk σ (pair (Ready s) log) π).
    Proof.
      split; [reflexivity|]. split; [reflexivity|]. split.
      - intros r Hr. unfold slot_snapshot, payload_of, ctrl_of. simpl.
        rewrite TMap.gro by exact Hr. reflexivity.
      - intros r Hr. unfold slot_token. simpl.
        rewrite TMap.gso by exact Hr. reflexivity.
    Qed.

    Lemma ret_image_kind_linr t ret σ s log π :
      kind_linr t
        (mk σ (pair (Ready (clear_snapshot t s)) log)
          (TMap.add t (ls_linr (@lgetTop A) ret) π)).
    Proof.
      exists (@lgetTop A), ret. unfold slot_token. simpl.
      rewrite TMap.gss. reflexivity.
    Qed.

    (** *** Errors *)

    Lemma getTop_value_no_error t count l :
      ⊨ GetTopScan t count (Some l) ==>>
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetValue l)))).
    Proof.
      intros w Hscan Herror.
      pose proof (getTop_scan_in_log _ _ _ _ Hscan) as Hin.
      pose proof (getTop_scan_entails_I _ _ _ _ Hscan) as HI.
      pose proof (source_I_in_log_defined _ _ HI Hin) as Hdef.
      destruct (source_I_defined_lookup _ _ HI Hdef) as (v & ts & tk & nx & Hcell).
      destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
      unfold heap_of in Hcell. rewrite Eσ in Hcell. simpl in Hcell.
      simpl in Herror. dependent destruction Herror. simpl in *. congruence.
    Qed.

    Lemma getTop_next_no_error t count l v :
      ⊨ GetTopScanVal t count l v ==>>
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetNext l)))).
    Proof.
      intros w [_ (ts & tk & nx & Hcell) ] Herror.
      destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
      unfold heap_of in Hcell. rewrite Eσ in Hcell. simpl in Hcell.
      simpl in Herror. dependent destruction Herror. simpl in *. congruence.
    Qed.

    Lemma getTop_ts_no_error t count l v nx :
      ⊨ GetTopScanAt t count l v nx ==>>
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetTS l)))).
    Proof.
      intros w [_ [ (ts & tk & nx' & Hcell) _]] Herror.
      destruct (SinglePossState.σ w) as [mc cc] eqn:Eσ.
      unfold heap_of in Hcell. rewrite Eσ in Hcell. simpl in Hcell.
      simpl in Herror. dependent destruction Herror. simpl in *. congruence.
    Qed.

    Lemma getTop_taken_no_error t count l v nx ts :
      ⊨ GetTopWindow t count l v nx ts ==>>
        AssertionsSet.A.ANoError
          (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetTaken l)))).
    Proof.
      intros s [_ [ (ts' & taken & nx' & Hcell) _] ] Herror.
      destruct (SetPossState.σ s) as [mc cc] eqn:Eσ.
      simpl in Hcell. simpl in Herror. dependent destruction Herror.
      simpl in *. congruence.
    Qed.

    (** *** Twins across the window steps *)

    Lemma filter_twins q t σ1 σ2 (Δ : @AbstractConfig (li_sig F) (li_lts F))
        (Sel : tmap (@LinState (li_sig F)) -> Prop) Hne :
      q <> t ->
      (forall π π', TMap.find t π = TMap.find t π' -> Sel π -> Sel π') ->
      twins_preserved q (mks σ1 Δ) (mks σ2 (filter_config Δ Sel Hne)).
    Proof.
      intros Hq Hsel.
      assert (Hgen : forall K : tid -> single_state -> Prop,
        (forall x y, slot_token q x = slot_token q y -> K q x -> K q y) ->
        HasKind K q (mks σ1 Δ) ->
        HasKind K q (mks σ2 (filter_config Δ Sel Hne))).
      { intros K Ktok HK ρ π [Hposs Hlin].
        destruct (HK _ _ Hposs) as (ρy & πy & Hpossy & Hoff & Hkind).
        exists ρy, πy. split.
        - split; [exact Hpossy|]. destruct Hoff as [_ [_ [_ Ht]]].
          apply (Hsel π πy); [|exact Hlin].
          exact (Ht t (fun Heq => Hq (eq_sym Heq))).
        - split; [eapply offslot_agree_change_σ; exact Hoff|].
          eapply Ktok; [|exact Hkind]. reflexivity. }
      split.
      - intros HK. exact (Hgen kind_lini (kind_lini_token q) HK).
      - intros HK. exact (Hgen kind_linr (kind_linr_token q) HK).
    Qed.

    Lemma ret_image_twins q t ret σ1 σ2 (Δ : @AbstractConfig (li_sig F) (li_lts F))
        (Sel : tmap (@LinState (li_sig F)) -> Prop) Hlini Hne :
      q <> t ->
      (forall ρ π, Δ ρ π -> exists s log, ρ = pair (Ready s) log) ->
      (forall π π', TMap.find t π = TMap.find t π' -> Sel π -> Sel π') ->
      twins_preserved q (mks σ1 Δ)
        (mks σ2 (ret_image_config Δ t ret Sel Hlini Hne)).
    Proof.
      intros Hq Hready Hsel.
      assert (Hgen : forall K : tid -> single_state -> Prop,
        (forall x y, slot_token q x = slot_token q y -> K q x -> K q y) ->
        HasKind K q (mks σ1 Δ) ->
        HasKind K q (mks σ2 (ret_image_config Δ t ret Sel Hlini Hne))).
      { intros K Ktok HK ρ' π' (s & log & π & Hposs & Hlin & -> & ->).
        destruct (HK _ _ Hposs) as (ρy & πy & Hpossy & Hoff & Hkind).
        destruct (Hready _ _ Hpossy) as [sy [logy ->]].
        assert (Hlogeq : logy = log).
        { destruct Hoff as [_ [Hl _]]. unfold log_of, log_of_ctrl in Hl. simpl in Hl.
          symmetry. exact Hl. }
        subst logy.
        exists (pair (Ready (clear_snapshot t sy)) log),
          (TMap.add t (ls_linr (@lgetTop A) ret) πy).
        split.
        - exists sy, log, πy. split; [exact Hpossy|]. split.
          + destruct Hoff as [_ [_ [_ Ht]]]. apply (Hsel π πy); [|exact Hlin].
            exact (Ht t (fun Heq => Hq (eq_sym Heq))).
          + split; reflexivity.
        - split.
          + apply ret_image_offslot; [exact Hq|].
            eapply offslot_agree_change_σ; exact Hoff.
          + eapply Ktok; [|exact Hkind]. unfold slot_token. simpl.
            rewrite TMap.gso by exact Hq. reflexivity. }
      split.
      - intros HK. exact (Hgen kind_lini (kind_lini_token q) HK).
      - intros HK. exact (Hgen kind_linr (kind_linr_token q) HK).
    Qed.

    Lemma fork_twins q t ret σ1 σ2 (Δ : @AbstractConfig (li_sig F) (li_lts F)) Hlini :
      q <> t ->
      (forall ρ π, Δ ρ π -> exists s log, ρ = pair (Ready s) log) ->
      twins_preserved q (mks σ1 Δ) (mks σ2 (fork_config Δ t ret Hlini)).
    Proof.
      intros Hq Hready.
      assert (Hgen : forall K : tid -> single_state -> Prop,
        (forall x y, slot_token q x = slot_token q y -> K q x -> K q y) ->
        HasKind K q (mks σ1 Δ) ->
        HasKind K q (mks σ2 (fork_config Δ t ret Hlini))).
      { intros K Ktok HK ρ' π' [Hposs | (s & log & π & Hposs & _ & -> & ->) ].
        - destruct (HK _ _ Hposs) as (ρy & πy & Hpossy & Hoff & Hkind).
          exists ρy, πy. split; [left; exact Hpossy|].
          split; [eapply offslot_agree_change_σ; exact Hoff|].
          eapply Ktok; [|exact Hkind]. reflexivity.
        - destruct (HK _ _ Hposs) as (ρy & πy & Hpossy & Hoff & Hkind).
          destruct (Hready _ _ Hpossy) as [sy [logy ->]].
          assert (Hlogeq : logy = log).
          { destruct Hoff as [_ [Hl _]]. unfold log_of, log_of_ctrl in Hl. simpl in Hl.
            symmetry. exact Hl. }
          subst logy.
          exists (pair (Ready (clear_snapshot t sy)) log),
            (TMap.add t (ls_linr (@lgetTop A) ret) πy).
          split.
          + right. exists sy, log, πy. split; [exact Hpossy|].
            split; [exact I|]. split; reflexivity.
          + split.
            * apply ret_image_offslot; [exact Hq|].
              eapply offslot_agree_change_σ; exact Hoff.
            * eapply Ktok; [|exact Hkind]. unfold slot_token. simpl.
              rewrite TMap.gso by exact Hq. reflexivity. }
      split.
      - intros HK. exact (Hgen kind_lini (kind_lini_token q) HK).
      - intros HK. exact (Hgen kind_linr (kind_linr_token q) HK).
    Qed.

    Lemma source_I_ready_ex w :
      source_I w -> exists s log, SinglePossState.ρ w = pair (Ready s) log.
    Proof. intros HI. eexists. eexists. exact (source_I_ready _ HI). Qed.


    (** *** Facts about a scan at an untaken node, per possibility *)

    Lemma getTop_scan_at_live_facts t count l v nx σ ρ π ts' nx' :
      GetTopScanAt t count l v nx (mk σ ρ π) ->
      mem_heap (fst σ) l = Some (pair (pair (pair v ts') false) nx') ->
      exists s log, ρ = pair (Ready s) log /\
        Step (li_lts F)
          (Build_ThreadEvent t
            (ResEv (@lgetTop A) (@inl (@LNode A) nat (pair (pair v ts') l))))
          (pair (Ready s) log) (pair (Ready (clear_snapshot t s)) log) /\
        DoneData count l (mk σ ρ π) /\
        TMap.find t π = Some (ls_lini (@lgetTop A)).
    Proof.
      intros [ (saved & logS & prefix & suffix & Hscan0) _] Hcell.
      pose proof (scan_core_entails_I _ _ _ _ _ _ _ _ Hscan0) as HI.
      destruct (source_I_ready_ex _ HI) as (s & log & Eρ). simpl in Eρ. subst ρ.
      destruct (scan_core_some_split _ _ _ _ _ _ _ _ Hscan0) as (tp & tl & -> & Htp & Hscan).
      exists s, log. split; [reflexivity|]. split.
      - eapply getTop_complete_step; [exact Hscan|exact Hcell].
      - destruct (scan_complete_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hscan Hcell)
          as (_ & _ & Hlin & Hdata).
        split; [exact Hdata|exact Hlin].
    Qed.

    (** *** Updates of the per-field reads *)

    Lemma getTop_value_inv_update t count l :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetValue l))))
        (GetTopScan t count (Some l)) (GetTopScan t count (Some l)).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      pose proof (getTop_scan_entails_I _ _ _ _ Hpre) as HIpre.
      pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
      split.
      - eapply getTop_scan_controls; [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc].
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply getTop_scan_entails_I; eapply getTop_scan_controls;
                [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma getTop_value_res_update t count l v :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_mem (nmgetValue l)) v))
        (GetTopScan t count (Some l)) (GetTopScanVal t count l v).
    Proof.
      pupdate_intros_atomic.
      match goal with H : _ _ = Some _ |- _ => rename H into Hconcrete end.
      pupdate_finish.
      pose proof (getTop_scan_entails_I _ _ _ _ Hpre) as HIpre.
      pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
      split.
      - split.
        + eapply getTop_scan_controls; [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc].
        + unfold NodeVal, heap_of. simpl. do 3 eexists. exact Hconcrete.
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply getTop_scan_entails_I; eapply getTop_scan_controls;
                [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma getTop_next_inv_update t count l v :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetNext l))))
        (GetTopScanVal t count l v) (GetTopScanVal t count l v).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      destruct Hpre as [Hscan Hval].
      pose proof (getTop_scan_entails_I _ _ _ _ Hscan) as HIpre.
      pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
      split.
      - split.
        + eapply getTop_scan_controls; [exact Hscan|reflexivity|reflexivity|exact I|exact Hcc].
        + eapply node_val_controls; [exact Hval|reflexivity].
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply getTop_scan_entails_I; eapply getTop_scan_controls;
                [exact Hscan|reflexivity|reflexivity|exact I|exact Hcc])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma getTop_next_res_update t count l v nx :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_mem (nmgetNext l)) nx))
        (GetTopScanVal t count l v) (GetTopScanAt t count l v nx).
    Proof.
      pupdate_intros_atomic.
      match goal with H : _ _ = Some _ |- _ => rename H into Hconcrete end.
      pupdate_finish.
      destruct Hpre as [Hscan Hval].
      pose proof (getTop_scan_entails_I _ _ _ _ Hscan) as HIpre.
      pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
      match goal with
      | |- _ /\ source_G _ ?w1 _ =>
        match type of Hconcrete with
        | _ ?ll = Some (pair (pair (pair _ _) _) ?nn) =>
          assert (Hsk : SkipsAfter ll nn w1)
        end
      end.
      { intros a b Hab.
        pose proof (source_I_rep _ HIpre) as ((_ & _ & Hlk) & _).
        rewrite Hab in Hlk.
        destruct (links_ok_split _ _ _ _ Hlk) as [n [Hn Hskn]].
        unfold heap_of in Hn. simpl in Hn. rewrite Hconcrete in Hn.
        injection Hn as <-. simpl in Hskn. exact Hskn. }
      split.
      - split; [|split].
        + eapply getTop_scan_controls; [exact Hscan|reflexivity|reflexivity|exact I|exact Hcc].
        + eapply node_val_controls; [exact Hval|reflexivity].
        + unfold SkipsAfter, heap_of, log_of in *. simpl in *. exact Hsk.
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply getTop_scan_entails_I; eapply getTop_scan_controls;
                [exact Hscan|reflexivity|reflexivity|exact I|exact Hcc])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma getTop_ts_inv_update t count l v nx :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetTS l))))
        (GetTopScanAt t count l v nx) (GetTopScanAt t count l v nx).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      pose proof (getTop_scan_at_entails_I _ _ _ _ _ _ Hpre) as HIpre.
      pose proof (source_I_cas_control _ HIpre) as Hcc. simpl in Hcc.
      split.
      - eapply getTop_scan_at_controls; [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc].
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply getTop_scan_at_entails_I; eapply getTop_scan_at_controls;
                [exact Hpre|reflexivity|reflexivity|exact I|exact Hcc])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    (** The timestamp read: every scanning possibility whose node is still
        untaken forks a possibility in which [getTop] has returned it. *)
    Lemma getTop_ts_res_update t count l v nx ts :
      AssertionsSet.PUpdate (G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_mem (nmgetTS l)) ts))
        (lift_assert (GetTopScanAt t count l v nx))
        (GetTopWindow t count l v nx ts).
    Proof.
      AssertionsSet.pupdate_intros_atomic.
      match goal with H : s3 l0 = Some _ |- _ => rename H into Hconcrete end.
      match goal with
      | |- context [GetTopWindow _ _ _ _ _ ?tss] => pose (TS := tss)
      end.
      pose (RET := @inl (@LNode A) nat (pair (pair v TS) l0)).
      destruct (ac_nonempty Δ1) as (ρ0 & π0 & Hposs0).
      destruct (Hpre _ _ Hposs0) as [_ [ (ts' & tk & nx' & Hc) _] ].
      unfold heap_of in Hc. simpl in Hc.
      rewrite Hc in Hconcrete. injection Hconcrete as Hv Hts Htk Hnx.
      rewrite Hts in Hc. clear Hv Hts Htk Hnx ts'.
      assert (Hlini : forall ρ π, Δ1 ρ π ->
        TMap.find t0 π = Some (ls_lini (@lgetTop A))).
      { intros ρ π Hposs.
        destruct (Hpre _ _ Hposs) as [ (saved & logS & prefix & suffix & Hscan) _].
        destruct Hscan as (_ & Hlin & _). exact Hlin. }
      assert (HIpre : forall ρ π, Δ1 ρ π ->
        source_I (mk (pair (Pending s3 t0 (nmgetTS l0)) s2) ρ π)).
      { intros ρ π Hposs. exact (getTop_scan_at_entails_I _ _ _ _ _ _ (Hpre _ _ Hposs)). }
      assert (Hready : forall ρ π, Δ1 ρ π -> exists s log, ρ = pair (Ready s) log).
      { intros ρ π Hposs. exact (source_I_ready_ex _ (HIpre _ _ Hposs)). }
      assert (Hcc : cas_control_ok s2).
      { exact (source_I_cas_control _ (HIpre _ _ Hposs0)). }
      assert (HpostA : forall ρ π, Δ1 ρ π ->
        GetTopScanAt t0 count l0 v nx (mk (pair (Idle s3) s2) ρ π)).
      { intros ρ π Hposs.
        exact (getTop_scan_at_controls _ _ _ _ _ _ _ _ (Idle s3) s2 (Hpre _ _ Hposs)
          eq_refl eq_refl I Hcc). }
      assert (HIpost : forall ρ π, Δ1 ρ π -> source_I (mk (pair (Idle s3) s2) ρ π)).
      { intros ρ π Hposs. exact (getTop_scan_at_entails_I _ _ _ _ _ _ (HpostA _ _ Hposs)). }
      assert (Gsame : forall ρ π, Δ1 ρ π ->
        source_G t0 (mk (pair (Pending s3 t0 (nmgetTS l0)) s2) ρ π)
          (mk (pair (Idle s3) s2) ρ π)).
      { intros ρ π Hposs. apply source_G_same_payload; simpl; auto. }
      destruct tk.
      - (* already taken: no fork *)
        exists Δ1. split; [apply ac_steps_refl|]. split.
        + split; [|split; [|split]].
          * intros ρ π Hposs. left. exact (HpostA _ _ Hposs).
          * exists TS, true, nx'. exact Hc.
          * intros ρ π Hposs. exists ρ, π. split; [exact Hposs|].
            split; [apply offslot_agree_refl|].
            exists (@lgetTop A). exact (Hlini _ _ Hposs).
          * intros Hlive. exfalso. unfold live_at, node_live in Hlive.
            simpl in Hlive. rewrite Hc in Hlive. discriminate.
        + split.
          * intros ρ π Hposs. exists ρ, π. split; [exact Hposs|].
            exact (Gsame _ _ Hposs).
          * intros q _. apply twins_preserved_refl.
      - (* untaken: fork *)
        assert (Hfacts : forall ρ π, Δ1 ρ π ->
          exists s log, ρ = pair (Ready s) log /\
            Step (li_lts F) (Build_ThreadEvent t0 (ResEv (@lgetTop A) RET))
              (pair (Ready s) log) (pair (Ready (clear_snapshot t0 s)) log) /\
            DoneData count l0 (mk (pair (Pending s3 t0 (nmgetTS l0)) s2) ρ π) /\
            TMap.find t0 π = Some (ls_lini (@lgetTop A))).
        { intros ρ π Hposs.
          eapply getTop_scan_at_live_facts; [exact (Hpre _ _ Hposs)|].
          simpl. exact Hc. }
        assert (HpostB : forall s log π, Δ1 (pair (Ready s) log) π ->
          GetTopDone t0 count l0 v TS
            (mk (pair (Idle s3) s2) (pair (Ready (clear_snapshot t0 s)) log)
              (TMap.add t0 (ls_linr (@lgetTop A) RET) π))).
        { intros s log π Hposs.
          destruct (Hfacts _ _ Hposs) as (s' & log' & Eρ & _ & Hdata & Hlin).
          inversion Eρ; subst s' log'.
          split.
          - apply getTop_ret_completed; [exact (HIpost _ _ Hposs) | exact Hlin].
          - pose proof (done_data_controls _ _ _ _ _ (Idle s3) s2 Hdata eq_refl) as Hdata'.
            destruct Hdata' as (logS & prefix & tl & HlogS & Hlog & Hlen & Hdead).
            exists logS, prefix, tl. split; [exact HlogS|]. split; [exact Hlog|].
            split; [exact Hlen|]. exact Hdead. }
        exists (fork_config Δ1 t0 RET Hlini).
        split; [|split].
        + intros ρ' π' [Hposs | (s & log & π & Hposs & _ & -> & ->) ].
          * apply ac_steps_refl. exact Hposs.
          * econstructor; [exact Hposs|]. apply rt_step.
            destruct (Hfacts _ _ Hposs) as (s' & log' & Eρ & Hstep' & _ & Hlin).
            inversion Eρ; subst s' log'.
            eapply ps_ret; [exact Hstep' | exact Hlin ].
        + split; [|split; [|split]].
          * intros ρ' π' [Hposs | (s & log & π & Hposs & _ & -> & ->) ].
            -- left. exact (HpostA _ _ Hposs).
            -- right. exact (HpostB _ _ _ Hposs).
          * exists TS, false, nx'. exact Hc.
          * intros ρ' π' [Hposs | (s & log & π & Hposs & _ & -> & ->) ].
            -- exists ρ', π'. split; [left; exact Hposs|].
               split; [apply offslot_agree_refl|].
               exists (@lgetTop A). exact (Hlini _ _ Hposs).
            -- exists (pair (Ready s) log), π. split; [left; exact Hposs|].
               split; [apply ret_image_offslot_orig|].
               exists (@lgetTop A). exact (Hlini _ _ Hposs).
          * intros _ ρ' π' [Hposs | (s & log & π & Hposs & _ & -> & ->) ].
            -- destruct (Hready _ _ Hposs) as [s [log ->]].
               exists (pair (Ready (clear_snapshot t0 s)) log),
                 (TMap.add t0 (ls_linr (@lgetTop A) RET) π').
               split.
               ++ right. exists s, log, π'. split; [exact Hposs|].
                  split; [exact I|]. split; reflexivity.
               ++ split; [apply offslot_agree_sym, ret_image_offslot_orig |
                          apply ret_image_kind_linr].
            -- exists (pair (Ready (clear_snapshot t0 s)) log),
                 (TMap.add t0 (ls_linr (@lgetTop A) RET) π).
               split.
               ++ right. exists s, log, π. split; [exact Hposs|].
                  split; [exact I|]. split; reflexivity.
               ++ split; [apply offslot_agree_refl | apply ret_image_kind_linr].
        + split.
          * intros ρ' π' [Hposs | (s & log & π & Hposs & _ & -> & ->) ].
            -- exists ρ', π'. split; [exact Hposs|]. exact (Gsame _ _ Hposs).
            -- exists (pair (Ready s) log), π. split; [exact Hposs|].
               apply getTop_ret_G; [reflexivity | reflexivity |
                 exact (HIpre _ _ Hposs) | exact (proj1 (proj1 (HpostB _ _ _ Hposs))) ].
          * intros q Hq. apply fork_twins; [exact Hq | exact Hready].
    Qed.

    Lemma getTop_taken_inv_update t count l v nx ts :
      AssertionsSet.PUpdate (G t)
        (Build_ThreadEvent t (@InvEv (li_sig E) (in_mem (nmgetTaken l))))
        (GetTopWindow t count l v nx ts) (GetTopWindow t count l v nx ts).
    Proof.
      AssertionsSet.pupdate_intros_atomic.
      destruct Hpre as [Hkinds [Hcell [Hlini Hlinr]]].
      destruct (ac_nonempty Δ1) as (ρ0 & π0 & Hposs0).
      assert (Hcc : cas_control_ok s2).
      { exact (source_I_cas_control _
          (getTop_kind_entails_I _ _ _ _ _ _ _ (Hkinds _ _ Hposs0))). }
      assert (Hkinds' : forall ρ π, Δ1 ρ π ->
        GetTopKind t0 count l0 v nx ts (mk (pair (Pending s3 t0 (nmgetTaken l0)) s2) ρ π)).
      { intros ρ π Hposs.
        exact (getTop_kind_controls _ _ _ _ _ _ _ _ _
          (Pending s3 t0 (nmgetTaken l0)) s2 (Hkinds _ _ Hposs)
          eq_refl eq_refl I Hcc). }
      exists Δ1. split; [apply ac_steps_refl|]. split.
      - split; [|split; [|split]].
        + intros ρ π Hposs. exact (Hkinds' _ _ Hposs).
        + exact Hcell.
        + exact (HasKind_change_σ kind_lini t0 (pair (Idle s3) s2)
            (pair (Pending s3 t0 (nmgetTaken l0)) s2) Δ1 (kind_lini_σ t0) Hlini).
        + intros Hlive.
          apply (HasKind_change_σ kind_linr t0 (pair (Idle s3) s2)
            (pair (Pending s3 t0 (nmgetTaken l0)) s2) Δ1 (kind_linr_σ t0)).
          apply Hlinr. exact Hlive.
      - split.
        + intros ρ π Hposs. exists ρ, π. split; [exact Hposs|].
          apply source_G_same_payload; simpl; auto.
          * exact (getTop_kind_entails_I _ _ _ _ _ _ _ (Hkinds _ _ Hposs)).
          * exact (getTop_kind_entails_I _ _ _ _ _ _ _ (Hkinds' _ _ Hposs)).
        + intros q _. apply twins_preserved_refl.
    Qed.

    (** The taken read: a [false] flag keeps the returned possibilities,
        a [true] flag keeps the scanning ones (and completes them with the
        empty result when the remembered successor is [None]). *)
    Lemma getTop_taken_res_update t count l v nx ts b :
      AssertionsSet.PUpdate (G t)
        (Build_ThreadEvent t (@ResEv (li_sig E) (in_mem (nmgetTaken l)) b))
        (GetTopWindow t count l v nx ts)
        (lift_assert (GetTopTakenPost t count l v nx ts b)).
    Proof.
      AssertionsSet.pupdate_intros_atomic.
      match goal with H : s3 l0 = Some _ |- _ => rename H into Hconcrete end.
      destruct Hpre as [Hkinds [Hcell [Hlini Hlinr]]].
      simpl in Hcell. destruct Hcell as (ts' & tk & nx' & Hc). simpl in Hc.
      rewrite Hc in Hconcrete. injection Hconcrete as Hv Hts Htk Hnx.
      subst tk. clear Hv Hts Hnx.
      pose (RET := @inl (@LNode A) nat (pair (pair v ts) l0)).
      destruct (ac_nonempty Δ1) as (ρ0 & π0 & Hposs0).
      assert (HIpre : forall ρ π, Δ1 ρ π ->
        source_I (mk (pair (Pending s3 t0 (nmgetTaken l0)) s2) ρ π)).
      { intros ρ π Hposs.
        exact (getTop_kind_entails_I _ _ _ _ _ _ _ (Hkinds _ _ Hposs)). }
      assert (Hcc : cas_control_ok s2).
      { exact (source_I_cas_control _ (HIpre _ _ Hposs0)). }
      assert (HIpost : forall ρ π, Δ1 ρ π -> source_I (mk (pair (Idle s3) s2) ρ π)).
      { intros ρ π Hposs.
        exact (source_I_controls _ _ _ (Idle s3) s2 (HIpre _ _ Hposs)
          eq_refl eq_refl I Hcc). }
      assert (Hready : forall ρ π, Δ1 ρ π -> exists s log, ρ = pair (Ready s) log).
      { intros ρ π Hposs. exact (source_I_ready_ex _ (HIpre _ _ Hposs)). }
      assert (Gsame : forall ρ π, Δ1 ρ π ->
        source_G t0 (mk (pair (Pending s3 t0 (nmgetTaken l0)) s2) ρ π)
          (mk (pair (Idle s3) s2) ρ π)).
      { intros ρ π Hposs. apply source_G_same_payload; simpl; auto. }
      assert (HkindA : forall ρ π, Δ1 ρ π ->
        TMap.find t0 π = Some (ls_lini (@lgetTop A)) ->
        GetTopScanAt t0 count l0 v nx (mk (pair (Pending s3 t0 (nmgetTaken l0)) s2) ρ π)).
      { intros ρ π Hposs Hlin.
        destruct (Hkinds _ _ Hposs) as [HA | [[_ HB] _]]; [exact HA|].
        unfold ALin in HB. simpl in HB.
        pose proof (eq_trans (eq_sym Hlin) HB) as Habs. discriminate Habs. }
      assert (HkindB : forall ρ π, Δ1 ρ π ->
        (exists f r, TMap.find t0 π = Some (ls_linr f r)) ->
        GetTopDone t0 count l0 v ts
          (mk (pair (Pending s3 t0 (nmgetTaken l0)) s2) ρ π)).
      { intros ρ π Hposs (f & r & Hlin).
        destruct (Hkinds _ _ Hposs) as [[ (saved & logS & prefix & suffix & Hscan) _] | HB]; [|exact HB].
        destruct Hscan as (_ & HA & _).
        unfold ALin in HA. simpl in HA.
        pose proof (eq_trans (eq_sym Hlin) HA) as Habs. discriminate Habs. }
      match goal with
      | |- context [GetTopTakenPost _ _ _ _ _ _ ?bb] => destruct bb
      end.
      - (* taken: keep the scanning possibilities *)
        assert (Htaken : taken_at s3 l0 = true).
        { unfold taken_at. rewrite Hc. reflexivity. }
        assert (Hne : exists ρ π,
          filter_prop Δ1 (fun π => TMap.find t0 π = Some (ls_lini (@lgetTop A))) ρ π).
        { destruct (Hlini _ _ Hposs0) as (ρ1 & π1 & Hposs1 & _ & [f Hf]).
          unfold slot_token in Hf. simpl in Hf.
          destruct (Hkinds _ _ Hposs1) as [[ (saved & logS & prefix & suffix & Hscan) _] | [[_ HB] _]].
          - exists ρ1, π1. split; [exact Hposs1|]. exact (proj1 (proj2 Hscan)).
          - unfold ALin in HB. simpl in HB.
            pose proof (eq_trans (eq_sym Hf) HB) as Habs. discriminate Habs. }
        match goal with
        | |- context [GetTopTakenPost _ _ _ _ ?nn _ _] => destruct nn as [l'|]
        end.
        + (* there is a next node: shift the scan *)
          exists (filter_config Δ1 _ Hne). split; [|split].
          * intros ρ π [Hposs _]. apply ac_steps_refl. exact Hposs.
          * intros ρ π [Hposs Hlin]. simpl.
            pose proof (getTop_shift_scan _ _ _ _ _ _ (HkindA _ _ Hposs Hlin) Htaken) as Hshift.
            exact (getTop_scan_controls _ _ _ _ _ _ (Idle s3) s2 Hshift
              eq_refl eq_refl I Hcc).
          * split.
            -- intros ρ π [Hposs _]. exists ρ, π. split; [exact Hposs|].
               exact (Gsame _ _ Hposs).
            -- intros q Hq. apply (filter_twins q t0); [exact Hq|].
               intros π π' Heq Hsel. exact (eq_trans (eq_sym Heq) Hsel).
        + (* the node was the last one: the list is empty *)
          assert (Hlini' : forall ρ π, Δ1 ρ π ->
            TMap.find t0 π = Some (ls_lini (@lgetTop A)) ->
            TMap.find t0 π = Some (ls_lini (@lgetTop A))).
          { intros ρ π _ H. exact H. }
          assert (Hne' : exists ρ' π',
            ret_image_prop Δ1 t0 (@inr (@LNode A) nat count)
              (fun π => TMap.find t0 π = Some (ls_lini (@lgetTop A))) ρ' π').
          { destruct Hne as (ρ1 & π1 & Hposs1 & Hlin1).
            destruct (Hready _ _ Hposs1) as [s1 [log1 ->]].
            exists (pair (Ready (clear_snapshot t0 s1)) log1),
              (TMap.add t0 (ls_linr (@lgetTop A) (@inr (@LNode A) nat count)) π1).
            exists s1, log1, π1. split; [exact Hposs1|]. split; [exact Hlin1|].
            split; reflexivity. }
          exists (ret_image_config Δ1 t0 (@inr (@LNode A) nat count) _ Hlini' Hne').
          split; [|split].
          * intros ρ' π' (s & log & π & Hposs & Hlin & -> & ->).
            econstructor; [exact Hposs|]. apply rt_step.
            eapply ps_ret; [|exact Hlin].
            eapply getTop_empty_step; [exact (HkindA _ _ Hposs Hlin) | exact Htaken].
          * intros ρ' π' (s & log & π & Hposs & Hlin & -> & ->). simpl.
            exact (getTop_ret_completed t0 (@inr (@LNode A) nat count)
              (pair (Idle s3) s2) s log π (HIpost _ _ Hposs) Hlin).
          * split.
            -- intros ρ' π' (s & log & π & Hposs & Hlin & -> & ->).
               exists (pair (Ready s) log), π. split; [exact Hposs|].
               apply getTop_ret_G; [reflexivity | reflexivity |
                 exact (HIpre _ _ Hposs) |].
               exact (proj1 (getTop_ret_completed t0 (@inr (@LNode A) nat count)
                 (pair (Idle s3) s2) s log π (HIpost _ _ Hposs) Hlin)).
            -- intros q Hq. apply ret_image_twins; [exact Hq | exact Hready |].
               intros π π' Heq Hsel. exact (eq_trans (eq_sym Heq) Hsel).
      - (* untaken: keep the returned possibilities *)
        assert (Hlive : live_at (mem_heap (fst
            (SetPossState.σ (mks (pair (Pending s3 t0 (nmgetTaken l0)) s2) Δ1)))) l0 = true).
        { unfold live_at, node_live. simpl. rewrite Hc. reflexivity. }
        assert (Hne : exists ρ π,
          filter_prop Δ1 (fun π => exists f r, TMap.find t0 π = Some (ls_linr f r)) ρ π).
        { destruct (Hlinr Hlive _ _ Hposs0) as (ρ1 & π1 & Hposs1 & _ & Hk).
          exists ρ1, π1. split; [exact Hposs1|]. exact Hk. }
        exists (filter_config Δ1 _ Hne). split; [|split].
        + intros ρ π [Hposs _]. apply ac_steps_refl. exact Hposs.
        + intros ρ π [Hposs Hlin]. simpl.
          exact (getTop_done_controls _ _ _ _ _ _ _ _ (Idle s3) s2
            (HkindB _ _ Hposs Hlin) eq_refl eq_refl I Hcc).
        + split.
          * intros ρ π [Hposs _]. exists ρ, π. split; [exact Hposs|].
            exact (Gsame _ _ Hposs).
          * intros q Hq. apply (filter_twins q t0); [exact Hq|].
            intros π π' Heq (f & r & Hsel). exists f, r.
            exact (eq_trans (eq_sym Heq) Hsel).
    Qed.

    (** *** The final CAS of [getTop] *)

    Lemma getTop_cas_inv_update t count top l v ts :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@InvEv (li_sig E) (in_cas (cas (pair top count) (pair (Some l) count)))))
        (GetTopDone t count l v ts) (GetTopDone t count l v ts).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      pose proof (getTop_done_entails_I _ _ _ _ _ _ Hpre) as HIpre.
      pose proof (source_I_mem_control _ HIpre) as Hmc. simpl in Hmc.
      split.
      - eapply getTop_done_controls; [exact Hpre|reflexivity|reflexivity|exact Hmc|exact I].
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply getTop_done_entails_I; eapply getTop_done_controls;
                [exact Hpre|reflexivity|reflexivity|exact Hmc|exact I])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    Lemma getTop_cas_succ_update t count top l v ts :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (in_cas (cas (pair top count) (pair (Some l) count))) true))
        (GetTopDone t count l v ts)
        (Completed t (@lgetTop A) (@inl (@LNode A) nat (pair (pair v ts) l))).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      destruct Hpre as [[HIpre Hlin] Hdata].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (mc & cc & s & log & Eσ & Eρ & Hmc & Hcc & Hrep & Hsnap).
      simpl in Eσ, Eρ. inversion Eσ; subst mc cc. subst ρ1.
      simpl in Hrep.
      destruct Hdata as (logS & prefix & tl & HlogS & [extra Hlog] & Hlen & Hdead).
      unfold log_of, log_of_ctrl in Hlog. simpl in Hlog.
      unfold heap_of in Hdead. simpl in Hdead.
      pose proof Hrep as (Hvalid & Hcount & Hlength & Hnodes & Horder).
      simpl in Hcount, Hlength.
      assert (Hextra : extra = nil).
      { rewrite Hlog, app_length, Hlen in Hlength.
        destruct extra as [|x0 extra0]; [reflexivity|]. simpl in Hlength. lia. }
      subst extra. simpl in Hlog.
      assert (Hsk : skips (mem_heap s1) log (Some l)).
      { rewrite Hlog, HlogS. apply skips_app_taken; [|constructor].
        apply Forall_forall. intros y Hy. apply live_false_taken.
        - eapply represents_defined; [exact Hrep|].
          rewrite Hlog, HlogS. apply in_or_app. now left.
        - apply Hdead. exact Hy. }
      assert (HIpost : source_I
        (mk (pair s1 (Idle (pair (Some l) count))) (pair (Ready s) log) π1)).
      { apply source_I_build; [exact Hmc|exact I| |exact Hsnap].
        eapply represents_cas_top; [exact Hrep|exact Hsk]. }
      split.
      - split; [exact HIpost|exact Hlin].
      - unfold source_G. split; [exact HIpre0|]. split; [exact HIpost|].
        split; [simpl; apply heap_evol_refl|].
        split; [intros q _ _; reflexivity|].
        split; [split; [intros _; reflexivity|exists nil; split; reflexivity]|].
        split; intros; reflexivity.
    Qed.

    Lemma getTop_cas_fail_update t count top l v ts :
      AssertionsSingle.PUpdate (source_G t)
        (Build_ThreadEvent t
          (@ResEv (li_sig E) (in_cas (cas (pair top count) (pair (Some l) count))) false))
        (GetTopDone t count l v ts)
        (Completed t (@lgetTop A) (@inl (@LNode A) nat (pair (pair v ts) l))).
    Proof.
      pupdate_intros_atomic. pupdate_finish.
      destruct Hpre as [Hcomp Hdata].
      pose proof (completed_entails_I _ _ _ _ Hcomp) as HIpre.
      pose proof (source_I_mem_control _ HIpre) as Hmc. simpl in Hmc.
      split.
      - eapply completed_controls; [exact Hcomp|reflexivity|reflexivity|exact Hmc|exact I].
      - match goal with
        | |- source_G _ _ ?w2 =>
            assert (HIpost : source_I w2) by
              (eapply completed_entails_I; eapply completed_controls;
                [exact Hcomp|reflexivity|reflexivity|exact Hmc|exact I])
        end.
        eapply source_G_same_payload; simpl; eauto.
    Qed.

    (** *** The [getTop] triple *)

    Lemma getTop_triple t :
      [li_lts E, li_lts F, R t, G t, SI, t] ⊢
        {{ SActive t (@lgetTop A) }}
          (@SPListUnlinkImpl.getTop_impl A t)
        {{ fun ret => SCompleted t (@lgetTop A) ret }}.
    Proof.
      unfold SPListUnlinkImpl.getTop_impl.
      eapply singleton_provable_vis_safe with
        (P' := Active t (@lgetTop A))
        (Q' := fun q => GetTopLoop t (snd q) (fst q)).
      - intros w Hpre Herror.
        destruct (SinglePossState.σ w) as [mc cc]. simpl in Herror.
        dependent destruction Herror.
      - apply active_entails_I.
      - intros q. apply getTop_loop_entails_I.
      - apply active_stable.
      - intros q. apply getTop_loop_stable.
      - apply getTop_get_inv_update.
      - intros q. apply getTop_get_res_update.
      - intros [top count]. simpl.
        eapply SetLogic.provable_seq with
          (Q' := fun r => lift_assert (GetTopResult t count r)).
        + eapply SetLogic.provable_doloop_data with
            (Iloop := fun p => SGetTopLoop t count p)
            (Q := fun ret => lift_assert (GetTopResult t count ret)).
          * intros ret w H.
            eapply lift_impl; [apply getTop_result_entails_I|exact H].
          * intros ret. apply lift_stable. apply getTop_result_stable.
          * intros p. destruct p as [l|]; simpl.
            -- unfold SGetTopLoop, GetTopLoop. simpl.
               eapply SetLogic.provable_conseq_weak_post with
                 (Q' := fun r => lift_assert (GetTopBodyPost t count r)).
               ++ intros [p|ret]; unfold GetTopBodyPost; simpl.
                  ** intros w Hpost. eapply lift_impl;
                       [apply getTop_loop_entails_I|exact Hpost].
                  ** intros w Hpost. eapply lift_impl;
                       [apply getTop_result_entails_I|exact Hpost].
               ++ intros [p|ret]; simpl.
                  ** apply lift_stable. apply getTop_loop_stable.
                  ** apply lift_stable. apply getTop_result_stable.
               ++ intros [p|ret]; unfold GetTopBodyPost; simpl.
                  ** unfold SGetTopLoop. intros w Hpost. exact Hpost.
                  ** intros w Hpost. exact Hpost.
               ++ (* value read *)
                  eapply singleton_provable_vis_safe with
                    (P' := GetTopScan t count (Some l))
                    (Q' := fun v => GetTopScanVal t count l v).
                  ** apply getTop_value_no_error.
                  ** apply getTop_scan_entails_I.
                  ** intros v. apply getTop_scan_val_entails_I.
                  ** apply getTop_scan_stable.
                  ** intros v. apply getTop_scan_val_stable.
                  ** apply getTop_value_inv_update.
                  ** intros v. apply getTop_value_res_update.
                  ** intros v. (* next read *)
                     eapply singleton_provable_vis_safe with
                       (P' := GetTopScanVal t count l v)
                       (Q' := fun nx => GetTopScanAt t count l v nx).
                     --- apply getTop_next_no_error.
                     --- apply getTop_scan_val_entails_I.
                     --- intros nx. apply getTop_scan_at_entails_I.
                     --- apply getTop_scan_val_stable.
                     --- intros nx. apply getTop_scan_at_stable.
                     --- apply getTop_next_inv_update.
                     --- intros nx. apply getTop_next_res_update.
                     --- intros nx. (* timestamp read: fork *)
                         eapply SetLogic.provable_vis_safe with
                           (P' := lift_assert (GetTopScanAt t count l v nx))
                           (Q' := fun ts => GetTopWindow t count l v nx ts).
                         +++ intros s HP. eapply lift_no_error;
                               [apply getTop_ts_no_error | exact HP].
                         +++ intros s HP. eapply lift_impl;
                               [apply getTop_scan_at_entails_I | exact HP].
                         +++ intros ts. apply getTop_window_entails_I.
                         +++ apply lift_stable. apply getTop_scan_at_stable.
                         +++ intros ts. apply getTop_window_stable.
                         +++ apply lift_pupdate.
                             *** apply getTop_scan_at_entails_I.
                             *** apply getTop_scan_at_entails_I.
                             *** apply slot_local_getTop_scan_at.
                             *** apply getTop_ts_inv_update.
                         +++ intros ts. apply getTop_ts_res_update.
                         +++ intros ts. (* taken read: drop *)
                             eapply SetLogic.provable_vis_safe with
                               (P' := GetTopWindow t count l v nx ts)
                               (Q' := fun b =>
                                 lift_assert (GetTopTakenPost t count l v nx ts b)).
                             *** apply getTop_taken_no_error.
                             *** apply getTop_window_entails_I.
                             *** intros b s HQ. eapply lift_impl;
                                   [apply getTop_taken_post_entails_I | exact HQ].
                             *** apply getTop_window_stable.
                             *** intros b. apply lift_stable.
                                 apply getTop_taken_post_stable.
                             *** apply getTop_taken_inv_update.
                             *** intros b. apply getTop_taken_res_update.
                             *** intros b. destruct b.
                                 ---- unfold GetTopTakenPost, GetTopBodyPost. singleton_ret_safe.
                                      ++++ intros w H. exact H.
                                      ++++ apply getTop_loop_entails_I.
                                      ++++ apply getTop_loop_stable.
                                 ---- unfold GetTopTakenPost, GetTopBodyPost. singleton_ret_safe.
                                      ++++ intros w H. exact H.
                                      ++++ apply getTop_done_entails_I.
                                      ++++ apply getTop_done_stable.
                     --- apply getTop_scan_val_entails_I.
                     --- apply slot_local_getTop_scan_val.
                     --- intros nx. apply slot_local_getTop_scan_at.
                  ** apply getTop_scan_entails_I.
                  ** apply slot_local_getTop_scan.
                  ** intros v. apply slot_local_getTop_scan_val.
            -- unfold SGetTopLoop, GetTopLoop. simpl.
               eapply SetLogic.provable_conseq_weak_post with
                 (Q' := fun r => lift_assert (GetTopBodyPost t count r)).
               ++ intros [p|ret]; unfold GetTopBodyPost; simpl.
                  ** intros w Hpost. eapply lift_impl;
                       [apply getTop_loop_entails_I|exact Hpost].
                  ** intros w Hpost. eapply lift_impl;
                       [apply getTop_result_entails_I|exact Hpost].
               ++ intros [p|ret]; simpl.
                  ** apply lift_stable. apply getTop_loop_stable.
                  ** apply lift_stable. apply getTop_result_stable.
               ++ intros [p|ret]; unfold GetTopBodyPost; simpl.
                  ** unfold SGetTopLoop. intros w Hpost. exact Hpost.
                  ** intros w Hpost. exact Hpost.
               ++ unfold GetTopBodyPost. simpl. singleton_ret_safe.
                  ** apply ImplRefl.
                  ** apply completed_entails_I.
                  ** apply completed_stable.
        + intros r. destruct r as [[[v ts] l]|c]; simpl.
          * destruct top as [t0|].
            -- destruct (Nat.eqb t0 l).
               ++ singleton_ret_safe.
                  ** intros w [H _]. exact H.
                  ** apply completed_entails_I.
                  ** apply completed_stable.
               ++ eapply singleton_provable_vis_safe with
                    (P' := GetTopDone t count l v ts)
                    (Q' := fun _ : bool =>
                      Completed t (@lgetTop A) (@inl (@LNode A) nat (pair (pair v ts) l))).
                  ** intros w Hpre Herror.
                     destruct (SinglePossState.σ w) as [mc cc]. simpl in Herror.
                     dependent destruction Herror.
                  ** apply getTop_done_entails_I.
                  ** intros _. apply completed_entails_I.
                  ** apply getTop_done_stable.
                  ** intros _. apply completed_stable.
                  ** apply getTop_cas_inv_update.
                  ** intros b. destruct b.
                     --- apply getTop_cas_succ_update.
                     --- apply getTop_cas_fail_update.
                  ** intros b. singleton_ret_safe.
                     --- apply ImplRefl.
                     --- apply completed_entails_I.
                     --- apply completed_stable.
                  ** apply getTop_done_entails_I.
                  ** apply slot_local_getTop_done.
                  ** intros _. apply slot_local_completed.
            -- singleton_ret_safe.
               ++ intros w [H _]. exact H.
               ++ apply completed_entails_I.
               ++ apply completed_stable.
          * singleton_ret_safe.
            -- apply ImplRefl.
            -- apply completed_entails_I.
            -- apply completed_stable.
      - apply active_entails_I.
      - apply slot_local_active.
      - intros q. apply slot_local_getTop_loop.
    Qed.

    (** * The layer *)

    Lemma initial_represents :
      represents (@empty_heap (@Node A)) None 0
        (@SPListImpl.empty_splist_state A) nil.
    Proof.
      split.
      { split; [constructor|]. split; [constructor|]. exact I. }
      split; [reflexivity|]. split; [reflexivity|]. split.
      - apply functional_extensionality. intro l.
        unfold empty_heap, abstract_nodes. simpl. reflexivity.
      - reflexivity.
    Qed.

    Lemma initial_snapshot_consistent :
      snapshot_consistent (@SPListImpl.empty_splist_state A)
        (@TMap.empty (@LinState (li_sig F))).
    Proof.
      intros t. simpl. rewrite TMap.gempty, TMap.gempty.
      split; [intros [? H]; discriminate|discriminate].
    Qed.

    Lemma initial_source_I :
      source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (li_init E) (li_init F)
          (@TMap.empty (@LinState (li_sig F)))).
    Proof.
      unfold source_I.
      exists (Idle (@empty_heap (@Node A))).
      exists (Idle (pair (@None Addr) O)).
      exists (@SPListImpl.empty_splist_state A), nil.
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [exact initial_represents|exact initial_snapshot_consistent].
    Qed.

    Lemma initial_SI :
      SI
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          (li_init E)
          (ac_singleton (li_init F)
            (@TMap.empty (@LinState (li_sig F))))).
    Proof.
      apply lift_initial. exact initial_source_I.
    Qed.

    Lemma active_closes_invariant t m :
      ⊨ SActive t m ==>> SI.
    Proof.
      intros w Hactive. eapply lift_impl; [apply active_entails_I|exact Hactive].
    Qed.

    Program Definition MSPListUnlink : layer_implementation_simulation E F :=
      {| li_impl := @SPListUnlinkImpl.splist_unlink_impl A owner |}.
    Next Obligation.
      eapply SetLogic.soundness with (R := R) (G := G) (I := SI).
      - exact valid_rg.
      - exact parallel_compatible.
      - intros t f. destruct f as [v|l ts| | |l].
        + exists (SActive t (linsert v)).
          exists (fun ret => SCompleted t (linsert v) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret σ Δ Hcompleted ρ pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply insert_triple.
        + exists (SActive t (lsetTS l ts)).
          exists (fun ret => SCompleted t (lsetTS l ts) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret σ Δ Hcompleted ρ pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply setTS_triple.
        + exists (SActive t (@lgetTop A)).
          exists (fun ret => SCompleted t (@lgetTop A) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret σ Δ Hcompleted ρ pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply getTop_triple.
        + exists (SActive t (@lgetCounter A)).
          exists (fun ret => SCompleted t (@lgetCounter A) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret σ Δ Hcompleted ρ pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply getCounter_triple.
        + exists (SActive t (ltryRemove l)).
          exists (fun ret => SCompleted t (ltryRemove l) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret σ Δ Hcompleted ρ pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply tryRemove_triple.
      - exact initial_SI.
    Qed.

    (** Linearizability against the ghost specification. *)
    Definition MSPListUnlinkGhost :
        layer_implementation_linearizability E F :=
      LISim2LILin MSPListUnlink.

    (** Erasing the ghost log: linearizability against the unchanged
        [SPListSpec], for the real implementation. *)
    Definition MSPListUnlinkLinearizable :
        layer_implementation_linearizability E FSpec :=
      @CompLinProj.LIProj E (@ESPList A) (@VSPListGhost A owner) (@VSPList A owner)
        (fun c => fst c)
        (fun e g g' H => @ghost_step_proj A owner e g g' H)
        (fun e g H => @ghost_error_proj A owner e g H)
        (li_init F) MSPListUnlinkGhost.

  End Proof.

  Print Assumptions MSPListUnlinkLinearizable.
End SPListUnlinkProof.
