Require Import FMapPositive.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Program.Equality.
Require Import Coq.Relations.Relation_Operators.
Require Import Lia.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import RGILogicSet.
Require Import SingletonPossibility.
Require Import CompLinLayer.

Require Import examples.Common.ThreadDomain.
Require Import examples.Common.IndexedFamilySpec.
Require Import examples.TSStack.TimestampSpec.
Require Import examples.TSStack.SPListSpec.
Require Import examples.TSStack.ListPoolSpec.
Require Import examples.TSStack.SPListFamilySpec.
Require Import examples.TSStack.SPListArraySpec.
Require Import examples.TSStack.SPListArray.
Require Import examples.TSStack.SPListFamily.

(** Correctness of the SPList-array adapter over the verified indexed
    SPList family, including all six methods and vertical composition. *)
Module SPListArrayProof.
  Import Reg LinCCALBase LTSSpec Lang Semantics.
  Import AssertionsSingle SingletonPossibility.
  Import Heap TimestampSpec ListPoolSpec.
  Import IndexedFamilySpec SPListSpec.
  Import SPListFamilySpec SPListArraySpec SPListArrayImpl.
  Module SetLogic := RGILogicSet.RGILogic.

  Import ListNotations.
  Import TPSimulationSet.TPSimulation.
  Import CompLinLayer.

  Open Scope assertion_scope.
  Open Scope rg_relation_scope.

  Section Proof.
    Context {A : Type} (D : ThreadDomain.t).

    Definition E : layer_interface := @SPListFamilyLayer.L A D.
    Definition F : layer_interface := @SPListArrayLayer.L A D.

    Definition concrete_state := State (li_lts E).
    Definition abstract_state := State (li_lts F).
    Definition single_state :=
      @SinglePossState.ProofStateSingle _ _ (li_lts E) (li_lts F).
    Definition assertion := @Logics.Assertion single_state.
    Definition rg_relation :=
      @AssertionsSingle.A.RGRelation _ _ (li_lts E) (li_lts F).

    Definition row_payload (r : @SPListControl A) : @SPListState A :=
      match r with
      | Ready s => s
      | AtomicPending s _ _ => s
      end.

    Definition payload_at
        (rows : concrete_state) (owner : tid) : option (@SPListState A) :=
      option_map row_payload (TMap.find owner rows).

    Definition node_at (rows : concrete_state) (n : tid * Addr) :
        option (A * TimestampSpec.TS) :=
      match payload_at rows (fst n) with
      | Some row => nodes row (snd n)
      | None => None
      end.

    Definition row_order_at (rows : concrete_state) (owner : tid) :
        list Addr :=
      match payload_at rows owner with
      | Some row => order row
      | None => nil
      end.

    Definition row_counter_at (rows : concrete_state) (owner : tid) : nat :=
      match payload_at rows owner with
      | Some row => counter row
      | None => 0
      end.

    Definition expected_snapshot
        (a : @SPListArrayState A) (actor owner : tid) :
        option (list Addr * nat) :=
      match TMap.find actor (as_scans a) with
      | Some p =>
          match scan_current p with
          | Some c =>
              if PositiveMap.E.eq_dec owner (current_owner c)
              then Some (pair (current_order c) (current_counter c))
              else None
          | None => None
          end
      | None => None
      end.

    Record represents
        (rows : concrete_state) (a : @SPListArrayState A) : Prop := {
      rep_domain : forall owner,
        (exists row, payload_at rows owner = Some row) <->
        ThreadDomain.contains D owner;
      rep_counter : forall owner,
        counter_at owner a = row_counter_at rows owner;
      rep_order : forall owner,
        order_at owner a = row_order_at rows owner;
      rep_node : forall n,
        match node_at rows n with
        | Some (pair v ts) =>
            as_values a n = Some v /\ as_timestamps a n = Some ts
        | None => as_values a n = None /\ as_timestamps a n = None
        end;
      rep_garbage : forall n,
        as_garbage a n <->
        node_at rows n <> None /\
        ~ In (snd n) (row_order_at rows (fst n));
      rep_order_nodup : forall owner row,
        payload_at rows owner = Some row -> NoDup (order row);
      rep_order_defined : forall owner row loc,
        payload_at rows owner = Some row -> In loc (order row) ->
        nodes row loc <> None;
      rep_snapshot : forall actor owner row,
        payload_at rows owner = Some row ->
        TMap.find actor (snapshot row) = expected_snapshot a actor owner
    }.

    Lemma payload_at_add_same rows owner control :
      payload_at (TMap.add owner control rows) owner =
      Some (row_payload control).
    Proof. unfold payload_at. rewrite TMap.gss. reflexivity. Qed.

    Lemma payload_at_add_other rows owner control other :
      other <> owner ->
      payload_at (TMap.add owner control rows) other = payload_at rows other.
    Proof. intros Hneq. unfold payload_at. rewrite TMap.gso by exact Hneq.
      reflexivity. Qed.

    Lemma node_at_pair rows owner loc :
      node_at rows (pair owner loc) =
      match payload_at rows owner with
      | Some row => nodes row loc
      | None => None
      end.
    Proof. reflexivity. Qed.

    Lemma represents_row_exists rows a owner :
      represents rows a -> ThreadDomain.contains D owner ->
      exists row, payload_at rows owner = Some row.
    Proof. intros Hrep. apply (proj2 (rep_domain _ _ Hrep owner)). Qed.

    Lemma represents_node_some rows a owner row loc v ts :
      represents rows a -> payload_at rows owner = Some row ->
      nodes row loc = Some (pair v ts) ->
      as_values a (pair owner loc) = Some v /\
      as_timestamps a (pair owner loc) = Some ts.
    Proof.
      intros Hrep Hrow Hnode.
      pose proof (rep_node _ _ Hrep (pair owner loc)) as H.
      unfold node_at in H. simpl in H. rewrite Hrow, Hnode in H. exact H.
    Qed.

    Lemma represents_node_none rows a owner row loc :
      represents rows a -> payload_at rows owner = Some row ->
      nodes row loc = None ->
      as_values a (pair owner loc) = None /\
      as_timestamps a (pair owner loc) = None.
    Proof.
      intros Hrep Hrow Hnode.
      pose proof (rep_node _ _ Hrep (pair owner loc)) as H.
      unfold node_at in H. simpl in H. rewrite Hrow, Hnode in H. exact H.
    Qed.

    Lemma represents_node_defined rows a owner row loc :
      represents rows a -> payload_at rows owner = Some row ->
      (nodes row loc <> None <-> array_vertex a (pair owner loc)).
    Proof.
      intros Hrep Hrow. unfold array_vertex.
      destruct (nodes row loc) as [value_ts|] eqn:Hnode.
      destruct value_ts as [v ts].
      - pose proof (represents_node_some _ _ _ _ _ _ _ Hrep Hrow Hnode)
          as [Hv _]. rewrite Hv. split; discriminate.
      - pose proof (represents_node_none _ _ _ _ _ Hrep Hrow Hnode)
          as [Hv _]. rewrite Hv. split; contradiction.
    Qed.

    Lemma represents_order rows a owner :
      represents rows a -> order_at owner a = row_order_at rows owner.
    Proof. intros Hrep. exact (rep_order _ _ Hrep owner). Qed.

    Lemma represents_counter rows a owner :
      represents rows a -> counter_at owner a = row_counter_at rows owner.
    Proof. intros Hrep. exact (rep_counter _ _ Hrep owner). Qed.

    Lemma represents_garbage rows a owner row loc :
      represents rows a -> payload_at rows owner = Some row ->
      (as_garbage a (pair owner loc) <->
       nodes row loc <> None /\ ~ In loc (order row)).
    Proof.
      intros Hrep Hrow.
      pose proof (rep_garbage _ _ Hrep (pair owner loc)) as H.
      unfold node_at, row_order_at in H. simpl in H. now rewrite Hrow in H.
    Qed.

    Lemma represents_live rows a owner row loc :
      represents rows a -> payload_at rows owner = Some row ->
      (array_live a (pair owner loc) <-> In loc (order row)).
    Proof.
      intros Hrep Hrow. unfold array_live.
      rewrite <- (represents_node_defined _ _ _ _ _ Hrep Hrow).
      rewrite (represents_garbage _ _ _ _ _ Hrep Hrow).
      split.
      - intros [Hdefined Hnotgarbage].
        destruct (in_dec Nat.eq_dec loc (order row)); auto.
        exfalso. apply Hnotgarbage. auto.
      - intros Hin. split.
        + eapply rep_order_defined; eauto.
        + intros [_ Hnotin]. contradiction.
    Qed.

    Lemma current_nodes_spec c owner loc :
      current_nodes c (pair owner loc) <->
      owner = current_owner c /\ In loc (current_order c).
    Proof.
      unfold current_nodes. simpl. split.
      - intros [Howner Hin]. now split.
      - intros [Howner Hin]. now split.
    Qed.

    Lemma actual_snapshot_actual_scan rows a actor owner row p c :
      represents rows a ->
      payload_at rows owner = Some row ->
      TMap.find actor (as_scans a) = Some p ->
      scan_current p = Some c ->
      current_owner c = owner ->
      actual_snapshot actor row =
        Some (pair (actual_scan_order c a) (current_counter c)).
    Proof.
      intros Hrep Hrow Hscan Hcurrent Howner.
      pose proof (rep_snapshot _ _ Hrep actor owner row Hrow) as Hsnapshot.
      unfold expected_snapshot in Hsnapshot. rewrite Hscan, Hcurrent in Hsnapshot.
      destruct (PositiveMap.E.eq_dec owner (current_owner c)); [|congruence].
      subst owner.
      unfold actual_snapshot, actual_scan_order. rewrite Hsnapshot.
      rewrite (rep_order _ _ Hrep (current_owner c)). unfold row_order_at.
      now rewrite Hrow.
    Qed.

    Lemma initial_rows_find_in owners owner :
      In owner owners ->
      TMap.find owner
        (initial_rows (@SPListIndexedObject A) owners) =
      Some (Ready (@empty_row_state A)).
    Proof.
      induction owners as [|head owners IH]; simpl; intros Hin.
      - contradiction.
      - destruct Hin as [<- | Hin].
        + apply TMap.gss.
        + destruct (PositiveMap.E.eq_dec owner head) as [->|Hneq].
          * apply TMap.gss.
          * rewrite TMap.gso by exact Hneq. now apply IH.
    Qed.

    Lemma initial_rows_find_out owners owner :
      ~ In owner owners ->
      TMap.find owner
        (initial_rows (@SPListIndexedObject A) owners) = None.
    Proof.
      induction owners as [|head owners IH]; simpl; intros Hout.
      - apply TMap.gempty.
      - assert (Hneq : owner <> head) by (intro; subst; apply Hout; now left).
        rewrite TMap.gso by exact Hneq. apply IH.
        intro Hin. apply Hout. now right.
    Qed.

    Lemma initial_counters_find_in owners owner :
      In owner owners ->
      TMap.find owner (initial_counters owners) = Some O.
    Proof.
      induction owners as [|head owners IH]; simpl; intros Hin.
      - contradiction.
      - destruct Hin as [<- | Hin].
        + apply TMap.gss.
        + destruct (PositiveMap.E.eq_dec owner head) as [->|Hneq].
          * apply TMap.gss.
          * rewrite TMap.gso by exact Hneq. now apply IH.
    Qed.

    Lemma initial_counters_find_out owners owner :
      ~ In owner owners ->
      TMap.find owner (initial_counters owners) = None.
    Proof.
      induction owners as [|head owners IH]; simpl; intros Hout.
      - apply TMap.gempty.
      - assert (Hneq : owner <> head) by (intro; subst; apply Hout; now left).
        rewrite TMap.gso by exact Hneq. apply IH.
        intro Hin. apply Hout. now right.
    Qed.

    Lemma initial_orders_find_in owners owner :
      In owner owners ->
      TMap.find owner (initial_orders owners) = Some nil.
    Proof.
      induction owners as [|head owners IH]; simpl; intros Hin.
      - contradiction.
      - destruct Hin as [<- | Hin].
        + apply TMap.gss.
        + destruct (PositiveMap.E.eq_dec owner head) as [->|Hneq].
          * apply TMap.gss.
          * rewrite TMap.gso by exact Hneq. now apply IH.
    Qed.

    Lemma initial_orders_find_out owners owner :
      ~ In owner owners ->
      TMap.find owner (initial_orders owners) = None.
    Proof.
      induction owners as [|head owners IH]; simpl; intros Hout.
      - apply TMap.gempty.
      - assert (Hneq : owner <> head) by (intro; subst; apply Hout; now left).
        rewrite TMap.gso by exact Hneq. apply IH.
        intro Hin. apply Hout. now right.
    Qed.

    Lemma initial_represents :
      represents (initial_family_state D (@SPListIndexedObject A))
        (@empty_array_state A D).
    Proof.
      constructor.
      - intro owner. split.
        + intros [row Hrow].
          unfold payload_at, initial_family_state in Hrow.
          destruct (ThreadDomain.contains_dec D owner) as [Hin|Hout]; auto.
          rewrite initial_rows_find_out in Hrow by exact Hout. discriminate.
        + intros Hin. exists (@empty_row_state A).
          unfold payload_at, initial_family_state.
          pose proof (initial_rows_find_in (ThreadDomain.threads D) owner Hin)
            as Hfind.
          rewrite Hfind. reflexivity.
      - intro owner. unfold counter_at, row_counter_at, payload_at,
          initial_family_state, empty_array_state.
        destruct (ThreadDomain.contains_dec D owner) as [Hin|Hout].
        + cbn. change (
            (match TMap.find owner
              (initial_counters (ThreadDomain.threads D)) with
             | Some count => count
             | None => Datatypes.O
             end) =
            (match option_map row_payload
              (TMap.find owner
                (initial_rows (@SPListIndexedObject A)
                  (ThreadDomain.threads D))) with
             | Some row => counter row
             | None => Datatypes.O
             end)).
          rewrite initial_counters_find_in, initial_rows_find_in by exact Hin.
          reflexivity.
        + cbn. change (
            (match TMap.find owner
              (initial_counters (ThreadDomain.threads D)) with
             | Some count => count
             | None => Datatypes.O
             end) =
            (match option_map row_payload
              (TMap.find owner
                (initial_rows (@SPListIndexedObject A)
                  (ThreadDomain.threads D))) with
             | Some row => counter row
             | None => Datatypes.O
             end)).
          rewrite initial_counters_find_out, initial_rows_find_out by exact Hout.
          reflexivity.
      - intro owner. unfold order_at, row_order_at, payload_at,
          initial_family_state, empty_array_state.
        destruct (ThreadDomain.contains_dec D owner) as [Hin|Hout].
        + cbn. change (
            (match TMap.find owner
              (initial_orders (ThreadDomain.threads D)) with
             | Some saved_order => saved_order
             | None => nil
             end) =
            (match option_map row_payload
              (TMap.find owner
                (initial_rows (@SPListIndexedObject A)
                  (ThreadDomain.threads D))) with
             | Some row => order row
             | None => nil
             end)).
          rewrite initial_orders_find_in, initial_rows_find_in by exact Hin.
          reflexivity.
        + cbn. change (
            (match TMap.find owner
              (initial_orders (ThreadDomain.threads D)) with
             | Some saved_order => saved_order
             | None => nil
             end) =
            (match option_map row_payload
              (TMap.find owner
                (initial_rows (@SPListIndexedObject A)
                  (ThreadDomain.threads D))) with
             | Some row => order row
             | None => nil
             end)).
          rewrite initial_orders_find_out, initial_rows_find_out by exact Hout.
          reflexivity.
      - intros [owner loc].
        destruct (ThreadDomain.contains_dec D owner) as [Hin|Hout].
        + change (
            match node_at
              (initial_family_state D (@SPListIndexedObject A))
              (pair owner loc) with
            | Some (pair v ts) =>
                (@None A) = Some v /\ (@None TS) = Some ts
            | None => (@None A) = None /\ (@None TS) = None
            end).
          unfold node_at, payload_at, initial_family_state.
          change (
            match
              match option_map row_payload
                (TMap.find owner
                  (initial_rows (@SPListIndexedObject A)
                    (ThreadDomain.threads D))) with
              | Some row => nodes row loc
              | None => None
              end
            with
            | Some (pair v ts) =>
                (@None A) = Some v /\ (@None TS) = Some ts
            | None => (@None A) = None /\ (@None TS) = None
            end).
          unfold option_map.
          pose proof
            (initial_rows_find_in (ThreadDomain.threads D) owner Hin)
            as Hfind.
          destruct (TMap.find owner
            (initial_rows (@SPListIndexedObject A)
              (ThreadDomain.threads D))) as [control|] eqn:Efind.
          * inversion Hfind; subst control.
            cbn [row_payload empty_row_state empty_heap].
            unfold empty_row_state, empty_heap.
            cbn. split; reflexivity.
          * discriminate.
        + change (
            match node_at
              (initial_family_state D (@SPListIndexedObject A))
              (pair owner loc) with
            | Some (pair v ts) =>
                (@None A) = Some v /\ (@None TS) = Some ts
            | None => (@None A) = None /\ (@None TS) = None
            end).
          unfold node_at, payload_at, initial_family_state.
          change (
            match
              match option_map row_payload
                (TMap.find owner
                  (initial_rows (@SPListIndexedObject A)
                    (ThreadDomain.threads D))) with
              | Some row => nodes row loc
              | None => None
              end
            with
            | Some (pair v ts) =>
                (@None A) = Some v /\ (@None TS) = Some ts
            | None => (@None A) = None /\ (@None TS) = None
            end).
          unfold option_map.
          pose proof
            (initial_rows_find_out (ThreadDomain.threads D) owner Hout)
            as Hfind.
          destruct (TMap.find owner
            (initial_rows (@SPListIndexedObject A)
              (ThreadDomain.threads D))) as [control|] eqn:Efind.
          * discriminate.
          * split; reflexivity.
      - intros [owner loc].
        destruct (ThreadDomain.contains_dec D owner) as [Hin|Hout].
        + change (False <->
            (match option_map row_payload
              (TMap.find owner
                (initial_rows (@SPListIndexedObject A)
                  (ThreadDomain.threads D))) with
             | Some row => nodes row loc
             | None => None
             end) <> None /\
            ~ In loc
              (match option_map row_payload
                (TMap.find owner
                  (initial_rows (@SPListIndexedObject A)
                    (ThreadDomain.threads D))) with
               | Some row => order row
               | None => nil
               end)).
          rewrite initial_rows_find_in by exact Hin. simpl. tauto.
        + change (False <->
            (match option_map row_payload
              (TMap.find owner
                (initial_rows (@SPListIndexedObject A)
                  (ThreadDomain.threads D))) with
             | Some row => nodes row loc
             | None => None
             end) <> None /\
            ~ In loc
              (match option_map row_payload
                (TMap.find owner
                  (initial_rows (@SPListIndexedObject A)
                    (ThreadDomain.threads D))) with
               | Some row => order row
               | None => nil
               end)).
          rewrite initial_rows_find_out by exact Hout. simpl. tauto.
      - intros owner row Hrow. unfold payload_at, initial_family_state in Hrow.
        destruct (ThreadDomain.contains_dec D owner) as [Hin|Hout].
        + rewrite initial_rows_find_in in Hrow by exact Hin.
          inversion Hrow; constructor.
        + rewrite initial_rows_find_out in Hrow by exact Hout. discriminate.
      - intros owner row loc Hrow Hin. unfold payload_at, initial_family_state in Hrow.
        destruct (ThreadDomain.contains_dec D owner) as [Hinside|Houtside].
        + rewrite initial_rows_find_in in Hrow by exact Hinside.
          inversion Hrow; subst row. inversion Hin.
        + rewrite initial_rows_find_out in Hrow by exact Houtside. discriminate.
      - intros actor owner row Hrow. unfold expected_snapshot, empty_array_state.
        rewrite TMap.gempty. unfold payload_at, initial_family_state in Hrow.
        destruct (ThreadDomain.contains_dec D owner) as [Hin|Hout].
        + rewrite initial_rows_find_in in Hrow by exact Hin.
          inversion Hrow; simpl. apply TMap.gempty.
        + rewrite initial_rows_find_out in Hrow by exact Hout. discriminate.
    Qed.

    Lemma payload_at_find rows owner control :
      TMap.find owner rows = Some control ->
      payload_at rows owner = Some (row_payload control).
    Proof.
      intro Hfind. unfold payload_at, option_map.
      destruct (TMap.find owner rows) as [found|] eqn:Efind.
      - inversion Hfind; reflexivity.
      - discriminate.
    Qed.

    Lemma represents_change_control rows a owner old_control new_control :
      TMap.find owner rows = Some old_control ->
      row_payload new_control = row_payload old_control ->
      represents rows a ->
      represents (TMap.add owner new_control rows) a.
    Proof.
      intros Hold Hpayload Hrep.
      pose proof (payload_at_find rows owner old_control Hold) as Holdpayload.
      assert (Hpayload_at : forall q,
        payload_at (TMap.add owner new_control rows) q = payload_at rows q).
      { intro q. destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        - rewrite payload_at_add_same, Hpayload. symmetry. exact Holdpayload.
        - apply payload_at_add_other. exact Hneq. }
      constructor.
      - intro q. rewrite Hpayload_at. apply (rep_domain _ _ Hrep q).
      - intro q. unfold row_counter_at. rewrite Hpayload_at.
        exact (rep_counter _ _ Hrep q).
      - intro q. unfold row_order_at. rewrite Hpayload_at.
        exact (rep_order _ _ Hrep q).
      - intros [q loc]. pose proof (rep_node _ _ Hrep (pair q loc)) as Hnode.
        unfold node_at in *. simpl in *. rewrite Hpayload_at. exact Hnode.
      - intros [q loc].
        pose proof (rep_garbage _ _ Hrep (pair q loc)) as Hgarbage.
        unfold node_at, row_order_at in *. simpl in *.
        repeat rewrite Hpayload_at. exact Hgarbage.
      - intros q row Hrow. rewrite Hpayload_at in Hrow.
        eapply rep_order_nodup; eauto.
      - intros q row loc Hrow Hin. rewrite Hpayload_at in Hrow.
        eapply rep_order_defined; eauto.
      - intros actor q row Hrow. rewrite Hpayload_at in Hrow.
        eapply rep_snapshot; eauto.
    Qed.

    Lemma represents_replace_same_payload rows a owner s new_control :
      payload_at rows owner = Some s ->
      row_payload new_control = s ->
      represents rows a ->
      represents (TMap.add owner new_control rows) a.
    Proof.
      intros Hrow Hnew Hrep. unfold payload_at, option_map in Hrow.
      destruct (TMap.find owner rows) as [old_control|] eqn:Hold.
      - inversion Hrow; subst s. eapply represents_change_control; eauto.
      - discriminate.
    Qed.

    Lemma represents_insert rows a owner s loc v :
      payload_at rows owner = Some s ->
      nodes s loc = None ->
      represents rows a ->
      represents (TMap.add owner (Ready (insert v loc s)) rows)
        (insert_node owner loc v a).
    Proof.
      intros Hrow Hfresh Hrep.
      assert (Hnotin : ~ In loc (order s)).
      { intro Hin. pose proof (rep_order_defined _ _ Hrep owner s loc Hrow Hin).
        congruence. }
      assert (Hnotgarbage : ~ as_garbage a (pair owner loc)).
      { intro Hg. apply (rep_garbage _ _ Hrep (pair owner loc)) in Hg.
        unfold node_at in Hg. simpl in Hg. rewrite Hrow, Hfresh in Hg.
        tauto. }
      constructor.
      - intro q. destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + split; intros _.
          * apply (proj1 (rep_domain _ _ Hrep owner)). now exists s.
          * exists (insert v loc s). apply payload_at_add_same.
        + rewrite payload_at_add_other by exact Hneq.
          apply (rep_domain _ _ Hrep q).
      - intro q. unfold counter_at, row_counter_at, insert_node. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite TMap.gss, payload_at_add_same. simpl.
          rewrite (rep_counter _ _ Hrep owner). unfold row_counter_at.
          rewrite Hrow. lia.
        + rewrite TMap.gso by exact Hneq.
          rewrite payload_at_add_other by exact Hneq.
          exact (rep_counter _ _ Hrep q).
      - intro q. unfold order_at, row_order_at, insert_node. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite TMap.gss, payload_at_add_same. simpl.
          rewrite (rep_order _ _ Hrep owner). unfold row_order_at.
          now rewrite Hrow.
        + rewrite TMap.gso by exact Hneq.
          rewrite payload_at_add_other by exact Hneq.
          exact (rep_order _ _ Hrep q).
      - intros [q address]. unfold node_at, insert_node. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Howner].
        + rewrite payload_at_add_same. simpl.
          destruct (Nat.eq_dec address loc) as [->|Hloc].
          * rewrite HeapUpdateSelf, node_update_eq.
            unfold timestamp_update.
            destruct (node_eq_dec (pair owner loc) (pair owner loc));
              [split; reflexivity|congruence].
          * rewrite HeapUpdateOther by congruence.
            rewrite node_update_neq by congruence.
            unfold timestamp_update.
            destruct (node_eq_dec (pair owner loc) (pair owner address)) as [Heq|_].
            { congruence. }
            pose proof (rep_node _ _ Hrep (pair owner address)) as Hnode.
            unfold node_at in Hnode. simpl in Hnode. now rewrite Hrow in Hnode.
        + rewrite payload_at_add_other by exact Howner.
          rewrite node_update_neq by congruence.
          unfold timestamp_update.
          destruct (node_eq_dec (pair owner loc) (pair q address)) as [Heq|_].
          { congruence. }
          exact (rep_node _ _ Hrep (pair q address)).
      - intros [q address]. unfold insert_node, node_at, row_order_at. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Howner].
        + rewrite payload_at_add_same. simpl.
          destruct (Nat.eq_dec address loc) as [->|Hloc].
          * rewrite HeapUpdateSelf. simpl. split; intros Hbad.
            { apply Hnotgarbage in Hbad. contradiction. }
            { destruct Hbad as [_ Hnot]. exfalso. apply Hnot. now left. }
          * rewrite HeapUpdateOther by congruence. simpl.
            pose proof (rep_garbage _ _ Hrep (pair owner address)) as Hg.
            unfold node_at, row_order_at in Hg. simpl in Hg. rewrite Hrow in Hg.
            split.
            { intro Hgarb. apply Hg in Hgarb. destruct Hgarb as [Hdef Hnot].
              split; auto. intro Hin. destruct Hin as [Heq|Hin]; auto.
            }
            { intros [Hdef Hnot]. apply Hg. split; auto. }
        + repeat rewrite payload_at_add_other by exact Howner.
          exact (rep_garbage _ _ Hrep (pair q address)).
      - intros q row Hnewrow. destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same in Hnewrow. inversion Hnewrow; subst row.
          simpl. constructor; [exact Hnotin|]. eapply rep_order_nodup; eauto.
        + rewrite payload_at_add_other in Hnewrow by exact Hneq.
          eapply rep_order_nodup; eauto.
      - intros q row address Hnewrow Hin.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same in Hnewrow. inversion Hnewrow; subst row.
          simpl in *. destruct Hin as [<-|Hin].
          * rewrite HeapUpdateSelf. discriminate.
          * destruct (Nat.eq_dec loc address) as [->|Hdifferent].
            { rewrite HeapUpdateSelf. discriminate. }
            rewrite HeapUpdateOther by exact Hdifferent.
            eapply rep_order_defined; eauto.
        + rewrite payload_at_add_other in Hnewrow by exact Hneq.
          eapply rep_order_defined; eauto.
      - intros actor q row Hnewrow.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same in Hnewrow. inversion Hnewrow; subst row.
          simpl. unfold expected_snapshot, insert_node. cbn.
          exact (rep_snapshot _ _ Hrep actor owner s Hrow).
        + rewrite payload_at_add_other in Hnewrow by exact Hneq.
          unfold expected_snapshot, insert_node. cbn.
          eapply rep_snapshot; eauto.
    Qed.

    Lemma represents_setTS_top rows a owner s loc value ts :
      payload_at rows owner = Some s ->
      nodes s loc = Some (pair value TSTop) ->
      represents rows a ->
      represents (TMap.add owner (Ready (setTS loc ts s)) rows)
        (set_node_timestamp owner loc ts a).
    Proof.
      intros Hrow Hnode Hrep.
      pose proof
        (represents_node_some _ _ _ _ _ _ _ Hrep Hrow Hnode)
        as [Hvalue Htimestamp].
      assert (Hset : setTS loc ts s =
        {| counter := counter s;
           nodes := heap_update loc (pair value ts) (nodes s);
           order := order s;
           snapshot := snapshot s |}).
      { unfold setTS. rewrite Hnode. reflexivity. }
      constructor.
      - intro q. destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + split; intros _.
          * apply (proj1 (rep_domain _ _ Hrep owner)). now exists s.
          * exists (setTS loc ts s). apply payload_at_add_same.
        + rewrite payload_at_add_other by exact Hneq.
          apply (rep_domain _ _ Hrep q).
      - intro q. unfold counter_at, row_counter_at, set_node_timestamp. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same, Hset. simpl.
          pose proof (rep_counter _ _ Hrep owner) as Hcounter.
          unfold row_counter_at in Hcounter. now rewrite Hrow in Hcounter.
        + rewrite payload_at_add_other by exact Hneq.
          exact (rep_counter _ _ Hrep q).
      - intro q. unfold order_at, row_order_at, set_node_timestamp. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same, Hset. simpl.
          pose proof (rep_order _ _ Hrep owner) as Horder.
          unfold row_order_at in Horder. rewrite Hrow in Horder.
          exact Horder.
        + rewrite payload_at_add_other by exact Hneq.
          exact (rep_order _ _ Hrep q).
      - intros [q address]. unfold node_at, set_node_timestamp. cbn.
        rewrite Htimestamp. destruct (PositiveMap.E.eq_dec q owner) as [->|Howner].
        + rewrite payload_at_add_same, Hset. simpl.
          destruct (Nat.eq_dec address loc) as [->|Hloc].
          * rewrite HeapUpdateSelf. unfold timestamp_update.
            destruct (node_eq_dec (pair owner loc) (pair owner loc));
              [split; [exact Hvalue|reflexivity]|congruence].
          * rewrite HeapUpdateOther by congruence.
            unfold timestamp_update.
            destruct (node_eq_dec (pair owner loc) (pair owner address));
              [congruence|].
            pose proof (rep_node _ _ Hrep (pair owner address)) as H.
            unfold node_at in H. simpl in H. now rewrite Hrow in H.
        + rewrite payload_at_add_other by exact Howner.
          unfold timestamp_update.
          destruct (node_eq_dec (pair owner loc) (pair q address));
            [congruence|].
          exact (rep_node _ _ Hrep (pair q address)).
      - intros [q address]. unfold node_at, row_order_at, set_node_timestamp. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Howner].
        + rewrite payload_at_add_same, Hset. simpl.
          pose proof (rep_garbage _ _ Hrep (pair owner address)) as H.
          unfold node_at, row_order_at in H. simpl in H. rewrite Hrow in H.
          destruct (Nat.eq_dec address loc) as [->|Hloc].
          * rewrite HeapUpdateSelf. rewrite Hnode in H. split.
            { intro Hg. apply H in Hg. destruct Hg as [_ Hnot].
              split; [discriminate|exact Hnot]. }
            { intros [_ Hnot]. apply H. split; [discriminate|exact Hnot]. }
          * rewrite HeapUpdateOther by congruence. exact H.
        + repeat rewrite payload_at_add_other by exact Howner.
          exact (rep_garbage _ _ Hrep (pair q address)).
      - intros q row Hnewrow. destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same in Hnewrow. inversion Hnewrow; subst row.
          rewrite Hset. simpl. eapply rep_order_nodup; eauto.
        + rewrite payload_at_add_other in Hnewrow by exact Hneq.
          eapply rep_order_nodup; eauto.
      - intros q row address Hnewrow Hin.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same in Hnewrow. inversion Hnewrow; subst row.
          rewrite Hset in *. simpl in *.
          destruct (Nat.eq_dec loc address) as [->|Hdifferent].
          * rewrite HeapUpdateSelf. discriminate.
          * rewrite HeapUpdateOther by exact Hdifferent.
            eapply rep_order_defined; eauto.
        + rewrite payload_at_add_other in Hnewrow by exact Hneq.
          eapply rep_order_defined; eauto.
      - intros actor q row Hnewrow.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same in Hnewrow. inversion Hnewrow; subst row.
          rewrite Hset. simpl. unfold expected_snapshot, set_node_timestamp.
          cbn.
          exact (rep_snapshot _ _ Hrep actor owner s Hrow).
        + rewrite payload_at_add_other in Hnewrow by exact Hneq.
          unfold expected_snapshot, set_node_timestamp. cbn.
          eapply rep_snapshot; eauto.
    Qed.

    Lemma represents_setTS rows a owner s loc ts :
      payload_at rows owner = Some s ->
      nodes s loc <> None ->
      represents rows a ->
      represents (TMap.add owner (Ready (setTS loc ts s)) rows)
        (set_node_timestamp owner loc ts a).
    Proof.
      intros Hrow Hdefined Hrep.
      destruct (nodes s loc) as [[value oldts]|] eqn:Hnode;
        [|contradiction].
      destruct oldts as [|lower upper].
      - eapply represents_setTS_top; eauto.
      - pose proof
          (represents_node_some _ _ _ _ _ _ _ Hrep Hrow Hnode)
          as [_ Htimestamp].
        unfold set_node_timestamp. cbn. rewrite Htimestamp.
        destruct a; cbn in *.
        unfold setTS. rewrite Hnode.
        eapply represents_replace_same_payload; eauto.
    Qed.

    Lemma nodup_remove_nat loc xs :
      NoDup xs -> NoDup (List.remove Nat.eq_dec loc xs).
    Proof.
      induction xs as [|head tail IH]; simpl; intro Hnodup; [constructor|].
      inversion Hnodup as [|? ? Hnotin Htail]; subst.
      destruct (Nat.eq_dec loc head) as [->|Hneq].
      - apply IH. exact Htail.
      - constructor.
        + intro Hin. apply in_remove in Hin. tauto.
        + apply IH. exact Htail.
    Qed.

    Lemma represents_remove rows a owner s loc :
      payload_at rows owner = Some s ->
      nodes s loc <> None ->
      represents rows a ->
      represents (TMap.add owner (Ready (remove loc s)) rows)
        (remove_node (pair owner loc) a).
    Proof.
      intros Hrow Hdefined Hrep. constructor.
      - intro q. destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + split; intros _.
          * apply (proj1 (rep_domain _ _ Hrep owner)). now exists s.
          * exists (remove loc s). apply payload_at_add_same.
        + rewrite payload_at_add_other by exact Hneq.
          apply (rep_domain _ _ Hrep q).
      - intro q. unfold counter_at, row_counter_at, remove_node. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same. simpl.
          pose proof (rep_counter _ _ Hrep owner) as Hcounter.
          unfold row_counter_at in Hcounter. now rewrite Hrow in Hcounter.
        + rewrite payload_at_add_other by exact Hneq.
          exact (rep_counter _ _ Hrep q).
      - intro q. unfold order_at, row_order_at, remove_node. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite TMap.gss, payload_at_add_same. simpl.
          pose proof (rep_order _ _ Hrep owner) as Horder.
          unfold row_order_at in Horder. rewrite Hrow in Horder.
          now rewrite Horder.
        + rewrite TMap.gso by exact Hneq.
          rewrite payload_at_add_other by exact Hneq.
          exact (rep_order _ _ Hrep q).
      - intros [q address]. unfold node_at, remove_node. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same. simpl.
          pose proof (rep_node _ _ Hrep (pair owner address)) as Hnode.
          unfold node_at in Hnode. simpl in Hnode. now rewrite Hrow in Hnode.
        + rewrite payload_at_add_other by exact Hneq.
          exact (rep_node _ _ Hrep (pair q address)).
      - intros [q address]. unfold remove_node, node_at, row_order_at. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Howner].
        + rewrite payload_at_add_same. simpl.
          pose proof (rep_garbage _ _ Hrep (pair owner address)) as Hg.
          unfold node_at, row_order_at in Hg. simpl in Hg. rewrite Hrow in Hg.
          unfold set_add. destruct (node_eq_dec (pair owner loc)
            (pair owner address)) as [Heq|Hneq].
          * inversion Heq; subst address. split; intros _.
            { split; [exact Hdefined|apply remove_In]. }
            { left. reflexivity. }
          * assert (Haddress : address <> loc) by congruence.
            split.
            { intros [Hequal|Hgarb]; [congruence|].
              apply Hg in Hgarb. destruct Hgarb as [Hdef Hnot].
              split; [exact Hdef|]. intro Hin.
              apply in_remove in Hin. apply Hnot. exact (proj1 Hin). }
            { intros [Hdef Hnot]. right. apply Hg. split; [exact Hdef|].
              intro Hin. apply Hnot. apply in_in_remove; auto. }
        + rewrite payload_at_add_other by exact Howner.
          unfold set_add.
          destruct (node_eq_dec (pair owner loc) (pair q address));
            [congruence|].
          pose proof (rep_garbage _ _ Hrep (pair q address)) as Hg.
          split.
          * intros [Hequal|Hgarbage].
            { congruence. }
            { apply Hg. exact Hgarbage. }
          * intro Hfacts. right. apply Hg. exact Hfacts.
      - intros q row Hnewrow. destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same in Hnewrow. inversion Hnewrow; subst row.
          simpl. apply nodup_remove_nat. eapply rep_order_nodup; eauto.
        + rewrite payload_at_add_other in Hnewrow by exact Hneq.
          eapply rep_order_nodup; eauto.
      - intros q row address Hnewrow Hin.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same in Hnewrow. inversion Hnewrow; subst row.
          simpl in *. apply in_remove in Hin.
          eapply rep_order_defined; eauto. exact (proj1 Hin).
        + rewrite payload_at_add_other in Hnewrow by exact Hneq.
          eapply rep_order_defined; eauto.
      - intros actor q row Hnewrow.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same in Hnewrow. inversion Hnewrow; subst row.
          simpl. unfold expected_snapshot, remove_node. cbn.
          exact (rep_snapshot _ _ Hrep actor owner s Hrow).
        + rewrite payload_at_add_other in Hnewrow by exact Hneq.
          unfold expected_snapshot, remove_node. cbn.
          eapply rep_snapshot; eauto.
    Qed.

    Lemma represents_start_counter rows a (actor : tid) :
      represents rows a -> represents rows (start_counter D actor a).
    Proof.
      intro Hrep. constructor.
      - exact (rep_domain _ _ Hrep).
      - exact (rep_counter _ _ Hrep).
      - exact (rep_order _ _ Hrep).
      - exact (rep_node _ _ Hrep).
      - exact (rep_garbage _ _ Hrep).
      - exact (rep_order_nodup _ _ Hrep).
      - exact (rep_order_defined _ _ Hrep).
      - intros caller owner row Hrow.
        unfold expected_snapshot, start_counter. cbn.
        eapply rep_snapshot; eauto.
    Qed.

    Lemma represents_finish_counter rows a (actor : tid) :
      represents rows a -> represents rows (finish_counter actor a).
    Proof.
      intro Hrep. constructor.
      - exact (rep_domain _ _ Hrep).
      - exact (rep_counter _ _ Hrep).
      - exact (rep_order _ _ Hrep).
      - exact (rep_node _ _ Hrep).
      - exact (rep_garbage _ _ Hrep).
      - exact (rep_order_nodup _ _ Hrep).
      - exact (rep_order_defined _ _ Hrep).
      - intros caller owner row Hrow.
        unfold expected_snapshot, finish_counter. cbn.
        eapply rep_snapshot; eauto.
    Qed.

    Definition scan_idle (a : @SPListArrayState A) (actor : tid) : Prop :=
      forall p, TMap.find actor (as_scans a) = Some p ->
        scan_current p = None.

    Lemma represents_reset_scan rows a (actor : tid) :
      represents rows a -> scan_idle a actor ->
      represents rows (reset_scan actor a).
    Proof.
      intros Hrep Hidle. constructor.
      - exact (rep_domain _ _ Hrep).
      - intro owner. exact (rep_counter _ _ Hrep owner).
      - intro owner. exact (rep_order _ _ Hrep owner).
      - exact (rep_node _ _ Hrep).
      - exact (rep_garbage _ _ Hrep).
      - exact (rep_order_nodup _ _ Hrep).
      - exact (rep_order_defined _ _ Hrep).
      - intros caller owner row Hrow.
        pose proof (rep_snapshot _ _ Hrep caller owner row Hrow) as Hsnap.
        unfold expected_snapshot, reset_scan in *. cbn.
        destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
        + rewrite TMap.gss. simpl.
          destruct (TMap.find actor (as_scans a)) as [p|] eqn:Hscan;
            [rewrite (Hidle p Hscan) in Hsnap|]; exact Hsnap.
        + rewrite TMap.gso by exact Hneq. exact Hsnap.
    Qed.

    Lemma represents_begin_scan rows a actor owner s p :
      represents rows a ->
      payload_at rows owner = Some s ->
      TMap.find actor (as_scans a) = Some p ->
      scan_current p = None ->
      represents
        (TMap.add owner (Ready (start_snapshot actor s)) rows)
        (begin_scan actor owner p a).
    Proof.
      intros Hrep Hrow Hscan Hidle. constructor.
      - intro q. destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + split; intros _.
          * apply (proj1 (rep_domain _ _ Hrep owner)). now exists s.
          * exists (start_snapshot actor s). apply payload_at_add_same.
        + rewrite payload_at_add_other by exact Hneq.
          apply (rep_domain _ _ Hrep q).
      - intro q. unfold counter_at, row_counter_at, begin_scan. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same. simpl.
          pose proof (rep_counter _ _ Hrep owner) as Hcounter.
          unfold row_counter_at in Hcounter. now rewrite Hrow in Hcounter.
        + rewrite payload_at_add_other by exact Hneq.
          exact (rep_counter _ _ Hrep q).
      - intro q. unfold order_at, row_order_at, begin_scan. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same. simpl.
          pose proof (rep_order _ _ Hrep owner) as Horder.
          unfold row_order_at in Horder. rewrite Hrow in Horder. exact Horder.
        + rewrite payload_at_add_other by exact Hneq.
          exact (rep_order _ _ Hrep q).
      - intros [q address]. unfold node_at, begin_scan. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same. simpl.
          pose proof (rep_node _ _ Hrep (pair owner address)) as Hnode.
          unfold node_at in Hnode. simpl in Hnode. now rewrite Hrow in Hnode.
        + rewrite payload_at_add_other by exact Hneq.
          exact (rep_node _ _ Hrep (pair q address)).
      - intros [q address]. unfold node_at, row_order_at, begin_scan. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same. simpl.
          pose proof (rep_garbage _ _ Hrep (pair owner address)) as H.
          unfold node_at, row_order_at in H. simpl in H. now rewrite Hrow in H.
        + repeat rewrite payload_at_add_other by exact Hneq.
          exact (rep_garbage _ _ Hrep (pair q address)).
      - intros q row Hnew. destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same in Hnew. inversion Hnew; subst row.
          simpl. eapply rep_order_nodup; eauto.
        + rewrite payload_at_add_other in Hnew by exact Hneq.
          eapply rep_order_nodup; eauto.
      - intros q row address Hnew Hin.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same in Hnew. inversion Hnew; subst row.
          simpl in *. eapply rep_order_defined; eauto.
        + rewrite payload_at_add_other in Hnew by exact Hneq.
          eapply rep_order_defined; eauto.
      - intros caller q row Hnew.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hq].
        + rewrite payload_at_add_same in Hnew. inversion Hnew; subst row.
          simpl. unfold expected_snapshot, begin_scan. cbn.
          destruct (PositiveMap.E.eq_dec caller actor) as [->|Hcaller].
          * rewrite TMap.gss, TMap.gss. simpl.
            destruct (PositiveMap.E.eq_dec owner owner); [|congruence].
            pose proof (rep_order _ _ Hrep owner) as Horder.
            pose proof (rep_counter _ _ Hrep owner) as Hcounter.
            unfold row_order_at in Horder. rewrite Hrow in Horder.
            unfold row_counter_at in Hcounter. rewrite Hrow in Hcounter.
            now rewrite Horder, Hcounter.
          * rewrite TMap.gso by exact Hcaller.
            rewrite TMap.gso by exact Hcaller.
            exact (rep_snapshot _ _ Hrep caller owner s Hrow).
        + rewrite payload_at_add_other in Hnew by exact Hq.
          unfold expected_snapshot, begin_scan. cbn.
          destruct (PositiveMap.E.eq_dec caller actor) as [->|Hcaller].
          * rewrite TMap.gss. simpl.
            destruct (PositiveMap.E.eq_dec q owner); [congruence|].
            pose proof (rep_snapshot _ _ Hrep actor q row Hnew) as Hold.
            unfold expected_snapshot in Hold. rewrite Hscan, Hidle in Hold.
            exact Hold.
          * rewrite TMap.gso by exact Hcaller.
            eapply rep_snapshot; eauto.
    Qed.

    Lemma represents_end_scan rows a actor owner s p c :
      represents rows a ->
      payload_at rows owner = Some s ->
      TMap.find actor (as_scans a) = Some p ->
      scan_current p = Some c ->
      current_owner c = owner ->
      represents
        (TMap.add owner (Ready (clear_snapshot actor s)) rows)
        (end_scan actor p c a).
    Proof.
      intros Hrep Hrow Hscan Hcurrent Howner. constructor.
      - intro q. destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + split; intros _.
          * apply (proj1 (rep_domain _ _ Hrep owner)). now exists s.
          * exists (clear_snapshot actor s). apply payload_at_add_same.
        + rewrite payload_at_add_other by exact Hneq.
          apply (rep_domain _ _ Hrep q).
      - intro q. unfold counter_at, row_counter_at, end_scan. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same. simpl.
          pose proof (rep_counter _ _ Hrep owner) as Hcounter.
          unfold row_counter_at in Hcounter. now rewrite Hrow in Hcounter.
        + rewrite payload_at_add_other by exact Hneq.
          exact (rep_counter _ _ Hrep q).
      - intro q. unfold order_at, row_order_at, end_scan. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same. simpl.
          pose proof (rep_order _ _ Hrep owner) as Horder.
          unfold row_order_at in Horder. rewrite Hrow in Horder. exact Horder.
        + rewrite payload_at_add_other by exact Hneq.
          exact (rep_order _ _ Hrep q).
      - intros [q address]. unfold node_at, end_scan. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same. simpl.
          pose proof (rep_node _ _ Hrep (pair owner address)) as Hnode.
          unfold node_at in Hnode. simpl in Hnode. now rewrite Hrow in Hnode.
        + rewrite payload_at_add_other by exact Hneq.
          exact (rep_node _ _ Hrep (pair q address)).
      - intros [q address]. unfold node_at, row_order_at, end_scan. cbn.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same. simpl.
          pose proof (rep_garbage _ _ Hrep (pair owner address)) as H.
          unfold node_at, row_order_at in H. simpl in H. now rewrite Hrow in H.
        + repeat rewrite payload_at_add_other by exact Hneq.
          exact (rep_garbage _ _ Hrep (pair q address)).
      - intros q row Hnew. destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same in Hnew. inversion Hnew; subst row.
          simpl. eapply rep_order_nodup; eauto.
        + rewrite payload_at_add_other in Hnew by exact Hneq.
          eapply rep_order_nodup; eauto.
      - intros q row address Hnew Hin.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
        + rewrite payload_at_add_same in Hnew. inversion Hnew; subst row.
          simpl in *. eapply rep_order_defined; eauto.
        + rewrite payload_at_add_other in Hnew by exact Hneq.
          eapply rep_order_defined; eauto.
      - intros caller q row Hnew.
        destruct (PositiveMap.E.eq_dec q owner) as [->|Hq].
        + rewrite payload_at_add_same in Hnew. inversion Hnew; subst row.
          simpl. unfold expected_snapshot, end_scan. cbn.
          destruct (PositiveMap.E.eq_dec caller actor) as [->|Hcaller].
          * rewrite TMap.grs, TMap.gss. reflexivity.
          * rewrite TMap.gro by exact Hcaller.
            rewrite TMap.gso by exact Hcaller.
            exact (rep_snapshot _ _ Hrep caller owner s Hrow).
        + rewrite payload_at_add_other in Hnew by exact Hq.
          unfold expected_snapshot, end_scan. cbn.
          destruct (PositiveMap.E.eq_dec caller actor) as [->|Hcaller].
          * rewrite TMap.gss. simpl.
            pose proof (rep_snapshot _ _ Hrep actor q row Hnew) as Hold.
            unfold expected_snapshot in Hold. rewrite Hscan, Hcurrent in Hold.
            destruct (PositiveMap.E.eq_dec q (current_owner c));
              [congruence|exact Hold].
          * rewrite TMap.gso by exact Hcaller.
            eapply rep_snapshot; eauto.
    Qed.

    Definition scan_token_consistent
        (a : @SPListArrayState A)
        (pi : tmap (@LinState (li_sig F))) : Prop :=
      forall actor p c,
        TMap.find actor (as_scans a) = Some p ->
        scan_current p = Some c ->
        TMap.find actor pi =
          Some (ls_lini (array_getTop (current_owner c))).

    Definition counter_token_consistent
        (a : @SPListArrayState A)
        (pi : tmap (@LinState (li_sig F))) : Prop :=
      forall actor saved,
        TMap.find actor (as_pending_counters a) = Some saved ->
        TMap.find actor pi = Some (ls_lini array_getCounter).

    Definition source_I : assertion :=
      fun w => exists rows a,
        SinglePossState.σ w = rows /\
        SinglePossState.ρ w = ArrayReady a /\
        represents rows a /\
        scan_token_consistent a (SinglePossState.π w) /\
        counter_token_consistent a (SinglePossState.π w).

    Definition SI := lift_assert source_I.

    Definition source_G (actor : tid) : rg_relation :=
      fun w w' =>
        source_I w /\ source_I w' /\
        (forall observer, observer <> actor ->
          TMap.find observer (SinglePossState.π w) =
          TMap.find observer (SinglePossState.π w')) /\
        (forall observer a a',
          SinglePossState.ρ w = ArrayReady a ->
          SinglePossState.ρ w' = ArrayReady a' ->
          observer <> actor ->
          TMap.find observer (as_scans a) =
          TMap.find observer (as_scans a')) /\
        (forall owner s pending_actor op,
          TMap.find owner (SinglePossState.σ w) =
            Some (AtomicPending s pending_actor op) ->
          pending_actor <> actor ->
          TMap.find owner (SinglePossState.σ w') =
            Some (AtomicPending s pending_actor op)) /\
        (forall owner,
          row_counter_at (SinglePossState.σ w) owner <=
          row_counter_at (SinglePossState.σ w') owner) /\
        (forall observer a a',
          SinglePossState.ρ w = ArrayReady a ->
          SinglePossState.ρ w' = ArrayReady a' ->
          observer <> actor ->
          TMap.find observer (as_pending_counters a) =
          TMap.find observer (as_pending_counters a')).

    Definition source_R (observer : tid) : rg_relation :=
      AssertionsSingle.GuaranteeGeneratedRely source_G observer.

    Definition R observer := lift_relation (source_R observer).
    Definition G actor := lift_relation (source_G actor).

    Definition token_eq (observer : tid) : rg_relation :=
      fun w w' =>
        TMap.find observer (SinglePossState.π w) =
        TMap.find observer (SinglePossState.π w').

    Lemma source_G_token_other actor observer :
      actor <> observer ->
      (source_G actor ⊆ token_eq observer)%RGRelation.
    Proof.
      intros Hneq w w' [_ [_ [Htokens _]]]. apply Htokens. congruence.
    Qed.

    Lemma observer_view_token observer :
      (AssertionsSingle.ObserverViewEq observer ⊆
        token_eq observer)%RGRelation.
    Proof. intros w w' [_ [_ Htoken]]. exact Htoken. Qed.

    Lemma source_R_token observer :
      (source_R observer ⊆ token_eq observer)%RGRelation.
    Proof.
      eapply AssertionsSingle.guarantee_generated_rely_facts.
      - intros actor Hneq. apply source_G_token_other. exact Hneq.
      - apply observer_view_token.
    Qed.

    Lemma source_valid_rg observer w w' :
      source_R observer w w' -> source_I w' ->
      TMap.find observer (SinglePossState.π w) = None <->
      TMap.find observer (SinglePossState.π w') = None.
    Proof.
      intros HR _. pose proof (source_R_token observer _ _ HR) as Heq.
      rewrite Heq. tauto.
    Qed.

    Lemma valid_rg observer :
      RGISimulationSet.RGISimulation.ValidRGI
        (R observer) (G observer) SI observer.
    Proof. eapply lift_valid_rgi. apply source_valid_rg. Qed.

    Lemma source_parallel_compatible actor observer :
      actor <> observer -> forall w w',
      (source_G actor w w' \/
       (AssertionsSingle.GINV actor w w' \/
        AssertionsSingle.GRET actor w w') \/
       AssertionsSingle.A.GId w w') ->
      source_R observer w w'.
    Proof.
      intros Hneq.
      eapply AssertionsSingle.guarantee_generated_parallel_compatible.
      exact Hneq.
    Qed.

    Lemma parallel_compatible actor observer :
      actor <> observer -> forall w w',
      (G actor w w' \/
       (AssertionsSet.GINV actor w w' \/ AssertionsSet.GRET actor w w') \/
       AssertionsSet.A.GId w w') /\ SI w ->
      R observer w w'.
    Proof.
      intros Hneq. eapply lift_parallel_compat; [exact Hneq|].
      apply source_parallel_compatible. exact Hneq.
    Qed.

    Definition Active (actor : tid) (m : Sig.op (li_sig F)) : assertion :=
      fun w => source_I w /\ ALin actor (ls_inv m) w.

    Definition Completed (actor : tid) (m : Sig.op (li_sig F))
        (ret : Sig.ar m) : assertion :=
      fun w => source_I w /\ ALin actor (ls_linr m ret) w.

    Definition SActive actor m := lift_assert (Active actor m).
    Definition SCompleted actor m ret := lift_assert (Completed actor m ret).

    Lemma active_entails_I actor m : ⊨ Active actor m ==>> source_I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma completed_entails_I actor m ret :
      ⊨ Completed actor m ret ==>> source_I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma active_stable actor m :
      AssertionsSingle.A.Stable (source_R actor) source_I (Active actor m).
    Proof.
      unfold AssertionsSingle.A.Stable, AssertionsSingle.A.ComposeA.
      intros w [[pre [[HI Hlin] HR]] HI']. split; [exact HI'|].
      unfold ALin in *. rewrite <- (source_R_token actor pre w HR). exact Hlin.
    Qed.

    Lemma completed_stable actor m ret :
      AssertionsSingle.A.Stable
        (source_R actor) source_I (Completed actor m ret).
    Proof.
      unfold AssertionsSingle.A.Stable, AssertionsSingle.A.ComposeA.
      intros w [[pre [[HI Hlin] HR]] HI']. split; [exact HI'|].
      unfold ALin in *. rewrite <- (source_R_token actor pre w HR). exact Hlin.
    Qed.

    Lemma scan_token_add_inv a pi actor m :
      scan_token_consistent a pi -> TMap.find actor pi = None ->
      scan_token_consistent a (TMap.add actor (ls_inv m) pi).
    Proof.
      intros Hconsistent Hnone caller p c Hscan Hcurrent.
      destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
      - pose proof (Hconsistent actor p c Hscan Hcurrent) as Hbad.
        rewrite Hnone in Hbad. discriminate.
      - rewrite TMap.gso by exact Hneq. eapply Hconsistent; eauto.
    Qed.

    Lemma counter_token_add_inv a pi actor m :
      counter_token_consistent a pi -> TMap.find actor pi = None ->
      counter_token_consistent a (TMap.add actor (ls_inv m) pi).
    Proof.
      intros Hconsistent Hnone caller saved Hpending.
      destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
      - pose proof (Hconsistent actor saved Hpending) as Hbad.
        rewrite Hnone in Hbad. discriminate.
      - rewrite TMap.gso by exact Hneq. eapply Hconsistent; eauto.
    Qed.

    Lemma scan_token_remove_linr a pi actor m ret :
      scan_token_consistent a pi ->
      TMap.find actor pi = Some (ls_linr m ret) ->
      scan_token_consistent a (TMap.remove actor pi).
    Proof.
      intros Hconsistent Hlin caller p c Hscan Hcurrent.
      destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
      - pose proof (Hconsistent actor p c Hscan Hcurrent) as Hbad.
        rewrite Hlin in Hbad. dependent destruction Hbad.
      - rewrite TMap.gro by exact Hneq. eapply Hconsistent; eauto.
    Qed.

    Lemma counter_token_remove_linr a pi actor m ret :
      counter_token_consistent a pi ->
      TMap.find actor pi = Some (ls_linr m ret) ->
      counter_token_consistent a (TMap.remove actor pi).
    Proof.
      intros Hconsistent Hlin caller saved Hpending.
      destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
      - pose proof (Hconsistent actor saved Hpending) as Hbad.
        rewrite Hlin in Hbad. dependent destruction Hbad.
      - rewrite TMap.gro by exact Hneq. eapply Hconsistent; eauto.
    Qed.

    Lemma ginv_exposes_active actor m :
      ⊨ AssertionsSingle.Ginv actor m ⊚ source_I ==>> Active actor m.
    Proof.
      intros out [pre [HI [Hsigma [Hrho [Hnone Hpi]]]]].
      destruct HI as
        (rows & a & Eσ & Eρ & Hrep & Hscan & Hcounter).
      split.
      - exists rows, a. split.
        + rewrite <- Hsigma. exact Eσ.
        + split.
          * rewrite <- Hrho. exact Eρ.
          * split; [exact Hrep|]. split.
            -- rewrite Hpi. eapply scan_token_add_inv; eauto.
            -- rewrite Hpi. eapply counter_token_add_inv; eauto.
      - unfold ALin. rewrite Hpi, TMap.gss. reflexivity.
    Qed.

    Lemma gret_closes_completed actor m ret :
      ⊨ AssertionsSingle.Gret actor m ret ⊚ Completed actor m ret ==>>
        source_I.
    Proof.
      intros out [pre [[HI Hlin] [Hsigma [Hrho [Hfind Hpi]]]]].
      destruct HI as
        (rows & a & Eσ & Eρ & Hrep & Hscan & Hcounter).
      exists rows, a. split.
      - rewrite <- Hsigma. exact Eσ.
      - split.
        + rewrite <- Hrho. exact Eρ.
        + split; [exact Hrep|]. split.
          * rewrite Hpi. eapply scan_token_remove_linr; eauto.
          * rewrite Hpi. eapply counter_token_remove_linr; eauto.
    Qed.

    Lemma set_ginv_exposes_active actor m :
      ⊨ AssertionsSet.A.ComposeA SI (AssertionsSet.Ginv actor m) ==>>
        SActive actor m.
    Proof.
      intros w Hcompose.
      eapply lift_ginv_compose; [apply ginv_exposes_active|exact Hcompose].
    Qed.

    Lemma set_gret_closes_completed actor m ret :
      ⊨ AssertionsSet.A.ComposeA (SCompleted actor m ret)
        (AssertionsSet.Gret actor m ret) ==>> SI.
    Proof.
      intros w Hcompose.
      eapply lift_gret_compose; [apply gret_closes_completed|exact Hcompose].
    Qed.

    Lemma completed_has_return_token actor m ret sigma Delta :
      SCompleted actor m ret
        (@SetPossState.Build_ProofStateSet _ _ (li_lts E) (li_lts F)
          sigma Delta) ->
      forall rho pi, Delta rho pi ->
        TMap.find actor pi = Some (ls_linr m ret).
    Proof.
      intros [w [Hview [_ Hlin]]] rho pi Hposs.
      eapply singleton_view_all_lin; eauto.
    Qed.

    Lemma family_step_preserves_foreign_pending actor ev rows rows' :
      te_tid ev = actor ->
      Step (li_lts E) ev rows rows' ->
      forall owner s pending_actor op,
        TMap.find owner rows = Some (AtomicPending s pending_actor op) ->
        pending_actor <> actor ->
        TMap.find owner rows' = Some (AtomicPending s pending_actor op).
    Proof.
      intros Hev Hstep owner s pending_actor op Hpending Hforeign.
      change (IndexedFamilySpec.StepIndexedFamily
        D (@SPListIndexedObject A) ev rows rows') in Hstep.
      dependent destruction Hstep. simpl in *.
      destruct (PositiveMap.E.eq_dec owner0 owner) as [Heq|Hneq].
      - subst owner0. rewrite H0 in Hpending. inversion Hpending; subst row.
        dependent destruction H1; simpl in Hev; congruence.
      - rewrite TMap.gso by exact Hneq. exact Hpending.
    Qed.

    Lemma counter_setTS loc ts (s : @SPListState A) :
      counter (setTS loc ts s) = counter s.
    Proof.
      unfold setTS. destruct (nodes s loc) as [[value old_ts]|].
      - destruct old_ts; reflexivity.
      - reflexivity.
    Qed.

    Lemma splist_step_counter_mono owner ev row row' :
      @StepSPList A owner ev row row' ->
      counter (row_payload row) <= counter (row_payload row').
    Proof.
      intro Hstep. inversion Hstep; subst; simpl;
        try (unfold start_snapshot, clear_snapshot, insert, remove; cbn; lia).
      rewrite counter_setTS. lia.
    Qed.

    Lemma family_step_counter_mono ev rows rows' :
      Step (li_lts E) ev rows rows' ->
      forall owner,
        row_counter_at rows owner <= row_counter_at rows' owner.
    Proof.
      intro Hstep. change (IndexedFamilySpec.StepIndexedFamily
        D (@SPListIndexedObject A) ev rows rows') in Hstep.
      dependent destruction Hstep. intro q.
      unfold row_counter_at, payload_at.
      destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
      - rewrite H0, TMap.gss. simpl.
        eapply splist_step_counter_mono. exact H1.
      - rewrite TMap.gso by exact Hneq. lia.
    Qed.

    Lemma source_G_of_step actor w w' :
      source_I w -> source_I w' ->
      (forall observer, observer <> actor ->
        TMap.find observer (SinglePossState.π w) =
        TMap.find observer (SinglePossState.π w')) ->
      (forall observer a a',
        SinglePossState.ρ w = ArrayReady a ->
        SinglePossState.ρ w' = ArrayReady a' ->
        observer <> actor ->
        TMap.find observer (as_scans a) =
        TMap.find observer (as_scans a')) ->
      (forall observer a a',
        SinglePossState.ρ w = ArrayReady a ->
        SinglePossState.ρ w' = ArrayReady a' ->
        observer <> actor ->
        TMap.find observer (as_pending_counters a) =
        TMap.find observer (as_pending_counters a')) ->
      (exists ev, te_tid ev = actor /\
        Step (li_lts E) ev (SinglePossState.σ w) (SinglePossState.σ w')) ->
      source_G actor w w'.
    Proof.
      intros HI HI' Htokens Hscans Hcounters [ev [Hev Hstep]].
      repeat split; auto.
      - intros owner s pending_actor op Hpending Hforeign.
        eapply family_step_preserves_foreign_pending; eauto.
      - eapply family_step_counter_mono. exact Hstep.
    Qed.

    Lemma source_G_same_concrete actor w w' :
      source_I w -> source_I w' ->
      SinglePossState.σ w = SinglePossState.σ w' ->
      (forall observer, observer <> actor ->
        TMap.find observer (SinglePossState.π w) =
        TMap.find observer (SinglePossState.π w')) ->
      (forall observer a a',
        SinglePossState.ρ w = ArrayReady a ->
        SinglePossState.ρ w' = ArrayReady a' ->
        observer <> actor ->
        TMap.find observer (as_scans a) =
        TMap.find observer (as_scans a')) ->
      (forall observer a a',
        SinglePossState.ρ w = ArrayReady a ->
        SinglePossState.ρ w' = ArrayReady a' ->
        observer <> actor ->
        TMap.find observer (as_pending_counters a) =
        TMap.find observer (as_pending_counters a')) ->
      source_G actor w w'.
    Proof.
      intros HI HI' Hsigma Htokens Hscans Hcounters. repeat split; auto.
      - intros owner s pending_actor op Hpending _. now rewrite <- Hsigma.
      - intro owner. rewrite Hsigma. lia.
    Qed.

    Lemma initial_source_I :
      source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (li_init E) (li_init F)
          (@TMap.empty (@LinState (li_sig F)))).
    Proof.
      unfold source_I, E, F. simpl.
      exists (initial_family_state D (@SPListIndexedObject A)).
      exists (@empty_array_state A D).
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact initial_represents|]. split.
      - intros actor p c Hscan. simpl in Hscan.
        rewrite TMap.gempty in Hscan. discriminate.
      - intros actor saved Hpending. simpl in Hpending.
        rewrite TMap.gempty in Hpending. discriminate.
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

    Lemma scan_token_atomic a a' pi actor m ret :
      scan_token_consistent a pi ->
      as_scans a' = as_scans a ->
      TMap.find actor pi = Some (ls_inv m) ->
      scan_token_consistent a'
        (TMap.add actor (ls_linr m ret)
          (TMap.add actor (ls_lini m) pi)).
    Proof.
      intros Hconsistent Hscans Hinv caller p c Hscan Hcurrent.
      destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
      - rewrite Hscans in Hscan.
        pose proof (Hconsistent actor p c Hscan Hcurrent) as Hbad.
        rewrite Hinv in Hbad. dependent destruction Hbad.
      - repeat rewrite TMap.gso by exact Hneq.
        eapply Hconsistent; [rewrite <- Hscans|]; eauto.
    Qed.

    Lemma counter_token_atomic a a' pi actor m ret :
      counter_token_consistent a pi ->
      as_pending_counters a' = as_pending_counters a ->
      TMap.find actor pi = Some (ls_inv m) ->
      counter_token_consistent a'
        (TMap.add actor (ls_linr m ret)
          (TMap.add actor (ls_lini m) pi)).
    Proof.
      intros Hconsistent Hpending Hinv caller saved Hfind.
      destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
      - rewrite Hpending in Hfind.
        pose proof (Hconsistent actor saved Hfind) as Hbad.
        rewrite Hinv in Hbad. dependent destruction Hbad.
      - repeat rewrite TMap.gso by exact Hneq.
        eapply Hconsistent. rewrite <- Hpending. exact Hfind.
    Qed.

    Definition RowPending (actor : tid) (m : Sig.op (li_sig F))
        (owner : tid) (op : @ESPList_op A) : assertion :=
      fun w => Active actor m w /\
        exists s, TMap.find owner (SinglePossState.σ w) =
          Some (AtomicPending s actor op).

    Definition linsert_response_addr
        (ev : @ThreadEvent (@ESPList A)) : option Addr :=
      match te_ev ev with
      | ResEv (linsert _) loc => Some loc
      | _ => None
      end.

    Lemma step_linsert_res_inv actor s (v : A) (loc : Addr) control :
      @StepSPList A actor
        (Build_ThreadEvent actor (ResEv (linsert v) loc))
        (AtomicPending s actor (linsert v)) control ->
      nodes s loc = None /\ control = Ready (insert v loc s).
    Proof.
      intro Hstep.
      remember (Build_ThreadEvent actor (ResEv (linsert v) loc))
        as ev eqn:Hev in Hstep.
      inversion Hstep.
      rewrite Hev in H0.
      pose proof (f_equal linsert_response_addr H0) as Haddr.
      simpl in Haddr. inversion Haddr; subst. auto.
    Qed.

    Lemma step_setTS_inv_shape owner actor loc ts control control' :
      @StepSPList A owner
        (Build_ThreadEvent actor (InvEv (lsetTS loc ts)))
        control control' ->
      exists s, control = Ready s /\
        control' = AtomicPending s actor (lsetTS loc ts).
    Proof.
      intro Hstep. inversion Hstep; subst; eauto.
    Qed.

    Lemma step_tryRemove_inv_shape owner actor loc control control' :
      @StepSPList A owner
        (Build_ThreadEvent actor (InvEv (ltryRemove loc)))
        control control' ->
      exists s, control = Ready s /\
        control' = AtomicPending s actor (ltryRemove loc).
    Proof.
      intro Hstep. inversion Hstep; subst; eauto.
    Qed.

    Lemma row_inv_update actor m owner op
        (Hshape : forall control control',
          @StepSPList A owner (Build_ThreadEvent actor (InvEv op))
            control control' ->
          exists s, control = Ready s /\
            control' = AtomicPending s actor op) :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor (InvEv (family_call owner op)))
        (Active actor m) (RowPending actor m owner op).
    Proof.
      intros sigma1 rho1 pi1 Hpre sigma2 Hstep.
      destruct Hpre as [HIpre Hlin]. pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea. subst sigma1 rho1.
      change (StepIndexedFamily D (@SPListIndexedObject A)
        (Build_ThreadEvent actor (InvEv (family_call owner op)))
        rows sigma2) in Hstep.
      dependent destruction Hstep. simpl in *.
      destruct (Hshape row row' H1) as (s & Erow & Erow').
      subst row row'.
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (TMap.add owner (AtomicPending s actor op) rows)
          (ArrayReady a) pi1)).
      { exists (TMap.add owner (AtomicPending s actor op) rows), a.
        simpl. split; [reflexivity|]. split; [reflexivity|]. split.
        - eapply represents_change_control; eauto.
        - split; assumption. }
      pupdate_finish. split.
      - split; [split; assumption|]. exists s. simpl. apply TMap.gss.
      - unfold source_G. repeat split; simpl; auto.
        + intros observer a0 a' E0 E' Hneq.
          assert (a0 = a) by congruence. assert (a' = a) by congruence.
          subst. reflexivity.
        + intros q s0 pending_actor op0 Hpending Hforeign.
          unfold owner0 in H0.
          destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
          * rewrite H0 in Hpending. discriminate.
          * rewrite TMap.gso by exact Hneq. exact Hpending.
        + unfold owner0 in H0.
          assert (Hrow : payload_at rows owner = Some s).
          { pose proof (payload_at_find rows owner (Ready s) H0) as Hrow.
            exact Hrow. }
          intro q. unfold row_counter_at.
          destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
          * rewrite Hrow, payload_at_add_same. simpl. lia.
          * rewrite payload_at_add_other by exact Hneq. lia.
        + intros observer a0 a' E0 E' Hneq.
          assert (a0 = a) by congruence. assert (a' = a) by congruence.
          subst. reflexivity.
    Qed.

    Lemma row_pending_entails_I actor m owner op :
      ⊨ RowPending actor m owner op ==>> source_I.
    Proof. intros w [[HI _] _]. exact HI. Qed.

    Lemma source_R_preserves_pending actor w w' owner s op :
      source_R actor w w' ->
      TMap.find owner (SinglePossState.σ w) =
        Some (AtomicPending s actor op) ->
      TMap.find owner (SinglePossState.σ w') =
        Some (AtomicPending s actor op).
    Proof.
      intros [Hother|Hadmin] Hpending.
      - destruct Hother as [other [Hneq HG]].
        destruct HG as [_ [_ [_ [_ Hlocks]]]].
        eapply Hlocks; eauto.
      - pose proof
          (AssertionsSingle.linearization_rely_observer_view actor _ _ Hadmin)
          as [Hsigma _].
        now rewrite <- Hsigma.
    Qed.

    Lemma row_pending_stable actor m owner op :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (RowPending actor m owner op).
    Proof.
      unfold AssertionsSingle.A.Stable, AssertionsSingle.A.ComposeA.
      intros w [[pre [[[HI Hlin] [s Hpending]] HR]] HI'].
      split.
      - split; [exact HI'|]. unfold ALin in *.
        rewrite <- (source_R_token actor pre w HR). exact Hlin.
      - exists s. eapply source_R_preserves_pending; eauto.
    Qed.

    Lemma insert_inv_update actor v :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor (InvEv (family_call actor (linsert v))))
        (Active actor (array_insert v))
        (RowPending actor (array_insert v) actor (linsert v)).
    Proof.
      intros σ1 ρ1 π1 Hpre σ2 Hstep.
      destruct Hpre as [HIpre Hlin].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea. subst σ1 ρ1. change (StepIndexedFamily D
        (@SPListIndexedObject A)
        (Build_ThreadEvent actor (InvEv (family_call actor (linsert v))))
        rows σ2) in Hstep.
      dependent destruction Hstep. simpl in *.
      dependent destruction H1.
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (TMap.add actor (AtomicPending s actor (linsert v)) rows)
          (ArrayReady a) π1)).
      { exists (TMap.add actor (AtomicPending s actor (linsert v)) rows), a.
        simpl. split; [reflexivity|]. split; [reflexivity|].
        split.
        - eapply represents_change_control; eauto.
        - split; assumption. }
      pupdate_finish. split.
      - split.
        + split; [exact HIpost|exact Hlin].
        + exists s. simpl. apply TMap.gss.
      - unfold source_G. repeat split; simpl; auto.
        + intros observer a0 a' E0 E' Hneq.
          assert (a0 = a) by congruence. assert (a' = a) by congruence.
          subst. reflexivity.
        + intros owner0 s0 pending_actor op Hpending Hforeign.
          unfold owner in H0.
          destruct (PositiveMap.E.eq_dec owner0 actor) as [->|Hneq].
          * rewrite H0 in Hpending. discriminate.
          * rewrite TMap.gso by exact Hneq. exact Hpending.
        + unfold owner in H0.
          assert (Hrow : payload_at rows actor = Some s).
          { pose proof (payload_at_find rows actor (Ready s) H0) as Hrow.
            exact Hrow. }
          intro q. unfold row_counter_at.
          destruct (PositiveMap.E.eq_dec q actor) as [->|Hneq].
          * rewrite Hrow, payload_at_add_same. simpl. lia.
          * rewrite payload_at_add_other by exact Hneq. lia.
        + intros observer a0 a' E0 E' Hneq.
          assert (a0 = a) by congruence. assert (a' = a) by congruence.
          subst. reflexivity.
    Qed.

    Lemma insert_res_update actor v loc :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor
          (ResEv (family_call actor (linsert v)) loc))
        (RowPending actor (array_insert v) actor (linsert v))
        (Completed actor (array_insert v) loc).
    Proof.
      intros σ1 ρ1 π1 Hpre σ2 Hstep.
      destruct Hpre as [[HIpre Hlin] [saved Hpending]].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea, Hpending. subst σ1 ρ1.
      change (StepIndexedFamily D (@SPListIndexedObject A)
        (Build_ThreadEvent actor
          (ResEv (family_call actor (linsert v)) loc)) rows σ2) in Hstep.
      dependent destruction Hstep.
      simpl in *.
      unfold owner in H0.
      rewrite Hpending in H0. inversion H0; subst row.
      destruct (step_linsert_res_inv actor saved v loc row' H1)
        as [Hnodefresh Erow']. subst row'.
      assert (Hrow : payload_at rows actor = Some saved).
      { pose proof (payload_at_find rows actor
          (AtomicPending saved actor (linsert v)) Hpending) as Hrow.
        exact Hrow. }
      assert (Hfresh : array_fresh a (pair actor loc)).
      { split.
        - pose proof (rep_node _ _ Hrep (pair actor loc)) as Hnode.
          unfold node_at in Hnode. simpl in Hnode.
          rewrite Hrow, Hnodefresh in Hnode. exact (proj1 Hnode).
        - intro Hgarbage. apply (rep_garbage _ _ Hrep (pair actor loc))
            in Hgarbage.
          unfold node_at in Hgarbage. simpl in Hgarbage.
          rewrite Hrow, Hnodefresh in Hgarbage. tauto. }
      pupdate_start.
      pupdate_forward actor (InvEv (array_insert v)).
      eapply step_insert_inv; [exact H|reflexivity].
      pupdate_forward actor (ResEv (array_insert v) loc).
      eapply step_insert_res; [exact Hfresh|reflexivity].
      pupdate_finish.
      assert (Hrep' : represents
        (TMap.add actor (Ready (insert v loc saved)) rows)
        (insert_node actor loc v a)).
      { eapply represents_insert; eauto. }
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (TMap.add actor (Ready (insert v loc saved)) rows)
          (ArrayReady (insert_node actor loc v a))
          (TMap.add actor (ls_linr (array_insert v) loc)
            (TMap.add actor (ls_lini (array_insert v)) π1)))).
      { exists (TMap.add actor (Ready (insert v loc saved)) rows),
          (insert_node actor loc v a). simpl.
        split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrep'|].
        split.
        - eapply scan_token_atomic; eauto.
        - eapply counter_token_atomic; eauto. }
      split.
      - split; [exact HIpost|]. unfold ALin. simpl. rewrite TMap.gss.
        reflexivity.
      - unfold source_G. repeat split; simpl; auto.
        + intros observer Hneq. repeat rewrite TMap.gso by exact Hneq.
          reflexivity.
        + intros observer a0 a' E0 E' Hneq.
          unfold owner in E'.
          assert (a0 = a) by congruence.
          assert (a' = insert_node actor loc v a) by congruence.
          subst. reflexivity.
        + intros owner0 s0 pending_actor op Hlock Hforeign.
          destruct (PositiveMap.E.eq_dec owner0 actor) as [->|Hneq].
          * rewrite Hpending in Hlock. inversion Hlock. congruence.
          * rewrite TMap.gso by exact Hneq. exact Hlock.
        + assert (Hrow0 : payload_at rows actor = Some saved).
          { pose proof (payload_at_find rows actor
              (AtomicPending saved actor (linsert v)) Hpending) as Hrow0.
            exact Hrow0. }
          intro q. unfold row_counter_at.
          destruct (PositiveMap.E.eq_dec q actor) as [->|Hneq].
          * rewrite Hrow0, payload_at_add_same. simpl. lia.
          * rewrite payload_at_add_other by exact Hneq. lia.
        + intros observer a0 a' E0 E' Hneq.
          unfold owner in E'.
          assert (a0 = a) by congruence.
          assert (a' = insert_node actor loc v a) by congruence.
          subst. reflexivity.
    Qed.

    Lemma setTS_inv_update actor loc ts :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor
          (InvEv (family_call actor (lsetTS loc ts))))
        (Active actor (array_setTS loc ts))
        (RowPending actor (array_setTS loc ts) actor (lsetTS loc ts)).
    Proof.
      eapply row_inv_update.
      intros control control' Hstep.
      eapply step_setTS_inv_shape; exact Hstep.
    Qed.

    Lemma tryRemove_inv_update actor owner loc :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor
          (InvEv (family_call owner (ltryRemove loc))))
        (Active actor (array_tryRemove owner loc))
        (RowPending actor (array_tryRemove owner loc) owner
          (ltryRemove loc)).
    Proof.
      eapply row_inv_update.
      intros control control' Hstep.
      eapply step_tryRemove_inv_shape; exact Hstep.
    Qed.

    Definition ContainsActive actor m : assertion :=
      fun w => Active actor m w /\ ThreadDomain.contains D actor.

    Lemma contains_active_entails_I actor m :
      ⊨ ContainsActive actor m ==>> source_I.
    Proof. intros w [[HI _] _]. exact HI. Qed.

    Lemma contains_active_stable actor m :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (ContainsActive actor m).
    Proof.
      unfold AssertionsSingle.A.Stable, AssertionsSingle.A.ComposeA.
      intros w [[pre [[[HI Hlin] Hcontains] HR]] HI'].
      split.
      - split; [exact HI'|]. unfold ALin in *.
        rewrite <- (source_R_token actor pre w HR). exact Hlin.
      - exact Hcontains.
    Qed.

    Lemma reset_update actor :
      AssertionsSingle.PUpdateId (source_G actor)
        (ContainsActive actor array_resetIter)
        (Completed actor array_resetIter tt).
    Proof.
      intros sigma rho pi Hpre.
      destruct Hpre as [[HIpre Hlin] Hcontains].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea. subst sigma rho.
      assert (Hidle : scan_idle a actor).
      { intros p Hfind. destruct (scan_current p) as [c|] eqn:Hcurrent;
          [|reflexivity].
        exfalso. pose proof (Hscan actor p c Hfind Hcurrent) as Hbad.
        unfold ALin in Hlin. rewrite Hlin in Hbad. dependent destruction Hbad. }
      pupdate_start.
      pupdate_forward actor (InvEv (@array_resetIter A)).
      eapply step_reset_inv; [exact Hcontains|reflexivity].
      pupdate_forward actor (ResEv (@array_resetIter A) tt).
      pupdate_finish.
      assert (Hrep' : represents rows (reset_scan actor a)).
      { eapply represents_reset_scan; eauto. }
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          rows (ArrayReady (reset_scan actor a))
          (TMap.add actor (ls_linr array_resetIter tt)
            (TMap.add actor (ls_lini array_resetIter) pi)))).
      { exists rows, (reset_scan actor a). simpl.
        split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrep'|].
        split.
        - intros caller p c Hfind Hcurrent.
          destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
          + unfold reset_scan in Hfind. cbn in Hfind.
            rewrite TMap.gss in Hfind. inversion Hfind; subst p.
            discriminate Hcurrent.
          + repeat rewrite TMap.gso by exact Hneq.
            eapply Hscan; [|exact Hcurrent].
            unfold reset_scan in Hfind. cbn in Hfind.
            rewrite TMap.gso in Hfind by exact Hneq. exact Hfind.
        - eapply counter_token_atomic; eauto. }
      split.
      - split; [exact HIpost|]. unfold ALin. simpl. rewrite TMap.gss.
        reflexivity.
      - unfold source_G. repeat split; simpl; auto.
        + intros observer Hneq. repeat rewrite TMap.gso by exact Hneq.
          reflexivity.
        + intros observer a0 a' E0 E' Hneq.
          assert (a0 = a) by congruence.
          assert (a' = reset_scan actor a) by congruence. subst.
          unfold reset_scan. cbn. rewrite TMap.gso by exact Hneq.
          reflexivity.
        + intros observer a0 a' E0 E' Hneq.
          assert (a0 = a) by congruence.
          assert (a' = reset_scan actor a) by congruence. subst.
          unfold reset_scan. cbn. reflexivity.
    Qed.

    Lemma active_contains_or_error actor m w :
      Active actor m w ->
      ContainsActive actor m w \/ AssertionsSingle.APError w.
    Proof.
      intros Hactive. destruct (ThreadDomain.contains_dec D actor)
        as [Hcontains|Houtside].
      - left. split; assumption.
      - right. destruct Hactive as [HI Hlin].
        destruct HI as
          (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
        unfold AssertionsSingle.APError. apply rt_step. econstructor.
        + rewrite Ea. constructor. exact Houtside.
        + exact Hlin.
    Qed.

    Lemma lift_active_contains_or_error actor m :
      forall s, SActive actor m s ->
        lift_assert (ContainsActive actor m) s \/ AssertionsSet.APError s.
    Proof.
      intros s [w [Hview Hactive]].
      destruct (active_contains_or_error actor m w Hactive)
        as [Hcontains|Herror].
      - left. exists w. auto.
      - right. econstructor.
        + eapply singleton_view_member; eauto.
        + exact Herror.
    Qed.

    Lemma reset_method_triple actor :
      SetLogic.HTripleProvable (R actor) (G actor) SI actor
        (SActive actor array_resetIter)
        (resetIter_impl D actor)
        (fun ret => SCompleted actor array_resetIter ret).
    Proof.
      eapply SetLogic.provable_perror with
        (P' := lift_assert (ContainsActive actor array_resetIter)).
      - intros s Hactive. eapply lift_active_contains_or_error; eauto.
      - unfold resetIter_impl.
        eapply singleton_provable_linstep with
          (P' := Completed actor array_resetIter tt).
        + apply completed_entails_I.
        + apply completed_stable.
        + apply reset_update.
        + eapply singleton_provable_ret_safe.
          * apply ImplRefl.
          * apply completed_entails_I.
          * apply completed_stable.
    Qed.

    Definition SafeActive actor m (nested : Sig.op (li_sig E)) : assertion :=
      fun w => Active actor m w /\
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent actor (InvEv nested)) w.

    Definition splist_event_kind (ev : @ThreadEvent (@ESPList A)) : nat :=
      match ev with
      | Build_ThreadEvent _ (InvEv (linsert _)) => 0
      | Build_ThreadEvent _ (InvEv (lsetTS _ _)) => 1
      | Build_ThreadEvent _ (InvEv lgetTop) => 2
      | Build_ThreadEvent _ (InvEv lgetCounter) => 3
      | Build_ThreadEvent _ (InvEv (ltryRemove _)) => 4
      | Build_ThreadEvent _ (ResEv _ _) => 5
      end.

    Lemma safe_active_entails_I actor m nested :
      ⊨ SafeActive actor m nested ==>> source_I.
    Proof. intros w [[HI _] _]. exact HI. Qed.

    Lemma insert_safe_or_error actor v w :
      Active actor (array_insert v) w ->
      SafeActive actor (array_insert v)
        (family_call actor (linsert v)) w \/
      AssertionsSingle.APError w.
    Proof.
      intros Hactive.
      destruct (classic (Error (li_lts E)
        (Build_ThreadEvent actor
          (InvEv (family_call actor (linsert v))))
        (SinglePossState.σ w))) as [Herror|Hsafe].
      - right. destruct Hactive as [HI Hlin].
        destruct HI as
          (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
        change (ErrorIndexedFamily D (@SPListIndexedObject A)
          (Build_ThreadEvent actor
            (InvEv (family_call actor (linsert v))))
          (SinglePossState.σ w)) in Herror.
        rewrite Erows in Herror.
        inversion Herror; subst; simpl in *.
        + inversion H1; subst.
          all: pose proof (f_equal splist_event_kind H3) as Hkind;
            simpl in Hkind; try discriminate.
          pose proof (f_equal (@te_tid (@ESPList A)) H3) as Htid.
          simpl in Htid. unfold owner in H2. congruence.
        + unfold AssertionsSingle.APError. apply rt_step. econstructor.
          * rewrite Ea. eapply error_actor_outside. exact H3.
          * exact Hlin.
        + exfalso.
          destruct (proj2 (rep_domain _ _ Hrep actor) H3) as [row Hrow].
          change (option_map row_payload (TMap.find actor
            (SinglePossState.σ w)) = Some row) in Hrow.
          pose proof (f_equal (option_map row_payload) H4) as Hnone.
          simpl in Hnone.
          pose proof (eq_trans (eq_sym Hrow) Hnone) as Hcontra.
          discriminate Hcontra.
      - left. split; assumption.
    Qed.

    Lemma lift_insert_safe_or_error actor v :
      forall s, SActive actor (array_insert v) s ->
        lift_assert (SafeActive actor (array_insert v)
          (family_call actor (linsert v))) s \/ AssertionsSet.APError s.
    Proof.
      intros s [w [Hview Hactive]].
      destruct (insert_safe_or_error actor v w Hactive) as [Hsafe|Herror].
      - left. exists w. auto.
      - right. econstructor.
        + eapply singleton_view_member; eauto.
        + exact Herror.
    Qed.

    Lemma insert_inv_update_safe actor v :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor (InvEv (family_call actor (linsert v))))
        (SafeActive actor (array_insert v)
          (family_call actor (linsert v)))
        (RowPending actor (array_insert v) actor (linsert v)).
    Proof.
      intros sigma rho pi [Hactive _].
      eapply insert_inv_update. exact Hactive.
    Qed.

    Lemma insert_method_triple actor v :
      SetLogic.HTripleProvable (R actor) (G actor) SI actor
        (SActive actor (array_insert v))
        (insert_impl D v actor)
        (fun ret => SCompleted actor (array_insert v) ret).
    Proof.
      eapply SetLogic.provable_perror with
        (P' := lift_assert (SafeActive actor (array_insert v)
          (family_call actor (linsert v)))).
      - intros s Hactive. eapply lift_insert_safe_or_error; eauto.
      - unfold insert_impl.
        eapply singleton_provable_vis_safe with
          (P' := RowPending actor (array_insert v) actor (linsert v))
          (Q' := fun loc => Completed actor (array_insert v) loc).
        + intros w [_ Hsafe]. exact Hsafe.
        + apply row_pending_entails_I.
        + intros. apply completed_entails_I.
        + apply row_pending_stable.
        + intros. apply completed_stable.
        + apply insert_inv_update_safe.
        + intros. apply insert_res_update.
        + intros loc. eapply singleton_provable_ret_safe.
          * apply ImplRefl.
          * apply completed_entails_I.
          * apply completed_stable.
    Qed.

    Definition DefinedPending actor m owner op loc : assertion :=
      fun w => RowPending actor m owner op w /\
        exists s value ts,
          TMap.find owner (SinglePossState.σ w) =
            Some (AtomicPending s actor op) /\
          nodes s loc = Some (pair value ts).

    Lemma defined_pending_entails_I actor m owner op loc :
      ⊨ DefinedPending actor m owner op loc ==>> source_I.
    Proof. intros w [[[HI _] _] _]. exact HI. Qed.

    Lemma defined_pending_stable actor m owner op loc :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (DefinedPending actor m owner op loc).
    Proof.
      unfold AssertionsSingle.A.Stable, AssertionsSingle.A.ComposeA.
      intros w [[pre [[Hrowpending
        [s [value [ts [Hpending Hnode]]]]] HR]] HI'].
      split.
      - unfold RowPending in *. destruct Hrowpending as [[HI Hlin] Hsaved].
        split.
        + split; [exact HI'|]. unfold ALin in *.
          rewrite <- (source_R_token actor pre w HR). exact Hlin.
        + destruct Hsaved as [saved Hsaved]. exists saved.
          eapply source_R_preserves_pending; eauto.
      - exists s, value, ts. split; [|exact Hnode].
        eapply source_R_preserves_pending; eauto.
    Qed.

    Definition setTS_response_args
        (ev : @ThreadEvent (@ESPList A)) : option (Addr * TS) :=
      match te_ev ev with
      | InvEv (lsetTS loc ts) => Some (pair loc ts)
      | ResEv (lsetTS loc ts) _ => Some (pair loc ts)
      | _ => None
      end.

    Lemma option_eq_some_not_none {X} (f : option X) x :
      f = Some x -> f <> None.
    Proof. intros ->. discriminate. Qed.

    Lemma step_setTS_res_inv actor s loc ts control :
      @StepSPList A actor
        (Build_ThreadEvent actor (ResEv (lsetTS loc ts) tt))
        (AtomicPending s actor (lsetTS loc ts)) control ->
      control = Ready (setTS loc ts s).
    Proof.
      intro Hstep.
      remember (Build_ThreadEvent actor (ResEv (lsetTS loc ts) tt))
        as ev eqn:Hev in Hstep.
      inversion Hstep.
      reflexivity.
    Qed.

    Lemma setTS_inv_defined_update actor loc ts :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor
          (InvEv (family_call actor (lsetTS loc ts))))
        (SafeActive actor (array_setTS loc ts)
          (family_call actor (lsetTS loc ts)))
        (DefinedPending actor (array_setTS loc ts) actor
          (lsetTS loc ts) loc).
    Proof.
      intros sigma1 rho1 pi1 [[HIpre Hlin] Hsafe] sigma2 Hstep.
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea. subst sigma1 rho1.
      change (StepIndexedFamily D (@SPListIndexedObject A)
        (Build_ThreadEvent actor
          (InvEv (family_call actor (lsetTS loc ts))))
        rows sigma2) in Hstep.
      dependent destruction Hstep. simpl in *.
      destruct (step_setTS_inv_shape actor actor loc ts row row' H1)
        as (s & Erow & Erow'). subst row row'.
      assert (Hnode : exists value oldts,
        nodes s loc = Some (pair value oldts)).
      { destruct (nodes s loc) as [[value oldts]|] eqn:Hfind.
        - eauto.
        - exfalso. apply Hsafe.
          change (ErrorIndexedFamily D (@SPListIndexedObject A)
            (Build_ThreadEvent actor
              (InvEv (family_call actor (lsetTS loc ts)))) rows).
          econstructor.
          + exact H.
          + exact H0.
          + change (@ErrorSPList A actor
              (Build_ThreadEvent actor (InvEv (lsetTS loc ts))) (Ready s)).
            eapply SPListSpec.error_setTS_undefined.
            * exact Hfind.
            * reflexivity. }
      destruct Hnode as (value & oldts & Hnode).
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (TMap.add actor (AtomicPending s actor (lsetTS loc ts)) rows)
          (ArrayReady a) pi1)).
      { exists (TMap.add actor (AtomicPending s actor (lsetTS loc ts)) rows), a.
        simpl. split; [reflexivity|]. split; [reflexivity|]. split.
        - eapply represents_change_control; eauto.
        - split; assumption. }
      pupdate_finish. split.
      - split.
        + split; [split; assumption|]. exists s. simpl. apply TMap.gss.
        + exists s, value, oldts. split; [simpl; apply TMap.gss|exact Hnode].
      - unfold source_G. repeat split; simpl; auto.
        + intros observer a0 a' E0 E' Hneq.
          assert (a0 = a) by congruence. assert (a' = a) by congruence.
          subst. reflexivity.
        + intros q s0 pending_actor op0 Hpending Hforeign.
          unfold owner in H0.
          destruct (PositiveMap.E.eq_dec q actor) as [->|Hneq].
          * rewrite H0 in Hpending. discriminate.
          * rewrite TMap.gso by exact Hneq. exact Hpending.
        + unfold owner in H0.
          assert (Hrow0 : payload_at rows actor = Some s).
          { pose proof (payload_at_find rows actor (Ready s) H0) as Hrow0.
            exact Hrow0. }
          intro q. unfold row_counter_at.
          destruct (PositiveMap.E.eq_dec q actor) as [->|Hneq].
          * rewrite Hrow0, payload_at_add_same. simpl. lia.
          * rewrite payload_at_add_other by exact Hneq. lia.
        + intros observer a0 a' E0 E' Hneq.
          assert (a0 = a) by congruence. assert (a' = a) by congruence.
          subst. reflexivity.
    Qed.

    Lemma setTS_res_update actor loc ts :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor
          (ResEv (family_call actor (lsetTS loc ts)) tt))
        (DefinedPending actor (array_setTS loc ts) actor
          (lsetTS loc ts) loc)
        (Completed actor (array_setTS loc ts) tt).
    Proof.
      intros sigma1 rho1 pi1 Hpre sigma2 Hstep.
      destruct Hpre as
        [[[HIpre Hlin] [saved0 Hpending0]]
          [saved [value [oldts [Hpending Hnode]]]]].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea, Hpending0, Hpending. subst sigma1 rho1.
      change (StepIndexedFamily D (@SPListIndexedObject A)
        (Build_ThreadEvent actor
          (ResEv (family_call actor (lsetTS loc ts)) tt))
        rows sigma2) in Hstep.
      dependent destruction Hstep. simpl in *.
      unfold owner in H0. rewrite Hpending in H0.
      inversion H0; subst row.
      pose proof (step_setTS_res_inv actor saved loc ts row' H1) as Erow'.
      subst row'.
      assert (Hrow : payload_at rows actor = Some saved).
      { pose proof (payload_at_find rows actor
          (AtomicPending saved actor (lsetTS loc ts)) Hpending) as Hrow.
        exact Hrow. }
      assert (Hvertex : array_vertex a (pair actor loc)).
      { unfold array_vertex.
        pose proof (rep_node _ _ Hrep (pair actor loc)) as Hlookup.
        unfold node_at in Hlookup. simpl in Hlookup.
        rewrite Hrow, Hnode in Hlookup. destruct Hlookup as [Hv _].
        rewrite Hv. discriminate. }
      exists (ArrayReady (set_node_timestamp actor loc ts a)).
      exists (TMap.add actor (ls_linr (array_setTS loc ts) tt)
        (TMap.add actor (ls_lini (array_setTS loc ts)) pi1)).
      split.
      - eapply rt_trans.
        + apply rt_step. eapply ps_inv.
          * eapply step_setTS_inv; [exact H|exact Hvertex|reflexivity].
          * exact Hlin.
        + apply rt_step. eapply ps_ret.
          * eapply step_setTS_res. reflexivity.
          * apply TMap.gss.
      - pose proof (represents_setTS rows a actor saved loc ts Hrow
          (option_eq_some_not_none (nodes saved loc) (pair value oldts) Hnode)
          Hrep) as Hrep'.
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (TMap.add actor (Ready (setTS loc ts saved)) rows)
          (ArrayReady (set_node_timestamp actor loc ts a))
          (TMap.add actor (ls_linr (array_setTS loc ts) tt)
            (TMap.add actor (ls_lini (array_setTS loc ts)) pi1)))).
      { exists (TMap.add actor (Ready (setTS loc ts saved)) rows),
          (set_node_timestamp actor loc ts a). simpl.
        split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrep'|].
        split.
        - eapply scan_token_atomic; eauto.
        - eapply counter_token_atomic; eauto. }
      split.
      + split; [exact HIpost|]. unfold ALin. simpl. rewrite TMap.gss.
        reflexivity.
      + unfold source_G. repeat split; simpl; auto.
        * intros observer Hneq. repeat rewrite TMap.gso by exact Hneq.
          reflexivity.
        * intros observer a0 a' E0 E' Hneq.
          unfold owner in E'.
          assert (a0 = a) by congruence.
          assert (a' = set_node_timestamp actor loc ts a) by congruence.
          subst. reflexivity.
        * intros q s0 pending_actor op0 Hlock Hforeign.
          destruct (PositiveMap.E.eq_dec q actor) as [->|Hneq].
          -- rewrite Hpending in Hlock. inversion Hlock. congruence.
          -- rewrite TMap.gso by exact Hneq. exact Hlock.
        * assert (Hrow0 : payload_at rows actor = Some saved).
          { pose proof (payload_at_find rows actor
              (AtomicPending saved actor (lsetTS loc ts)) Hpending) as Hrow0.
            exact Hrow0. }
          intro q. unfold row_counter_at.
          destruct (PositiveMap.E.eq_dec q actor) as [->|Hneq].
          -- rewrite Hrow0, payload_at_add_same. simpl.
             rewrite counter_setTS. lia.
          -- rewrite payload_at_add_other by exact Hneq. lia.
        * intros observer a0 a' E0 E' Hneq.
          unfold owner in E'.
          assert (a0 = a) by congruence.
          assert (a' = set_node_timestamp actor loc ts a) by congruence.
          subst. reflexivity.
    Qed.

    Lemma setTS_safe_or_error actor loc ts w :
      Active actor (array_setTS loc ts) w ->
      SafeActive actor (array_setTS loc ts)
        (family_call actor (lsetTS loc ts)) w \/
      AssertionsSingle.APError w.
    Proof.
      intros Hactive. destruct Hactive as [HI Hlin].
      pose proof HI as HI0.
      destruct HI as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      destruct (ThreadDomain.contains_dec D actor) as [Hcontains|Houtside].
      - destruct (classic (array_vertex a (pair actor loc)))
          as [Hvertex|Hundefined].
        + left. split; [split; assumption|]. intro Herror.
          change (ErrorIndexedFamily D (@SPListIndexedObject A)
            (Build_ThreadEvent actor
              (InvEv (family_call actor (lsetTS loc ts))))
            (SinglePossState.σ w)) in Herror.
          rewrite Erows in Herror. inversion Herror; subst; simpl in *.
          * inversion H1; subst.
            all: pose proof (f_equal splist_event_kind H3) as Hkind;
              simpl in Hkind; try discriminate.
            -- pose proof (f_equal (@te_tid (@ESPList A)) H3) as Htid.
               simpl in Htid. unfold owner in H2. congruence.
            -- unfold array_vertex in Hvertex.
               pose proof (f_equal setTS_response_args H3) as Hargs.
               simpl in Hargs. inversion Hargs; subst l ts0.
               unfold owner in H0.
               assert (Hrow : payload_at (SinglePossState.σ w) actor = Some s).
               { pose proof (payload_at_find (SinglePossState.σ w) actor
                   (Ready s) H0) as Hrow. exact Hrow. }
               pose proof (represents_node_none
                 (SinglePossState.σ w) a actor s loc Hrep Hrow H2)
                 as [Hvalue _].
               rewrite Hvalue in Hvertex. contradiction.
          * contradiction.
          * destruct (proj2 (rep_domain _ _ Hrep actor) Hcontains)
              as [row Hrow].
            change (option_map row_payload
              (TMap.find actor (SinglePossState.σ w)) = Some row) in Hrow.
            pose proof (f_equal (option_map row_payload) H4) as Hnone.
            simpl in Hnone.
            pose proof (eq_trans (eq_sym Hrow) Hnone) as Hcontra.
            discriminate Hcontra.
        + right. unfold AssertionsSingle.APError. apply rt_step. econstructor.
          * rewrite Ea. eapply error_setTS_undefined. exact Hundefined.
          * exact Hlin.
      - right. unfold AssertionsSingle.APError. apply rt_step. econstructor.
        + rewrite Ea. eapply error_actor_outside. exact Houtside.
        + exact Hlin.
    Qed.

    Lemma lift_setTS_safe_or_error actor loc ts :
      forall s, SActive actor (array_setTS loc ts) s ->
        lift_assert (SafeActive actor (array_setTS loc ts)
          (family_call actor (lsetTS loc ts))) s \/ AssertionsSet.APError s.
    Proof.
      intros s [w [Hview Hactive]].
      destruct (setTS_safe_or_error actor loc ts w Hactive)
        as [Hsafe|Herror].
      - left. exists w. auto.
      - right. econstructor.
        + eapply singleton_view_member; eauto.
        + exact Herror.
    Qed.

    Lemma setTS_method_triple actor loc ts :
      SetLogic.HTripleProvable (R actor) (G actor) SI actor
        (SActive actor (array_setTS loc ts))
        (setTS_impl D loc ts actor)
        (fun ret => SCompleted actor (array_setTS loc ts) ret).
    Proof.
      eapply SetLogic.provable_perror with
        (P' := lift_assert (SafeActive actor (array_setTS loc ts)
          (family_call actor (lsetTS loc ts)))).
      - intros s Hactive. eapply lift_setTS_safe_or_error; eauto.
      - unfold setTS_impl.
        eapply singleton_provable_vis_safe with
          (P' := DefinedPending actor (array_setTS loc ts) actor
            (lsetTS loc ts) loc)
          (Q' := fun _ => Completed actor (array_setTS loc ts) tt).
        + intros w [_ Hsafe]. exact Hsafe.
        + apply defined_pending_entails_I.
        + intros. apply completed_entails_I.
        + apply defined_pending_stable.
        + intros. apply completed_stable.
        + apply setTS_inv_defined_update.
        + intros []. apply setTS_res_update.
        + intros []. eapply singleton_provable_ret_safe.
          * apply ImplRefl.
          * apply completed_entails_I.
          * apply completed_stable.
    Qed.

    Lemma step_tryRemove_inv_defined owner actor loc control control' :
      @StepSPList A owner
        (Build_ThreadEvent actor (InvEv (ltryRemove loc)))
        control control' ->
      exists s value ts,
        control = Ready s /\
        control' = AtomicPending s actor (ltryRemove loc) /\
        nodes s loc = Some (pair value ts).
    Proof.
      intro Hstep. inversion Hstep; subst.
      destruct (nodes s loc) as [[value ts]|] eqn:Hnode; [|contradiction].
      exists s, value, ts. auto.
    Qed.

    Definition TryRemovePending actor owner loc : assertion :=
      fun w => DefinedPending actor (array_tryRemove owner loc) owner
        (ltryRemove loc) loc w /\ ThreadDomain.contains D actor.

    Lemma tryRemove_pending_entails_I actor owner loc :
      ⊨ TryRemovePending actor owner loc ==>> source_I.
    Proof. intros w [Hdefined _]. eapply defined_pending_entails_I; eauto. Qed.

    Lemma tryRemove_pending_stable actor owner loc :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (TryRemovePending actor owner loc).
    Proof.
      unfold AssertionsSingle.A.Stable, AssertionsSingle.A.ComposeA.
      intros w [[pre [[Hdefined Hcontains] HR]] HI'].
      split; [|exact Hcontains].
      eapply defined_pending_stable.
      split; [exists pre; split; assumption|exact HI'].
    Qed.

    Lemma tryRemove_inv_defined_update actor owner loc :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor
          (InvEv (family_call owner (ltryRemove loc))))
        (ContainsActive actor (array_tryRemove owner loc))
        (TryRemovePending actor owner loc).
    Proof.
      intros sigma1 rho1 pi1 [[HIpre Hlin] Hactor] sigma2 Hstep.
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea. subst sigma1 rho1.
      change (StepIndexedFamily D (@SPListIndexedObject A)
        (Build_ThreadEvent actor
          (InvEv (family_call owner (ltryRemove loc))))
        rows sigma2) in Hstep.
      dependent destruction Hstep. simpl in *.
      unfold owner0 in *.
      destruct (step_tryRemove_inv_defined owner actor loc row row' H1)
        as (s & value & ts & Erow & Erow' & Hnode).
      subst row row'.
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (TMap.add owner (AtomicPending s actor (ltryRemove loc)) rows)
          (ArrayReady a) pi1)).
      { exists (TMap.add owner (AtomicPending s actor (ltryRemove loc)) rows), a.
        simpl. split; [reflexivity|]. split; [reflexivity|]. split.
        - eapply represents_change_control; eauto.
        - split; assumption. }
      pupdate_finish. split.
      - split; [|exact Hactor]. split.
        + split; [split; assumption|]. exists s. simpl. apply TMap.gss.
        + exists s, value, ts. split; [simpl; apply TMap.gss|exact Hnode].
      - unfold source_G. repeat split; simpl; auto.
        + intros observer a0 a' E0 E' Hneq.
          assert (a0 = a) by congruence. assert (a' = a) by congruence.
          subst. reflexivity.
        + intros q s0 pending_actor op0 Hpending Hforeign.
          destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
          * rewrite H0 in Hpending. discriminate.
          * rewrite TMap.gso by exact Hneq. exact Hpending.
        + assert (Hrow0 : payload_at rows owner = Some s).
          { pose proof (payload_at_find rows owner (Ready s) H0) as Hrow0.
            exact Hrow0. }
          intro q. unfold row_counter_at.
          destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
          * rewrite Hrow0, payload_at_add_same. simpl. lia.
          * rewrite payload_at_add_other by exact Hneq. lia.
        + intros observer a0 a' E0 E' Hneq.
          assert (a0 = a) by congruence. assert (a' = a) by congruence.
          subst. reflexivity.
    Qed.

    Definition tryRemove_response_info
        (ev : @ThreadEvent (@ESPList A)) : option (Addr * bool) :=
      match te_ev ev with
      | ResEv (ltryRemove loc) removed => Some (pair loc removed)
      | _ => None
      end.

    Lemma step_tryRemove_true_inv owner actor s loc control :
      @StepSPList A owner
        (Build_ThreadEvent actor (ResEv (ltryRemove loc) true))
        (AtomicPending s actor (ltryRemove loc)) control ->
      In loc (order s) /\ control = Ready (remove loc s).
    Proof.
      intro Hstep.
      remember (Build_ThreadEvent actor (ResEv (ltryRemove loc) true))
        as ev eqn:Hev in Hstep.
      inversion Hstep.
      - auto.
      - rewrite Hev in H1.
        pose proof (f_equal tryRemove_response_info H1) as Hinfo.
        simpl in Hinfo. discriminate.
    Qed.

    Lemma step_tryRemove_false_inv owner actor s loc control :
      @StepSPList A owner
        (Build_ThreadEvent actor (ResEv (ltryRemove loc) false))
        (AtomicPending s actor (ltryRemove loc)) control ->
      ~ In loc (order s) /\ control = Ready s.
    Proof.
      intro Hstep.
      remember (Build_ThreadEvent actor (ResEv (ltryRemove loc) false))
        as ev eqn:Hev in Hstep.
      inversion Hstep.
      - rewrite Hev in H1.
        pose proof (f_equal tryRemove_response_info H1) as Hinfo.
        simpl in Hinfo. discriminate.
      - auto.
    Qed.

    Lemma tryRemove_true_res_update actor owner loc :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor
          (ResEv (family_call owner (ltryRemove loc)) true))
        (TryRemovePending actor owner loc)
        (Completed actor (array_tryRemove owner loc) true).
    Proof.
      intros sigma1 rho1 pi1 Hpre sigma2 Hstep.
      destruct Hpre as
        [[[[HIpre Hlin] [saved0 Hpending0]]
          [saved [value [ts [Hpending Hnode]]]]] Hactor].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea, Hpending0, Hpending. subst sigma1 rho1.
      change (StepIndexedFamily D (@SPListIndexedObject A)
        (Build_ThreadEvent actor
          (ResEv (family_call owner (ltryRemove loc)) true))
        rows sigma2) in Hstep.
      dependent destruction Hstep. simpl in *. unfold owner0 in *.
      rewrite Hpending in H0. inversion H0; subst row.
      destruct (step_tryRemove_true_inv owner actor saved loc row' H1)
        as [Hin Erow']. subst row'.
      assert (Hrow : payload_at rows owner = Some saved).
      { pose proof (payload_at_find rows owner
          (AtomicPending saved actor (ltryRemove loc)) Hpending) as Hrow.
        exact Hrow. }
      pose proof (proj2 (represents_live rows a owner saved loc Hrep Hrow) Hin)
        as Hlive.
      exists (ArrayReady (remove_node (pair owner loc) a)).
      exists (TMap.add actor (ls_linr (array_tryRemove owner loc) true)
        (TMap.add actor (ls_lini (array_tryRemove owner loc)) pi1)).
      split.
      - eapply rt_trans.
        + apply rt_step. eapply ps_inv.
          * eapply step_tryRemove_inv;
              [exact Hactor|exact H|exact (proj1 Hlive)|reflexivity].
          * exact Hlin.
        + apply rt_step. eapply ps_ret.
          * eapply step_tryRemove_succ; [exact Hlive|reflexivity].
          * apply TMap.gss.
      - pose proof (represents_remove rows a owner saved loc Hrow
          (option_eq_some_not_none (nodes saved loc) (pair value ts) Hnode)
          Hrep) as Hrep'.
        assert (HIpost : source_I
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (TMap.add owner (Ready (remove loc saved)) rows)
            (ArrayReady (remove_node (pair owner loc) a))
            (TMap.add actor (ls_linr (array_tryRemove owner loc) true)
              (TMap.add actor (ls_lini (array_tryRemove owner loc)) pi1)))).
        { exists (TMap.add owner (Ready (remove loc saved)) rows),
            (remove_node (pair owner loc) a). simpl.
          split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrep'|].
          split.
          - eapply scan_token_atomic; eauto.
          - eapply counter_token_atomic; eauto. }
        split.
        + split; [exact HIpost|]. unfold ALin. simpl. rewrite TMap.gss.
          reflexivity.
        + unfold source_G. repeat split; simpl; auto.
          * intros observer Hneq. repeat rewrite TMap.gso by exact Hneq.
            reflexivity.
          * intros observer a0 a' E0 E' Hneq.
            assert (a0 = a) by congruence.
            assert (a' = remove_node (pair owner loc) a) by congruence.
            subst. reflexivity.
          * intros q s0 pending_actor op0 Hlock Hforeign.
            destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
            -- rewrite Hpending in Hlock. inversion Hlock. congruence.
            -- rewrite TMap.gso by exact Hneq. exact Hlock.
          * assert (Hrow0 : payload_at rows owner = Some saved).
            { pose proof (payload_at_find rows owner
                (AtomicPending saved actor (ltryRemove loc)) Hpending) as Hrow0.
              exact Hrow0. }
            intro q. unfold row_counter_at.
            destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
            -- rewrite Hrow0, payload_at_add_same. simpl.
               unfold remove. cbn. lia.
            -- rewrite payload_at_add_other by exact Hneq. lia.
          * intros observer a0 a' E0 E' Hneq.
            assert (a0 = a) by congruence.
            assert (a' = remove_node (pair owner loc) a) by congruence.
            subst. reflexivity.
    Qed.

    Lemma tryRemove_false_res_update actor owner loc :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor
          (ResEv (family_call owner (ltryRemove loc)) false))
        (TryRemovePending actor owner loc)
        (Completed actor (array_tryRemove owner loc) false).
    Proof.
      intros sigma1 rho1 pi1 Hpre sigma2 Hstep.
      destruct Hpre as
        [[[[HIpre Hlin] [saved0 Hpending0]]
          [saved [value [ts [Hpending Hnode]]]]] Hactor].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea, Hpending0, Hpending. subst sigma1 rho1.
      change (StepIndexedFamily D (@SPListIndexedObject A)
        (Build_ThreadEvent actor
          (ResEv (family_call owner (ltryRemove loc)) false))
        rows sigma2) in Hstep.
      dependent destruction Hstep. simpl in *. unfold owner0 in *.
      rewrite Hpending in H0. inversion H0; subst row.
      destruct (step_tryRemove_false_inv owner actor saved loc row' H1)
        as [Hnotin Erow']. subst row'.
      assert (Hrow : payload_at rows owner = Some saved).
      { pose proof (payload_at_find rows owner
          (AtomicPending saved actor (ltryRemove loc)) Hpending) as Hrow.
        exact Hrow. }
      assert (Hgarbage : as_garbage a (pair owner loc)).
      { apply (proj2 (rep_garbage _ _ Hrep (pair owner loc))).
        split.
        - unfold node_at. simpl. rewrite Hrow, Hnode. discriminate.
        - simpl. unfold row_order_at.
          destruct (payload_at rows owner) as [found|] eqn:Epayload.
          + inversion Hrow; subst found. exact Hnotin.
          + discriminate Hrow. }
      exists (ArrayReady a).
      exists (TMap.add actor (ls_linr (array_tryRemove owner loc) false)
        (TMap.add actor (ls_lini (array_tryRemove owner loc)) pi1)).
      split.
      - eapply rt_trans.
        + apply rt_step. eapply ps_inv.
          * eapply step_tryRemove_inv;
              [exact Hactor|exact H|unfold array_vertex;
                pose proof (represents_node_some rows a owner saved loc value ts
                  Hrep Hrow Hnode) as [Hv _]; rewrite Hv; discriminate
              |reflexivity].
          * exact Hlin.
        + apply rt_step. eapply ps_ret.
          * eapply step_tryRemove_fail; [exact Hgarbage|reflexivity].
          * apply TMap.gss.
      - pose proof (represents_change_control rows a owner
          (AtomicPending saved actor (ltryRemove loc)) (Ready saved)
          Hpending eq_refl Hrep) as Hrep'.
        assert (HIpost : source_I
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (TMap.add owner (Ready saved) rows) (ArrayReady a)
            (TMap.add actor (ls_linr (array_tryRemove owner loc) false)
              (TMap.add actor (ls_lini (array_tryRemove owner loc)) pi1)))).
        { exists (TMap.add owner (Ready saved) rows), a. simpl.
          split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrep'|].
          split.
          - eapply scan_token_atomic; eauto.
          - eapply counter_token_atomic; eauto. }
        split.
        + split; [exact HIpost|]. unfold ALin. simpl. rewrite TMap.gss.
          reflexivity.
        + unfold source_G. repeat split; simpl; auto.
          * intros observer Hneq. repeat rewrite TMap.gso by exact Hneq.
            reflexivity.
          * intros observer a0 a' E0 E' Hneq.
            assert (a0 = a) by congruence. assert (a' = a) by congruence.
            subst. reflexivity.
          * intros q s0 pending_actor op0 Hlock Hforeign.
            destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
            -- rewrite Hpending in Hlock. inversion Hlock. congruence.
            -- rewrite TMap.gso by exact Hneq. exact Hlock.
          * assert (Hrow0 : payload_at rows owner = Some saved).
            { pose proof (payload_at_find rows owner
                (AtomicPending saved actor (ltryRemove loc)) Hpending) as Hrow0.
              exact Hrow0. }
            intro q. unfold row_counter_at.
            destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
            -- rewrite Hrow0, payload_at_add_same. simpl. lia.
            -- rewrite payload_at_add_other by exact Hneq. lia.
          * intros observer a0 a' E0 E' Hneq.
            assert (a0 = a) by congruence. assert (a' = a) by congruence.
            subst. reflexivity.
    Qed.

    Definition TryRemoveSafe actor owner loc : assertion :=
      fun w => SafeActive actor (array_tryRemove owner loc)
        (family_call owner (ltryRemove loc)) w /\
        ThreadDomain.contains D actor.

    Lemma tryRemove_safe_or_error actor owner loc w :
      Active actor (array_tryRemove owner loc) w ->
      TryRemoveSafe actor owner loc w \/ AssertionsSingle.APError w.
    Proof.
      intros Hactive. destruct Hactive as [HI Hlin]. pose proof HI as HI0.
      destruct HI as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      destruct (ThreadDomain.contains_dec D actor) as [Hactor|Hactorout].
      2:{ right. unfold AssertionsSingle.APError. apply rt_step. econstructor.
          - rewrite Ea. eapply error_actor_outside. exact Hactorout.
          - exact Hlin. }
      destruct (ThreadDomain.contains_dec D owner) as [Howner|Hownerout].
      2:{ right. unfold AssertionsSingle.APError. apply rt_step. econstructor.
          - rewrite Ea. eapply error_tryRemove_owner_outside. exact Hownerout.
          - exact Hlin. }
      destruct (classic (array_vertex a (pair owner loc)))
        as [Hvertex|Hundefined].
      2:{ right. unfold AssertionsSingle.APError. apply rt_step. econstructor.
          - rewrite Ea. eapply error_tryRemove_undefined. exact Hundefined.
          - exact Hlin. }
      left. split; [|exact Hactor]. split; [split; assumption|].
      intro Herror.
      change (ErrorIndexedFamily D (@SPListIndexedObject A)
        (Build_ThreadEvent actor
          (InvEv (family_call owner (ltryRemove loc))))
        (SinglePossState.σ w)) in Herror.
      rewrite Erows in Herror. inversion Herror; subst; simpl in *.
      - inversion H1; subst.
        all: pose proof (f_equal splist_event_kind H3) as Hkind;
          simpl in Hkind; try discriminate.
        unfold array_vertex in Hvertex.
        pose proof (f_equal (fun ev =>
          match te_ev ev with
          | InvEv (ltryRemove address) => Some address
          | _ => None
          end) H3) as Hloc.
        simpl in Hloc. inversion Hloc; subst l.
        assert (Hrow : payload_at (SinglePossState.σ w) owner = Some s).
        { unfold owner0 in H0.
          pose proof (payload_at_find (SinglePossState.σ w) owner
            (Ready s) H0) as Hrow. exact Hrow. }
        pose proof (represents_node_none (SinglePossState.σ w) a
          owner s loc Hrep Hrow H2) as [Hvalue _].
        rewrite Hvalue in Hvertex. contradiction.
      - contradiction.
      - destruct (proj2 (rep_domain _ _ Hrep owner) Howner) as [row Hrow].
        change (option_map row_payload
          (TMap.find owner (SinglePossState.σ w)) = Some row) in Hrow.
        pose proof (f_equal (option_map row_payload) H4) as Hnone.
        simpl in Hnone.
        pose proof (eq_trans (eq_sym Hrow) Hnone) as Hcontra.
        discriminate Hcontra.
    Qed.

    Lemma lift_tryRemove_safe_or_error actor owner loc :
      forall s, SActive actor (array_tryRemove owner loc) s ->
        lift_assert (TryRemoveSafe actor owner loc) s \/ AssertionsSet.APError s.
    Proof.
      intros s [w [Hview Hactive]].
      destruct (tryRemove_safe_or_error actor owner loc w Hactive)
        as [Hsafe|Herror].
      - left. exists w. auto.
      - right. econstructor.
        + eapply singleton_view_member; eauto.
        + exact Herror.
    Qed.

    Lemma tryRemove_inv_update_safe actor owner loc :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor
          (InvEv (family_call owner (ltryRemove loc))))
        (TryRemoveSafe actor owner loc)
        (TryRemovePending actor owner loc).
    Proof.
      intros sigma rho pi [[Hactive _] Hcontains].
      eapply tryRemove_inv_defined_update. split; assumption.
    Qed.

    Lemma tryRemove_method_triple actor owner loc :
      SetLogic.HTripleProvable (R actor) (G actor) SI actor
        (SActive actor (array_tryRemove owner loc))
        (tryRemove_impl D owner loc actor)
        (fun ret => SCompleted actor (array_tryRemove owner loc) ret).
    Proof.
      eapply SetLogic.provable_perror with
        (P' := lift_assert (TryRemoveSafe actor owner loc)).
      - intros s Hactive. eapply lift_tryRemove_safe_or_error; eauto.
      - unfold tryRemove_impl.
        eapply singleton_provable_vis_safe with
          (P' := TryRemovePending actor owner loc)
          (Q' := fun removed =>
            Completed actor (array_tryRemove owner loc) removed).
        + intros w [[_ Hsafe] _]. exact Hsafe.
        + apply tryRemove_pending_entails_I.
        + intros. apply completed_entails_I.
        + apply tryRemove_pending_stable.
        + intros. apply completed_stable.
        + apply tryRemove_inv_update_safe.
        + intros [|]; [apply tryRemove_true_res_update|
            apply tryRemove_false_res_update].
        + intros removed. eapply singleton_provable_ret_safe.
          * apply ImplRefl.
          * apply completed_entails_I.
          * apply completed_stable.
    Qed.

    Definition Linearizing actor m : assertion :=
      fun w => source_I w /\ ALin actor (ls_lini m) w.

    Definition SLinearizing actor m := lift_assert (Linearizing actor m).

    Lemma linearizing_entails_I actor m :
      ⊨ Linearizing actor m ==>> source_I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma linearizing_stable actor m :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (Linearizing actor m).
    Proof.
      unfold AssertionsSingle.A.Stable, AssertionsSingle.A.ComposeA.
      intros w [[pre [[HI Hlin] HR]] HI']. split; [exact HI'|].
      unfold ALin in *. rewrite <- (source_R_token actor pre w HR).
      exact Hlin.
    Qed.

    Definition GetTopReady actor owner : assertion :=
      fun w => Active actor (array_getTop owner) w /\
        ThreadDomain.contains D actor /\
        ThreadDomain.contains D owner /\
        exists a p,
          SinglePossState.ρ w = ArrayReady a /\
          TMap.find actor (as_scans a) = Some p /\
          scan_current p = None /\
          ~ In owner (scan_visited p).

    Lemma step_getTop_inv_shape owner actor control control' :
      @StepSPList A owner
        (Build_ThreadEvent actor (InvEv lgetTop)) control control' ->
      exists s, control = Ready s /\
        control' = Ready (start_snapshot actor s).
    Proof. intro Hstep. inversion Hstep; subst; eauto. Qed.

    Lemma getTop_inv_update actor owner :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor (InvEv (family_call owner lgetTop)))
        (GetTopReady actor owner)
        (Linearizing actor (array_getTop owner)).
    Proof.
      intros sigma1 rho1 pi1 Hpre sigma2 Hstep.
      destruct Hpre as
        [[HIpre Hlin] [Hactor [Howner [a0 [p0
          [Erho0 [Hscan0 [Hidle0 Hnotvisited]]]]]]]].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea, Erho0. subst sigma1 rho1.
      inversion Erho0; subst a0.
      change (StepIndexedFamily D (@SPListIndexedObject A)
        (Build_ThreadEvent actor (InvEv (family_call owner lgetTop)))
        rows sigma2) in Hstep.
      dependent destruction Hstep. simpl in *. unfold owner0 in *.
      destruct (step_getTop_inv_shape owner actor row row' H1)
        as (s & Erow & Erow'). subst row row'.
      assert (Hrow : payload_at rows owner = Some s).
      { pose proof (payload_at_find rows owner (Ready s) H0) as Hrow.
        exact Hrow. }
      pose proof (represents_begin_scan rows a actor owner s p0
        Hrep Hrow Hscan0 Hidle0) as Hrep'.
      exists (ArrayReady (begin_scan actor owner p0 a)).
      exists (TMap.add actor (ls_lini (array_getTop owner)) pi1).
      split.
      - apply rt_step. eapply ps_inv.
        + eapply step_getTop_inv;
            [exact Hactor|exact Howner|exact Hscan0|exact Hidle0|
              exact Hnotvisited|reflexivity].
        + exact Hlin.
      - assert (HIpost : source_I
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (TMap.add owner (Ready (start_snapshot actor s)) rows)
            (ArrayReady (begin_scan actor owner p0 a))
            (TMap.add actor (ls_lini (array_getTop owner)) pi1))).
        { exists (TMap.add owner (Ready (start_snapshot actor s)) rows),
            (begin_scan actor owner p0 a). simpl.
          split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrep'|].
          split.
          - intros caller p c Hfind Hcurrent.
            destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
            + unfold begin_scan in Hfind. cbn in Hfind.
              rewrite TMap.gss in Hfind. inversion Hfind; subst p.
              cbn in Hcurrent. inversion Hcurrent; subst c.
              rewrite TMap.gss. reflexivity.
            + rewrite TMap.gso by exact Hneq. eapply Hscan.
              * unfold begin_scan in Hfind. cbn in Hfind.
                rewrite TMap.gso in Hfind by exact Hneq. exact Hfind.
              * exact Hcurrent.
          - intros caller saved Hfind.
            destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
            + pose proof (Hcounter actor saved) as Hbad.
              unfold begin_scan in Hfind. cbn in Hfind.
              apply Hbad in Hfind. unfold ALin in Hlin. simpl in Hlin.
              exfalso. pose proof (eq_trans (eq_sym Hlin) Hfind) as Hcontra.
              dependent destruction Hcontra.
            + rewrite TMap.gso by exact Hneq. eapply Hcounter.
              unfold begin_scan in Hfind. cbn in Hfind. exact Hfind. }
        split.
        + split; [exact HIpost|]. unfold ALin. simpl. rewrite TMap.gss.
          reflexivity.
        + unfold source_G. repeat split; simpl; auto.
          * intros observer Hneq. rewrite TMap.gso by exact Hneq. reflexivity.
          * intros observer a1 a2 E1 E2 Hneq.
            assert (a1 = a) by congruence.
            assert (a2 = begin_scan actor owner p0 a) by congruence.
            subst. unfold begin_scan. cbn. rewrite TMap.gso by exact Hneq.
            reflexivity.
          * intros q s0 pending_actor op0 Hlock Hforeign.
            destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
            -- rewrite H0 in Hlock. discriminate.
            -- rewrite TMap.gso by exact Hneq. exact Hlock.
          * assert (Hrow0 : payload_at rows owner = Some s).
            { pose proof (payload_at_find rows owner (Ready s) H0) as Hrow0.
              exact Hrow0. }
            intro q. unfold row_counter_at.
            destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
            -- rewrite Hrow0, payload_at_add_same. simpl.
               unfold start_snapshot. cbn. lia.
            -- rewrite payload_at_add_other by exact Hneq. lia.
          * intros observer a1 a2 E1 E2 Hneq.
            assert (a1 = a) by congruence.
            assert (a2 = begin_scan actor owner p0 a) by congruence.
            subst. unfold begin_scan. cbn. reflexivity.
    Qed.

    Lemma snapshot_implies_current rows a actor owner row saved count :
      represents rows a ->
      payload_at rows owner = Some row ->
      TMap.find actor (snapshot row) = Some (pair saved count) ->
      exists p c,
        TMap.find actor (as_scans a) = Some p /\
        scan_current p = Some c /\
        current_owner c = owner /\
        current_order c = saved /\ current_counter c = count.
    Proof.
      intros Hrep Hrow Hsnapshot.
      pose proof (rep_snapshot _ _ Hrep actor owner row Hrow) as Hexpected.
      rewrite Hsnapshot in Hexpected.
      unfold expected_snapshot in Hexpected.
      destruct (TMap.find actor (as_scans a)) as [p|] eqn:Hscan;
        [|discriminate].
      destruct (scan_current p) as [c|] eqn:Hcurrent; [|discriminate].
      destruct (PositiveMap.E.eq_dec owner (current_owner c)) as [Heq|Hneq];
        [|discriminate].
      inversion Hexpected; subst. exists p, c. repeat split; auto.
    Qed.

    Lemma actual_snapshot_saved (actor : tid) (row : @SPListState A)
        (result : list Addr) (count : nat) :
      actual_snapshot actor row = Some (pair result count) ->
      exists saved,
        TMap.find actor (snapshot row) = Some (pair saved count).
    Proof.
      unfold actual_snapshot.
      destruct (TMap.find actor (snapshot row)) as [[saved saved_count]|]
        eqn:Hfind; [|discriminate].
      intro Hactual. inversion Hactual; subst saved_count.
      exists saved. reflexivity.
    Qed.

    Definition getTop_response_result
        (ev : @ThreadEvent (@ESPList A)) : option (@LNode A + nat) :=
      match ev with
      | Build_ThreadEvent _ (ResEv lgetTop result) => Some result
      | _ => None
      end.

    Lemma step_getTop_nonempty_inv owner actor s value ts loc control :
      @StepSPList A owner
        (Build_ThreadEvent actor
          (ResEv lgetTop (@inl (@LNode A) nat
            (pair (pair value ts) loc))))
        (Ready s) control ->
      exists remaining count,
        actual_snapshot actor s = Some (pair (loc :: remaining) count) /\
        nodes s loc = Some (pair value ts) /\
        control = Ready (clear_snapshot actor s).
    Proof.
      intro Hstep.
      remember (Build_ThreadEvent actor
        (ResEv lgetTop (@inl (@LNode A) nat
          (pair (pair value ts) loc))))
        as ev eqn:Hev in Hstep.
      inversion Hstep.
      - rewrite Hev in H0. pose proof (f_equal splist_event_kind H0) as Hkind.
        cbv [splist_event_kind] in Hkind. simpl in Hkind. discriminate.
      - rewrite Hev in H1. pose proof (f_equal getTop_response_result H1) as Hresult.
        cbv [getTop_response_result] in Hresult. simpl in Hresult.
        inversion Hresult; subst.
        pose proof (f_equal (@te_tid (@ESPList A)) H1) as Htid.
        simpl in Htid. subst t0. exists tl, count. auto.
      - rewrite Hev in H0. pose proof (f_equal getTop_response_result H0) as Hresult.
        cbv [getTop_response_result] in Hresult. simpl in Hresult.
        discriminate.
      - match goal with
        | Hevent : @eq (@ThreadEvent (@ESPList A)) _ ev |- _ =>
            rewrite Hev in Hevent;
            pose proof (f_equal splist_event_kind Hevent) as Hkind;
            cbv [splist_event_kind] in Hkind; simpl in Hkind; discriminate
        end.
      - match goal with
        | Hevent : @eq (@ThreadEvent (@ESPList A)) _ ev |- _ =>
            rewrite Hev in Hevent;
            pose proof (f_equal splist_event_kind Hevent) as Hkind;
            cbv [splist_event_kind] in Hkind; simpl in Hkind; discriminate
        end.
      - match goal with
        | Hevent : @eq (@ThreadEvent (@ESPList A)) _ ev |- _ =>
            rewrite Hev in Hevent;
            pose proof (f_equal splist_event_kind Hevent) as Hkind;
            cbv [splist_event_kind] in Hkind; simpl in Hkind; discriminate
        end.
      - match goal with
        | Hevent : @eq (@ThreadEvent (@ESPList A)) _ ev |- _ =>
            rewrite Hev in Hevent;
            pose proof (f_equal splist_event_kind Hevent) as Hkind;
            cbv [splist_event_kind] in Hkind; simpl in Hkind; discriminate
        end.
    Qed.

    Lemma step_getTop_empty_inv owner actor s count control :
      @StepSPList A owner
        (Build_ThreadEvent actor (ResEv lgetTop (@inr (@LNode A) nat count)))
        (Ready s) control ->
      actual_snapshot actor s = Some (pair nil count) /\
      control = Ready (clear_snapshot actor s).
    Proof.
      intro Hstep.
      remember (Build_ThreadEvent actor
        (ResEv lgetTop (@inr (@LNode A) nat count))) as ev eqn:Hev in Hstep.
      inversion Hstep.
      - rewrite Hev in H0. pose proof (f_equal splist_event_kind H0) as Hkind.
        cbv [splist_event_kind] in Hkind. simpl in Hkind. discriminate.
      - rewrite Hev in H1. pose proof (f_equal getTop_response_result H1)
          as Hresult.
        cbv [getTop_response_result] in Hresult. simpl in Hresult.
        discriminate.
      - rewrite Hev in H0. pose proof (f_equal getTop_response_result H0)
          as Hresult.
        cbv [getTop_response_result] in Hresult. simpl in Hresult.
        inversion Hresult; subst.
        pose proof (f_equal (@te_tid (@ESPList A)) H0) as Htid.
        simpl in Htid. subst t0. auto.
      - match goal with
        | Hevent : @eq (@ThreadEvent (@ESPList A)) _ ev |- _ =>
            rewrite Hev in Hevent;
            pose proof (f_equal splist_event_kind Hevent) as Hkind;
            cbv [splist_event_kind] in Hkind; simpl in Hkind; discriminate
        end.
      - match goal with
        | Hevent : @eq (@ThreadEvent (@ESPList A)) _ ev |- _ =>
            rewrite Hev in Hevent;
            pose proof (f_equal splist_event_kind Hevent) as Hkind;
            cbv [splist_event_kind] in Hkind; simpl in Hkind; discriminate
        end.
      - match goal with
        | Hevent : @eq (@ThreadEvent (@ESPList A)) _ ev |- _ =>
            rewrite Hev in Hevent;
            pose proof (f_equal splist_event_kind Hevent) as Hkind;
            cbv [splist_event_kind] in Hkind; simpl in Hkind; discriminate
        end.
      - match goal with
        | Hevent : @eq (@ThreadEvent (@ESPList A)) _ ev |- _ =>
            rewrite Hev in Hevent;
            pose proof (f_equal splist_event_kind Hevent) as Hkind;
            cbv [splist_event_kind] in Hkind; simpl in Hkind; discriminate
        end.
    Qed.

    Lemma scan_token_end a pi actor owner p c ret :
      scan_token_consistent a pi ->
      TMap.find actor (as_scans a) = Some p ->
      scan_current p = Some c -> current_owner c = owner ->
      TMap.find actor pi = Some (ls_lini (array_getTop owner)) ->
      scan_token_consistent (end_scan actor p c a)
        (TMap.add actor (ls_linr (array_getTop owner) ret) pi).
    Proof.
      intros Hconsistent Hscanp Hcurrent Howner Hlin caller p' c'
        Hfind Hcurrent'.
      destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
      - unfold end_scan in Hfind. cbn in Hfind. rewrite TMap.gss in Hfind.
        inversion Hfind; subst p'. cbn in Hcurrent'. discriminate.
      - rewrite TMap.gso by exact Hneq. eapply Hconsistent.
        + unfold end_scan in Hfind. cbn in Hfind.
          rewrite TMap.gso in Hfind by exact Hneq. exact Hfind.
        + exact Hcurrent'.
    Qed.

    Lemma counter_token_getTop_res a pi actor owner p c ret :
      counter_token_consistent a pi ->
      TMap.find actor pi = Some (ls_lini (array_getTop owner)) ->
      counter_token_consistent (end_scan actor p c a)
        (TMap.add actor (ls_linr (array_getTop owner) ret) pi).
    Proof.
      intros Hconsistent Hlin caller saved Hfind.
      destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
      - unfold end_scan in Hfind. cbn in Hfind.
        pose proof (Hconsistent actor saved Hfind) as Hcounterlin.
        pose proof (eq_trans (eq_sym Hlin) Hcounterlin) as Hcontra.
        dependent destruction Hcontra.
      - rewrite TMap.gso by exact Hneq. eapply Hconsistent.
        unfold end_scan in Hfind. cbn in Hfind. exact Hfind.
    Qed.

    Lemma getTop_nonempty_res_update actor owner value ts loc :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor
          (ResEv (family_call owner lgetTop)
            (@inl (@LNode A) nat (pair (pair value ts) loc))))
        (Linearizing actor (array_getTop owner))
        (Completed actor (array_getTop owner)
          (@inl (@LNode A) nat (pair (pair value ts) loc))).
    Proof.
      intros sigma1 rho1 pi1 [HIpre Hlin] sigma2 Hstep.
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea. subst sigma1 rho1.
      change (StepIndexedFamily D (@SPListIndexedObject A)
        (Build_ThreadEvent actor
          (ResEv (family_call owner lgetTop)
            (@inl (@LNode A) nat (pair (pair value ts) loc))))
        rows sigma2) in Hstep.
      dependent destruction Hstep. simpl in *. unfold owner0 in *.
      destruct row as [s|s pending_actor op];
        [|dependent destruction H1].
      destruct (step_getTop_nonempty_inv owner actor s value ts loc row' H1)
        as (remaining & count & Hactual & Hnode & Erow'). subst row'.
      assert (Hrow : payload_at rows owner = Some s).
      { pose proof (payload_at_find rows owner (Ready s) H0) as Hrow.
        exact Hrow. }
      destruct (actual_snapshot_saved actor s (loc :: remaining) count Hactual)
        as [saved_order Hsnapshot].
      destruct (snapshot_implies_current rows a actor owner s saved_order count
        Hrep Hrow Hsnapshot)
        as (p & c & Hscanp & Hcurrent & Hcowner & Hcorder & Hccounter).
      pose proof (actual_snapshot_actual_scan rows a actor owner s p c
        Hrep Hrow Hscanp Hcurrent Hcowner) as Hbridge.
      rewrite Hactual in Hbridge. inversion Hbridge.
      assert (Hscanorder : actual_scan_order c a = loc :: remaining)
        by congruence.
      pose proof (represents_node_some rows a owner s loc value ts
        Hrep Hrow Hnode) as [Hvalue Htimestamp].
      pose proof (represents_end_scan rows a actor owner s p c Hrep Hrow
        Hscanp Hcurrent Hcowner) as Hrep'.
      set (result := @inl (@LNode A) nat (pair (pair value ts) loc)).
      exists (ArrayReady (end_scan actor p c a)).
      exists (TMap.add actor (ls_linr (array_getTop owner) result) pi1).
      split.
      - apply rt_step. eapply ps_ret.
        + eapply step_getTop_nonempty_res;
            [exact Hscanp|exact Hcurrent|exact Hcowner|exact Hscanorder|
              exact Hvalue|exact Htimestamp|reflexivity].
        + exact Hlin.
      - assert (HIpost : source_I
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (TMap.add owner (Ready (clear_snapshot actor s)) rows)
            (ArrayReady (end_scan actor p c a))
            (TMap.add actor (ls_linr (array_getTop owner) result) pi1))).
        { exists (TMap.add owner (Ready (clear_snapshot actor s)) rows),
            (end_scan actor p c a). simpl.
          split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrep'|].
          split.
          - eapply scan_token_end; eauto.
          - eapply counter_token_getTop_res; eauto. }
        split.
        + split; [exact HIpost|]. unfold ALin. simpl. rewrite TMap.gss.
          reflexivity.
        + unfold source_G. repeat split; simpl; auto.
          * intros observer Hneq. rewrite TMap.gso by exact Hneq. reflexivity.
          * intros observer a1 a2 E1 E2 Hneq.
            assert (a1 = a) by congruence.
            assert (a2 = end_scan actor p c a) by congruence. subst.
            unfold end_scan. cbn. rewrite TMap.gso by exact Hneq.
            reflexivity.
          * intros q s0 pending_actor op0 Hlock Hforeign.
            destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
            -- rewrite H0 in Hlock. discriminate.
            -- rewrite TMap.gso by exact Hneq. exact Hlock.
          * intro q. unfold row_counter_at.
            destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
            -- rewrite Hrow, payload_at_add_same. simpl.
               unfold clear_snapshot. cbn. lia.
            -- rewrite payload_at_add_other by exact Hneq. lia.
          * intros observer a1 a2 E1 E2 Hneq.
            assert (a1 = a) by congruence.
            assert (a2 = end_scan actor p c a) by congruence. subst.
            unfold end_scan. cbn. reflexivity.
    Qed.

    Lemma getTop_empty_res_update actor owner count :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor
          (ResEv (family_call owner lgetTop)
            (@inr (@LNode A) nat count)))
        (Linearizing actor (array_getTop owner))
        (Completed actor (array_getTop owner)
          (@inr (@LNode A) nat count)).
    Proof.
      intros sigma1 rho1 pi1 [HIpre Hlin] sigma2 Hstep.
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea. subst sigma1 rho1.
      change (StepIndexedFamily D (@SPListIndexedObject A)
        (Build_ThreadEvent actor
          (ResEv (family_call owner lgetTop)
            (@inr (@LNode A) nat count)))
        rows sigma2) in Hstep.
      dependent destruction Hstep. simpl in *. unfold owner0 in *.
      destruct row as [s|s pending_actor op];
        [|dependent destruction H1].
      destruct (step_getTop_empty_inv owner actor s count row' H1)
        as [Hactual Erow']. subst row'.
      assert (Hrow : payload_at rows owner = Some s).
      { pose proof (payload_at_find rows owner (Ready s) H0) as Hrow.
        exact Hrow. }
      destruct (actual_snapshot_saved actor s nil count Hactual)
        as [saved_order Hsnapshot].
      destruct (snapshot_implies_current rows a actor owner s saved_order count
        Hrep Hrow Hsnapshot)
        as (p & c & Hscanp & Hcurrent & Hcowner & Hcorder & Hccounter).
      pose proof (actual_snapshot_actual_scan rows a actor owner s p c
        Hrep Hrow Hscanp Hcurrent Hcowner) as Hbridge.
      rewrite Hactual in Hbridge. inversion Hbridge.
      assert (Hscanorder : actual_scan_order c a = nil) by congruence.
      assert (Hcount : current_counter c = count) by congruence.
      subst count.
      pose proof (represents_end_scan rows a actor owner s p c Hrep Hrow
        Hscanp Hcurrent Hcowner) as Hrep'.
      set (result := @inr (@LNode A) nat (current_counter c)).
      exists (ArrayReady (end_scan actor p c a)).
      exists (TMap.add actor (ls_linr (array_getTop owner) result) pi1).
      split.
      - apply rt_step. eapply ps_ret.
        + eapply step_getTop_empty_res;
            [exact Hscanp|exact Hcurrent|exact Hcowner|exact Hscanorder|
              reflexivity].
        + exact Hlin.
      - assert (HIpost : source_I
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            (TMap.add owner (Ready (clear_snapshot actor s)) rows)
            (ArrayReady (end_scan actor p c a))
            (TMap.add actor (ls_linr (array_getTop owner) result) pi1))).
        { exists (TMap.add owner (Ready (clear_snapshot actor s)) rows),
            (end_scan actor p c a). simpl.
          split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrep'|].
          split.
          - eapply scan_token_end; eauto.
          - eapply counter_token_getTop_res; eauto. }
        split.
        + split; [exact HIpost|]. unfold ALin. simpl. rewrite TMap.gss.
          reflexivity.
        + unfold source_G. repeat split; simpl; auto.
          * intros observer Hneq. rewrite TMap.gso by exact Hneq. reflexivity.
          * intros observer a1 a2 E1 E2 Hneq.
            assert (a1 = a) by congruence.
            assert (a2 = end_scan actor p c a) by congruence. subst.
            unfold end_scan. cbn. rewrite TMap.gso by exact Hneq.
            reflexivity.
          * intros q s0 pending_actor op0 Hlock Hforeign.
            destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
            -- rewrite H0 in Hlock. discriminate.
            -- rewrite TMap.gso by exact Hneq. exact Hlock.
          * intro q. unfold row_counter_at.
            destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
            -- rewrite Hrow, payload_at_add_same. simpl.
               unfold clear_snapshot. cbn. lia.
            -- rewrite payload_at_add_other by exact Hneq. lia.
          * intros observer a1 a2 E1 E2 Hneq.
            assert (a1 = a) by congruence.
            assert (a2 = end_scan actor p c a) by congruence. subst.
            unfold end_scan. cbn. reflexivity.
    Qed.

    Definition GetTopSafe actor owner : assertion :=
      fun w => GetTopReady actor owner w /\
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent actor
            (InvEv (family_call owner lgetTop))) w.

    Lemma getTop_safe_or_error actor owner w :
      Active actor (array_getTop owner) w ->
      GetTopSafe actor owner w \/ AssertionsSingle.APError w.
    Proof.
      intros Hactive. destruct Hactive as [HI Hlin]. pose proof HI as HI0.
      destruct HI as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      destruct (ThreadDomain.contains_dec D actor) as [Hactor|Hactorout].
      2:{ right. unfold AssertionsSingle.APError. apply rt_step. econstructor.
          - rewrite Ea. eapply error_actor_outside. exact Hactorout.
          - exact Hlin. }
      destruct (ThreadDomain.contains_dec D owner) as [Howner|Hownerout].
      2:{ right. unfold AssertionsSingle.APError. apply rt_step. econstructor.
          - rewrite Ea. eapply error_getTop_owner_outside. exact Hownerout.
          - exact Hlin. }
      destruct (TMap.find actor (as_scans a)) as [p|] eqn:Hscanp.
      2:{ right. unfold AssertionsSingle.APError. apply rt_step. econstructor.
          - rewrite Ea. eapply error_getTop_without_reset. exact Hscanp.
          - exact Hlin. }
      destruct (scan_current p) as [c|] eqn:Hcurrent.
      - right. unfold AssertionsSingle.APError. apply rt_step. econstructor.
        + rewrite Ea. eapply error_getTop_repeat with (p := p).
          * exact Hscanp.
          * right. congruence.
        + exact Hlin.
      - destruct (in_dec PositiveMap.E.eq_dec owner (scan_visited p))
          as [Hvisited|Hnotvisited].
        + right. unfold AssertionsSingle.APError. apply rt_step. econstructor.
          * rewrite Ea. eapply error_getTop_repeat with (p := p).
            -- exact Hscanp.
            -- left. exact Hvisited.
          * exact Hlin.
        + left. split.
          * split.
            -- split; [exact HI0|exact Hlin].
            -- repeat split; eauto. exists a, p. repeat split; eauto.
          * intro Herror.
            change (ErrorIndexedFamily D (@SPListIndexedObject A)
              (Build_ThreadEvent actor
                (InvEv (family_call owner lgetTop)))
              (SinglePossState.σ w)) in Herror.
            rewrite Erows in Herror. inversion Herror; subst; simpl in *.
            -- inversion H1; subst;
                 pose proof (f_equal splist_event_kind H3) as Hkind;
                 simpl in Hkind; discriminate.
            -- contradiction.
            -- destruct (proj2 (rep_domain _ _ Hrep owner) Howner)
                 as [row Hrow].
               change (option_map row_payload (TMap.find owner
                 (SinglePossState.σ w)) = Some row) in Hrow.
               pose proof (f_equal (option_map row_payload) H4) as Hnone.
               simpl in Hnone.
               pose proof (eq_trans (eq_sym Hrow) Hnone) as Hcontra.
               discriminate Hcontra.
    Qed.

    Lemma lift_getTop_safe_or_error actor owner :
      forall s, SActive actor (array_getTop owner) s ->
        lift_assert (GetTopSafe actor owner) s \/ AssertionsSet.APError s.
    Proof.
      intros s [w [Hview Hactive]].
      destruct (getTop_safe_or_error actor owner w Hactive)
        as [Hsafe|Herror].
      - left. exists w. auto.
      - right. econstructor.
        + eapply singleton_view_member; eauto.
        + exact Herror.
    Qed.

    Lemma getTop_inv_update_safe actor owner :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor
          (InvEv (family_call owner lgetTop)))
        (GetTopSafe actor owner)
        (Linearizing actor (array_getTop owner)).
    Proof.
      intros sigma rho pi [Hready _]. eapply getTop_inv_update. exact Hready.
    Qed.

    Lemma getTop_method_triple actor owner :
      SetLogic.HTripleProvable (R actor) (G actor) SI actor
        (SActive actor (array_getTop owner))
        (getTop_impl D owner actor)
        (fun ret => SCompleted actor (array_getTop owner) ret).
    Proof.
      eapply SetLogic.provable_perror with
        (P' := lift_assert (GetTopSafe actor owner)).
      - intros s Hactive. eapply lift_getTop_safe_or_error; eauto.
      - unfold getTop_impl.
        eapply singleton_provable_vis_safe with
          (P' := Linearizing actor (array_getTop owner))
          (Q' := fun ret => Completed actor (array_getTop owner) ret).
        + intros w [_ Hsafe]. exact Hsafe.
        + apply linearizing_entails_I.
        + intros. apply completed_entails_I.
        + apply linearizing_stable.
        + intros. apply completed_stable.
        + apply getTop_inv_update_safe.
        + intros [node|count].
          * destruct node as [[value ts] loc].
            apply getTop_nonempty_res_update.
          * apply getTop_empty_res_update.
        + intros result. eapply singleton_provable_ret_safe.
          * apply ImplRefl.
          * apply completed_entails_I.
          * apply completed_stable.
    Qed.

    Fixpoint sum_row_counters
        (owners : list tid) (rows : concrete_state) : nat :=
      match owners with
      | nil => 0
      | owner :: owners' =>
          row_counter_at rows owner + sum_row_counters owners' rows
      end.

    Lemma sum_row_counters_app owners1 owners2 rows :
      sum_row_counters (owners1 ++ owners2) rows =
      Nat.add (sum_row_counters owners1 rows)
        (sum_row_counters owners2 rows).
    Proof. induction owners1; simpl; lia. Qed.

    Lemma sum_row_counters_snoc owners owner rows :
      sum_row_counters (owners ++ owner :: nil) rows =
      Nat.add (sum_row_counters owners rows) (row_counter_at rows owner).
    Proof. rewrite sum_row_counters_app. simpl. lia. Qed.

    Lemma sum_row_counters_mono owners rows rows' :
      (forall owner, row_counter_at rows owner <= row_counter_at rows' owner) ->
      sum_row_counters owners rows <= sum_row_counters owners rows'.
    Proof.
      intro Hmono. induction owners as [|owner owners IH]; simpl; [lia|].
      specialize (Hmono owner). lia.
    Qed.

    Lemma represents_sum_counters rows a owners :
      represents rows a ->
      sum_counters owners (as_counters a) = sum_row_counters owners rows.
    Proof.
      intro Hrep. induction owners as [|owner owners IH]; simpl; [reflexivity|].
      change (Nat.add (counter_at owner a)
          (sum_counters owners (as_counters a)) =
        Nat.add (row_counter_at rows owner) (sum_row_counters owners rows)).
      rewrite (rep_counter _ _ Hrep owner), IH. reflexivity.
    Qed.

    Lemma represents_total_counter rows a :
      represents rows a ->
      total_counter D a =
        sum_row_counters (ThreadDomain.threads D) rows.
    Proof.
      intro Hrep. unfold total_counter.
      apply represents_sum_counters. exact Hrep.
    Qed.

    Lemma source_R_counter_mono observer w w' :
      source_R observer w w' ->
      forall owner,
        row_counter_at (SinglePossState.σ w) owner <=
        row_counter_at (SinglePossState.σ w') owner.
    Proof.
      intros [Hother|Hadmin] owner.
      - destruct Hother as [other [Hneq HG]].
        destruct HG as [_ [_ [_ [_ [_ [Hmono _]]]]]]. exact (Hmono owner).
      - pose proof
          (AssertionsSingle.linearization_rely_observer_view observer _ _ Hadmin)
          as [Hsigma _]. rewrite Hsigma. lia.
    Qed.

    Lemma source_R_pending_counter observer w w' saved :
      source_R observer w w' ->
      source_I w -> source_I w' ->
      (exists a, SinglePossState.ρ w = ArrayReady a /\
        TMap.find observer (as_pending_counters a) = Some saved) ->
      exists a', SinglePossState.ρ w' = ArrayReady a' /\
        TMap.find observer (as_pending_counters a') = Some saved.
    Proof.
      intros HR HI HI' [a [Erho Hfind]].
      destruct HI' as
        (rows' & a' & Erows' & Erho' & Hrep' & Hscan' & Hcounter').
      exists a'. split; [exact Erho'|].
      destruct HR as [Hother|Hadmin].
      - destruct Hother as [other [Hneq HG]].
        destruct HG as [_ [_ [_ [_ [_ [_ Hpending]]]]]].
        pose proof (Hpending observer a a' Erho Erho') as Heq.
        specialize (Heq ltac:(congruence)). rewrite <- Heq. exact Hfind.
      - pose proof
          (AssertionsSingle.linearization_rely_observer_view observer _ _ Hadmin)
          as [_ [Hrho _]].
        assert (a = a') by congruence. subst. exact Hfind.
    Qed.

    Definition CounterReady actor : assertion :=
      fun w => Active actor array_getCounter w /\
        ThreadDomain.contains D actor /\
        exists a, SinglePossState.ρ w = ArrayReady a /\
          TMap.find actor (as_pending_counters a) = None.

    Lemma counter_ready_or_error actor w :
      Active actor array_getCounter w ->
      CounterReady actor w \/ AssertionsSingle.APError w.
    Proof.
      intros Hactive. destruct Hactive as [HI Hlin]. pose proof HI as HI0.
      destruct HI as
        (rows & a & Erows & Ea & Hrep & Hscan & Hcounter).
      destruct (ThreadDomain.contains_dec D actor) as [Hactor|Houtside].
      2:{ right. unfold AssertionsSingle.APError. apply rt_step. econstructor.
          - rewrite Ea. eapply error_actor_outside. exact Houtside.
          - exact Hlin. }
      left. split; [split; assumption|]. split; [exact Hactor|].
      exists a. split; [exact Ea|].
      destruct (TMap.find actor (as_pending_counters a)) as [saved|]
        eqn:Hpending; [|reflexivity].
      pose proof (Hcounter actor saved Hpending) as Hbad.
      unfold ALin in Hlin. rewrite Hlin in Hbad. dependent destruction Hbad.
    Qed.

    Lemma lift_counter_ready_or_error actor :
      forall s, SActive actor array_getCounter s ->
        lift_assert (CounterReady actor) s \/ AssertionsSet.APError s.
    Proof.
      intros s [w [Hview Hactive]].
      destruct (counter_ready_or_error actor w Hactive) as [Hready|Herror].
      - left. exists w. auto.
      - right. econstructor.
        + eapply singleton_view_member; eauto.
        + exact Herror.
    Qed.

    Lemma scan_token_start_counter a pi actor :
      scan_token_consistent a pi ->
      TMap.find actor pi = Some (ls_inv array_getCounter) ->
      scan_token_consistent (start_counter D actor a)
        (TMap.add actor (ls_lini array_getCounter) pi).
    Proof.
      intros Hconsistent Hlin caller p c Hscan Hcurrent.
      destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
      - pose proof (Hconsistent actor p c Hscan Hcurrent) as Hbad.
        rewrite Hlin in Hbad. dependent destruction Hbad.
      - rewrite TMap.gso by exact Hneq. eapply Hconsistent; eauto.
    Qed.

    Lemma counter_token_start_counter a pi actor :
      counter_token_consistent a pi ->
      TMap.find actor (as_pending_counters a) = None ->
      counter_token_consistent (start_counter D actor a)
        (TMap.add actor (ls_lini array_getCounter) pi).
    Proof.
      intros Hconsistent Hnone caller saved Hfind.
      destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
      - rewrite TMap.gss. reflexivity.
      - rewrite TMap.gso by exact Hneq. eapply Hconsistent.
        unfold start_counter in Hfind. cbn in Hfind.
        rewrite TMap.gso in Hfind by exact Hneq. exact Hfind.
    Qed.

    Definition CounterStarted actor : assertion :=
      fun w => source_I w /\ ALin actor (ls_lini array_getCounter) w /\
        exists rows a,
          SinglePossState.σ w = rows /\
          SinglePossState.ρ w = ArrayReady a /\
          TMap.find actor (as_pending_counters a) =
            Some (sum_row_counters (ThreadDomain.threads D) rows).

    Lemma counter_started_entails_I actor :
      ⊨ CounterStarted actor ==>> source_I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma counter_start_update actor :
      AssertionsSingle.PUpdateId (source_G actor)
        (CounterReady actor) (CounterStarted actor).
    Proof.
      intros rows a pi [[HIpre Hlin] [Hactor [a0 [Ea Hnone]]]].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows0 & a1 & Erows & Ea1 & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea1, Ea. subst rows a. inversion Ea; subst a0.
      exists (ArrayReady (start_counter D actor a1)).
      exists (TMap.add actor (ls_lini array_getCounter) pi).
      split.
      - apply rt_step. eapply ps_inv.
        + eapply step_counter_inv; [exact Hactor|exact Hnone|reflexivity].
        + exact Hlin.
      - assert (HIpost : source_I
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            rows0 (ArrayReady (start_counter D actor a1))
            (TMap.add actor (ls_lini array_getCounter) pi))).
        { exists rows0, (start_counter D actor a1). simpl.
          split; [reflexivity|]. split; [reflexivity|]. split.
          - apply represents_start_counter. exact Hrep.
          - split.
            + eapply scan_token_start_counter; eauto.
            + eapply counter_token_start_counter; eauto. }
        split.
        + split; [exact HIpost|]. split.
          * unfold ALin. simpl. rewrite TMap.gss. reflexivity.
          * exists rows0, (start_counter D actor a1). simpl.
            repeat split; try reflexivity.
            unfold start_counter. cbn. rewrite TMap.gss.
            f_equal.
            change (sum_counters (ThreadDomain.threads D) (as_counters a1) =
              sum_row_counters (ThreadDomain.threads D) rows0).
            apply represents_sum_counters. exact Hrep.
        + eapply source_G_same_concrete.
          * exact HIpre0.
          * exact HIpost.
          * reflexivity.
          * intros observer Hneq. simpl. rewrite TMap.gso by exact Hneq.
            reflexivity.
          * intros observer a2 a3 E2 E3 Hneq.
            inversion E2; inversion E3; subst.
            reflexivity.
          * intros observer a2 a3 E2 E3 Hneq.
            inversion E2; inversion E3; subst.
            unfold start_counter. cbn. rewrite TMap.gso by exact Hneq.
            reflexivity.
    Qed.

    Definition CounterFold actor (remaining : list tid) (acc : nat) :
        assertion :=
      fun w => source_I w /\ ALin actor (ls_lini array_getCounter) w /\
        exists base rows a visited saved,
          SinglePossState.σ w = rows /\
          SinglePossState.ρ w = ArrayReady a /\
          ThreadDomain.threads D = visited ++ remaining /\
          TMap.find actor (as_pending_counters a) = Some saved /\
          saved = sum_row_counters (ThreadDomain.threads D) base /\
          (forall owner,
            row_counter_at base owner <= row_counter_at rows owner) /\
          sum_row_counters visited base <= acc /\
          acc <= sum_row_counters visited rows.

    Lemma counter_started_entails_fold actor :
      ⊨ CounterStarted actor ==>>
        CounterFold actor (ThreadDomain.threads D) 0.
    Proof.
      intros w [HI [Hlin [rows [a [Erows [Ea Hpending]]]]]].
      split; [exact HI|]. split; [exact Hlin|].
      exists rows, rows, a, nil,
        (sum_row_counters (ThreadDomain.threads D) rows).
      repeat split; simpl; auto; lia.
    Qed.

    Lemma counter_fold_entails_I actor remaining acc :
      ⊨ CounterFold actor remaining acc ==>> source_I.
    Proof. intros w [HI _]. exact HI. Qed.

    Lemma counter_fold_stable actor remaining acc :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (CounterFold actor remaining acc).
    Proof.
      unfold AssertionsSingle.A.Stable, AssertionsSingle.A.ComposeA.
      intros w [[pre [[HI [Hlin
        [base [rows [a [visited [saved
          [Erows [Ea [Hparts [Hpending
            [Hsaved [Hbase [Hlower Hupper]]]]]]]]]]]]]] HR]] HI'].
      destruct HI' as
        (rows' & a' & Erows' & Ea' & Hrep' & Hscan' & Hcounter').
      assert (Hmono : forall owner,
          row_counter_at rows owner <= row_counter_at rows' owner).
      { intro owner. rewrite <- Erows, <- Erows'.
        eapply source_R_counter_mono. exact HR. }
      destruct (source_R_pending_counter actor pre w saved HR HI
        (ex_intro _ rows'
          (ex_intro _ a'
            (conj Erows' (conj Ea'
              (conj Hrep' (conj Hscan' Hcounter'))))))
        (ex_intro _ a (conj Ea Hpending)))
        as [a'' [Ea'' Hpending']].
      assert (a'' = a') by congruence. subst a''.
      split.
      - exists rows', a'. split; [exact Erows'|]. split; [exact Ea'|].
        split; [exact Hrep'|]. split; [exact Hscan'|exact Hcounter'].
      - split.
        + unfold ALin in Hlin |- *.
          pose proof (source_R_token actor pre w HR) as Htoken.
          exact (eq_trans (eq_sym Htoken) Hlin).
        + exists base, rows', a', visited, saved. repeat split; try assumption.
          * intros owner. specialize (Hbase owner). specialize (Hmono owner).
            lia.
          * eapply Nat.le_trans; [exact Hupper|].
            apply sum_row_counters_mono. exact Hmono.
    Qed.

    Lemma sum_row_counters_ext owners rows rows' :
      (forall owner, row_counter_at rows owner = row_counter_at rows' owner) ->
      sum_row_counters owners rows = sum_row_counters owners rows'.
    Proof.
      intro Heq. induction owners as [|owner owners IH]; simpl; [reflexivity|].
      rewrite Heq, IH. reflexivity.
    Qed.

    Lemma row_counter_add_control rows owner before after :
      TMap.find owner rows = Some before ->
      row_payload before = row_payload after ->
      forall q,
        row_counter_at rows q =
        row_counter_at (TMap.add owner after rows) q.
    Proof.
      intros Hfind Hpayload q. unfold row_counter_at.
      destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
      - pose proof (payload_at_find rows owner before Hfind) as Hbefore.
        rewrite Hbefore, payload_at_add_same, Hpayload. reflexivity.
      - rewrite payload_at_add_other by exact Hneq. reflexivity.
    Qed.

    Definition CounterPending actor remaining acc owner : assertion :=
      fun w => CounterFold actor remaining acc w /\
        exists s, TMap.find owner (SinglePossState.σ w) =
          Some (AtomicPending s actor lgetCounter).

    Lemma counter_pending_entails_I actor remaining acc owner :
      ⊨ CounterPending actor remaining acc owner ==>> source_I.
    Proof. intros w [[HI _] _]. exact HI. Qed.

    Lemma counter_pending_stable actor remaining acc owner :
      AssertionsSingle.A.Stable (source_R actor) source_I
        (CounterPending actor remaining acc owner).
    Proof.
      unfold AssertionsSingle.A.Stable, AssertionsSingle.A.ComposeA.
      intros w [[pre [[Hfold [s Hpending]] HR]] HI'].
      split.
      - pose proof (counter_fold_stable actor remaining acc) as Hstable.
        unfold AssertionsSingle.A.Stable,
          AssertionsSingle.A.ComposeA in Hstable.
        exact (Hstable w
          (conj (ex_intro _ pre (conj Hfold HR)) HI')).
      - exists s. eapply source_R_preserves_pending; eauto.
    Qed.

    Lemma step_getCounter_inv_shape owner actor control control' :
      @StepSPList A owner
        (Build_ThreadEvent actor (InvEv lgetCounter)) control control' ->
      exists s, control = Ready s /\
        control' = AtomicPending s actor lgetCounter.
    Proof. intro Hstep. inversion Hstep; subst; eauto. Qed.

    Lemma counter_row_inv_update actor owner remaining acc :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor (InvEv (family_call owner lgetCounter)))
        (CounterFold actor (owner :: remaining) acc)
        (CounterPending actor (owner :: remaining) acc owner).
    Proof.
      intros sigma1 rho1 pi1 Hfold sigma2 Hstep.
      destruct Hfold as [HIpre [Hlin
        [base [rows [a [visited [saved
          [Erows [Ea [Hparts [Hpending
            [Hsaved [Hbase [Hlower Hupper]]]]]]]]]]]]]].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows0 & a0 & Erows0 & Ea0 & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea, Erows0, Ea0. subst sigma1 rho1.
      assert (rows0 = rows) by congruence. subst rows0.
      assert (a0 = a) by congruence. subst a0.
      change (StepIndexedFamily D (@SPListIndexedObject A)
        (Build_ThreadEvent actor (InvEv (family_call owner lgetCounter)))
        rows sigma2) in Hstep.
      dependent destruction Hstep. simpl in *. unfold owner0 in *.
      destruct (step_getCounter_inv_shape owner actor row row' H2)
        as (s & Erow & Erow'). subst row row'.
      assert (Hroweq : forall q,
          row_counter_at rows q =
          row_counter_at
            (TMap.add owner (AtomicPending s actor lgetCounter) rows) q).
      { eapply row_counter_add_control; [exact H1|reflexivity]. }
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (TMap.add owner (AtomicPending s actor lgetCounter) rows)
          (ArrayReady a) pi1)).
      { exists (TMap.add owner (AtomicPending s actor lgetCounter) rows), a.
        simpl. split; [reflexivity|]. split; [reflexivity|]. split.
        - eapply represents_change_control; eauto.
        - split; assumption. }
      pupdate_finish. split.
      - split.
        + split; [exact HIpost|]. split; [exact Hlin|].
          exists base,
            (TMap.add owner (AtomicPending s actor lgetCounter) rows),
            a, visited, saved. repeat split; try assumption.
          * intros q. rewrite <- Hroweq. apply Hbase.
          * rewrite <- (sum_row_counters_ext visited rows
              (TMap.add owner (AtomicPending s actor lgetCounter) rows) Hroweq).
            exact Hupper.
        + exists s. simpl. apply TMap.gss.
      - unfold source_G. repeat split; simpl; auto.
        + intros observer a1 a2 E1 E2 Hneq.
          assert (a1 = a) by congruence. assert (a2 = a) by congruence.
          subst. reflexivity.
        + intros q s0 pending_actor op Hlock Hforeign.
          destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
          * rewrite H1 in Hlock. discriminate.
          * rewrite TMap.gso by exact Hneq. exact Hlock.
        + intro q. rewrite <- Hroweq. lia.
        + intros observer a1 a2 E1 E2 Hneq.
          assert (a1 = a) by congruence. assert (a2 = a) by congruence.
          subst. reflexivity.
    Qed.

    Definition getCounter_response_result
        (ev : @ThreadEvent (@ESPList A)) : option nat :=
      match ev with
      | Build_ThreadEvent _ (ResEv lgetCounter count) => Some count
      | _ => None
      end.

    Lemma step_getCounter_res_shape owner actor s count control :
      @StepSPList A owner
        (Build_ThreadEvent actor (ResEv lgetCounter count))
        (AtomicPending s actor lgetCounter) control ->
      count = counter s /\ control = Ready s.
    Proof.
      intro Hstep.
      remember (Build_ThreadEvent actor (ResEv lgetCounter count))
        as ev eqn:Hev in Hstep.
      inversion Hstep.
      all: try (match goal with
      | Htarget : @eq (@ThreadEvent (@ESPList A)) ?v
          (Build_ThreadEvent _ (ResEv lgetCounter _)),
        Hevent : @eq (@ThreadEvent (@ESPList A))
          (Build_ThreadEvent _ (ResEv lgetCounter _)) ?v |- _ =>
          is_var v; rewrite Htarget in Hevent;
          pose proof (f_equal getCounter_response_result Hevent) as Hresult;
          cbv [getCounter_response_result] in Hresult;
          simpl in Hresult; inversion Hresult; subst; auto
      end).
      all: try discriminate.
    Qed.

    Lemma counter_row_res_update actor owner remaining acc count :
      AssertionsSingle.PUpdate (source_G actor)
        (Build_ThreadEvent actor
          (ResEv (family_call owner lgetCounter) count))
        (CounterPending actor (owner :: remaining) acc owner)
        (CounterFold actor remaining (Nat.add acc count)).
    Proof.
      intros sigma1 rho1 pi1 [Hfold [s Hrowpending]] sigma2 Hstep.
      destruct Hfold as [HIpre [Hlin
        [base [rows [a [visited [saved
          [Erows [Ea [Hparts [Hpending
            [Hsaved [Hbase [Hlower Hupper]]]]]]]]]]]]]].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows0 & a0 & Erows0 & Ea0 & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea, Erows0, Ea0, Hrowpending.
      subst sigma1 rho1.
      assert (rows0 = rows) by congruence. subst rows0.
      assert (a0 = a) by congruence. subst a0.
      change (StepIndexedFamily D (@SPListIndexedObject A)
        (Build_ThreadEvent actor
          (ResEv (family_call owner lgetCounter) count))
        rows sigma2) in Hstep.
      dependent destruction Hstep. simpl in *. unfold owner0 in *.
      rewrite Hrowpending in H1. inversion H1; subst row.
      destruct (step_getCounter_res_shape owner actor s count row' H2)
        as [Hcount Erow']. subst count row'.
      assert (Hroweq : forall q,
          row_counter_at rows q =
          row_counter_at (TMap.add owner (Ready s) rows) q).
      { eapply row_counter_add_control; [exact Hrowpending|reflexivity]. }
      assert (Howner_counter : row_counter_at rows owner = counter s).
      { unfold row_counter_at.
        pose proof (payload_at_find rows owner
          (AtomicPending s actor lgetCounter) Hrowpending) as Hpayload.
        rewrite Hpayload. reflexivity. }
      assert (HIpost : source_I
        (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
          (TMap.add owner (Ready s) rows) (ArrayReady a) pi1)).
      { exists (TMap.add owner (Ready s) rows), a. simpl.
        split; [reflexivity|]. split; [reflexivity|]. split.
        - eapply represents_change_control; eauto.
        - split; assumption. }
      pupdate_finish. split.
      - split; [exact HIpost|]. split; [exact Hlin|].
        exists base, (TMap.add owner (Ready s) rows), a,
          (visited ++ owner :: nil), saved.
        repeat split; try assumption.
        + rewrite Hparts. rewrite <- app_assoc. reflexivity.
        + intros q. rewrite <- Hroweq. apply Hbase.
        + rewrite sum_row_counters_snoc.
          specialize (Hbase owner). rewrite Howner_counter in Hbase. lia.
        + rewrite sum_row_counters_snoc.
          rewrite <- (sum_row_counters_ext visited rows
            (TMap.add owner (Ready s) rows) Hroweq).
          rewrite <- Hroweq, Howner_counter. lia.
      - unfold source_G. repeat split; simpl; auto.
        + intros observer a1 a2 E1 E2 Hneq.
          assert (a1 = a) by congruence. assert (a2 = a) by congruence.
          subst. reflexivity.
        + intros q s0 pending_actor op Hlock Hforeign.
          destruct (PositiveMap.E.eq_dec q owner) as [->|Hneq].
          * rewrite Hrowpending in Hlock. inversion Hlock. congruence.
          * rewrite TMap.gso by exact Hneq. exact Hlock.
        + intro q. rewrite <- Hroweq. lia.
        + intros observer a1 a2 E1 E2 Hneq.
          assert (a1 = a) by congruence. assert (a2 = a) by congruence.
          subst. reflexivity.
    Qed.

    Lemma no_getCounter_error owner actor row :
      ~ @ErrorSPList A owner
          (Build_ThreadEvent actor (InvEv lgetCounter)) row.
    Proof.
      intro Herror. inversion Herror.
      all: pose proof (f_equal splist_event_kind H0) as Hkind;
        simpl in Hkind; discriminate.
    Qed.

    Lemma counter_fold_no_error actor owner remaining acc :
      ⊨ CounterFold actor (owner :: remaining) acc ==>>
        AssertionsSingle.A.ANoError
          (Build_ThreadEvent actor
            (InvEv (family_call owner lgetCounter))).
    Proof.
      intros w [HI [Hlin
        [base [rows [a [visited [saved
          [Erows [Ea [Hparts [Hpending
            [Hsaved [Hbase [Hlower Hupper]]]]]]]]]]]]]] Herror.
      destruct HI as
        (rows0 & a0 & Erows0 & Ea0 & Hrep & Hscan & Hcounter).
      assert (rows0 = rows) by congruence. subst rows0.
      assert (a0 = a) by congruence. subst a0.
      assert (Howner : ThreadDomain.contains D owner).
      { unfold ThreadDomain.contains. rewrite Hparts.
        apply in_or_app. right. simpl. auto. }
      change (ErrorIndexedFamily D (@SPListIndexedObject A)
        (Build_ThreadEvent actor (InvEv (family_call owner lgetCounter)))
        (SinglePossState.σ w)) in Herror.
      rewrite Erows in Herror. inversion Herror; subst; simpl in *.
      - eapply no_getCounter_error. exact H2.
      - contradiction.
      - destruct (proj2 (rep_domain _ _ Hrep owner) Howner) as [row Hrow].
        change (option_map row_payload (TMap.find owner
          (SinglePossState.σ w)) = Some row) in Hrow.
        pose proof (f_equal (option_map row_payload) H5) as Hnone.
        simpl in Hnone.
        pose proof (eq_trans (eq_sym Hrow) Hnone) as Hcontra.
        discriminate Hcontra.
    Qed.

    Lemma counter_start_fold_update actor :
      AssertionsSingle.PUpdateId (source_G actor)
        (CounterReady actor)
        (CounterFold actor (ThreadDomain.threads D) 0).
    Proof.
      intros rows a pi Hready.
      destruct (counter_start_update actor rows a pi Hready)
        as (a' & pi' & Hsteps & Hstarted & HG).
      exists a', pi'. split; [exact Hsteps|]. split; [|exact HG].
      apply counter_started_entails_fold. exact Hstarted.
    Qed.

    Lemma scan_token_finish_counter a pi actor result :
      scan_token_consistent a pi ->
      TMap.find actor pi = Some (ls_lini array_getCounter) ->
      scan_token_consistent (finish_counter actor a)
        (TMap.add actor (ls_linr array_getCounter result) pi).
    Proof.
      intros Hconsistent Hlin caller p c Hscan Hcurrent.
      destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
      - pose proof (Hconsistent actor p c Hscan Hcurrent) as Hbad.
        rewrite Hlin in Hbad. dependent destruction Hbad.
      - rewrite TMap.gso by exact Hneq. eapply Hconsistent; eauto.
    Qed.

    Lemma counter_token_finish_counter a pi actor result :
      counter_token_consistent a pi ->
      counter_token_consistent (finish_counter actor a)
        (TMap.add actor (ls_linr array_getCounter result) pi).
    Proof.
      intros Hconsistent caller saved Hfind.
      destruct (PositiveMap.E.eq_dec caller actor) as [->|Hneq].
      - unfold finish_counter in Hfind. cbn in Hfind.
        rewrite TMap.grs in Hfind. discriminate.
      - rewrite TMap.gso by exact Hneq. eapply Hconsistent.
        unfold finish_counter in Hfind. cbn in Hfind.
        rewrite TMap.gro in Hfind by exact Hneq. exact Hfind.
    Qed.

    Lemma counter_finish_update actor result :
      AssertionsSingle.PUpdateId (source_G actor)
        (CounterFold actor nil result)
        (Completed actor array_getCounter result).
    Proof.
      intros rows a pi [HIpre [Hlin
        [base [rows0 [a0 [visited [saved
          [Erows [Ea [Hparts [Hpending
            [Hsaved [Hbase [Hlower Hupper]]]]]]]]]]]]]].
      pose proof HIpre as HIpre0.
      destruct HIpre as
        (rows1 & a1 & Erows1 & Ea1 & Hrep & Hscan & Hcounter).
      simpl in Erows, Ea, Erows1, Ea1. subst rows a.
      assert (rows1 = rows0) by congruence. subst rows1.
      assert (a1 = a0) by congruence. subst a1.
      rewrite app_nil_r in Hparts. subst visited.
      assert (Htotal :
          sum_row_counters (ThreadDomain.threads D) rows0 =
          total_counter D a0).
      { symmetry. apply represents_total_counter. exact Hrep. }
      exists (ArrayReady (finish_counter actor a0)).
      exists (TMap.add actor (ls_linr array_getCounter result) pi).
      split.
      - apply rt_step. eapply ps_ret.
        + eapply step_counter_res;
            [exact Hpending|rewrite Hsaved; exact Hlower|
              rewrite <- Htotal; exact Hupper|reflexivity].
        + exact Hlin.
      - assert (HIpost : source_I
          (@SinglePossState.Build_ProofStateSingle _ _ (li_lts E) (li_lts F)
            rows0 (ArrayReady (finish_counter actor a0))
            (TMap.add actor (ls_linr array_getCounter result) pi))).
        { exists rows0, (finish_counter actor a0). simpl.
          split; [reflexivity|]. split; [reflexivity|]. split.
          - apply represents_finish_counter. exact Hrep.
          - split.
            + eapply scan_token_finish_counter; eauto.
            + eapply counter_token_finish_counter; eauto. }
        split.
        + split; [exact HIpost|]. unfold ALin. simpl. rewrite TMap.gss.
          reflexivity.
        + eapply source_G_same_concrete.
          * exact HIpre0.
          * exact HIpost.
          * reflexivity.
          * intros observer Hneq. simpl. rewrite TMap.gso by exact Hneq.
            reflexivity.
          * intros observer a2 a3 E2 E3 Hneq.
            inversion E2; inversion E3; subst. reflexivity.
          * intros observer a2 a3 E2 E3 Hneq.
            inversion E2; inversion E3; subst.
            unfold finish_counter. cbn. rewrite TMap.gro by exact Hneq.
            reflexivity.
    Qed.

    Lemma counter_exit_triple actor result :
      SetLogic.HTripleProvable (R actor) (G actor) SI actor
        (lift_assert (CounterFold actor nil result))
        (Ret result)
        (fun ret => SCompleted actor array_getCounter ret).
    Proof.
      eapply singleton_provable_linstep with
        (P' := Completed actor array_getCounter result).
      - apply completed_entails_I.
      - apply completed_stable.
      - apply counter_finish_update.
      - eapply singleton_provable_ret_safe.
        + apply ImplRefl.
        + apply completed_entails_I.
        + apply completed_stable.
    Qed.

    Lemma counter_step_triple actor owner remaining acc :
      SetLogic.HTripleProvable (R actor) (G actor) SI actor
        (lift_assert (CounterFold actor (owner :: remaining) acc))
        (counter_step D acc owner)
        (fun acc' => lift_assert (CounterFold actor remaining acc')).
    Proof.
      unfold counter_step.
      eapply singleton_provable_vis_safe with
        (P' := CounterPending actor (owner :: remaining) acc owner)
        (Q' := fun count =>
          CounterFold actor remaining (Nat.add acc count)).
      - apply counter_fold_no_error.
      - apply counter_pending_entails_I.
      - intros. apply counter_fold_entails_I.
      - apply counter_pending_stable.
      - intros. apply counter_fold_stable.
      - apply counter_row_inv_update.
      - intros. apply counter_row_res_update.
      - intros count. eapply singleton_provable_ret_safe.
        + apply ImplRefl.
        + apply counter_fold_entails_I.
        + apply counter_fold_stable.
    Qed.

    Lemma counter_foreach_triple actor :
      SetLogic.HTripleProvable (R actor) (G actor) SI actor
        (lift_assert
          (CounterFold actor (ThreadDomain.threads D) 0))
        (getCounter_impl D actor)
        (fun ret => SCompleted actor array_getCounter ret).
    Proof.
      unfold getCounter_impl.
      eapply SetLogic.provable_foreach
        with (Inv := fun remaining acc =>
          lift_assert (CounterFold actor remaining acc)).
      - apply counter_exit_triple.
      - intros item items acc. apply counter_step_triple.
    Qed.

    Lemma getCounter_method_triple actor :
      SetLogic.HTripleProvable (R actor) (G actor) SI actor
        (SActive actor array_getCounter)
        (getCounter_impl D actor)
        (fun ret => SCompleted actor array_getCounter ret).
    Proof.
      eapply SetLogic.provable_perror with
        (P' := lift_assert (CounterReady actor)).
      - intros s Hactive. eapply lift_counter_ready_or_error; eauto.
      - eapply singleton_provable_linstep with
          (P' := CounterFold actor (ThreadDomain.threads D) 0).
        + apply counter_fold_entails_I.
        + apply counter_fold_stable.
        + apply counter_start_fold_update.
        + apply counter_foreach_triple.
    Qed.

    Lemma active_closes_invariant actor m :
      ⊨ SActive actor m ==>> SI.
    Proof.
      intros w Hactive. eapply lift_impl; [apply active_entails_I|exact Hactive].
    Qed.

    Program Definition MSPListArray : layer_implementation_simulation E F :=
      {| li_impl := splist_array_impl D |}.
    Next Obligation.
      eapply SetLogic.soundness with (R := R) (G := G) (I := SI).
      - exact valid_rg.
      - exact parallel_compatible.
      - intros actor m. destruct m as [v|loc ts|owner| |owner loc|].
        + exists (SActive actor (array_insert v)).
          exists (fun ret => SCompleted actor (array_insert v) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret sigma Delta Hcompleted rho pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply insert_method_triple.
        + exists (SActive actor (array_setTS loc ts)).
          exists (fun ret => SCompleted actor (array_setTS loc ts) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret sigma Delta Hcompleted rho pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply setTS_method_triple.
        + exists (SActive actor (array_getTop owner)).
          exists (fun ret => SCompleted actor (array_getTop owner) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret sigma Delta Hcompleted rho pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply getTop_method_triple.
        + exists (SActive actor array_resetIter).
          exists (fun ret => SCompleted actor array_resetIter ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret sigma Delta Hcompleted rho pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply reset_method_triple.
        + exists (SActive actor (array_tryRemove owner loc)).
          exists (fun ret => SCompleted actor (array_tryRemove owner loc) ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret sigma Delta Hcompleted rho pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply tryRemove_method_triple.
        + exists (SActive actor array_getCounter).
          exists (fun ret => SCompleted actor array_getCounter ret).
          constructor.
          * intros w Hcompose. eapply set_ginv_exposes_active; exact Hcompose.
          * apply active_closes_invariant.
          * apply lift_stable. apply active_stable.
          * intros ret w Hcompose. eapply set_gret_closes_completed;
              exact Hcompose.
          * intros ret sigma Delta Hcompleted rho pi Hposs.
            eapply completed_has_return_token; eauto.
          * apply getCounter_method_triple.
      - exact initial_SI.
    Qed.

    Definition MSPListArrayLinearizable :
        layer_implementation_linearizability E F :=
      LISim2LILin MSPListArray.

    Definition compose_splist_array :
        layer_implementation_linearizability
          (@SPListFamilyImpl.TensorSPListUnderlay A D) F :=
      LIVComp (@SPListFamilyImpl.compose_splist_family A D)
        MSPListArrayLinearizable.
  End Proof.
End SPListArrayProof.
