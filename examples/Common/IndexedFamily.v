Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulationSet.
Require Import CompLin.
Require Import CompLinHComp.
Require Import CompLinLayer.
Require Import examples.Common.ThreadDomain.
Require Import examples.Common.IndexedFamilySpec.


(** Runtime packaging of a non-empty, right-associated tensor of uniform
    objects as an [IndexedFamilySpec] object. *)
Module IndexedFamilyImpl.
  Import Reg.
  Import LTSSpec.
  Import LinCCALBase.
  Import Lang.
  Import TPSimulationSet.TPSimulation.
  Import CompLinLayer.
  Import IndexedFamilySpec.

  Lemma tmap_add_comm {X : Type}
      (i j : tid) (x y : X) (m : TMap.t X) :
      i <> j ->
      TMap.add i x (TMap.add j y m) =
      TMap.add j y (TMap.add i x m).
  Proof.
    revert j m. induction i; intros j m Hneq; destruct j;
      destruct m; simpl in *; try congruence; f_equal; auto;
      apply IHi; congruence.
  Qed.

  Lemma tmap_add_shadow {X : Type}
      (i : tid) (x y : X) (m : TMap.t X) :
      TMap.add i x (TMap.add i y m) = TMap.add i x m.
  Proof.
    revert m. induction i; intros m; destruct m; simpl; f_equal; auto.
  Qed.

  Section TensorFamily.
    Context {E : Op.t}.
    Context (O : IndexedObject E).

    Definition ComponentLTS (owner : tid) : @LTS E :=
      {|
        State := component_state O;
        Step := component_step O owner;
        Error := component_error O owner
      |}.

    Definition ComponentLayer (owner : tid) : layer_interface :=
      @Build_layer_interface
        E (ComponentLTS owner) (component_init O owner).

    Definition SetComponentLayer (owner : tid) : layer_interface :=
      ComponentLayer owner.

    (** [TensorFrom first rest] represents exactly [first :: rest].
        There is deliberately no empty tensor and hence no need for a
        distinguished/default thread. *)
    Fixpoint TensorFrom (first : tid) (rest : list tid) : layer_interface :=
      match rest with
      | nil => SetComponentLayer first
      | next :: tail =>
          layer_interface_hcomp
            (SetComponentLayer first) (TensorFrom next tail)
      end.

    Definition TensorLayer (D : ThreadDomain.t) : layer_interface :=
      TensorFrom (ThreadDomain.first_thread D)
        (ThreadDomain.other_threads D).

    CoFixpoint diverge {X : Op.t} {R : Type} : Prog X R :=
      Tau diverge.

    Fixpoint dispatch_from
        (first : tid) (rest : list tid)
        (owner : tid) (op : Sig.op E) :
        Prog (li_sig (TensorFrom first rest)) (Sig.ar op) :=
      match rest as owners
        return Prog (li_sig (TensorFrom first owners)) (Sig.ar op)
      with
      | nil =>
          if Pos.eq_dec owner first
          then Vis op (fun ret => Ret ret)
          else diverge
      | next :: tail =>
          if Pos.eq_dec owner first
          then @Vis (li_sig (TensorFrom first (next :: tail)))
                 (Sig.ar op)
                 (@inl (Sig.op E)
                   (Sig.op (li_sig (TensorFrom next tail))) op)
                 (fun ret => Ret ret)
          else CompLinHComp.CompLinHComp.liftRightProg
                 (dispatch_from next tail owner op)
      end.

    Definition dispatch
        (D : ThreadDomain.t) (owner : tid) (op : Sig.op E) :
        Prog (li_sig (TensorLayer D)) (Sig.ar op) :=
      dispatch_from (ThreadDomain.first_thread D)
        (ThreadDomain.other_threads D) owner op.

    Inductive RoutesFrom :
        forall (first : tid) (rest : list tid) (owner : tid)
          (op : Sig.op E),
          Sig.op (li_sig (TensorFrom first rest)) -> Prop :=
    | routes_only owner op :
        RoutesFrom owner nil owner op op
    | routes_head first next tail op :
        RoutesFrom first (next :: tail) first op
          (@inl (Sig.op E)
            (Sig.op (li_sig (TensorFrom next tail))) op)
    | routes_tail first next tail owner op nested :
        owner <> first ->
        RoutesFrom next tail owner op nested ->
        RoutesFrom first (next :: tail) owner op
          (@inr (Sig.op E)
            (Sig.op (li_sig (TensorFrom next tail))) nested).

    Inductive RoutesReturn :
        forall (first : tid) (rest : list tid) (owner : tid)
          (op : Sig.op E) (nested : Sig.op (li_sig (TensorFrom first rest))),
          Sig.ar nested -> Sig.ar op -> Prop :=
    | routes_return_only owner op ret :
        RoutesReturn owner nil owner op op ret ret
    | routes_return_head first next tail op ret :
        RoutesReturn first (next :: tail) first op
          (@inl (Sig.op E)
            (Sig.op (li_sig (TensorFrom next tail))) op) ret ret
    | routes_return_tail first next tail owner op nested nested_ret ret :
        owner <> first ->
        RoutesReturn next tail owner op nested nested_ret ret ->
        RoutesReturn first (next :: tail) owner op
          (@inr (Sig.op E)
            (Sig.op (li_sig (TensorFrom next tail))) nested) nested_ret ret.

    Lemma dispatch_from_valid_full first rest owner op :
      NoDup (first :: rest) ->
      In owner (first :: rest) ->
      exists nested k,
        RoutesFrom first rest owner op nested /\
        dispatch_from first rest owner op = Vis nested k /\
        forall nested_ret, exists ret,
          k nested_ret = Ret ret /\
          RoutesReturn first rest owner op nested nested_ret ret.
    Proof.
      revert first. induction rest as [| next tail IH].
      - intros first Hnodup Hin. simpl in Hin.
        destruct Hin as [Heq | []]. subst first. simpl.
        destruct (Pos.eq_dec owner owner); [|contradiction].
        do 2 eexists. repeat split; try constructor; auto.
        intro nested_ret. exists nested_ret. split; [reflexivity|constructor].
      - intros first Hnodup Hin.
        inversion Hnodup as [| first' rest' Hfirst Hrest]; subst.
        simpl. destruct (Pos.eq_dec owner first) as [Heq | Hneq].
        + subst first. do 2 eexists. repeat split; try constructor; auto.
          intro nested_ret. exists nested_ret. split; [reflexivity|constructor].
        + destruct Hin as [Heq | Hin]; [congruence|].
          destruct (IH next Hrest Hin) as
            [nested [k [Hroute [Hdispatch Hreturns]]]].
          exists (@inr (Sig.op E)
            (Sig.op (li_sig (TensorFrom next tail))) nested).
          exists (fun ret =>
            CompLinHComp.CompLinHComp.liftRightProg (E1 := E) (k ret)).
          repeat split.
          * constructor; assumption.
          * rewrite Hdispatch.
            apply CompLinHComp.CompLinHComp.liftRightProgVis.
          * intro nested_ret.
            destruct (Hreturns nested_ret) as [ret [Hk Hreturn]].
            exists ret. split.
            -- rewrite Hk.
               apply CompLinHComp.CompLinHComp.liftRightProgRet.
            -- constructor; assumption.
    Qed.

    Definition pack_impl (D : ThreadDomain.t) :
        ModuleImpl (li_sig (TensorLayer D))
          (li_sig (IndexedFamilyLayer D O)) :=
      fun indexed_op _actor =>
        match indexed_op with
        | indexed_call owner op => dispatch D owner op
        end.

    (** Flattening is the representation relation used by the packaging
        proof.  It exposes tensor components as a finite map without
        changing their local state or separation algebra. *)
    Fixpoint flatten_from
        (first : tid) (rest : list tid) :
        State (li_lts (TensorFrom first rest)) ->
        TMap.t (component_state O) :=
      match rest as owners
        return State (li_lts (TensorFrom first owners)) ->
               TMap.t (component_state O)
      with
      | nil => fun state =>
          TMap.add first state (TMap.empty (component_state O))
      | next :: tail => fun state =>
          TMap.add first (fst state)
            (flatten_from next tail (snd state))
      end.

    Definition flatten (D : ThreadDomain.t) :
        State (li_lts (TensorLayer D)) ->
        TMap.t (component_state O) :=
      flatten_from (ThreadDomain.first_thread D)
        (ThreadDomain.other_threads D).

    Lemma flatten_from_initial first rest :
      flatten_from first rest (li_init (TensorFrom first rest)) =
      initial_rows O (first :: rest).
    Proof.
      revert first. induction rest as [| next tail IH]; intro first; simpl.
      - reflexivity.
      - rewrite IH. reflexivity.
    Qed.

    Lemma flatten_initial (D : ThreadDomain.t) :
      flatten D (li_init (TensorLayer D)) =
      initial_family_state D O.
    Proof.
      unfold flatten, TensorLayer, initial_family_state.
      apply flatten_from_initial.
    Qed.

    Lemma flatten_from_route_find first rest owner op nested state :
      RoutesFrom first rest owner op nested ->
      exists row, TMap.find owner (flatten_from first rest state) = Some row.
    Proof.
      intros Hroute. induction Hroute.
      - exists state. simpl. apply TMap.gss.
      - exists (fst state). simpl. apply TMap.gss.
      - destruct state as [head tail_state]. simpl.
        destruct (IHHroute tail_state) as [row Hfind]. exists row.
        rewrite TMap.gso by congruence. exact Hfind.
    Qed.

    Lemma routes_inv_step_sound
        (D : ThreadDomain.t) first rest owner op nested actor state state' :
      RoutesFrom first rest owner op nested ->
      Step (li_lts (TensorFrom first rest))
        {| te_tid := actor; te_ev := InvEv nested |} state state' ->
      ThreadDomain.contains D owner ->
      Step (li_lts (IndexedFamilyLayer D O))
        {| te_tid := actor;
           te_ev := InvEv (indexed_call owner op) |}
        (flatten_from first rest state)
        (flatten_from first rest state').
    Proof.
      intros Hroute. induction Hroute; intros Hstep Hcontains.
      - simpl in Hstep |- *.
        assert (Hfamily := @step_indexed_family E D O
          {| te_tid := actor; te_ev := InvEv (indexed_call owner op) |}
          (TMap.add owner state (TMap.empty (component_state O)))
          state state' Hcontains (@TMap.gss (component_state O) owner state
            (TMap.empty (component_state O))) Hstep).
        rewrite tmap_add_shadow in Hfamily. exact Hfamily.
      - destruct state as [head tail_state].
        destruct state' as [head' tail_state'].
        simpl in Hstep |- *. destruct Hstep as [Hstep Htail]. subst tail_state'.
        assert (Hfamily := @step_indexed_family E D O
          {| te_tid := actor; te_ev := InvEv (indexed_call first op) |}
          (TMap.add first head
            (flatten_from next tail tail_state))
          head head' Hcontains
          (@TMap.gss (component_state O) first head
            (flatten_from next tail tail_state)) Hstep).
        rewrite tmap_add_shadow in Hfamily. exact Hfamily.
      - destruct state as [head tail_state].
        destruct state' as [head' tail_state'].
        simpl in Hstep |- *. destruct Hstep as [Hstep Hhead]. subst head'.
        specialize (IHHroute tail_state tail_state' Hstep Hcontains).
        inversion IHHroute as
          [ev rows row row' Hcontains' Hfind Hcomponent]; subst.
        subst Hcontains'.
        simpl in Hfind, Hcomponent, H0, H3.
        assert (Hfind_global :
          TMap.find owner
            (TMap.add first head (flatten_from next tail tail_state)) =
          Some row).
        { rewrite TMap.gso by congruence. exact Hcomponent. }
        assert (Hfamily := @step_indexed_family E D O
          {| te_tid := actor; te_ev := InvEv (indexed_call owner op) |}
          (TMap.add first head (flatten_from next tail tail_state))
          row row' Hcontains Hfind_global H0).
        simpl in Hfamily.
        rewrite (tmap_add_comm owner first row' head
          (flatten_from next tail tail_state)) in Hfamily by congruence.
        exact Hfamily.
    Qed.

    Lemma routes_return_res_step_sound
        (D : ThreadDomain.t) first rest owner op nested actor
        (nested_ret : Sig.ar nested) (ret : Sig.ar op) state state' :
      RoutesReturn first rest owner op nested nested_ret ret ->
      Step (li_lts (TensorFrom first rest))
        {| te_tid := actor; te_ev := ResEv nested nested_ret |} state state' ->
      ThreadDomain.contains D owner ->
      Step (li_lts (IndexedFamilyLayer D O))
        {| te_tid := actor;
           te_ev := ResEv (indexed_call owner op) ret |}
        (flatten_from first rest state)
        (flatten_from first rest state').
    Proof.
      intros Hreturn. induction Hreturn; intros Hstep Hcontains.
      - simpl in Hstep |- *.
        assert (Hfamily := @step_indexed_family E D O
          {| te_tid := actor; te_ev := ResEv (indexed_call owner op) ret |}
          (TMap.add owner state (TMap.empty (component_state O)))
          state state' Hcontains (@TMap.gss (component_state O) owner state
            (TMap.empty (component_state O))) Hstep).
        rewrite tmap_add_shadow in Hfamily. exact Hfamily.
      - destruct state as [head tail_state].
        destruct state' as [head' tail_state'].
        simpl in Hstep |- *. destruct Hstep as [Hstep Htail]. subst tail_state'.
        assert (Hfamily := @step_indexed_family E D O
          {| te_tid := actor; te_ev := ResEv (indexed_call first op) ret |}
          (TMap.add first head (flatten_from next tail tail_state))
          head head' Hcontains
          (@TMap.gss (component_state O) first head
            (flatten_from next tail tail_state)) Hstep).
        rewrite tmap_add_shadow in Hfamily. exact Hfamily.
      - destruct state as [head tail_state].
        destruct state' as [head' tail_state'].
        simpl in Hstep |- *. destruct Hstep as [Hstep Hhead]. subst head'.
        specialize (IHHreturn tail_state tail_state' Hstep Hcontains).
        inversion IHHreturn as
          [ev rows row row' Hcontains' Hfind Hcomponent]; subst.
        subst Hcontains'. simpl in Hfind, Hcomponent, H0, H3.
        assert (Hfind_global :
          TMap.find owner
            (TMap.add first head (flatten_from next tail tail_state)) =
          Some row).
        { rewrite TMap.gso by congruence. exact Hcomponent. }
        assert (Hfamily := @step_indexed_family E D O
          {| te_tid := actor;
             te_ev := ResEv (indexed_call owner op) ret |}
          (TMap.add first head (flatten_from next tail tail_state))
          row row' Hcontains Hfind_global H0).
        simpl in Hfamily.
        rewrite (tmap_add_comm owner first row' head
          (flatten_from next tail tail_state)) in Hfamily by congruence.
        exact Hfamily.
    Qed.

    Lemma routes_error_sound
        (D : ThreadDomain.t) first rest owner op nested actor state :
      forall (Hroute : RoutesFrom first rest owner op nested),
      Error (li_lts (TensorFrom first rest))
        {| te_tid := actor; te_ev := InvEv nested |} state ->
      ThreadDomain.contains D owner ->
      Error (li_lts (IndexedFamilyLayer D O))
        {| te_tid := actor;
           te_ev := InvEv (indexed_call owner op) |}
        (flatten_from first rest state).
    Proof.
      intros Hroute. induction Hroute; intros Herror Hcontains.
      - simpl in Herror |- *.
        econstructor; simpl; eauto. apply TMap.gss.
      - destruct state as [head tail_state]. simpl in Herror |- *.
        econstructor; simpl; eauto. apply TMap.gss.
      - destruct state as [head tail_state]. simpl in Herror |- *.
        specialize (IHHroute tail_state Herror Hcontains).
        inversion IHHroute as
          [ev rows row Howner Hinside Hfind Herr
          | actor0 owner0 op0 rows Houtside
          | actor0 owner0 op0 rows Hinside Hnone]; subst.
        + subst Howner. simpl in Hinside, Hfind, Herr.
          econstructor; simpl in *; eauto.
          rewrite TMap.gso by congruence. exact Hfind.
        + contradiction.
        + destruct (flatten_from_route_find next tail owner op nested
            tail_state Hroute) as [row Hrow]. congruence.
    Qed.

    Lemma dispatch_from_outside_tau first rest owner op :
      ~ In owner (first :: rest) ->
      exists p, dispatch_from first rest owner op = Tau p.
    Proof.
      revert first. induction rest as [| next tail IH];
        intros first Houtside; simpl in *.
      - destruct (Pos.eq_dec owner first) as [Heq | Hneq].
        + subst. exfalso. apply Houtside. auto.
        + exists (@diverge (li_sig (TensorFrom first nil)) (Sig.ar op)).
          rewrite Lang.PPid at 1. reflexivity.
      - destruct (Pos.eq_dec owner first) as [Heq | Hneq].
        + subst. exfalso. apply Houtside. auto.
        + destruct (IH next) as [p Hp].
          * intro Hin. apply Houtside. right. exact Hin.
          * exists (CompLinHComp.CompLinHComp.liftRightProg
              (E1 := E) p).
            rewrite Hp.
            rewrite CompLinHComp.CompLinHComp.liftRightProgTau.
            reflexivity.
    Qed.

    Lemma dispatch_outside_tau (D : ThreadDomain.t) owner op :
      ~ ThreadDomain.contains D owner ->
      exists p, dispatch D owner op = Tau p.
    Proof.
      unfold dispatch, TensorLayer, ThreadDomain.contains,
        ThreadDomain.threads.
      apply dispatch_from_outside_tau.
    Qed.

  End TensorFamily.

  Arguments ComponentLTS {E} O owner.
  Arguments ComponentLayer {E} O owner.
  Arguments SetComponentLayer {E} O owner.
  Arguments TensorFrom {E} O first rest.
  Arguments TensorLayer {E} O D.
  Arguments dispatch_from {E} O first rest owner op.
  Arguments dispatch {E} O D owner op.
  Arguments pack_impl {E} O D.
  Arguments flatten_from {E} O first rest _.
  Arguments flatten {E} O D _.

  Section HorizontalComposition.
    Context {E : Op.t}.
    Context (O : IndexedObject E).
    Context (Underlay : tid -> layer_interface).
    Context (component_correct : forall owner,
      layer_implementation_linearizability
        (Underlay owner) (SetComponentLayer O owner)).

    Fixpoint TensorUnderlayFrom
        (first : tid) (rest : list tid) : layer_interface :=
      match rest with
      | nil => Underlay first
      | next :: tail =>
          layer_interface_hcomp
            (Underlay first) (TensorUnderlayFrom next tail)
      end.

    Fixpoint tensor_components_correct
        (first : tid) (rest : list tid) :
        layer_implementation_linearizability
          (TensorUnderlayFrom first rest) (TensorFrom O first rest) :=
      match rest as owners return
        layer_implementation_linearizability
          (TensorUnderlayFrom first owners) (TensorFrom O first owners)
      with
      | nil => component_correct first
      | next :: tail =>
          LIHComp (component_correct first)
            (tensor_components_correct next tail)
      end.

    Definition TensorUnderlay (D : ThreadDomain.t) : layer_interface :=
      TensorUnderlayFrom (ThreadDomain.first_thread D)
        (ThreadDomain.other_threads D).

    Definition all_components_correct (D : ThreadDomain.t) :
        layer_implementation_linearizability
          (TensorUnderlay D) (TensorLayer O D) :=
      tensor_components_correct (ThreadDomain.first_thread D)
        (ThreadDomain.other_threads D).

    (** Once the generic packaging adapter is discharged, vertical
        composition yields the desired end-to-end family implementation.
        This theorem is the reusable compositional boundary: component
        proofs are combined horizontally, packaging is combined vertically. *)
    Definition compose_indexed_family
        (D : ThreadDomain.t)
        (pack_correct : layer_implementation_linearizability
          (TensorLayer O D) (IndexedFamilyLayer D O)) :
        layer_implementation_linearizability
          (TensorUnderlay D) (IndexedFamilyLayer D O) :=
      LIVComp (all_components_correct D) pack_correct.

  End HorizontalComposition.

End IndexedFamilyImpl.
