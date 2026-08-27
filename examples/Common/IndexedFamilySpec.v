Require Import FMapPositive.
Require Import Coq.Lists.List.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulation.
Require Import examples.Common.ThreadDomain.


(** A common interface for a finite, tid-indexed family of uniform
    objects.  Components have the same operation signature and state type,
    but their transition systems may depend on the owner tid. *)
Module IndexedFamilySpec.
  Import Reg.
  Import LTSSpec.
  Import LinCCALBase.
  Import TPSimulation.

  Record IndexedObject (E : Op.t) : Type := {
    component_state : Type;
    component_step :
      tid -> @ThreadEvent E -> component_state -> component_state -> Prop;
    component_error :
      tid -> @ThreadEvent E -> component_state -> Prop;
    component_init : tid -> component_state;
  }.
  Arguments component_state {E} _.
  Arguments component_step {E} _ _ _ _ _.
  Arguments component_error {E} _ _ _ _.
  Arguments component_init {E} _ _.

  Section Family.
    Context {E : Op.t}.
    Context (D : ThreadDomain.t).
    Context (O : IndexedObject E).

    Variant EIndexed_op :=
    | indexed_call (owner : tid) (op : Sig.op E).

    Definition EIndexed_ar (m : EIndexed_op) : Type :=
      match m with
      | indexed_call _ op => Sig.ar op
      end.

    Canonical Structure EIndexed : Op.t :=
    {|
      Sig.op := EIndexed_op;
      Sig.ar := EIndexed_ar
    |}.

    Definition indexed_owner (m : EIndexed_op) : tid :=
      match m with indexed_call owner _ => owner end.

    Definition indexed_event_op (ev : @Event EIndexed) : EIndexed_op :=
      match ev with
      | InvEv op => op
      | ResEv op _ => op
      end.

    Definition project_event (ev : @Event EIndexed) : @Event E :=
      match ev with
      | InvEv (indexed_call _ op) => InvEv op
      | ResEv (indexed_call _ op) ret => ResEv op ret
      end.

    Definition project_thread_event
        (ev : @ThreadEvent EIndexed) : @ThreadEvent E :=
      {|
        te_tid := te_tid ev;
        te_ev := project_event (te_ev ev)
      |}.

    Definition FamilyState : Type := TMap.t (component_state O).

    Fixpoint initial_rows (owners : list tid) : FamilyState :=
      match owners with
      | nil => TMap.empty (component_state O)
      | owner :: owners' =>
          TMap.add owner (component_init O owner) (initial_rows owners')
      end.

    Definition initial_family_state : FamilyState :=
      initial_rows (ThreadDomain.threads D).

    Variant StepIndexedFamily :
        @ThreadEvent EIndexed -> FamilyState -> FamilyState -> Prop :=
    | step_indexed_family ev rows row row' :
        let owner := indexed_owner (indexed_event_op (te_ev ev)) in
        ThreadDomain.contains D owner ->
        TMap.find owner rows = Some row ->
        component_step O owner (project_thread_event ev) row row' ->
        StepIndexedFamily ev rows (TMap.add owner row' rows).

    Variant ErrorIndexedFamily :
        @ThreadEvent EIndexed -> FamilyState -> Prop :=
    | error_indexed_family_inner ev rows row :
        let owner := indexed_owner (indexed_event_op (te_ev ev)) in
        ThreadDomain.contains D owner ->
        TMap.find owner rows = Some row ->
        component_error O owner (project_thread_event ev) row ->
        ErrorIndexedFamily ev rows
    | error_indexed_owner_outside actor owner op rows :
        ~ ThreadDomain.contains D owner ->
        ErrorIndexedFamily
          {| te_tid := actor; te_ev := InvEv (indexed_call owner op) |}
          rows
    | error_indexed_owner_missing actor owner op rows :
        ThreadDomain.contains D owner ->
        TMap.find owner rows = None ->
        ErrorIndexedFamily
          {| te_tid := actor; te_ev := InvEv (indexed_call owner op) |}
          rows.

    Definition VIndexedFamily : @LTS EIndexed :=
    {|
      State := FamilyState;
      Step := StepIndexedFamily;
      Error := ErrorIndexedFamily
    |}.

    Definition IndexedFamilyLayer : layer_interface :=
    {|
      li_sig := EIndexed;
      li_lts := VIndexedFamily;
      li_init := initial_family_state
    |}.

  End Family.

  Arguments EIndexed_op : clear implicits.
  Arguments indexed_call {E} _ _.
  Arguments EIndexed : clear implicits.
  Arguments indexed_owner {E} _.
  Arguments project_event {E} _.
  Arguments project_thread_event {E} _.
  Arguments FamilyState {E} O.
  Arguments initial_rows {E} O _.
  Arguments initial_family_state {E} D O.
  Arguments VIndexedFamily {E} D O.
  Arguments IndexedFamilyLayer {E} D O.

End IndexedFamilySpec.
