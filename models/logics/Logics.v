Require Import models.logics.SeparationAlgebra.

Section PropositionalLogic.
    Context {model : Type}.

    Definition Assertion : Type := model -> Prop.
        
    Definition Conj (P Q : Assertion) : Assertion := fun s => P s /\ Q s.
    Definition Disj (P Q : Assertion) : Assertion := fun s => P s \/ Q s.
    Definition Imply (P Q : Assertion) : Assertion := fun s => P s -> Q s.
    Definition Neg P : Assertion := fun s => ~P s.
    Definition APure (P : Prop) : Assertion := fun _ => P.
    Definition FF : Assertion := fun _ => False.
    Definition TT : Assertion := fun _ => True.

End PropositionalLogic.

#[global] Hint Unfold APure TT FF : core.


Delimit Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Assertion.

Notation "P //\\ Q" := (Conj P Q) (at level 45, right associativity) : assertion_scope.
Notation "P \\// Q" := (Disj P Q) (at level 46, right associativity) : assertion_scope.
Notation "P ==>> Q" := (Imply P Q) (at level 55, right associativity) : assertion_scope.
Notation "P <<==>> Q" := (Imply P Q //\\ Imply Q P)%Assertion (at level 60) : assertion_scope.
(* \ulcorner \urcorner *)
Notation "⌜ P ⌝" := (APure P) (at level 35, format "⌜ P ⌝") : assertion_scope.
Notation "!! P" := (Neg P) (at level 35) : assertion_scope.
Notation "⊨ P" := (forall s, P s) (at level 80, no associativity) : assertion_scope.

Section QuantifierLogic.
  Context {model : Type}.
  
  Definition Exists {A} (P : A -> Assertion) : Assertion :=
    fun s : model => exists v : A, P v s.
  Definition Forall {A} (P : A -> Assertion) : Assertion :=
    fun s : model => forall v : A, P v s.
End QuantifierLogic.

Notation "'∀' x , P" := (Forall (fun x => P)) (at level 60, x binder) : assertion_scope.
Notation "'∃' x , P" := (Exists (fun x => P)) (at level 60, x binder) : assertion_scope.

Notation "'∀' x .. y , P" :=
  (Forall (fun x => .. (Forall (fun y => P)) ..))
  (at level 200, x binder, y binder) : assertion_scope.

Notation "'∃' x .. y , P" :=
  (Exists (fun x => .. (Exists (fun y => P)) ..))
  (at level 200, x binder, y binder) : assertion_scope.

Section SeparationLogic.
  Context {model : Type}.
  Context {J : Join model}.
  Context {SA : SeparationAlgebra model}.

  Definition sepcon (P Q : Assertion) : Assertion :=
    fun s => exists s1 s2, join s1 s2 s /\ P s1 /\ Q s2.
  Definition emp : Assertion :=
    fun s => unit_element s.
  Definition wand (P Q : Assertion) : Assertion :=
    fun s => forall s1 s2, join s s1 s2 -> P s1 -> Q s2.
End SeparationLogic.

Notation "x * y" := (sepcon x y) (at level 40, left associativity) : assertion_scope.
Notation "x -* y" := (wand x y) (at level 55, right associativity) : assertion_scope.

Section SeparationLogicRules.
  Context {model : Type}.
  Context {J : Join model}.
  Context {SA : SeparationAlgebra model}.

  Open Scope assertion_scope.

  Lemma sepcon_comm_impp : forall x y, ⊨ x * y ==>> y * x.
  Proof.
    intros ? ? ? ?. destruct H as [? [? [? [? ?]]]].
    apply join_comm in H.
    do 2 eexists. eauto.
  Qed.
  
  Lemma sepcon_assoc1: forall x y z, ⊨ x * (y * z) ==>> (x * y) * z.
  Proof.
    intros x y z ? [? [? [? [? [? [? [? [? ?]]]]]]]].
    apply join_comm in H, H1.
    pose proof join_assoc _ _ _ _ _ H1 H as [? [? ?]].
    apply join_comm in H5, H4.
    do 2 eexists; do 2 (split; eauto).
    do 2 eexists. eauto.
  Qed.

  Lemma sepcon_assoc2: forall x y z, ⊨ (x * y) * z ==>> x * (y * z).
  Proof.
    intros. intros [? [? [? [[? [? [? [? ?]]]] ?]]]].
    pose proof join_assoc _ _ _ _ _ H0 H as [? [? ?]].
    do 2 eexists; do 2 (split; eauto).
    do 2 eexists; eauto.
  Qed.

  Lemma sepcon_mono: forall x1 x2 y1 y2, ⊨ x1 ==>> x2 -> ⊨ y1 ==>> y2 -> ⊨ (x1 * y1) ==>> (x2 * y2).
  Proof.
    intros. intros [? [? [? [? ?]]]].
    apply H in H2. apply H0 in H3.
    do 2 eexists; eauto.
  Qed.

  Lemma orp_sepcon_left: forall x y z,
    ⊨ (x \\// y) * z ==>> x * z \\// y * z.
  Proof.
    intros. intros [? [? [? [? ?]]]].
    destruct H0; [left | right];
    do 2 eexists; eauto.
  Qed.

  Lemma orp_sepcon_right: forall x y z,
    ⊨ x * z \\// y * z ==>> (x \\// y) * z.
  Proof.
    intros. intros [[? [? [? [? ?]]]] | [? [? [? [? ?]]]]];
    do 2 eexists; do 2 (split; eauto);
    [left | right]; auto.
  Qed.

  Lemma falsep_sepcon_left: forall x,
    ⊨ FF * x ==>> FF.
  Proof.
    intros. intros [? [? [? [? ?]]]].
    inversion H0.
  Qed.

  Lemma sepcon_emp1: forall x, ⊨ x * emp ==>> x.
  Proof.
    intros. intros [? [? [? [? ?]]]].
    apply join_comm, H1 in H; subst; auto.
  Qed.

  Lemma sepcon_emp2 {UE : SeparationAlgebraUnit model SA}: forall x, ⊨ x ==>> x * emp.
  Proof.
    intros. intros ?.
    exists s, ue. split.
    - apply unit_join.
    - split; auto. apply unit_spec.
  Qed.

  Lemma wand_sepcon_adjoint: forall x y z, ⊨ x * y ==>> z <-> ⊨ x ==>> (y -* z).
  Proof.
    split; intros.
    - intros ? ? ? ? ?.
      apply H. do 2 eexists; eauto.
    - intros [? [? [? [? ?]]]].
      apply H in H1. eapply H1 in H2; eauto.
  Qed.

  (** Stable, symmetric forms used by clients. *)
  Lemma sepcon_comm (P Q : @Assertion model) :
    ⊨ P * Q <<==>> Q * P.
  Proof. split; apply sepcon_comm_impp. Qed.

  Lemma sepcon_assoc (P Q R : @Assertion model) :
    ⊨ (P * Q) * R <<==>> P * (Q * R).
  Proof. split; [apply sepcon_assoc2|apply sepcon_assoc1]. Qed.

  Lemma sepcon_consequence (P P' Q Q' : @Assertion model) :
    (⊨ P ==>> P') -> (⊨ Q ==>> Q') ->
    ⊨ P * Q ==>> P' * Q'.
  Proof. apply sepcon_mono. Qed.

  Lemma sepcon_mono_l (P P' Q : @Assertion model) :
    (⊨ P ==>> P') -> ⊨ P * Q ==>> P' * Q.
  Proof. intro H; eapply sepcon_mono; [exact H|firstorder]. Qed.

  Lemma sepcon_mono_r (P Q Q' : @Assertion model) :
    (⊨ Q ==>> Q') -> ⊨ P * Q ==>> P * Q'.
  Proof. intro H; eapply sepcon_mono; [firstorder|exact H]. Qed.

  Lemma sepcon_equiv (P P' Q Q' : @Assertion model) :
    (⊨ P <<==>> P') -> (⊨ Q <<==>> Q') ->
    ⊨ P * Q <<==>> P' * Q'.
  Proof.
    intros HP HQ s; split; intros [s1 [s2 [Hj [H1 H2]]]];
      exists s1, s2; repeat split; auto.
    - apply (proj1 (HP s1)); exact H1.
    - apply (proj1 (HQ s2)); exact H2.
    - apply (proj2 (HP s1)); exact H1.
    - apply (proj2 (HQ s2)); exact H2.
  Qed.

  Section WithUnit.
    Context {UE : @SeparationAlgebraUnit model J SA}.

    Lemma sepcon_emp (P : @Assertion model) : ⊨ P * emp <<==>> P.
    Proof. split; [apply sepcon_emp1|apply sepcon_emp2]. Qed.

    Lemma emp_sepcon (P : @Assertion model) : ⊨ emp * P <<==>> P.
    Proof.
      intros s; split.
      - intro H. apply sepcon_comm_impp in H. apply sepcon_emp1 in H; exact H.
      - intro H. apply sepcon_comm_impp. apply sepcon_emp2; exact H.
    Qed.

    Lemma pure_sepcon_intro (phi : Prop) (P : @Assertion model) :
      phi -> ⊨ P ==>> ⌜phi⌝ * P.
    Proof.
      intros Hphi s HP.
      exists ue, s; repeat split; auto using unit_join_left.
    Qed.

    Lemma pure_sepcon_elim (phi : Prop) (P : @Assertion model) :
      (⊨ (⌜phi⌝ * P)%Assertion) -> phi.
    Proof.
      intro Hvalid. specialize (Hvalid ue).
      destruct Hvalid as [s1 [s2 [_ [Hphi _]]]]. exact Hphi.
    Qed.
  End WithUnit.

  Lemma sepcon_disj_l (P Q R : @Assertion model) :
    ⊨ (P \\// Q) * R <<==>> (P * R) \\// (Q * R).
  Proof. split; [apply orp_sepcon_left|apply orp_sepcon_right]. Qed.

  Lemma sepcon_disj_r (P Q R : @Assertion model) :
    ⊨ P * (Q \\// R) <<==>> (P * Q) \\// (P * R).
  Proof.
    intros s; split; intro H.
    - apply sepcon_comm_impp in H. apply orp_sepcon_left in H.
      destruct H as [H|H]; [left|right]; apply sepcon_comm_impp; exact H.
    - apply sepcon_comm_impp. apply orp_sepcon_right.
      destruct H as [H|H]; [left|right]; apply sepcon_comm_impp; exact H.
  Qed.

  Lemma sepcon_exists_l {A} (P : A -> @Assertion model) Q :
    ⊨ (Exists P) * Q <<==>> Exists (fun x => P x * Q).
  Proof.
    intros s; split; intro H.
    - destruct H as [s1 [s2 [Hj [[x HP] HQ]]]].
      exists x. exists s1, s2. repeat split; assumption.
    - destruct H as [x [s1 [s2 [Hj [HP HQ]]]]].
      exists s1, s2. split; [exact Hj|]. split; [exists x; exact HP|exact HQ].
  Qed.

  Lemma sepcon_exists_r {A} P (Q : A -> @Assertion model) :
    ⊨ P * (Exists Q) <<==>> Exists (fun x => P * Q x).
  Proof.
    intros s; split; intro H.
    - destruct H as [s1 [s2 [Hj [HP [x HQ]]]]].
      exists x. exists s1, s2. repeat split; assumption.
    - destruct H as [x [s1 [s2 [Hj [HP HQ]]]]].
      exists s1, s2. split; [exact Hj|]. split; [exact HP|exists x; exact HQ].
  Qed.

  Lemma pure_sepcon_extract_l (phi : Prop) (P : @Assertion model) :
    ⊨ ⌜phi⌝ * P ==>> ⌜phi⌝.
  Proof. intros s [s1 [s2 [Hj [Hphi HP]]]]; exact Hphi. Qed.

  Lemma pure_sepcon_extract_r (phi : Prop) (P : @Assertion model) :
    ⊨ P * ⌜phi⌝ ==>> ⌜phi⌝.
  Proof.
    intros s H. apply sepcon_comm_impp in H. eapply pure_sepcon_extract_l; eauto.
  Qed.

  Lemma sepcon_wand_apply (P Q : @Assertion model) :
    ⊨ P * (P -* Q) ==>> Q.
  Proof.
    intros s [s1 [s2 [Hj [HP HW]]]].
    eapply HW; [apply join_comm; exact Hj|exact HP].
  Qed.

  Lemma wand_mono (P P' Q Q' : @Assertion model) :
    (⊨ P' ==>> P) -> (⊨ Q ==>> Q') ->
    ⊨ (P -* Q) ==>> (P' -* Q').
  Proof.
    intros HP HQ s HW frame out Hj HP'.
    apply HQ. eapply HW; [exact Hj|apply HP; exact HP'].
  Qed.

  Lemma wand_equiv (P P' Q Q' : @Assertion model) :
    (⊨ P <<==>> P') -> (⊨ Q <<==>> Q') ->
    ⊨ (P -* Q) <<==>> (P' -* Q').
  Proof.
    intros HP HQ s; split; intros HW frame out Hj Hpre.
    - apply (proj1 (HQ out)). eapply HW; [exact Hj|].
      apply (proj2 (HP frame)); exact Hpre.
    - apply (proj2 (HQ out)). eapply HW; [exact Hj|].
      apply (proj1 (HP frame)); exact Hpre.
  Qed.

  Lemma wand_sepcon_adjoint_equiv (P Q R : @Assertion model) :
    (⊨ P * Q ==>> R) <-> (⊨ P ==>> (Q -* R)).
  Proof. apply wand_sepcon_adjoint. Qed.
    

End SeparationLogicRules.

(** Deliberately small and non-rewriting: these hints only close canonical
    elimination/introduction goals and cannot loop through commutativity. *)
Create HintDb separation.
#[global] Hint Resolve sepcon_emp1 sepcon_emp2
  pure_sepcon_extract_l pure_sepcon_extract_r sepcon_wand_apply : separation.

Ltac solve_sep := eauto with separation.
