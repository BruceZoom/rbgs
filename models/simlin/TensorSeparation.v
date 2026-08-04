Require Import models.logics.SeparationAlgebra.
Require Import models.logics.Logics.
Require Import models.EffectSignatures.
Require Import models.LinCCAL.
Require Import models.simlin.LTS.

Module TensorSeparation.
  Import Reg LinCCALBase.
  Import LTSSpec.

  (** These are named constructors, rather than new algebra definitions.
      Their low priority lets a user-provided state algebra win. *)
  Section TensorInstances.
    Context {E1 E2 : Op.t} {V1 : @LTS E1} {V2 : @LTS E2}.
    Context {J1 : Join (State V1)} {SA1 : @SeparationAlgebra _ J1}.
    Context {U1 : @SeparationAlgebraUnit _ J1 SA1}.
    Context {J2 : Join (State V2)} {SA2 : @SeparationAlgebra _ J2}.
    Context {U2 : @SeparationAlgebraUnit _ J2 SA2}.

    #[global] Instance tensor_state_Join : Join (State (tens_lts V1 V2)) | 100 :=
      prod_Join (State V1) (State V2).
    #[global] Instance tensor_state_SA :
      @SeparationAlgebra (State (tens_lts V1 V2)) tensor_state_Join :=
      prod_SA (State V1) (State V2).
    #[global] Instance tensor_state_unit :
      @SeparationAlgebraUnit (State (tens_lts V1 V2))
        tensor_state_Join tensor_state_SA :=
      prod_unit (State V1) (State V2).
  End TensorInstances.

  Section ComponentAssertions.
    Context {A B : Type}.
    Context {JA : Join A} {SAA : @SeparationAlgebra A JA}.
    Context {UA : @SeparationAlgebraUnit A JA SAA}.
    Context {JB : Join B} {SAB : @SeparationAlgebra B JB}.
    Context {UB : @SeparationAlgebraUnit B JB SAB}.

    Local Definition JP : Join (A * B) := prod_Join A B.
    Local Definition SAP : @SeparationAlgebra (A * B) JP := prod_SA A B.

    Definition tensor_left (P : Assertion) : @Assertion (A * B) :=
      fun s => P (fst s) /\ snd s = @ue B JB SAB UB.
    Definition tensor_right (Q : @Assertion B) : @Assertion (A * B) :=
      fun s => fst s = @ue A JA SAA UA /\ Q (snd s).
    Definition tensor_pair (P : @Assertion A) (Q : @Assertion B) :
      @Assertion (A * B) := fun s => P (fst s) /\ Q (snd s).

    Lemma tensor_left_mono (P Q : @Assertion A) :
      (forall s, P s -> Q s) ->
      forall s, tensor_left P s -> tensor_left Q s.
    Proof. firstorder. Qed.

    Lemma tensor_right_mono (P Q : @Assertion B) :
      (forall s, P s -> Q s) ->
      forall s, tensor_right P s -> tensor_right Q s.
    Proof. firstorder. Qed.

    Lemma tensor_components (P : @Assertion A) (Q : @Assertion B) :
      forall s, @sepcon (A * B) JP (tensor_left P) (tensor_right Q) s
                <-> tensor_pair P Q s.
    Proof.
      intros [a b]; split.
      - intros [[a1 b1] [[a2 b2] [[Ha Hb] [[HP Heqb1] [Heqa2 HQ]]]]].
        simpl in *. subst.
        split.
        + assert (a1 = a) by (eapply join_unit_right_inv; eauto). subst; exact HP.
        + assert (b2 = b) by (eapply join_unit_left_inv; eauto). subst; exact HQ.
      - intros [HP HQ].
        exists (a, @ue B JB SAB UB), (@ue A JA SAA UA, b).
        repeat split; simpl; auto using unit_join, unit_join_left.
    Qed.

    Lemma tensor_left_sep (P Q : @Assertion A) :
      forall s,
        tensor_left (@sepcon A JA P Q) s <->
        @sepcon (A * B) JP (tensor_left P) (tensor_left Q) s.
    Proof.
      intros [a b]; split.
      - intros [[a1 [a2 [Ha [HP HQ]]]] Hb]. simpl in *. subst b.
        exists (a1, @ue B JB SAB UB), (a2, @ue B JB SAB UB).
        repeat split; simpl; auto using unit_join.
      - intros [[a1 b1] [[a2 b2] [[Ha Hb] [[HP H1] [HQ H2]]]]].
        simpl in *. subst b1 b2. split.
        + exists a1, a2. repeat split; auto.
        + apply unit_spec in Hb. symmetry; exact Hb.
    Qed.

    Lemma tensor_right_sep (P Q : @Assertion B) :
      forall s,
        tensor_right (@sepcon B JB P Q) s <->
        @sepcon (A * B) JP (tensor_right P) (tensor_right Q) s.
    Proof.
      intros [a b]; split.
      - intros [Ha [b1 [b2 [Hb [HP HQ]]]]]. simpl in *. subst a.
        exists (@ue A JA SAA UA, b1), (@ue A JA SAA UA, b2).
        repeat split; simpl; auto using unit_join.
      - intros [[a1 b1] [[a2 b2] [[Ha Hb] [[H1 HP] [H2 HQ]]]]].
        simpl in *. subst a1 a2. split.
        + apply unit_spec in Ha. symmetry; exact Ha.
        + exists b1, b2. repeat split; auto.
    Qed.

    Lemma tensor_left_emp :
      forall s, tensor_left (@emp A JA) s <-> @emp (A * B) JP s.
    Proof.
      intros [a b]; split.
      - intros [Ha Hb]. simpl in *. subst.
        unfold emp, unit_element, JP, prod_Join; simpl.
        intros [a1 b1] [a2 b2] [H1 H2].
        f_equal; [apply Ha in H1|apply unit_spec in H2]; auto.
      - intro H. unfold emp, unit_element, JP, prod_Join in H; simpl in H.
        assert (a = @ue A JA SAA UA).
        { apply unit_element_eq. intros n n' Hn.
          exact (f_equal fst
            (H (n, @ue B JB SAB UB) (n', b)
               (conj Hn (unit_join b)))). }
        assert (b = @ue B JB SAB UB).
        { apply unit_element_eq. intros n n' Hn.
          exact (f_equal snd
            (H (@ue A JA SAA UA, n) (a, n')
               (conj (unit_join a) Hn))). }
        subst. split; [apply unit_spec|reflexivity].
    Qed.

    Lemma tensor_right_emp :
      forall s, tensor_right (@emp B JB) s <-> @emp (A * B) JP s.
    Proof.
      intros [a b]; split.
      - intros [Ha Hb]. simpl in *. subst.
        unfold emp, unit_element, JP, prod_Join; simpl.
        intros [a1 b1] [a2 b2] [H1 H2].
        f_equal; [apply unit_spec in H1|apply Hb in H2]; auto.
      - intro H. unfold emp, unit_element, JP, prod_Join in H; simpl in H.
        assert (a = @ue A JA SAA UA).
        { apply unit_element_eq. intros n n' Hn.
          exact (f_equal fst
            (H (n, @ue B JB SAB UB) (n', b)
               (conj Hn (unit_join b)))). }
        split; [exact H0|].
        intros n n' Hn.
        exact (f_equal snd
          (H (@ue A JA SAA UA, n) (a, n')
             (conj (unit_join a) Hn))).
    Qed.
  End ComponentAssertions.

  Section TensorTransitions.
    Context {E1 E2 : Op.t} {V1 : @LTS E1} {V2 : @LTS E2}.

    Lemma tensor_left_inv_preserves_right t (op : Sig.op E1)
        (s1 s1' : State V1) (s2 s2' : State V2) :
      Step (tens_lts V1 V2)
        (Build_ThreadEvent t
          (@InvEv (Sig.Plus.omap E1 E2) (inl op))) (s1, s2) (s1', s2') ->
      s2 = s2'.
    Proof. simpl; tauto. Qed.

    Lemma tensor_left_res_preserves_right t (op : Sig.op E1) (r : Sig.ar op)
        (s1 s1' : State V1) (s2 s2' : State V2) :
      Step (tens_lts V1 V2)
        (Build_ThreadEvent t
          (@ResEv (Sig.Plus.omap E1 E2) (inl op) r)) (s1, s2) (s1', s2') ->
      s2 = s2'.
    Proof. simpl; tauto. Qed.

    Lemma tensor_right_inv_preserves_left t (op : Sig.op E2)
        (s1 s1' : State V1) (s2 s2' : State V2) :
      Step (tens_lts V1 V2)
        (Build_ThreadEvent t
          (@InvEv (Sig.Plus.omap E1 E2) (inr op))) (s1, s2) (s1', s2') ->
      s1 = s1'.
    Proof. simpl; tauto. Qed.

    Lemma tensor_right_res_preserves_left t (op : Sig.op E2) (r : Sig.ar op)
        (s1 s1' : State V1) (s2 s2' : State V2) :
      Step (tens_lts V1 V2)
        (Build_ThreadEvent t
          (@ResEv (Sig.Plus.omap E1 E2) (inr op) r)) (s1, s2) (s1', s2') ->
      s1 = s1'.
    Proof. simpl; tauto. Qed.
  End TensorTransitions.
End TensorSeparation.
