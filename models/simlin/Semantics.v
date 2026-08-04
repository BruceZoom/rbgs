Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Program.
Require Import Logic.ProofIrrelevance.
Require Import Logic.FunctionalExtensionality.
Require Import Logic.PropExtensionality.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import SeparationAlgebra.
Require Import FMapPositive.

Section TMapSA.
  Context {A : Type}.

  Inductive tree_join : LinCCAL.tmap A -> LinCCAL.tmap A -> LinCCAL.tmap A -> Prop :=
  | TJ_LeafLeft : forall t, tree_join (LinCCAL.TMap.Leaf _) t t
  | TJ_LeafRight : forall t, tree_join t (LinCCAL.TMap.Leaf _) t
  | TJ_Node : forall ml ml' ml'' mr mr' mr'' o o' o'',
      tree_join ml ml' ml'' ->
      tree_join mr mr' mr'' ->
      @option_Join _ trivial_Join o o' o'' ->
      tree_join (LinCCAL.TMap.Node ml o mr)
                (LinCCAL.TMap.Node ml' o' mr')
                (LinCCAL.TMap.Node ml'' o'' mr'').
  
  Lemma tree_join_increasing:
    forall t1 t2 t, tree_join t1 t2 t ->
      forall a b, LinCCAL.TMap.find a t1 = Some b -> LinCCAL.TMap.find a t = Some b.
  Proof.
    induction 1; intros; auto.
    - destruct a; simpl in *; congruence.
    - destruct a; simpl in *; auto; subst.
      inversion H1; subst; auto.
      inversion H3.
  Qed.
  
  Lemma tree_join_none:
    forall t1 t2 t, tree_join t1 t2 t ->
      forall a, LinCCAL.TMap.find a t = None <-> (LinCCAL.TMap.find a t1 = None /\ LinCCAL.TMap.find a t2 = None).
  Proof.
    induction 1; intros.
    - split; try tauto.
      intros. split; auto.
      destruct a; auto.
    - split; try tauto.
      intros. split; auto.
      destruct a; auto.
    - destruct a; simpl; auto.
      inversion H1; subst; try tauto.
  Qed.

  Lemma tree_join_disjoint :
    forall t1 t2 t, tree_join t1 t2 t ->
      forall a b1 b2,
        LinCCAL.TMap.find a t1 = Some b1 ->
        LinCCAL.TMap.find a t2 = Some b2 -> False.
  Proof.
    induction 1; intros; auto.
    - destruct a; simpl in *; congruence.
    - destruct a; simpl in *; congruence.
    - destruct a; simpl in *; eauto.
      subst. inversion H1; subst; contradiction.
  Qed.

  #[global] Instance tmap_Join : Join (LinCCAL.tmap A) := tree_join.
  #[global] Program Instance tmap_SA : SeparationAlgebra (LinCCAL.tmap A).
  Next Obligation.
    induction H; constructor; auto.
    eapply join_comm; auto.
    Unshelve. exact (@option_SA A trivial_Join trivial_SA).
  Qed.
  Next Obligation.
    rename H0 into Hz.
    revert mz mxyz Hz.
    induction H; intros; inversion Hz; subst;
    try solve [eexists; split; econstructor; eauto].
    apply IHtree_join1 in H5 as [mlyz [? ?]].
    apply IHtree_join2 in H8 as [mryz [? ?]].
    epose proof join_assoc o o' o'0 o'' o''0 H1 H9 as [moyz [? ?]].
    exists (LinCCAL.TMap.Node mlyz moyz mryz).
    split; constructor; auto.
    Unshelve. exact (@option_SA A trivial_Join trivial_SA).
  Defined.

  #[global] Program Instance tmap_unit : SeparationAlgebraUnit (LinCCAL.tmap A) tmap_SA :=
  {| ue := LinCCAL.TMap.Leaf _ |}.
  Next Obligation.
    constructor.
  Qed.
  Next Obligation.
    intros ? ? ?.
    inversion H; subst; auto.
  Qed.
End TMapSA.

Existing Instance tmap_Join.
Existing Instance tmap_SA.
Existing Instance tmap_unit.

Module Semantics.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.

  Definition ThreadDomain : Type := tid -> Prop.

  Definition domain_equiv (A B : ThreadDomain) : Prop :=
    forall t, A t <-> B t.

  Definition domain_empty : ThreadDomain := fun _ => False.
  Definition domain_add (t : tid) (A : ThreadDomain) : ThreadDomain :=
    fun t' => t' = t \/ A t'.
  Definition domain_remove (t : tid) (A : ThreadDomain) : ThreadDomain :=
    fun t' => t' <> t /\ A t'.
  Definition domain_union (A B : ThreadDomain) : ThreadDomain :=
    fun t => A t \/ B t.
  Definition domain_disjoint (A B : ThreadDomain) : Prop :=
    forall t, A t -> B t -> False.

  Definition map_domain {X} (pi : tmap X) : ThreadDomain :=
    fun t => exists x, TMap.find t pi = Some x.

  Lemma domain_equiv_refl : forall A, domain_equiv A A.
  Proof. firstorder. Qed.
  Lemma domain_equiv_symm : forall A B, domain_equiv A B -> domain_equiv B A.
  Proof. firstorder. Qed.
  Lemma domain_equiv_trans : forall A B C,
      domain_equiv A B -> domain_equiv B C -> domain_equiv A C.
  Proof. firstorder. Qed.
  Lemma domain_union_comm : forall A B,
      domain_equiv (domain_union A B) (domain_union B A).
  Proof. firstorder. Qed.
  Lemma domain_union_assoc : forall A B C,
      domain_equiv (domain_union (domain_union A B) C)
                   (domain_union A (domain_union B C)).
  Proof. firstorder. Qed.
  Lemma domain_union_empty_l : forall A,
      domain_equiv (domain_union domain_empty A) A.
  Proof. firstorder. Qed.
  Lemma domain_union_empty_r : forall A,
      domain_equiv (domain_union A domain_empty) A.
  Proof. firstorder. Qed.

  Lemma map_domain_empty {X} :
    domain_equiv (map_domain (TMap.empty X)) domain_empty.
  Proof.
    intros t; unfold map_domain, domain_empty.
    rewrite TMap.gempty. split; [intros [? H]; discriminate|tauto].
  Qed.

  Lemma map_domain_add {X} (pi : tmap X) t x :
    domain_equiv (map_domain (TMap.add t x pi))
                 (domain_add t (map_domain pi)).
  Proof.
    intros t'; unfold map_domain, domain_add.
    destruct (Pos.eq_dec t' t); subst.
    - rewrite TMap.gss. split; [tauto|intros; eauto].
    - rewrite TMap.gso; auto. firstorder.
  Qed.

  Lemma map_domain_remove {X} (pi : tmap X) t :
    domain_equiv (map_domain (TMap.remove t pi))
                 (domain_remove t (map_domain pi)).
  Proof.
    intros t'; unfold map_domain, domain_remove.
    destruct (Pos.eq_dec t' t); subst.
    - rewrite TMap.grs. split; [intros [? H]; discriminate|tauto].
    - rewrite TMap.gro; auto. firstorder.
  Qed.

  Lemma map_domain_join {X} (pi1 pi2 pi : tmap X) :
    @join _ tmap_Join pi1 pi2 pi ->
    domain_equiv (map_domain pi)
                 (domain_union (map_domain pi1) (map_domain pi2)).
  Proof.
    intros Hj t; unfold map_domain, domain_union.
    split.
    - intros [x Hx].
      pose proof (tree_join_none _ _ _ Hj t) as Hnone.
      destruct (TMap.find t pi1) eqn:H1; [left; eauto|].
      destruct (TMap.find t pi2) eqn:H2; [right; eauto|].
      assert (TMap.find t pi = None) as Hout.
      { apply (proj2 Hnone). split; auto. }
      congruence.
    - intros [[x Hx]|[x Hx]].
      + exists x. eapply tree_join_increasing; eauto.
      + exists x. eapply tree_join_increasing; [apply join_comm; exact Hj|exact Hx].
  Qed.

  Lemma map_domain_join_disjoint {X} (pi1 pi2 pi : tmap X) :
    @join _ tmap_Join pi1 pi2 pi ->
    domain_disjoint (map_domain pi1) (map_domain pi2).
  Proof.
    intros Hj t [x Hx] [y Hy].
    eapply tree_join_disjoint; eauto.
  Qed.

  Section Semantics.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.
    Context (M : ModuleImpl E F).

    Record ThreadState := {
      (* overlay operation in process *)
      ts_op : Sig.op F;
      (* continuation *)
      ts_prog : Prog E (Sig.ar ts_op);
      (* pending underlay opertion *)
      ts_pend : option (Sig.op E);
    }.

    Definition ThreadPoolState : Type := tmap ThreadState.

    Definition pool_domain (c : ThreadPoolState) : ThreadDomain :=
      map_domain c.

    Variant ts_step (f : Sig.op F) : ThreadEvent -> State VE -> ThreadState -> State VE -> ThreadState -> Prop :=
    | ts_inv t op k s1 s2
        (Hstep : Step VE (Build_ThreadEvent t (InvEv op)) s1 s2) :
        ts_step f (Build_ThreadEvent t (InvEv op))
          s1 (Build_ThreadState f (Vis op k) None)
          s2 (Build_ThreadState f (Vis op k) (Some op))
    | ts_res t op ret k s1 s2
        (Hstep : Step VE (Build_ThreadEvent t (ResEv op ret)) s1 s2) :
        ts_step f (Build_ThreadEvent t (ResEv op ret))
          s1 (Build_ThreadState f (Vis op k) (Some op))
          s2 (Build_ThreadState f (k ret) None).
    
    Variant ts_taustep : ThreadState -> ThreadState -> Prop :=
    | ts_tau f p b :
        ts_taustep
          (Build_ThreadState f (Tau p) b)
          (Build_ThreadState f p b).
    
    Variant ts_error (f : Sig.op F) : ThreadEvent -> State VE -> ThreadState -> Prop :=
    | ts_err t op s k
        (Herror : Error VE (Build_ThreadEvent t (InvEv op)) s):
        ts_error f (Build_ThreadEvent t (InvEv op)) s (Build_ThreadState f (Vis op k) None).

    Lemma ts_step_inversion f:
      forall ev σ f' p b σ' ts', ts_step f ev σ (Build_ThreadState f' p b) σ' ts' ->
      f = f' /\
      exists p' b', ts' = Build_ThreadState f p' b'.
    Proof.
      inversion 1; subst; split; auto.
      - dependent destruction H4.
        exists (Vis op k0), (Some op). auto.
      - dependent destruction H4. eexists; eauto.
    Qed.
      
    Variant ustep (ev : ThreadEvent) (s1 : State VE) (c1 : ThreadPoolState) (s2 : State VE) (c2 : ThreadPoolState) : Prop :=
    | UStep f
        (ts1 ts2 : ThreadState)
        (Hfind : TMap.find (te_tid ev) c1 = Some ts1)
        (Hstep : ts_step f ev s1 ts1 s2 ts2)
        (Hupd : c2 = TMap.add (te_tid ev) ts2 c1).

    Variant uerror (ev : ThreadEvent) (s1 : State VE) (c1 : ThreadPoolState) : Prop :=
    | UError f
        (ts : ThreadState)
        (Hfind : TMap.find (te_tid ev) c1 = Some ts)
        (Herror : ts_error f ev s1 ts).

    Variant taustep t (c1 : ThreadPoolState) (c2 : ThreadPoolState) : Prop :=
    | TauStep
        (ts1 ts2 : ThreadState)
        (Hfind : TMap.find t c1 = Some ts1)
        (Hstep : ts_taustep ts1 ts2)
        (Hupd : c2 = TMap.add t ts2 c1).

    Variant invstep (t : tid) (f : Sig.op F) (c1 c2 : ThreadPoolState) : Prop :=
    | InvStep
        (Hfind : TMap.find t c1 = None)
        (Hupd : c2 = TMap.add t (Build_ThreadState f (M f t) None) c1).

    Variant retstep (t : tid) (f : Sig.op F) (ret : Sig.ar f) (c1 c2 : ThreadPoolState) : Prop :=
    | RetStep
        (Hfind : TMap.find t c1 = Some (Build_ThreadState f (Ret ret) None))
        (Hupd : c2 = TMap.remove t c1).

    (* Variant estep (s1 : State VE) (c1 : ThreadPoolState) (s2 : State VE) (c2 : ThreadPoolState) : Prop :=
    | estep_ustep ev
        (Hstep : ustep ev s1 c1 s2 c2)
    | estep_inv t f
        (Hstep : invstep t f c1 c2)
    | estep_ret t f ret
        (Hstep : retstep t f ret c1 c2). *)

    Variant LinState : Type :=
    | ls_inv (f : Sig.op F)
    | ls_lini (f : Sig.op F)
    | ls_linr (f : Sig.op F) (ret : Sig.ar f).

    Variant Poss : Type :=
    | PossOk (s : State VF) (π : tmap LinState)
    | PossError.

    Variant poss_step : Poss -> Poss -> Prop :=
    | ps_inv t f s1 s2 π
        (Hstep : Step VF (Build_ThreadEvent t (InvEv f)) s1 s2)
        (Hlin : TMap.find t π = Some (ls_inv f)) :
        poss_step (PossOk s1 π) (PossOk s2 (TMap.add t (ls_lini f) π))
    | ps_ret t f ret s1 s2 π
        (Hstep : Step VF (Build_ThreadEvent t (ResEv f ret)) s1 s2)
        (Hlin : TMap.find t π = Some (ls_lini f)) :
        poss_step (PossOk s1 π) (PossOk s2 (TMap.add t (ls_linr f ret) π))
    | ps_error t f s π
        (Herror : Error VF (Build_ThreadEvent t (InvEv f)) s)
        (Hlin : TMap.find t π = Some (ls_inv f)) :
        poss_step (PossOk s π) PossError.
            
    Definition poss_steps := clos_refl_trans _ poss_step.
    Definition nonemp_poss_steps := clos_trans _ poss_step.
    
    Definition linstate_atomic_step t f r (π : tmap LinState) : tmap LinState :=
      TMap.add t (Semantics.ls_linr f r) (TMap.add t (Semantics.ls_lini f) π).

    (* Lemmas *)

    Lemma ustep_local_cont : forall t ev s1 c1 s2 c2 t',
      ustep (Build_ThreadEvent t ev) s1 c1 s2 c2 ->
      t <> t' -> TMap.find t' c1 = TMap.find t' c2.
    Proof.
      inversion 1; subst.
      intros. simpl.
      rewrite PositiveMap.gso; auto.
    Qed.

    Lemma taustep_local_cont : forall t c1 c2 t',
      taustep t c1 c2 ->
      t <> t' -> TMap.find t' c1 = TMap.find t' c2.
    Proof.
      inversion 1; subst.
      intros. simpl.
      rewrite PositiveMap.gso; auto.
    Qed.

    Lemma ustep_local_determ : forall t ev s s' c1 c1' c2,
      ustep (Build_ThreadEvent t ev) s c1 s' c1' ->
      TMap.find t c1 = TMap.find t c2 ->
      exists c2',
      ustep (Build_ThreadEvent t ev) s c2 s' c2' /\
      TMap.find t c1' = TMap.find t c2'.
    Proof.
      inversion 1; subst.
      intros.
      exists (TMap.add t0 ts2 c2).
      simpl in *.
      split; auto.
      - econstructor; simpl; eauto.
        rewrite <- H0; auto.
      - do 2 rewrite PositiveMap.gss; auto.
    Qed.

    Lemma taustep_local_determ : forall t c1 c1' c2,
      taustep t c1 c1' ->
      TMap.find t c1 = TMap.find t c2 ->
      exists c2',
      taustep t c2 c2' /\
      TMap.find t c1' = TMap.find t c2'.
    Proof.
      inversion 1; subst.
      intros.
      exists (TMap.add t0 ts2 c2).
      split; auto.
      - econstructor; simpl; eauto.
        rewrite <- H0; auto.
      - do 2 rewrite PositiveMap.gss; auto.
    Qed.

    Lemma uerror_local_determ : forall t ev s c c',
      uerror (Build_ThreadEvent t ev) s c ->
      TMap.find t c = TMap.find t c' ->
      uerror (Build_ThreadEvent t ev) s c'.
    Proof.
      intros.
      inversion H; subst.
      econstructor; eauto.
      simpl in *. rewrite <- H0. auto.
    Qed.

    Lemma invstep_local_cont : forall t f c1 c2 t',
      invstep t f c1 c2 ->
      t <> t' -> TMap.find t' c1 = TMap.find t' c2.
    Proof.
      inversion 1; subst.
      intros. simpl.
      rewrite PositiveMap.gso; auto.
    Qed.

    Lemma invstep_local_determ : forall t f c1 c1' c2,
      invstep t f c1 c1' ->
      TMap.find t c1 = TMap.find t c2 ->
      exists c2',
      invstep t f c2 c2' /\
      TMap.find t c1' = TMap.find t c2'.
    Proof.
      inversion 1; subst.
      intros.
      exists (TMap.add t0 (Build_ThreadState f (M f t0) None) c2).
      simpl in *.
      split; auto.
      - econstructor; simpl; eauto.
        rewrite <- H0; auto.
      - do 2 rewrite PositiveMap.gss; auto.
    Qed.

    Lemma retstep_local_cont : forall t f ret c1 c2 t',
      retstep t f ret c1 c2 ->
      t <> t' -> TMap.find t' c1 = TMap.find t' c2.
    Proof.
      inversion 1; subst.
      intros.
      rewrite PositiveMap.gro; auto.
    Qed.

    Lemma retstep_local_determ : forall t f ret c1 c1' c2,
      retstep t f ret c1 c1' ->
      TMap.find t c1 = TMap.find t c2 ->
      exists c2',
      retstep t f ret c2 c2' /\
      TMap.find t c1' = TMap.find t c2'.
    Proof.
      inversion 1; subst.
      intros.
      exists (TMap.remove t0 c2).
      simpl in *.
      split; auto.
      - econstructor; simpl; eauto.
        rewrite <- H0; auto.
      - do 2 rewrite PositiveMap.grs; auto.
    Qed.
    
    Lemma poss_step_nondec : forall t ρ ρ' π π' ls,
      poss_step (PossOk ρ π) (PossOk ρ' π') ->
      TMap.find t π = Some ls ->
      exists ls, TMap.find t π' = Some ls.
    Proof.
      inversion 1; subst;
      destruct (Pos.eq_dec t0 t1); subst;
      intros.
      - rewrite PositiveMap.gss; eauto.
      - rewrite PositiveMap.gso; eauto.
      - rewrite PositiveMap.gss; eauto.
      - rewrite PositiveMap.gso; eauto.
    Qed.

    Lemma poss_steps_nondec : forall t ρ ρ' π π' ls,
      poss_steps (PossOk ρ π) (PossOk ρ' π') ->
      TMap.find t π = Some ls ->
      exists ls, TMap.find t π' = Some ls.
    Proof.
      intros ? ? ? ? ? ? H.
      revert ls.
      unfold poss_steps in H.
      apply clos_rt_rtn1_iff in H.
      remember (PossOk ρ π) as s1.
      remember (PossOk ρ' π') as s2.
      revert  ρ ρ' π π' Heqs1 Heqs2.
      induction H; intros; subst.
      - inversion Heqs2; subst. eauto.
      - destruct y.
        eapply (IHclos_refl_trans_n1 _ _ _ _ eq_refl eq_refl) in H1 as [? ?]; eauto.
        eapply poss_step_nondec in H1; eauto.
        inversion H.
    Qed.

  End Semantics.

  Section AbstractConfig.
    Context {F : Op.t} {VF : @LTS F}.

    Definition AbstractConfigProp : Type := State VF -> tmap (@LinState F) -> Prop.

    Record AbstractConfig : Type := mkAC {
      ac_active : ThreadDomain;
      ac_prop :> State VF -> tmap (@LinState F) -> Prop;
      ac_nonempty : exists ρ π, ac_prop ρ π;
      ac_domain : forall ρ π, ac_prop ρ π ->
                    domain_equiv (map_domain π) ac_active
    }.

    Definition ac_equiv (Δ1 Δ2 : AbstractConfig) : Prop :=
      forall ρ π, Δ1 ρ π <-> Δ2 ρ π.

    Program Instance Equivalence_ACEquiv : Equivalence ac_equiv.
    Next Obligation. constructor; auto. Defined.
    Next Obligation. constructor; apply H. Defined.
    Next Obligation.
      constructor.
      - unfold ac_equiv in *. intros. apply H0, H. auto.
      - unfold ac_equiv in *. intros. apply H, H0. auto.
    Defined.

    Definition ac_subset (Δ1 Δ2 : AbstractConfig) : Prop :=
      forall ρ π, Δ1 ρ π -> Δ2 ρ π.

    Lemma ac_equiv_active : forall Δ1 Δ2,
      ac_equiv Δ1 Δ2 -> domain_equiv (ac_active Δ1) (ac_active Δ2).
    Proof.
      intros Δ1 Δ2 Heq.
      destruct (ac_nonempty Δ1) as [ρ [π Hposs]].
      pose proof (ac_domain Δ1 _ _ Hposs) as Hdom1.
      pose proof (ac_domain Δ2 _ _ (proj1 (Heq _ _) Hposs)) as Hdom2.
      firstorder.
    Qed.

    Lemma ac_subset_active : forall Δ1 Δ2,
      ac_subset Δ1 Δ2 -> domain_equiv (ac_active Δ1) (ac_active Δ2).
    Proof.
      intros Δ1 Δ2 Hsub.
      destruct (ac_nonempty Δ1) as [ρ [π Hposs]].
      pose proof (ac_domain Δ1 _ _ Hposs) as Hdom1.
      pose proof (ac_domain Δ2 _ _ (Hsub _ _ Hposs)) as Hdom2.
      firstorder.
    Qed.

    Lemma ac_find_some_iff : forall (Δ : AbstractConfig) ρ π t,
      Δ ρ π ->
      (ac_active Δ t <-> exists ls, TMap.find t π = Some ls).
    Proof.
      intros Δ ρ π t Hposs.
      symmetry. apply ac_domain with (ρ := ρ); auto.
    Qed.

    Lemma ac_find_none_iff : forall (Δ : AbstractConfig) ρ π t,
      Δ ρ π ->
      (~ ac_active Δ t <-> TMap.find t π = None).
    Proof.
      intros Δ ρ π t Hposs.
      rewrite ac_find_some_iff with (ρ := ρ) (π := π); auto.
      destruct (TMap.find t π); firstorder congruence.
    Qed.

    Lemma ac_find_none_same : forall (Δ : AbstractConfig)
      ρ1 π1 ρ2 π2 t,
      Δ ρ1 π1 -> Δ ρ2 π2 ->
      TMap.find t π1 = None -> TMap.find t π2 = None.
    Proof.
      intros Δ ρ1 π1 ρ2 π2 t H1 H2 Hnone.
      apply (proj1 (ac_find_none_iff Δ ρ2 π2 t H2)).
      apply (proj2 (ac_find_none_iff Δ ρ1 π1 t H1)).
      exact Hnone.
    Qed.

    Lemma ac_find_none_equiv : forall (Δ : AbstractConfig)
      ρ1 π1 ρ2 π2,
      Δ ρ1 π1 -> Δ ρ2 π2 ->
      forall t, TMap.find t π1 = None <-> TMap.find t π2 = None.
    Proof.
      intros Δ ρ1 π1 ρ2 π2 H1 H2 t; split; intro Hnone.
      - exact (ac_find_none_same Δ ρ1 π1 ρ2 π2 t H1 H2 Hnone).
      - exact (ac_find_none_same Δ ρ2 π2 ρ1 π1 t H2 H1 Hnone).
    Qed.

    Lemma AbstractConfig_ext : forall Δ1 Δ2,
      ac_equiv Δ1 Δ2 -> Δ1 = Δ2.
    Proof.
      intros [A1 P1 Hn1 Hd1] [A2 P2 Hn2 Hd2] Heq; simpl in *.
      assert (A1 = A2) as HA.
      { apply functional_extensionality; intros t.
        apply propositional_extensionality.
        exact (ac_equiv_active _ _ Heq t). }
      assert (P1 = P2) as HP.
      { apply functional_extensionality_dep; intros ρ.
        apply functional_extensionality_dep; intros π.
        apply propositional_extensionality. apply Heq. }
      subst. f_equal; apply proof_irrelevance.
    Qed.

    Definition ac_empty_prop : AbstractConfigProp :=
      fun _ _ => False.

    Variant ac_singleton_prop ρ π : AbstractConfigProp :=
    | ACSingle : ac_singleton_prop ρ π ρ π.

    Program Definition ac_singleton ρ π : AbstractConfig :=
      {| ac_active := map_domain π;
         ac_prop := ac_singleton_prop ρ π |}.
    Next Obligation. exists ρ, π. constructor. Qed.
    Next Obligation. inversion H; subst; apply domain_equiv_refl. Qed.

    Lemma ac_singleton_active : forall ρ π,
      domain_equiv (ac_active (ac_singleton ρ π)) (map_domain π).
    Proof. intros; apply domain_equiv_refl. Qed.

    Variant ac_union_prop (Δ1 Δ2 : AbstractConfigProp) : AbstractConfigProp :=
    | ACUnionLeft ρ π: Δ1 ρ π -> ac_union_prop Δ1 Δ2 ρ π
    | ACUnionRight ρ π: Δ2 ρ π -> ac_union_prop Δ1 Δ2 ρ π.
    Program Definition ac_union (Δ1 Δ2 : AbstractConfig)
      {Hactive : domain_equiv (ac_active Δ1) (ac_active Δ2)} : AbstractConfig :=
      {| ac_active := ac_active Δ1;
         ac_prop := ac_union_prop Δ1 Δ2 |}.
    Next Obligation.
      pose proof ac_nonempty Δ1 as [ρ [π ?]].
      exists ρ, π.
      apply ACUnionLeft; auto.
    Qed.
    Next Obligation.
      inversion H; subst.
      - eapply ac_domain; eauto.
      - eapply domain_equiv_trans; [eapply ac_domain; eauto|].
        apply domain_equiv_symm; exact Hactive.
    Defined.

    Lemma ac_union_active : forall Δ1 Δ2 Hactive,
      domain_equiv (ac_active (@ac_union Δ1 Δ2 Hactive)) (ac_active Δ1).
    Proof. intros; apply domain_equiv_refl. Qed.

    Variant ac_intersect_prop (Δ1 Δ2 : AbstractConfigProp) : AbstractConfigProp :=
    | ACIntersect ρ π: Δ1 ρ π -> Δ2 ρ π -> ac_intersect_prop Δ1 Δ2 ρ π.

    Variant ac_inv_prop (Δ : AbstractConfigProp) t f : AbstractConfigProp :=
    | ACInv ρ π (Hposs : Δ ρ π) :
        ac_inv_prop Δ t f ρ (TMap.add t (ls_inv f) π).
      
    Program Definition ac_inv (Δ : AbstractConfig) t f : AbstractConfig :=
      {| ac_active := domain_add t (ac_active Δ);
         ac_prop := ac_inv_prop Δ t f |}.
    Next Obligation.
      destruct (ac_nonempty Δ) as [ρ [π H]].
      exists ρ, (TMap.add t0 (ls_inv f) π). constructor. auto.
    Qed.
    Next Obligation.
      inversion H; subst.
      eapply domain_equiv_trans; [apply map_domain_add|].
      unfold domain_add. intros t1. rewrite (ac_domain Δ _ _ Hposs t1).
      reflexivity.
    Qed.

    Lemma ac_inv_active : forall Δ t f,
      domain_equiv (ac_active (ac_inv Δ t f))
                   (domain_add t (ac_active Δ)).
    Proof. intros; apply domain_equiv_refl. Qed.

    Lemma ac_inv_find_eq : forall Δ t f ρ π,
      ac_inv Δ t f ρ π -> TMap.find t π = Some (ls_inv f).
    Proof. intros; inversion H; subst; apply TMap.gss. Qed.

    Lemma ac_inv_find_neq : forall Δ t f ρ π t',
      ac_inv Δ t f ρ π -> t' <> t ->
      exists π0, Δ ρ π0 /\ TMap.find t' π = TMap.find t' π0.
    Proof.
      intros; inversion H; subst. eexists; split; eauto.
      rewrite TMap.gso; auto.
    Qed.

    Variant ac_res_prop (Δ : AbstractConfigProp) t : AbstractConfigProp :=
    | ACRes ρ π (Hposs : Δ ρ π):
        ac_res_prop Δ t ρ (TMap.remove t π).
    
    Program Definition ac_res (Δ : AbstractConfig) t : AbstractConfig :=
      {| ac_active := domain_remove t (ac_active Δ);
         ac_prop := ac_res_prop Δ t |}.
    Next Obligation.
      destruct (ac_nonempty Δ) as [ρ [π H]].
      exists ρ, (TMap.remove t0 π). constructor. auto.
    Qed.
    Next Obligation.
      inversion H; subst.
      eapply domain_equiv_trans; [apply map_domain_remove|].
      unfold domain_remove. intros t1. rewrite (ac_domain Δ _ _ Hposs t1).
      reflexivity.
    Qed.

    Lemma ac_res_active : forall Δ t,
      domain_equiv (ac_active (ac_res Δ t))
                   (domain_remove t (ac_active Δ)).
    Proof. intros; apply domain_equiv_refl. Qed.

    Lemma ac_res_find_eq : forall Δ t ρ π,
      ac_res Δ t ρ π -> TMap.find t π = None.
    Proof. intros; inversion H; subst; apply TMap.grs. Qed.

    Lemma ac_res_find_neq : forall Δ t ρ π t',
      ac_res Δ t ρ π -> t' <> t ->
      exists π0, Δ ρ π0 /\ TMap.find t' π = TMap.find t' π0.
    Proof.
      intros; inversion H; subst. eexists; split; eauto.
      rewrite TMap.gro; auto.
    Qed.

    Variant ac_steps_prop (Δ : AbstractConfigProp) : AbstractConfigProp :=
    | ACSteps ρ π ρ' π' (Hposs : Δ ρ π)
        (Hpstep : poss_steps (PossOk ρ π) (PossOk ρ' π')):
        ac_steps_prop Δ ρ' π'.

    Lemma poss_step_domain : forall ρ π ρ' π',
      @poss_step _ VF (PossOk ρ π) (PossOk ρ' π') ->
      domain_equiv (map_domain π) (map_domain π').
    Proof.
      inversion 1; subst; intros t'; unfold map_domain.
      all: destruct (Pos.eq_dec t' t0); subst.
      all: try (rewrite TMap.gss; split; [intros; eauto|intros; eauto]).
      all: rewrite TMap.gso; auto; reflexivity.
    Qed.

    Lemma poss_steps_domain : forall ρ π ρ' π',
      @poss_steps _ VF (PossOk ρ π) (PossOk ρ' π') ->
      domain_equiv (map_domain π) (map_domain π').
    Proof.
      intros.
      remember (PossOk ρ π) as p.
      remember (PossOk ρ' π') as p'.
      revert ρ' π' Heqp'.
      apply clos_rt_rtn1 in H.
      induction H; intros; subst.
      - inversion Heqp'; subst. apply domain_equiv_refl.
      - inversion H; subst;
        specialize (IHclos_refl_trans_n1 _ _ eq_refl);
        eapply domain_equiv_trans; eauto; eapply poss_step_domain; eauto.
    Qed.

    Program Definition ac_steps (Δ : AbstractConfig) : AbstractConfig :=
      {| ac_active := ac_active Δ;
         ac_prop := ac_steps_prop Δ |}.
    Next Obligation.
      destruct (ac_nonempty Δ) as [ρ [π H]].
      exists ρ, π. econstructor; eauto. apply rt_refl.
    Qed.
    Next Obligation.
      inversion H; subst.
      eapply domain_equiv_trans; [apply domain_equiv_symm; eapply poss_steps_domain; eauto|].
      eapply ac_domain; eauto.
    Qed.

    Lemma ac_steps_active : forall Δ,
      domain_equiv (ac_active (ac_steps Δ)) (ac_active Δ).
    Proof. intros; apply domain_equiv_refl. Qed.

    Lemma ac_steps_refl : forall Δ, ac_subset Δ (ac_steps Δ).
    Proof.
      intros. intros ? ? ?.
      econstructor; eauto.
      apply rt_refl.
    Qed.

    Variant ac_steps_π_prop (Δ : AbstractConfigProp) t ls1 ls2 ρf
      (Hpstep : forall ρ π, Δ ρ π -> poss_steps (PossOk ρ π) (PossOk (ρf ρ) (TMap.add t ls2 (TMap.add t ls1 π)))) : AbstractConfigProp :=
    | ACSteps_π ρ π (Hposs : Δ ρ π):
        ac_steps_π_prop Δ t ls1 ls2 ρf Hpstep (ρf ρ) (TMap.add t ls2 (TMap.add t ls1 π)).
    
    Program Definition ac_steps_π (Δ : AbstractConfig) t ls1 ls2 ρf Hpstep : AbstractConfig :=
      {| ac_active := ac_active Δ;
         ac_prop := ac_steps_π_prop Δ t ls1 ls2 ρf Hpstep |}.
    Next Obligation.
      pose proof ac_nonempty Δ as [? [? ?]].
      do 2 eexists. econstructor; eauto.
    Qed.
    Next Obligation.
      inversion H; subst.
      pose proof (Hpstep _ _ Hposs) as Hsteps.
      eapply domain_equiv_trans; [apply domain_equiv_symm; eapply poss_steps_domain; eauto|].
      eapply ac_domain; eauto.
    Defined.

    Lemma ac_steps_π_active : forall Δ t ls1 ls2 ρf Hpstep,
      domain_equiv (ac_active (ac_steps_π Δ t ls1 ls2 ρf Hpstep))
                   (ac_active Δ).
    Proof. intros; apply domain_equiv_refl. Qed.

    Variant ac_branch_prop (Δ : AbstractConfigProp) ρ π ρ' π' : AbstractConfigProp :=
    | ACBranch
      (Hposs : Δ ρ π)
      (Hpstep : poss_steps (PossOk ρ π) (PossOk ρ' π')):
      ac_branch_prop Δ ρ π ρ' π' ρ' π'.
    
      Program Definition ac_branch (Δ : AbstractConfig) ρ π ρ' π' 
        (Hposs : Δ ρ π)
        (Hpstep : poss_steps (PossOk ρ π) (PossOk ρ' π')): AbstractConfig :=
        {| ac_active := ac_active Δ;
           ac_prop := ac_branch_prop Δ ρ π ρ' π' |}.
      Next Obligation.
        exists ρ', π'.
        econstructor; eauto.
      Qed.
      Next Obligation.
        inversion H; subst.
        eapply domain_equiv_trans; [apply domain_equiv_symm; eapply poss_steps_domain; eauto|].
        eapply ac_domain; eauto.
      Defined.

    Lemma ac_branch_active : forall Δ ρ π ρ' π' Hposs Hpstep,
      domain_equiv
        (ac_active (ac_branch Δ ρ π ρ' π' Hposs Hpstep))
        (ac_active Δ).
    Proof. intros; apply domain_equiv_refl. Qed.

    Lemma ac_branch_subset_steps : forall (Δ : AbstractConfig) ρ π ρ' π' 
        Hposs Hpstep,
      ac_subset (ac_branch Δ ρ π ρ' π' Hposs Hpstep) (ac_steps Δ).
    Proof.
      intros. intros ? ? ?.
      inversion H; subst.
      econstructor; eauto.
    Qed.

    Variant ac_trylin_choice (Δ : AbstractConfig) : (option AbstractConfig) -> Prop :=
    | ACTrylinContinue Δ' :
      ac_subset Δ' (ac_steps Δ) ->
      ac_trylin_choice Δ (Some Δ')
    | ACTrylinFinish :
      ac_trylin_choice Δ None.

    Program Definition ac_trylin (Δ : AbstractConfig) ρ π ρ' π' 
        Hposs Hpstep
        (oΔ' : option AbstractConfig)
        (Htrylinchoice : ac_trylin_choice Δ oΔ') : AbstractConfig :=
      {| ac_active := ac_active Δ;
         ac_prop := match oΔ' with
                    | Some Δ' => ac_union_prop Δ' (ac_branch Δ ρ π ρ' π' Hposs Hpstep)
                    | None => ac_branch Δ ρ π ρ' π' Hposs Hpstep
                    end |}.
    Next Obligation.
      destruct oΔ'.
      - exists ρ', π'. right. econstructor; eauto.
      - exists ρ', π'. econstructor; eauto.
    Qed.
    Next Obligation.
      inversion Htrylinchoice; subst; simpl in *.
      - inversion H; subst.
        + eapply domain_equiv_trans; [eapply ac_domain; eauto|].
          eapply domain_equiv_trans; [apply ac_subset_active; exact H0|].
          apply ac_steps_active.
        + exact (ac_domain (ac_branch Δ ρ π ρ' π' Hposs Hpstep) _ _ H1).
      - exact (ac_domain (ac_branch Δ ρ π ρ' π' Hposs Hpstep) _ _ H).
    Defined.

    Lemma ac_trylin_active : forall Δ ρ π ρ' π' Hposs Hpstep oΔ' Hchoice,
      domain_equiv
        (ac_active (ac_trylin Δ ρ π ρ' π' Hposs Hpstep oΔ' Hchoice))
        (ac_active Δ).
    Proof. intros; apply domain_equiv_refl. Qed.

    Lemma ac_trylin_single : forall Δ ρ π ρ' π' Hposs Hstep Hnext,
      ac_equiv (ac_trylin Δ ρ π ρ' π' Hposs Hstep None Hnext) (ac_singleton ρ' π').
    Proof.
      intros. split; inversion 1; subst; try constructor; eauto.
    Qed.

    Lemma ac_trylin_subset_steps (Δ : AbstractConfig) ρ π ρ' π'
        Hposs Hpstep
        (oΔ' : option AbstractConfig)
        Htrylinchoice :
      ac_subset (ac_trylin Δ ρ π ρ' π' Hposs Hpstep oΔ' Htrylinchoice) (ac_steps Δ).
    Proof.
      intros.
      intros ? ? ?.
      inversion Htrylinchoice; subst; simpl in *.
      - inversion H; subst.
        + apply H0; auto.
        + apply ac_branch_subset_steps in H1; auto.
      - apply ac_branch_subset_steps in H; auto.
    Qed.

    Section ACSA.
      Context `{FJ : Join (State VF)} {FSA : SeparationAlgebra (State VF)} {Funit : SeparationAlgebraUnit (State VF) FSA}.

      (* Record ac_join (ac1 ac2 ac3 : AbstractConfig) : Prop :=
      {
        ACJoin: forall ρ1 ρ2 π1 π2, ac1 ρ1 π1 -> ac2 ρ2 π2 ->
            exists ρ π, ac3 ρ π /\ join ρ1 ρ2 ρ /\ @join _ tmap_Join π1 π2 π;
        ACSplit: forall ρ π, ac3 ρ π -> exists ρ1 ρ2 π1 π2, ac1 ρ1 π1 /\ ac2 ρ2 π2
                                /\ join ρ1 ρ2 ρ /\ @join _ tmap_Join π1 π2 π
      }.
      Instance ac_Join : Join AbstractConfig := ac_join.
      Program Instance : SeparationAlgebra AbstractConfig.
      Next Obligation.
        inversion H.
        constructor; intros.
        - specialize (ACJoin0 _ _ _ _ H1 H0) as [? [? [? [? ?]]]].
          apply join_comm in H3.
          apply (@join_comm _ _ tmap_SA) in H4. eauto.
        - apply ACSplit0 in H0 as [? [? [? [? [? [? [? ?]]]]]]].
          apply join_comm in H2.
          apply (@join_comm _ _ tmap_SA) in H3.
          do 4 eexists; eauto.
      Qed.
      Next Obligation.
        inversion H; inversion H0.
        eauto. *)

      (* Definition ac_disjoint (ac1 ac2 : AbstractConfigProp) : Prop :=
        forall ρ1 ρ2 π1 π2, ac1 ρ1 π1 -> ac2 ρ2 π2 ->
          exists ρ π, join ρ1 ρ2 ρ /\ @join _ tmap_Join π1 π2 π. *)

      Definition ac_disjoint (ac1 ac2 : AbstractConfigProp) : Prop :=
        exists ρ1 ρ2 ρ π1 π2 π, ac1 ρ1 π1 /\ ac2 ρ2 π2 /\
          join ρ1 ρ2 ρ /\ @join _ tmap_Join π1 π2 π.

      Ltac destruct_disjoint H := destruct H as (?ρ1&?ρ2&?ρ&?π1&?π2&?π&?&?&?&?).
      
      Lemma ac_disjoint_symm: forall ac1 ac2,
        ac_disjoint ac1 ac2 -> ac_disjoint ac2 ac1.
      Proof.
        intros.
        destruct_disjoint H.
        apply join_comm in H1. apply (@join_comm _ _ tmap_SA) in H2.
        do 6 eexists; eauto.
      Qed.

      Variant ac_join_prop (ac1 ac2 : AbstractConfigProp) : AbstractConfigProp :=
      | ACJoinProp : forall ρ1 ρ2 π1 π2 ρ π,
          ac1 ρ1 π1 -> ac2 ρ2 π2 ->
          join ρ1 ρ2 ρ -> @join _ tmap_Join π1 π2 π ->
          ac_join_prop ac1 ac2 ρ π.
      Program Definition ac_join (ac1 ac2 : AbstractConfig)
        (Hdisjoint : ac_disjoint ac1 ac2) : AbstractConfig :=
        {| ac_active := domain_union (ac_active ac1) (ac_active ac2);
           ac_prop := ac_join_prop ac1 ac2 |}.
      Next Obligation.
        destruct_disjoint Hdisjoint.
        do 2 eexists; econstructor; eauto.
      Qed.
      Next Obligation.
        inversion H; subst.
        eapply domain_equiv_trans; [eapply map_domain_join; eauto|].
        unfold domain_union. intros t0.
        rewrite (ac_domain ac1 _ _ H0 t0), (ac_domain ac2 _ _ H1 t0).
        reflexivity.
      Qed.

      Lemma ac_compatible_domain_disjoint : forall (ac1 ac2 : AbstractConfig),
        ac_disjoint ac1 ac2 ->
        domain_disjoint (ac_active ac1) (ac_active ac2).
      Proof.
        intros ac1 ac2 Hd.
        destruct_disjoint Hd.
        pose proof (map_domain_join_disjoint _ _ _ H2) as Hmap.
        pose proof (ac_domain ac1 _ _ H) as Hdom1.
        pose proof (ac_domain ac2 _ _ H0) as Hdom2.
        intros t Ha1 Ha2. eapply Hmap.
        - apply (proj2 (Hdom1 t)); exact Ha1.
        - apply (proj2 (Hdom2 t)); exact Ha2.
      Qed.

      Lemma ac_join_active : forall (ac1 ac2 : AbstractConfig)
        (Hd : ac_disjoint ac1 ac2),
        domain_equiv (ac_active (ac_join ac1 ac2 Hd))
                     (domain_union (ac_active ac1) (ac_active ac2)).
      Proof. intros; apply domain_equiv_refl. Qed.

      Lemma ac_join_active_disjoint : forall (ac1 ac2 : AbstractConfig)
        (Hd : ac_disjoint ac1 ac2),
        domain_disjoint (ac_active ac1) (ac_active ac2).
      Proof. intros; eapply ac_compatible_domain_disjoint; eauto. Qed.

      Lemma ac_join_comm: forall ac1 ac2 Hd1 Hd2 ρ π,
        ac_join ac1 ac2 Hd1 ρ π -> ac_join ac2 ac1 Hd2 ρ π.
      Proof.
        intros. inversion H; subst.
        econstructor; eauto.
        apply join_comm; auto.
      Qed.

      Lemma ac_disjoint_distr: forall 
        (mx my mz mxy mxyz: AbstractConfig)
        (x: ac_disjoint mx my)
        (H1: ac_equiv mxy (ac_join mx my x))
        (x0: ac_disjoint mxy mz)
        (H2: ac_equiv mxyz (ac_join mxy mz x0)),
        ac_disjoint my mz.
      Proof.
        intros.
        (* pose proof x.
        destruct_disjoint H. *)
        pose proof x0.
        destruct_disjoint H.
        apply H1 in H.
        inversion H; subst.
        pose proof join_assoc _ _ _ _ _ H7 H3 as [? [? ?]].
        pose proof @join_assoc _ _ tmap_SA _ _ _ _ _ H8 H4 as [? [? ?]].
        do 6 eexists; eauto.
      Qed.

      #[global] Instance ac_Join : Join AbstractConfig :=
        fun ac1 ac2 ac => 
          exists (Hdisjoint : ac_disjoint ac1 ac2),
          ac_equiv ac (ac_join ac1 ac2 Hdisjoint).

      Lemma join_ac_active : forall ac1 ac2 ac,
        join ac1 ac2 ac ->
        domain_equiv (ac_active ac)
                     (domain_union (ac_active ac1) (ac_active ac2)).
      Proof.
        intros ac1 ac2 ac [Hd Heq].
        eapply domain_equiv_trans; [apply ac_equiv_active; exact Heq|].
        apply ac_join_active.
      Qed.

      Lemma join_ac_active_disjoint : forall ac1 ac2 ac,
        join ac1 ac2 ac ->
        domain_disjoint (ac_active ac1) (ac_active ac2).
      Proof.
        intros ac1 ac2 ac [Hd Heq].
        exact (ac_join_active_disjoint ac1 ac2 Hd).
      Qed.

      #[global] Program Instance ac_SA : SeparationAlgebra AbstractConfig.
      Next Obligation.
        inversion H.
        pose proof x.
        apply ac_disjoint_symm in H1.
        exists H1.
        unfold ac_equiv in *.
        split; intros.
        - apply H0 in H2. eapply ac_join_comm; eauto.
        - apply H0. eapply ac_join_comm; eauto.
      Qed.
      Next Obligation.
        inversion H. inversion H0.
        clear H H0.

        assert (ac_disjoint my mz).
        {
          eapply ac_disjoint_distr; eauto.
        }
        assert (ac_disjoint mx (ac_join my mz H)).
        {
          pose proof x0.
          destruct_disjoint H0.
          apply H1 in H0.
          inversion H0; subst.
          pose proof join_assoc _ _ _ _ _ H8 H4 as [? [? ?]].
          pose proof @join_assoc _ _ tmap_SA _ _ _ _ _ H9 H5 as [? [? ?]].
          do 6 eexists; split; eauto. split; eauto.
          econstructor; eauto.
        }
        exists (ac_join my mz H).
        split.
        - exists H. reflexivity.
        - exists H0.
          etransitivity; eauto.
          split; intros.
          + inversion H3; subst.
            apply H1 in H4.
            inversion H4; subst.
            pose proof join_assoc _ _ _ _ _ H10 H6 as [? [? ?]].
            pose proof @join_assoc _ _ tmap_SA _ _ _ _ _ H11 H7 as [? [? ?]].
            econstructor; eauto.
            econstructor; eauto.
          + inversion H3; subst.
            inversion H5; subst.
            apply join_comm in H6, H10. apply (@join_comm _ _ tmap_SA) in H7, H11.
            pose proof join_assoc _ _ _ _ _ H10 H6 as [? [? ?]].
            pose proof @join_assoc _ _ tmap_SA _ _ _ _ _ H11 H7 as [? [? ?]].
            apply join_comm in H13, H12. apply (@join_comm _ _ tmap_SA) in H15, H14.
            econstructor; eauto.
            apply H1. econstructor; eauto.
      Defined.

      Lemma ac_unit_join : forall n : AbstractConfig,
        join n (ac_singleton ue (LinCCAL.TMap.Leaf LinState)) n.
      Proof.
        econstructor. Unshelve.
        split; intros.
        - econstructor; eauto; try constructor.
        - inversion H; subst.
          inversion H1; subst.
          apply join_comm, unit_spec in H2; subst.
          apply (@join_comm _ _ tmap_SA), (@unit_spec _ _ _ tmap_unit) in H3; subst.
          auto.
        - pose proof ac_nonempty n as [? [? ?]].
          do 6 eexists.
          split; eauto.
          split; constructor.
          + apply unit_join.
          + apply (@unit_join _ _ _ tmap_unit).
      Qed.

      Lemma ac_unit_active :
        domain_equiv
          (ac_active (ac_singleton ue (LinCCAL.TMap.Leaf LinState)))
          domain_empty.
      Proof. apply map_domain_empty. Qed.

      #[global] Program Instance ac_unit : SeparationAlgebraUnit AbstractConfig ac_SA :=
        {| ue := ac_singleton ue (LinCCAL.TMap.Leaf _) |}.
      Next Obligation.
        apply ac_unit_join.
      Qed.
      Next Obligation.
        intros ? ? ?.
        inversion H; subst.
        apply AbstractConfig_ext.
        unfold ac_equiv in *. intros ρ π.
        rewrite H0. split; intros.
        - econstructor; eauto.
          + constructor.
          + apply (@join_comm _ _ tmap_SA), (@unit_join _ _ tmap_SA tmap_unit π).
        - inversion H1; subst.
          inversion H2; subst.
          apply unit_spec in H4; subst.
          apply (@unit_spec _ _ _ tmap_unit) in H5; subst; auto.
      Defined.
    End ACSA.

  End AbstractConfig.

  Arguments AbstractConfigProp {F} VF.
  Arguments AbstractConfig {F} VF.

  #[global] Existing Instance Equivalence_ACEquiv.

  Delimit Scope ac_scope with AbstractConfig.
  Bind Scope ac_scope with AbstractConfig.

  Notation "[( ρ , π )]" := (ac_singleton ρ π) (at level 10) : ac_scope.
  Notation "Δ1 ⊆ Δ2" := (ac_subset Δ1 Δ2) (at level 70) : ac_scope.
  Notation "Δ1 ≡ Δ2" := (ac_equiv Δ1 Δ2) (at level 70) : ac_scope.
  Notation "Δ1 ∪ Δ2" := (ac_union Δ1 Δ2) (at level 50) : ac_scope.
  Notation "Δ1 ∩ Δ2" := (ac_intersect_prop Δ1 Δ2) (at level 40) : ac_scope.
  
  Delimit Scope poss_scope with Poss.
  Bind Scope poss_scope with Poss.
  
  Notation "( ρ , π )" := (PossOk ρ π) : poss_scope.

End Semantics.
