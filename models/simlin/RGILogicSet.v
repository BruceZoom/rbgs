Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import Relation_Operators Operators_Properties.
Require Import Classical.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import SeparationAlgebra.
Require Import LTSLocality.
Require Import Assertion.
Require Import RGISimulationSet.

(** Production set-based program logic.  The finite abstract-update chain
    is separated from the coinductive concrete core;
    this is definitionally the same mixed fixed point as an inductive head,
    while avoiding Coq's guarded-elimination restriction in structural
    proofs.  This is the production set-level logic. *)
Module RGILogic.
  Import Reg LinCCALBase LTSSpec Semantics AssertionsSet Lang.
  Open Scope assertion_scope.

  Section ProgramLogic.
    Context {E F : Op.t} {VE : @LTS E} {VF : @LTS F}.
    Context (R G : @RGRelation _ _ VE VF).
    Context (I : @Assertion (@ProofState _ _ VE VF)).
    Context (t : tid).

    (** A finite sequence of possibility updates.  [UpdateCons] also stores
        the same unsafe-precondition gate used by the primitive rules, so
        consequence and error weakening do not force an update after the
        source has already become erroneous. *)
    Inductive UpdateChain : Assertion -> Assertion -> Prop :=
    | UpdateNil P : UpdateChain P P
    | UpdateCons : forall Punsafe P P' Pfinal,
        (⊨ Punsafe ==>> P \\// APError) ->
        (⊨ P' ==>> I) -> Stable R I P' -> (G ⊨ P ⭆ P') ->
        UpdateChain P' Pfinal -> UpdateChain Punsafe Pfinal.

    Inductive HTripleCore {A}
        (X : Assertion -> Prog E A -> (A -> Assertion) -> Prop) :
        Assertion -> Prog E A -> (A -> Assertion) -> Prop :=
    | CoreRet : forall a P Q Punsafe,
        (⊨ Punsafe ==>> P \\// APError) ->
        (⊨ P ==>> Q a) -> (⊨ Q a ==>> I) -> Stable R I (Q a) ->
        HTripleCore X Punsafe (Ret a) Q
    | CoreVis : forall P Q m k P' Q' Punsafe,
        (⊨ Punsafe ==>> P \\// APError) ->
        (⊨ P ==>> ANoError (Build_ThreadEvent t (InvEv m))) ->
        (⊨ P' ==>> I) -> (forall a, ⊨ Q' a ==>> I) ->
        Stable R I P' -> (forall a, Stable R I (Q' a)) ->
        (G ⊨ P [ Build_ThreadEvent t (InvEv m) ]⭆ P') ->
        (forall ret,
          G ⊨ P' [ Build_ThreadEvent t (ResEv m ret) ]⭆ Q' ret) ->
        (forall ret, X (Q' ret) (k ret) Q) ->
        HTripleCore X Punsafe (Vis m k) Q
    | CoreTau : forall P Q p,
        X P p Q -> HTripleCore X P (Tau p) Q.

    CoInductive HTripleProvable {A} (P : Assertion) (p : Prog E A)
        (Q : A -> Assertion) : Prop :=
    | HTripleRoll : forall Pcore,
        UpdateChain P Pcore ->
        HTripleCore HTripleProvable Pcore p Q ->
        HTripleProvable P p Q.

    Inductive UpdateChainRanked : nat -> Assertion -> Assertion -> Prop :=
    | UpdateRankNil P : UpdateChainRanked O P P
    | UpdateRankCons : forall n Punsafe P P' Pfinal,
        (⊨ Punsafe ==>> P \\// APError) ->
        (⊨ P' ==>> I) -> Stable R I P' -> (G ⊨ P ⭆ P') ->
        UpdateChainRanked n P' Pfinal ->
        UpdateChainRanked (S n) Punsafe Pfinal.

    Lemma update_chain_has_rank P P' : UpdateChain P P' ->
      exists n, UpdateChainRanked n P P'.
    Proof.
      intro H. induction H.
      - exists O. constructor.
      - destruct IHUpdateChain as [n Hrank].
        exists (S n). econstructor; eauto.
    Qed.

    Lemma update_chain_ranked_unrank n P P' :
      UpdateChainRanked n P P' -> UpdateChain P P'.
    Proof.
      intro H. induction H.
      - constructor.
      - eapply UpdateCons; eauto.
    Qed.

    Inductive HTripleRanked {A} : nat -> Assertion -> Prog E A ->
        (A -> Assertion) -> Prop :=
    | HTripleRankIntro : forall n P p Q Pcore,
        UpdateChainRanked n P Pcore ->
        HTripleCore HTripleProvable Pcore p Q ->
        HTripleRanked n P p Q.

    Lemma htriple_has_rank {A} P (p : Prog E A) Q :
      HTripleProvable P p Q -> exists n, HTripleRanked n P p Q.
    Proof.
      intros [Pcore Hadmin Hcore].
      destruct (update_chain_has_rank _ _ Hadmin) as [n Hrank].
      exists n. econstructor; eauto.
    Qed.

    Lemma htriple_ranked_provable {A} n P (p : Prog E A) Q :
      HTripleRanked n P p Q -> HTripleProvable P p Q.
    Proof.
      intro Hrank. destruct Hrank as
        [rank0 P0 p0 Q0 Pcore Hadmin Hcore].
      econstructor.
      - apply update_chain_ranked_unrank in Hadmin. exact Hadmin.
      - exact Hcore.
    Qed.

    Definition HTripleView {A}
        (X : Assertion -> Prog E A -> (A -> Assertion) -> Prop)
        P p Q : Prop :=
      exists Pcore, UpdateChain P Pcore /\ HTripleCore X Pcore p Q.

    Lemma HTripleProvable_coinduction {A}
        (X : Assertion -> Prog E A -> (A -> Assertion) -> Prop) :
      (forall P p Q, X P p Q -> HTripleView X P p Q) ->
      forall P p Q, X P p Q -> HTripleProvable P p Q.
    Proof.
      intros Hstep. cofix CIH. intros P p Q HX.
      destruct (Hstep P p Q HX) as [Pcore [Hadmin Hcore]].
      destruct Hcore.
      - econstructor; [exact Hadmin|]. eapply CoreRet; eauto.
      - econstructor; [exact Hadmin|]. eapply CoreVis; eauto.
      - econstructor; [exact Hadmin|]. apply CoreTau. eapply CIH; eauto.
    Qed.

    Lemma HTripleView_include {A}
        (X : Assertion -> Prog E A -> (A -> Assertion) -> Prop) :
      (forall P p Q, HTripleProvable P p Q -> X P p Q) ->
      forall P p Q, HTripleProvable P p Q -> HTripleView X P p Q.
    Proof.
      intros Hincl P p Q [Pcore Hadmin Hcore].
      exists Pcore. split; [exact Hadmin|]. destruct Hcore.
      - eapply CoreRet; eauto.
      - eapply CoreVis; eauto.
      - apply CoreTau. apply Hincl. exact H.
    Qed.

    Lemma provable_ret {A} : forall (a : A) (P : Assertion)
        (Q : A -> Assertion) (Punsafe : Assertion),
      (⊨ Punsafe ==>> P \\// APError) ->
      (⊨ P ==>> Q a) -> (⊨ Q a ==>> I) -> Stable R I (Q a) ->
      HTripleProvable Punsafe (Ret a) Q.
    Proof. intros. econstructor; [constructor|]. eapply CoreRet; eauto. Qed.

    Lemma provable_vis {A} : forall (P : Assertion) (Q : A -> Assertion)
        (m : Sig.op E) (k : Sig.ar m -> Prog E A) (P' : Assertion)
        (Q' : Sig.ar m -> Assertion) (Punsafe : Assertion),
      (⊨ Punsafe ==>> P \\// APError) ->
      (⊨ P ==>> ANoError (Build_ThreadEvent t (InvEv m))) ->
      (⊨ P' ==>> I) -> (forall a, ⊨ Q' a ==>> I) ->
      Stable R I P' -> (forall a, Stable R I (Q' a)) ->
      (G ⊨ P [ Build_ThreadEvent t (InvEv m) ]⭆ P') ->
      (forall ret,
        G ⊨ P' [ Build_ThreadEvent t (ResEv m ret) ]⭆ Q' ret) ->
      (forall ret, HTripleProvable (Q' ret) (k ret) Q) ->
      HTripleProvable Punsafe (Vis m k) Q.
    Proof. intros. econstructor; [constructor|]. eapply CoreVis; eauto. Defined.

    Lemma provable_tau {A} : forall (P : Assertion) (Q : A -> Assertion)
        (p : Prog E A),
      HTripleProvable P p Q -> HTripleProvable P (Tau p) Q.
    Proof. intros. econstructor; [constructor|]. now apply CoreTau. Defined.

    Lemma provable_linstep {A} : forall (P P' : Assertion)
        (Q : A -> Assertion) (p : Prog E A),
      (⊨ P' ==>> I) -> Stable R I P' -> (G ⊨ P ⭆ P') ->
      HTripleProvable P' p Q -> HTripleProvable P p Q.
    Proof.
      intros P P' Q p HI HS HU [Pcore Hadmin Hcore].
      econstructor; [|exact Hcore].
      eapply UpdateCons with (P := P) (P' := P'); eauto.
      apply ImplDisjLeft, ImplRefl.
    Qed.
  End ProgramLogic.

  Notation "[ VE , VF , R , G , I , t ] ⊢ {{ P }} c {{ Q }}" :=
    (@HTripleProvable _ _ VE VF R G I t _ P c Q) (at level 100).

  Section DerivedRules.
    Context {E F : Op.t} {VE : @LTS E} {VF : @LTS F}.
    Context (R G : @RGRelation _ _ VE VF) (I : @Assertion (@ProofState _ _ VE VF)).
    Context (t : tid).

    Lemma provable_perror {A} : forall P P' Q (p : Prog E A),
      (⊨ P ==>> P' \\// APError) ->
      [VE, VF, R, G, I, t] ⊢ {{ P' }} p {{ Q }} ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q }}.
    Proof.
      intros Pstart P' Qstart pstart Hstart Hproof.
      eapply (@HTripleProvable_coinduction E F VE VF R G I t A
        (fun P p Q => exists P',
          (⊨ P ==>> P' \\// APError) /\
          [VE, VF, R, G, I, t] ⊢ {{ P' }} p {{ Q }})).
      - intros P0 p0 Q0 [Pmid [Hweak [Pcore Hadmin Hcore]]].
        inversion Hadmin; subst.
        + exists P0. split; [constructor|]. destruct Hcore.
          * eapply CoreRet with (P := P); eauto.
            firstorder.
          * eapply CoreVis with (P := P) (P' := P'0) (Q' := Q'); eauto.
            firstorder.
            intros ret. exists (Q' ret). split.
            -- apply ImplDisjLeft, ImplRefl.
            -- apply H7.
          * apply CoreTau. eauto.
        + exists Pcore. split.
          * unshelve refine (@UpdateCons E F VE VF R G I
              P0 P P'0 Pcore _ H0 H1 H2 H3).
            intros state HP0.
            destruct (Hweak state HP0) as [HPu | HE].
            -- apply H in HPu. exact HPu.
            -- right; exact HE.
          * destruct Hcore.
            -- eapply CoreRet; eauto.
            -- eapply CoreVis with (P := P1) (P' := P'1) (Q' := Q').
               ++ exact H4.
               ++ exact H5.
               ++ exact H6.
               ++ exact H7.
               ++ exact H8.
               ++ exact H9.
               ++ exact H10.
               ++ exact H11.
               ++ intros ret.
               exists (Q' ret). split.
               ** apply ImplDisjLeft, ImplRefl.
               ** apply H12.
            -- apply CoreTau. exists P1. split.
               ++ apply ImplDisjLeft, ImplRefl.
               ++ exact H4.
      - exists P'. split; assumption.
    Qed.

    Lemma provable_vis_safe {A} : forall P Q m
        (k : Sig.ar m -> Prog E A) P' Q',
      (⊨ P ==>> ANoError (Build_ThreadEvent t (InvEv m))) ->
      (⊨ P' ==>> I) -> (forall a, ⊨ Q' a ==>> I) ->
      Stable R I P' -> (forall a, Stable R I (Q' a)) ->
      (G ⊨ P [ Build_ThreadEvent t (InvEv m) ]⭆ P') ->
      (forall ret,
        G ⊨ P' [ Build_ThreadEvent t (ResEv m ret) ]⭆ Q' ret) ->
      (forall ret, [VE, VF, R, G, I, t] ⊢ {{ Q' ret }} k ret {{ Q }}) ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} Vis m k {{ Q }}.
    Proof. intros. eapply provable_vis; eauto. apply ImplDisjLeft, ImplRefl. Qed.

    Lemma provable_ret_safe {A} : forall (a : A) P Q,
      (⊨ P ==>> Q a) -> (⊨ Q a ==>> I) -> Stable R I (Q a) ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} Ret a {{ Q }}.
    Proof.
      intros. eapply provable_ret with (P := P); eauto.
      apply ImplDisjLeft, ImplRefl.
    Qed.

    Lemma provable_conseq_weak_pre {A} : forall P Q P' (p : Prog E A),
      (⊨ P ==>> P') ->
      [VE, VF, R, G, I, t] ⊢ {{ P' }} p {{ Q }} ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q }}.
    Proof.
      intros P Q P' p Hweak Hproof.
      eapply provable_perror; [|exact Hproof].
      eapply ImplTrans; [exact Hweak|]. apply ImplDisjLeft, ImplRefl.
    Qed.

    Lemma provable_conseq_weak_post {A} : forall P Q Q' (p : Prog E A),
      (forall a, ⊨ Q a ==>> I) -> (forall a, Stable R I (Q a)) ->
      (forall a, ⊨ Q' a ==>> Q a) ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q' }} ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q }}.
    Proof.
      intros Pstart Qstart Q' pstart Hinvstart Hstablestart
        Hpoststart Hproof.
      eapply (@HTripleProvable_coinduction E F VE VF R G I t A
        (fun P p Q => exists Q',
          (forall a, ⊨ Q' a ==>> Q a) /\
          (forall a, ⊨ Q a ==>> I) /\
          (forall a, Stable R I (Q a)) /\
          [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q' }})).
      - intros P0 p0 Q0 [Q1 [HQ [HQI [HQS [Pcore Hadmin Hcore]]]]].
        exists Pcore. split; [exact Hadmin|]. destruct Hcore.
        + eapply CoreRet with (P := P); eauto. eapply ImplTrans; eauto.
        + eapply CoreVis with (P := P) (P' := P'); eauto.
        + apply CoreTau. exists Q. repeat split; assumption.
      - exists Q'. repeat split; assumption.
    Qed.

    Lemma provable_conseq_weak {A} : forall P Q P' Q' (p : Prog E A),
      (forall a, ⊨ Q a ==>> I) -> (forall a, Stable R I (Q a)) ->
      (⊨ P ==>> P') -> (forall a, ⊨ Q' a ==>> Q a) ->
      [VE, VF, R, G, I, t] ⊢ {{ P' }} p {{ Q' }} ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q }}.
    Proof.
      intros. eapply provable_conseq_weak_pre; eauto.
      eapply provable_conseq_weak_post; eauto.
    Qed.

    Lemma update_chain_trans : forall P Pmid Pfinal,
      UpdateChain R G I P Pmid -> UpdateChain R G I Pmid Pfinal ->
      UpdateChain R G I P Pfinal.
    Proof.
      intros P Pmid Pfinal Hleft Hright. induction Hleft.
      - exact Hright.
      - eapply UpdateCons; eauto.
    Qed.

    Lemma provable_seq {A B} : forall (p : Prog E A)
        (k : A -> Prog E B) P Q Q',
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q' }} ->
      (forall a, [VE, VF, R, G, I, t] ⊢ {{ Q' a }} k a {{ Q }}) ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} bindProg p k {{ Q }}.
    Proof.
      intros pstart kstart Pstart Qstart Q'start Hpstart Hkstart.
      eapply (@HTripleProvable_coinduction E F VE VF R G I t B
        (fun P pk Q =>
          [VE, VF, R, G, I, t] ⊢ {{ P }} pk {{ Q }} \/
          exists A (p : Prog E A) (k : A -> Prog E B) Q',
            pk = bindProg p k /\
            [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q' }} /\
            (forall a, [VE, VF, R, G, I, t] ⊢ {{ Q' a }} k a {{ Q }}))).
      - intros P0 pk Q0 HX. destruct HX as [[Pcore Hadmin Hcore] |
          [T [p [k [Q' [-> [[Pcore Hadmin Hcore] Hk]]]]]]].
        + exists Pcore. split; [exact Hadmin|]. destruct Hcore.
          * eapply CoreRet; eauto.
          * eapply CoreVis; eauto.
          * apply CoreTau. left. exact H.
        + destruct Hcore.
          * rewrite bindRetUnfold.
          assert ([VE, VF, R, G, I, t] ⊢ {{ P }} k a {{ Q0 }}) as Hcont.
          { eapply provable_conseq_weak_pre; [exact H0|apply Hk]. }
          assert ([VE, VF, R, G, I, t] ⊢ {{ Punsafe }} k a {{ Q0 }})
            as Hcont'.
          { eapply provable_perror; eauto. }
          destruct Hcont' as [Pnext Hadmin' Hcore'].
          exists Pnext. split.
          -- apply update_chain_trans with (Pmid := Punsafe);
               assumption.
          -- destruct Hcore'.
             ++ eapply CoreRet; eauto.
             ++ eapply CoreVis; eauto.
             ++ apply CoreTau. left. exact H3.
          * exists Punsafe. split; [exact Hadmin|]. rewrite bindVisUnfold.
          eapply CoreVis; eauto.
          intros ret. right. do 4 eexists. split; [reflexivity|]. split; eauto.
          * exists P. split; [exact Hadmin|]. rewrite bindTauUnfold.
          apply CoreTau.
          right. do 4 eexists. split; [reflexivity|]. split; eauto.
      - right. do 4 eexists.
        split; [reflexivity|]. split; eauto.
    Qed.

    (** The proof interface for finite [ForEach] programs.  [Inv remaining
        acc] describes the state before processing [remaining].  The exit is
        itself a triple so that it may contain a final possibility update.
        This rule alone performs the structural induction and sequencing. *)
    Lemma provable_foreach {Item Acc}
        (step : Acc -> Item -> Prog E Acc)
        (Inv : list Item -> Acc -> Assertion)
        (Q : Acc -> Assertion) :
      (forall acc,
        [VE, VF, R, G, I, t] ⊢ {{ Inv nil acc }}
          Ret acc {{ Q }}) ->
      (forall item items acc,
        [VE, VF, R, G, I, t] ⊢ {{ Inv (item :: items) acc }}
          step acc item {{ fun acc' => Inv items acc' }}) ->
      forall items acc,
        [VE, VF, R, G, I, t] ⊢ {{ Inv items acc }}
          foldM step items acc {{ Q }}.
    Proof.
      intros Hexit Hstep items.
      induction items as [|item items IH]; intro acc.
      - rewrite foldM_nil. apply Hexit.
      - rewrite foldM_cons. eapply provable_seq with
            (Q' := fun acc' => Inv items acc').
        + apply Hstep.
        + intro acc'. apply IH.
    Qed.

    Lemma provable_dowhile_unroll {A} : forall
        (pbody piter : Prog E A) (b : A -> bool) P Q,
      [VE, VF, R, G, I, t] ⊢ {{ P }} bindProg piter
        (fun r => if b r then Tau (whileAux b pbody pbody) else Ret r)
        {{ Q }} ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} whileAux b pbody piter {{ Q }}.
    Proof.
      intros pbody0 piter0 b0 P0 Q0 Hproof.
      eapply (@HTripleProvable_coinduction E F VE VF R G I t A
        (fun P p Q =>
          [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q }} \/
          exists pbody piter b,
            p = whileAux b pbody piter /\
            [VE, VF, R, G, I, t] ⊢ {{ P }} bindProg piter
              (fun r => if b r then Tau (whileAux b pbody pbody)
                        else Ret r) {{ Q }})).
      - intros P p Q [Hdirect | [pbody [piter [b [-> Hbind]]]]].
        + eapply HTripleView_include; [|exact Hdirect].
          intros; left; assumption.
        + destruct piter.
          * rewrite bindVisUnfold in Hbind.
            destruct Hbind as [Pcore Hadmin Hcore].
            dependent destruction Hcore.
            exists Punsafe. split; [exact Hadmin|].
            rewrite whileAuxVisUnfold.
            eapply CoreVis; eauto.
            intros ret. right. do 3 eexists. split; [reflexivity|].
            exact (H7 ret).
          * rewrite bindRetUnfold in Hbind.
            rewrite whileAuxRetUnfold.
            eapply HTripleView_include; [|exact Hbind].
            intros; left; assumption.
          * rewrite bindTauUnfold in Hbind.
            destruct Hbind as [Pcore Hadmin Hcore].
            dependent destruction Hcore.
            exists P1. split; [exact Hadmin|].
            rewrite whileAuxTauUnfold. apply CoreTau.
            right. do 3 eexists. split; [reflexivity|]. exact H.
      - right. do 3 eexists. split; [reflexivity|exact Hproof].
    Qed.

    Lemma provable_dowhile {A} : forall Iloop Q b (p : Prog E A),
      (forall a, ⊨ Q a //\\ ⌜b a = true⌝ ==>> Iloop) ->
      (forall a, ⊨ Q a ==>> I) ->
      (forall a, Stable R I (Q a)) ->
      [VE, VF, R, G, I, t] ⊢ {{ Iloop }} p {{ Q }} ->
      [VE, VF, R, G, I, t] ⊢ {{ Iloop }}
        Do { p } While (b x) >= x
        {{ fun a => Q a //\\ ⌜b a = false⌝ }}.
    Proof.
      intros Iloop Q b p Hpost HQI HQstable Hbody.
      unfold doWhile.
      eapply (@HTripleProvable_coinduction E F VE VF R G I t A
        (fun P0 p0 Q0 =>
          [VE, VF, R, G, I, t] ⊢ {{ P0 }} p0 {{ Q0 }} \/
          exists piter,
            p0 = whileAux b p piter /\
            Q0 = (fun a => Q a //\\ ⌜b a = false⌝) /\
            [VE, VF, R, G, I, t] ⊢ {{ P0 }} piter {{ Q }})).
      - intros P0 p0 Q0 [Hdirect | [piter [-> [-> Hiter]]]].
        + eapply HTripleView_include; [|exact Hdirect].
          intros; left; assumption.
        + destruct Hiter as [Pcore Hadmin Hcore].
          exists Pcore. split; [exact Hadmin|]. destruct Hcore.
          * rewrite whileAuxRetUnfold. destruct (b a) eqn:Hb.
            -- apply CoreTau. right. exists p. repeat split; auto.
               eapply provable_perror; [|exact Hbody].
               intros state HPunsafe. apply H in HPunsafe as [HPsafe|Herr].
               ++ left. apply (Hpost a). split;
                    [apply H0; exact HPsafe|exact Hb].
               ++ right; exact Herr.
            -- eapply CoreRet with (P := P).
               ++ exact H.
               ++ intros state HPsafe. split; [apply H0; exact HPsafe|exact Hb].
               ++ intros state [HQ _]. apply HQI with a; exact HQ.
               ++ eapply EquivStable with (P := Q a).
                  ** intros state. split; intros Hstate.
                     --- split; [exact Hstate|exact Hb].
                     --- destruct Hstate; assumption.
                  ** exact (HQstable a).
          * rewrite whileAuxVisUnfold.
            eapply CoreVis; eauto.
          * rewrite whileAuxTauUnfold. apply CoreTau. right.
            exists p0. repeat split; auto.
      - right. exists p. repeat split; auto.
    Qed.

    Lemma provable_doloop_data {TT FT} :
      forall (Iloop : TT -> Assertion) (Q : FT -> Assertion)
        (p : TT -> Prog E (TT + FT)) init,
      (forall a, ⊨ Q a ==>> I) ->
      (forall a, Stable R I (Q a)) ->
      (forall x, @HTripleProvable E F VE VF R G I t (TT + FT)
        (Iloop x) (p x)
        (fun r : TT + FT => match r with
                  | inl x' => Iloop x'
                  | inr v => Q v
                  end)) ->
      [VE, VF, R, G, I, t] ⊢ {{ Iloop init }} loop p init {{ Q }}.
    Proof.
      intros Iloop Q p init HQI HQstable Hbody.
      unfold loop.
      eapply (@HTripleProvable_coinduction E F VE VF R G I t FT
        (fun P0 p0 Q0 =>
          [VE, VF, R, G, I, t] ⊢ {{ P0 }} p0 {{ Q0 }} \/
          exists x piter,
            p0 = loopAux p piter /\ Q0 = Q /\
            @HTripleProvable E F VE VF R G I t (TT + FT) P0 piter
              (fun r : TT + FT => match r with
                        | inl x' => Iloop x'
                        | inr v => Q v
                        end))).
      - intros P0 p0 Q0 [Hdirect | [x [piter [-> [-> Hiter]]]]].
        + eapply HTripleView_include; [|exact Hdirect].
          intros; left; assumption.
        + remember (fun r : TT + FT => match r with
                    | inl x' => Iloop x'
                    | inr v => Q v
                    end) as Qloop eqn:HQloop in Hiter.
          destruct Hiter as [Pcore Hadmin Hcore].
          exists Pcore. split; [exact Hadmin|]. destruct Hcore.
          * rewrite loopAuxRetUnfold. destruct a as [next|result].
            -- rewrite HQloop in H0.
               apply CoreTau. right. exists next, (p next).
               repeat split; auto.
               eapply provable_perror; [|apply Hbody].
               intros state HPunsafe. apply H in HPunsafe as [HPsafe|Herr].
               ++ left. apply H0; exact HPsafe.
               ++ right; exact Herr.
            -- rewrite HQloop in H0, H1, H2.
               eapply CoreRet with (P := P); eauto.
          * rewrite loopAuxVisUnfold.
            rewrite HQloop in H7.
            eapply CoreVis; eauto.
            intros ret. right. exists x, (k ret). repeat split; auto.
          * rewrite HQloop in H. rewrite loopAuxTauUnfold.
            apply CoreTau. right.
            exists x, p0. repeat split; auto.
      - right. exists init, (p init). repeat split; auto.
    Qed.

    Lemma provable_doloop {TT FT} : forall Iloop Q
        (p : Prog E (TT + FT)),
      (forall a, ⊨ Q a ==>> I) ->
      (forall a, Stable R I (Q a)) ->
      [VE, VF, R, G, I, t] ⊢ {{ Iloop }} p
        {{ fun r => match r with
                    | inl _ => Iloop
                    | inr v => Q v
                    end }} ->
      [VE, VF, R, G, I, t] ⊢ {{ Iloop }} Do { p } Loop {{ Q }}.
    Proof.
      intros Iloop Q p HQI HQstable Hbody. unfold loop.
      eapply (@HTripleProvable_coinduction E F VE VF R G I t FT
        (fun P0 p0 Q0 =>
          [VE, VF, R, G, I, t] ⊢ {{ P0 }} p0 {{ Q0 }} \/
          exists piter,
            p0 = loopAux (fun _ : TT => p) piter /\ Q0 = Q /\
            @HTripleProvable E F VE VF R G I t (TT + FT) P0 piter
              (fun r : TT + FT => match r with
                        | inl _ => Iloop
                        | inr v => Q v
                        end))).
      - intros P0 p0 Q0 [Hdirect | [piter [-> [-> Hiter]]]].
        + eapply HTripleView_include; [|exact Hdirect].
          intros; left; assumption.
        + remember (fun r : TT + FT => match r with
                    | inl _ => Iloop
                    | inr v => Q v
                    end) as Qloop eqn:HQloop in Hiter.
          destruct Hiter as [Pcore Hadmin Hcore].
          exists Pcore. split; [exact Hadmin|]. destruct Hcore.
          * rewrite loopAuxRetUnfold. destruct a as [ignored|result].
            -- rewrite HQloop in H0. apply CoreTau. right. exists p.
               repeat split; auto.
               eapply provable_perror; [|exact Hbody].
               intros state HPunsafe. apply H in HPunsafe as [HPsafe|Herr].
               ++ left. apply H0; exact HPsafe.
               ++ right; exact Herr.
            -- rewrite HQloop in H0, H1, H2.
               eapply CoreRet with (P := P); eauto.
          * rewrite loopAuxVisUnfold. rewrite HQloop in H7.
            eapply CoreVis; eauto.
          * rewrite HQloop in H. rewrite loopAuxTauUnfold.
            apply CoreTau. right. exists p0. repeat split; auto.
      - right. exists p. repeat split; auto.
    Qed.
  End DerivedRules.

  Section MethodLogic.
    Context {E F : Op.t} (VE : @LTS E) (VF : @LTS F).
    Context (M : ModuleImpl E F).
    Context (R G : @RGRelation _ _ VE VF)
      (I : @Assertion (@ProofState E F VE VF)) (t : tid).
    Import RGISimulation.

    Record MethodProvable f P Q : Prop := {
      Pinv : ⊨ Ginv t f ⊚ I ==>> P;
      PI : ⊨ P ==>> I;
      Pstable : Stable R I P;
      Qret : forall ret, ⊨ Gret t f ret ⊚ Q ret ==>> I;
      Qlin : forall ret sigma Delta, Q ret (sigma, Delta) ->
        forall rho pi, Delta rho pi ->
          TMap.find t pi = Some (ls_linr f ret);
      Triple : [VE, VF, R, G, I, t] ⊢ {{ P }} M f t {{ Q }}
    }.

    Lemma method_updates_identity (Gbig : RGRelation) n sigma Delta :
      (forall s, Gbig s s) -> I (sigma, Delta) ->
      RGISimulation.MethodUpdateSteps Gbig I sigma n Delta Delta.
    Proof.
      intros HGid HI. induction n.
      - constructor.
      - eapply RGISimulation.MethodUpdatesStep with (Delta' := Delta).
        + apply ac_steps_refl.
        + apply HGid.
        + exact HI.
        + exact IHn.
    Qed.

    Lemma update_chain_semantics (Gbig : RGRelation) (n : nat)
        (P Pfinal : Assertion) :
      (G ⊆ Gbig)%RGRelation ->
      (forall s, Gbig s s) ->
      @UpdateChainRanked E F VE VF R G I n P Pfinal ->
      forall sigma Delta, (⊨ P ==>> I) -> P (sigma, Delta) ->
      exists DeltaFinal,
        RGISimulation.MethodUpdateSteps Gbig I sigma n Delta DeltaFinal /\
        I (sigma, DeltaFinal) /\
        (Pfinal (sigma, DeltaFinal) \/ APError (sigma, DeltaFinal)).
    Proof.
      intros HGsub HGid Hchain. induction Hchain as
        [P0|n0 Punsafe P0 P0' Pfinal Hsafe HI' HS HU Htail IH];
        intros sigma Delta HPI HPstate.
      - exists Delta. split; [constructor|]. split.
        + apply HPI; exact HPstate.
        + left; exact HPstate.
      - pose proof HPstate as HPunsafe.
        apply Hsafe in HPstate as [HP | Herr].
        + destruct (HU _ _ HP) as [Delta' [Hreach [HP' HG]]].
          destruct (IH sigma Delta' HI' HP') as
            [DeltaFinal [Hadmin [HIFinal Hfinal]]].
          exists DeltaFinal. split.
          * eapply RGISimulation.MethodUpdatesStep; eauto.
            apply HPI; exact HPunsafe.
          * split; assumption.
        + exists Delta. split.
          * eapply method_updates_identity; eauto.
            apply HPI; exact HPunsafe.
          * split.
            -- apply HPI; exact HPunsafe.
            -- right; exact Herr.
    Qed.

    Lemma update_chain_final_valid P Pfinal :
      (⊨ P ==>> I) -> Stable R I P -> UpdateChain R G I P Pfinal ->
      (⊨ Pfinal ==>> I) /\ Stable R I Pfinal.
    Proof.
      intros HPI Hstable Hchain. induction Hchain.
      - auto.
      - apply IHHchain; auto.
    Qed.

    Lemma find_some_rely :
      (forall s s', R s s' -> I s' ->
        (forall rho pi, Δ s rho pi -> TMap.find t pi = None) <->
        (forall rho pi, Δ s' rho pi -> TMap.find t pi = None)) ->
      forall (sigma : State VE) (Delta : AbstractConfig VF)
        (sigma' : State VE) (Delta' : AbstractConfig VF),
        (forall rho pi, Delta rho pi -> exists ls,
          TMap.find t pi = Some ls) ->
        R (sigma, Delta) (sigma', Delta') -> I (sigma', Delta') ->
        forall rho pi, Delta' rho pi -> exists ls,
          TMap.find t pi = Some ls.
    Proof.
      intros HR sigma Delta sigma' Delta' Hfind HRstep HI'
        rho pi Hposs.
      destruct (TMap.find t pi) eqn:Hnone; eauto.
      exfalso.
      assert (Hallnone : forall rho' pi', Delta' rho' pi' ->
        TMap.find t pi' = None).
      { intros rho' pi' Hposs'.
        exact (ac_find_none_same Delta' rho pi rho' pi' t
          Hposs Hposs' Hnone). }
      pose proof (proj2 (HR _ _ HRstep HI') Hallnone) as Holdnone.
      destruct (@ac_nonempty F VF Delta) as [rho0 [pi0 Hposs0]].
      destruct (Hfind _ _ Hposs0) as [ls Hsome].
      specialize (Holdnone _ _ Hposs0). congruence.
    Qed.

    Lemma logic_soundness f P Q
      (HvalidRG : RGISimulation.ValidRGI R G I t)
      (Hprovable : MethodProvable f P Q) :
      forall sigma Delta,
        (Ginv t f ⊚ I) (sigma, Delta) ->
        (forall rho pi, Delta rho pi ->
          TMap.find t pi = Some (ls_inv f)) ->
        RGISimulation.MethodSimulation R
          (G ∪ (GINV t ∪ GRET t ∪ GId)) I t f sigma (M f t) None Delta.
    Proof.
      intros sigma0 Delta0 Hinitial Hlininitial.
      destruct HvalidRG as [HRinv0].
      destruct Hprovable as [HPinv HPI HPstable HQret HQlin HTriple].
      apply HPinv in Hinitial. rename Hinitial into HP.
      assert (Hfind0 : forall rho pi, Delta0 rho pi -> exists ls,
        TMap.find t pi = Some ls) by eauto.
      destruct (@htriple_has_rank E F VE VF R G I t _ P (M f t) Q HTriple)
        as [initialRank Hrank0].
      exists initialRank.
      eapply RGISimulation.MethodSimulation_coinduction_ranked with
        (X := fun n sigma p b (Delta : AbstractConfig VF) =>
          (forall rho pi, Delta rho pi -> exists ls,
            TMap.find t pi = Some ls) /\
          match b with
          | None => exists P0, P0 (sigma, Delta) /\
              @HTripleRanked E F VE VF R G I t _ n P0 p Q /\
              (⊨ P0 ==>> I) /\ Stable R I P0
          | Some m => n = O /\ exists k P' Q',
              p = Vis m k /\ P' (sigma, Delta) /\
              (forall ret, G ⊨ P'
                [ Build_ThreadEvent t (ResEv m ret) ]⭆ Q' ret) /\
              (forall ret, [VE, VF, R, G, I, t]
                ⊢ {{ Q' ret }} k ret {{ Q }}) /\
              (⊨ P' ==>> I) /\ Stable R I P' /\
              (forall ret, ⊨ Q' ret ==>> I) /\
              (forall ret, Stable R I (Q' ret))
          end).
      - intros n sigma p b Delta [Hfind Hstate].
        assert (Hrely_state : forall sigma' Delta',
          R (sigma, Delta) (sigma', Delta') -> I (sigma', Delta') ->
          (forall rho pi, Delta' rho pi -> exists ls,
            TMap.find t pi = Some ls) /\
          match b with
          | None => exists P0, P0 (sigma', Delta') /\
              @HTripleRanked E F VE VF R G I t _ n P0 p Q /\
              (⊨ P0 ==>> I) /\ Stable R I P0
          | Some m => n = O /\ exists k P' Q',
              p = Vis m k /\ P' (sigma', Delta') /\
              (forall ret, G ⊨ P'
                [ Build_ThreadEvent t (ResEv m ret) ]⭆ Q' ret) /\
              (forall ret, [VE, VF, R, G, I, t]
                ⊢ {{ Q' ret }} k ret {{ Q }}) /\
              (⊨ P' ==>> I) /\ Stable R I P' /\
              (forall ret, ⊨ Q' ret ==>> I) /\
              (forall ret, Stable R I (Q' ret))
          end).
        { intros sigma' Delta' HR HI'. split.
          - intros rho pi Hposs.
            destruct (TMap.find t pi) eqn:Hnone; eauto.
            exfalso.
            assert (Hallnone : forall rho' pi', Delta' rho' pi' ->
              TMap.find t pi' = None).
            { intros rho' pi' Hposs'.
              exact (ac_find_none_same Delta' rho pi rho' pi' t
                Hposs Hposs' Hnone). }
            pose proof (proj2 (HRinv0 _ _ HR HI') Hallnone) as Holdnone.
            destruct (@ac_nonempty F VF Delta) as [rho0 [pi0 Hposs0]].
            destruct (Hfind _ _ Hposs0) as [ls Hsome].
            specialize (Holdnone _ _ Hposs0). congruence.
          - destruct b.
            + destruct Hstate as [Hn Hstate]. subst n.
              destruct Hstate as
                (k & P' & Q' & -> & HP' & Hupd & Hnext & HPI' &
                 Hstable' & HQI & HQstable).
              split; [reflexivity|]. exists k, P', Q'. repeat split; eauto.
              apply Hstable'. split.
              * exists (sigma, Delta). split; assumption.
              * exact HI'.
            + destruct Hstate as (P0 & HP0 & Hproof & HPI0 & Hstable0).
              exists P0. repeat split; eauto.
              apply Hstable0. split.
              * exists (sigma, Delta). split; assumption.
              * exact HI'. }
        destruct b.
        + destruct Hstate as [Hn Hstate]. subst n.
          destruct Hstate as
            (k & P' & Q' & -> & HP' & Hupd & Hnext & HPI' &
             Hstable' & HQI & HQstable).
          exists Delta. split; [constructor|].
          split.
          * eapply RGISimulation.MCore_Continue.
          -- intros ev sigma' p' b' Hstep.
            inversion Hstep; subst. dependent destruction H7.
            destruct (Hupd ret0 sigma Delta HP' sigma' Hstep0) as
              [Delta' [Hreach [HQ' HGstep]]].
            exists Delta'. split; [exact Hreach|]. split.
            ++ left; exact HGstep.
            ++ destruct (@htriple_has_rank E F VE VF R G I t _
                 (Q' ret0) (k ret0) Q (Hnext ret0)) as
                 [nextRank HnextRank].
               exists nextRank. split.
               ** intros rho pi Hposs. apply Hreach in Hposs.
                  inversion Hposs; subst.
                  destruct (Hfind _ _ Hposs0) as [ls Hls].
                  eapply poss_steps_nondec; eauto.
               ** exists (Q' ret0). repeat split; eauto.
          -- intros ret [Hret _]. inversion Hret.
          -- intros p' b' Htau. inversion Htau.
          -- apply HPI'; exact HP'.
          -- intros sigma' Delta' HR HI'. apply Hrely_state; auto.
          -- intros ev Herr. inversion Herr; subst.
          * intros sigma' Delta' HR HI'. exists O. split; [lia|].
            apply Hrely_state; auto.
        + destruct Hstate as (P0 & HP0 & Hproof & HPI0 & Hstable0).
          destruct Hproof as
            [rankProof Pstart pProof QProof Pcore Hadmin Hcore].
          pose (Pterminal := Pcore).
          pose proof (@update_chain_ranked_unrank E F VE VF R G I
            rankProof Pstart Pcore Hadmin) as HadminOld.
          pose proof (update_chain_final_valid _ Pcore
            HPI0 Hstable0 HadminOld) as [HPIcore Hstablecore].
          assert (HGsub :
            (G ⊆ G ∪ (GINV t ∪ GRET t ∪ GId))%RGRelation).
          { intros s s' HGs. left; exact HGs. }
          assert (HGid : forall s,
            (G ∪ (GINV t ∪ GRET t ∪ GId))%RGRelation s s).
          { intro s. right. right. reflexivity. }
          destruct (update_chain_semantics
            (G ∪ (GINV t ∪ GRET t ∪ GId)) rankProof Pstart Pcore
            HGsub HGid Hadmin sigma Delta HPI0 HP0) as
            [DeltaCore [HadminSim [HICore [HPcore | HPerror]]]].
          * exists DeltaCore. split; [exact HadminSim|]. split.
            { destruct Hcore.
            -- pose proof HPcore as HPunsafe.
               apply H in HPcore as [HPsafe | Herr].
               ++ eapply RGISimulation.MCore_Continue.
                  ** intros ev sigma' p' b' Hstep.
                     inversion Hstep; subst; simpl in *; congruence.
                  ** intros ret [Hret Hb]. inversion Hret; subst.
                     repeat split.
                     --- intros s s' HGret. right; left; right.
                         exists f, ret. exact HGret.
                     --- eapply HQret. exists (sigma, DeltaCore). split.
                         +++ apply H0; exact HPsafe.
                         +++ unfold Gret, LiftRelation_Δ. simpl.
                             repeat split; auto.
                             intros rho pi Hposs.
                             eapply HQlin; [apply H0; exact HPsafe|exact Hposs].
                     --- intros rho pi Hposs.
                         eapply HQlin; [apply H0; exact HPsafe|exact Hposs].
                  ** intros p' b' Htau. inversion Htau.
                  ** exact HICore.
                  ** intros sigma' Delta' HR HI'. split.
                     --- eapply (find_some_rely HRinv0 sigma DeltaCore
                           sigma' Delta').
                         +++ eapply RGISimulation.method_updates_find_some;
                             eauto.
                         +++ exact HR.
                         +++ exact HI'.
                     --- exists Punsafe. repeat split.
                         +++ apply Hstablecore. split.
                             *** exists (sigma, DeltaCore). split;
                                 [exact HPunsafe|exact HR].
                             *** exact HI'.
                         +++ econstructor; [constructor|].
                             eapply CoreRet; eauto.
                         +++ exact HPIcore.
                         +++ exact Hstablecore.
                  ** intros ev Herr0. inversion Herr0.
               ++ inversion Herr; subst. eapply RGISimulation.MCore_Error;
                    eauto.
            -- pose proof HPcore as HPunsafe.
               apply H in HPcore as [HPsafe | Herr].
               ++ eapply RGISimulation.MCore_Continue.
                  ** intros ev sigma' p0 b' Hstep.
                     inversion Hstep; subst.
                     dependent destruction H13. dependent destruction H15.
                     destruct (H5 sigma DeltaCore HPsafe sigma' Hstep0) as
                       [Delta' [Hreach [HP' HGstep]]].
                     exists Delta'. split; [exact Hreach|]. split.
                     --- left; exact HGstep.
                     --- exists O. split.
                         +++ intros rho pi Hposs. apply Hreach in Hposs.
                             inversion Hposs; subst.
                             pose proof
                               (@RGISimulation.method_updates_find_some
                                 E F VE VF
                                 (G ∪ (GINV t ∪ GRET t ∪ GId)) I sigma
                                 rankProof Delta DeltaCore t
                                 HadminSim Hfind _ _ Hposs0)
                               as Hsome.
                             destruct Hsome as [ls Hls].
                             eapply poss_steps_nondec; eauto.
                         +++ split; [reflexivity|].
                             exists k, P', Q'. repeat split; eauto.
                  ** intros ret [Hret _]. inversion Hret.
                  ** intros p0 b' Htau. inversion Htau.
                  ** exact HICore.
                  ** intros sigma' Delta' HR HI'. split.
                     --- eapply (find_some_rely HRinv0 sigma DeltaCore
                           sigma' Delta').
                         +++ eapply RGISimulation.method_updates_find_some;
                             eauto.
                         +++ exact HR.
                         +++ exact HI'.
                     --- exists Punsafe. repeat split.
                         +++ apply Hstablecore. split.
                             *** exists (sigma, DeltaCore). split;
                                 [exact HPunsafe|exact HR].
                             *** exact HI'.
                         +++ econstructor; [constructor|].
                             eapply CoreVis with (P := P0) (P' := P')
                               (Q' := Q'); eauto.
                         +++ exact HPIcore.
                         +++ exact Hstablecore.
                  ** intros ev Herr0. inversion Herr0; subst.
                     dependent destruction H13.
                     apply H0 in HPsafe. exact (HPsafe Herror).
               ++ inversion Herr; subst. eapply RGISimulation.MCore_Error;
                    eauto.
            -- eapply RGISimulation.MCore_Continue.
               ++ intros ev sigma' p0 b' Hstep.
                  inversion Hstep; subst; simpl in *; congruence.
               ++ intros ret [Hret _]. inversion Hret.
               ++ intros p0 b' Htau. inversion Htau; subst.
                  dependent destruction H2. dependent destruction H4.
                  destruct (@htriple_has_rank E F VE VF R G I t _
                    Pterminal _ Q H) as
                    [nextRank HnextRank].
                  exists nextRank. split.
                  ** eapply RGISimulation.method_updates_find_some; eauto.
                  ** exists Pterminal. repeat split; auto.
               ++ exact HICore.
               ++ intros sigma' Delta' HR HI'. split.
                  ** eapply (find_some_rely HRinv0 sigma DeltaCore
                       sigma' Delta').
                     --- eapply RGISimulation.method_updates_find_some;
                         eauto.
                     --- exact HR.
                     --- exact HI'.
                  ** exists Pterminal. repeat split.
                     --- apply Hstablecore. split.
                         +++ exists (sigma, DeltaCore). split;
                             [exact HPcore|exact HR].
                         +++ exact HI'.
                     --- econstructor; [constructor|]. apply CoreTau. exact H.
                     --- exact HPIcore.
                     --- exact Hstablecore.
               ++ intros ev Herr. inversion Herr. }
            { intros sigma' Delta' HR HI'. exists rankProof.
              split; [lia|]. apply Hrely_state; auto. }
          * exists DeltaCore. split; [exact HadminSim|]. split.
            { inversion HPerror; subst.
              eapply RGISimulation.MCore_Error; eauto. }
            { intros sigma' Delta' HR HI'. exists rankProof.
              split; [lia|]. apply Hrely_state; auto. }
      - split; [exact Hfind0|]. exists P. repeat split; auto.
    Qed.
  End MethodLogic.

  Section FrameRules.
    Context {E F : Op.t} {VE : @LTS E} {VF : @LTS F}.
    Context {EJ : Join (State VE)} {ESA : @SeparationAlgebra _ EJ}.
    Context {Eunit : @SeparationAlgebraUnit _ EJ ESA}.
    Context {FJ : Join (State VF)} {FSA : @SeparationAlgebra _ FJ}.
    Context {Funit : @SeparationAlgebraUnit _ FJ FSA}.
    Context {Hlocal : @LocalLTS E VE EJ}.

    #[local] Existing Instance SetPossState.PSS_Join.
    #[local] Existing Instance SetPossState.PSS_SA.

    Context (R G : @RGRelation _ _ VE VF).
    Context (I : @Assertion (@ProofState _ _ VE VF)) (t : tid).

    Lemma update_chain_frame_same P P' Fr :
      FramePreservingUpdate G -> FramePreservingSteps (VF := VF) ->
      FrameInvariant I Fr -> FrameStable R I Fr ->
      FramePreservingError Fr ->
      UpdateChain R G I P P' ->
      UpdateChain R G I (P * Fr) (P' * Fr).
    Proof.
      intros HG Hsteps Hinv Hstable Herr Hchain. induction Hchain.
      - constructor.
      - eapply UpdateCons.
        + eapply perror_sepcon_frame; eauto.
        + eapply Hinv; eauto.
        + eapply Hstable; eauto.
        + eapply PUpdateId_frame; eauto.
        + eauto.
    Qed.

    Theorem provable_frame_same_context {A}
        (P : Assertion) (Q : A -> Assertion) (Fr : Assertion)
        (p : Prog E A) :
      FramePreservingUpdate G -> FramePreservingSteps (VF := VF) ->
      FrameInvariant I Fr -> FrameStable R I Fr ->
      FramePreservingError Fr ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q }} ->
      [VE, VF, R, G, I, t] ⊢ {{ P * Fr }} p {{ fun a => Q a * Fr }}.
    Proof.
      intros HG Hsteps Hinv Hstable Herr Hproof.
      eapply (@HTripleProvable_coinduction E F VE VF R G I t A
        (fun Pf p' Qf => exists P0 Q0,
          Pf = P0 * Fr /\ Qf = (fun a => Q0 a * Fr) /\
          [VE, VF, R, G, I, t] ⊢ {{ P0 }} p' {{ Q0 }})).
      - intros Pf p' Qf [P0 [Q0 [-> [-> [Pcore Hadmin Hcore]]]]].
        exists (Pcore * Fr). split.
        + eapply update_chain_frame_same; eauto.
        + destruct Hcore.
          * eapply CoreRet with (P := P1 * Fr).
            -- eapply perror_sepcon_frame; [exact Herr|exact H].
            -- eapply sepcon_consequence; [exact H0|apply ImplRefl].
            -- apply Hinv; exact H1.
            -- apply Hstable; exact H2.
          * eapply CoreVis with (P := P1 * Fr) (P' := P' * Fr)
              (Q' := fun a => Q' a * Fr).
            -- eapply perror_sepcon_frame; [exact Herr|exact H].
            -- eapply ANoError_sepcon_inv; exact H0.
            -- apply Hinv; exact H1.
            -- intros; apply Hinv; auto.
            -- apply Hstable; exact H3.
            -- intros; apply Hstable; auto.
            -- eapply PUpdate_frame_inv; eauto.
            -- intros; eapply PUpdate_frame_res; eauto.
            -- intros ret. do 2 eexists. repeat split; eauto.
          * apply CoreTau. do 2 eexists. repeat split; eauto.
      - do 2 eexists. repeat split; eauto.
    Qed.

    Lemma update_chain_frame_context P P' Fr :
      FrameCompatibleUpdate G -> FramePreservingSteps (VF := VF) ->
      FrameStableContext R I Fr -> FramePreservingError Fr ->
      UpdateChain R G I P P' ->
      UpdateChain (RelSep R (FrameIdentity Fr))
        (RelSep G (FrameIdentity Fr)) (I * Fr)
        (P * Fr) (P' * Fr).
    Proof.
      intros HG Hsteps Hstable Herr Hchain. induction Hchain.
      - constructor.
      - eapply UpdateCons.
        + eapply perror_sepcon_frame; eauto.
        + eapply sepcon_consequence; [exact H0|apply ImplRefl].
        + apply Hstable; assumption.
        + eapply PUpdateId_frame_context; eauto.
        + assumption.
    Qed.

    Theorem provable_frame {A}
        (P : Assertion) (Q : A -> Assertion) (Fr : Assertion)
        (p : Prog E A) :
      FrameCompatibleUpdate G -> FramePreservingSteps (VF := VF) ->
      FrameStableContext R I Fr -> FramePreservingError Fr ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q }} ->
      [VE, VF, RelSep R (FrameIdentity Fr),
        RelSep G (FrameIdentity Fr), I * Fr, t]
        ⊢ {{ P * Fr }} p {{ fun a => Q a * Fr }}.
    Proof.
      intros HG Hsteps Hstable Herr Hproof.
      eapply (@HTripleProvable_coinduction E F VE VF
        (RelSep R (FrameIdentity Fr)) (RelSep G (FrameIdentity Fr))
        (I * Fr) t A
        (fun Pf p' Qf => exists P0 Q0,
          Pf = P0 * Fr /\ Qf = (fun a => Q0 a * Fr) /\
          [VE, VF, R, G, I, t] ⊢ {{ P0 }} p' {{ Q0 }})).
      - intros Pf p' Qf [P0 [Q0 [-> [-> [Pcore Hadmin Hcore]]]]].
        exists (Pcore * Fr). split.
        + eapply update_chain_frame_context; eauto.
        + destruct Hcore.
          * eapply CoreRet with (P := P1 * Fr).
            -- eapply perror_sepcon_frame; [exact Herr|exact H].
            -- eapply sepcon_consequence; [exact H0|apply ImplRefl].
            -- eapply sepcon_consequence; [exact H1|apply ImplRefl].
            -- apply Hstable; exact H2.
          * eapply CoreVis with (P := P1 * Fr) (P' := P' * Fr)
              (Q' := fun a => Q' a * Fr).
            -- eapply perror_sepcon_frame; [exact Herr|exact H].
            -- eapply ANoError_sepcon_inv; exact H0.
            -- eapply sepcon_consequence; [exact H1|apply ImplRefl].
            -- intros a. eapply sepcon_consequence;
                 [exact (H2 a)|apply ImplRefl].
            -- apply Hstable; exact H3.
            -- intros; apply Hstable; auto.
            -- eapply PUpdate_frame_inv_context; eauto.
            -- intros; eapply PUpdate_frame_res_context; eauto.
            -- intros ret. do 2 eexists. repeat split; eauto.
          * apply CoreTau. do 2 eexists. repeat split; eauto.
      - do 2 eexists. repeat split; eauto.
    Qed.
  End FrameRules.

  Import RGISimulationSet.RGISimulation.

  Lemma soundness
    {E F} (VE : @LTS E) (VF : @LTS F) (M : ModuleImpl E F)
    (R G : tid -> RGRelation) I
    (HvalidRG : forall t, ValidRGI (R t) (G t) I t)
    (HRG : forall t1 t2 : tid, t1 <> t2 ->
      (I ⊓ (G t1 ∪ (GINV t1 ∪ GRET t1 ∪ GId)) ⊆ R t2)%RGRelation)
    (Hprovable : forall t f, exists P Q,
      MethodProvable VE VF M (R t) (G t) I t f P Q)
    sigma0 rho0
    (Hinit : I (sigma0, rho0, (@TMap.empty _))) :
    TPSimulationSet.TPSimulation.cal M sigma0 rho0.
  Proof.
    unfold TPSimulationSet.TPSimulation.cal.
    eapply rgisim_parapllel_composition with
      (I := I) (G := fun t =>
        (G t ∪ (GINV t ∪ GRET t ∪ GId))%RGRelation).
    - exact HRG.
    - intros t0.
      eapply msim_sequential_composition; eauto.
      + destruct (HvalidRG t0). constructor; auto.
      + intros.
        destruct (Hprovable t0 f) as [P [Q Hmethod]].
        eapply logic_soundness; eauto.
      + intros ? ? ? ?.
        right; do 2 left.
        unfold GINV. eauto.
      + right; right. reflexivity.
  Qed.
End RGILogic.
