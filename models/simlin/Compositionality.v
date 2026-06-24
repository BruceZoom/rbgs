Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import models.EffectSignatures.
Require Import TPSimulation.
Require Import TPSimulationSet.
Require Import Semantics.
Require Import FMapPositive.
Require Import Coq.Program.Equality.
Require Import Coq.PArith.PArith.
Require Import Relation_Operators Operators_Properties.

Import LinCCALBase.
Import Lang.
Import Reg.

CoFixpoint substProg
          {E F}
          (t : tid)
          (impl : ModuleImpl E F)
          {R}
          (p : Prog F R) :
  Prog E R :=
  match p with
    | Vis m k => Tau (bindSubstProg t impl (impl m t) k)
    | Ret r => Ret r
    | Tau p => Tau (substProg t impl p)
  end

with bindSubstProg
          (t : tid)
          {E F} (impl : ModuleImpl E F)
          {R R'} (p: Prog E R) (k: R -> Prog F R') :=
  match p with
  | Vis m' k' => Vis m' (fun r => bindSubstProg t impl (k' r) k)
  | Ret r => Tau (substProg t impl (k r))
  | Tau p => Tau (bindSubstProg t impl p k)
  end.

Definition implVComp {E F G} (implEF : ModuleImpl E F) (implFG : ModuleImpl F G) : ModuleImpl E G := 
  fun g t => substProg t implEF (implFG g t).

Notation "M ▶ N" := (implVComp M N) (at level 80, right associativity).

CoFixpoint liftLeftProg
           {E1 E2}
           {R}
           (p : Prog E1 R) :
  Prog (Sig.Plus.omap E1 E2) R :=
  match p with
    | Vis m k =>
        @Vis (Sig.Plus.omap E1 E2) R
          (@inl (Sig.op E1) (Sig.op E2) m)
          (fun a => liftLeftProg (E2 := E2) (k a))
    | Ret r => Ret r
    | Tau p' => Tau (liftLeftProg (E2 := E2) p')
  end.

CoFixpoint liftRightProg
           {E1 E2}
           {R}
           (p : Prog E2 R) :
  Prog (Sig.Plus.omap E1 E2) R :=
  match p with
    | Vis m k =>
        @Vis (Sig.Plus.omap E1 E2) R
          (@inr (Sig.op E1) (Sig.op E2) m)
          (fun a => liftRightProg (E1 := E1) (k a))
    | Ret r => Ret r
    | Tau p' => Tau (liftRightProg (E1 := E1) p')
  end.

Definition implHComp {E1 F1 E2 F2}
    (impl1 : ModuleImpl E1 F1) (impl2 : ModuleImpl E2 F2) :
    ModuleImpl (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2) :=
  fun f t =>
    match f with
    | inl f => liftLeftProg (E2 := E2) (impl1 f t)
    | inr f => liftRightProg (E1 := E1) (impl2 f t)
    end.

Notation "M ⊗ N" := (implHComp M N) (at level 40).

Module VCompTPSim.
  Import LTSSpec.
  Import TPSimulation.TPSimulation.
  Import Semantics.

  Lemma substProgVis {E F R} t (impl : ModuleImpl E F) m
        (k : Sig.ar m -> Prog F R) :
    substProg t impl (Vis m k) =
    Tau (bindSubstProg t impl (impl m t) k).
  Proof.
    rewrite (PPid (substProg t impl (Vis m k))) at 1.
    unfold PP, substProg at 1.
    reflexivity.
  Qed.

  Lemma substProgRet {E F R} t (impl : ModuleImpl E F) (r : R) :
    substProg t impl (Ret r) = Ret r.
  Proof.
    rewrite (PPid (substProg t impl (Ret r))) at 1.
    unfold PP, substProg at 1.
    reflexivity.
  Qed.

  Lemma substProgTau {E F R} t (impl : ModuleImpl E F)
        (p : Prog F R) :
    substProg t impl (Tau p) = Tau (substProg t impl p).
  Proof.
    rewrite (PPid (substProg t impl (Tau p))) at 1.
    unfold PP, substProg at 1.
    reflexivity.
  Qed.

  Lemma bindSubstProgVis {E F R R'} t (impl : ModuleImpl E F)
        m (k' : Sig.ar m -> Prog E R) (k : R -> Prog F R') :
    bindSubstProg t impl (Vis m k') k =
    Vis m (fun r => bindSubstProg t impl (k' r) k).
  Proof.
    rewrite (PPid (bindSubstProg t impl (Vis m k') k)) at 1.
    unfold PP, bindSubstProg at 1.
    reflexivity.
  Qed.

  Lemma bindSubstProgRet {E F R R'} t (impl : ModuleImpl E F)
        (r : R) (k : R -> Prog F R') :
    bindSubstProg t impl (Ret r) k =
    Tau (substProg t impl (k r)).
  Proof.
    rewrite (PPid (bindSubstProg t impl (Ret r) k)) at 1.
    unfold PP, bindSubstProg at 1.
    reflexivity.
  Qed.

  Lemma bindSubstProgTau {E F R R'} t (impl : ModuleImpl E F)
        (p : Prog E R) (k : R -> Prog F R') :
    bindSubstProg t impl (Tau p) k =
    Tau (bindSubstProg t impl p k).
  Proof.
    rewrite (PPid (bindSubstProg t impl (Tau p) k)) at 1.
    unfold PP, bindSubstProg at 1.
    reflexivity.
  Qed.

  Lemma substProg_ret_inv {E F R} t (impl : ModuleImpl E F)
        (p : Prog F R) r :
    substProg t impl p = Ret r ->
    p = Ret r.
  Proof.
    destruct p.
    - rewrite substProgVis. discriminate.
    - rewrite substProgRet. intros H. inversion H. reflexivity.
    - rewrite substProgTau. discriminate.
  Qed.

  Lemma substProg_not_vis {E F R} t (impl : ModuleImpl E F)
        (p : Prog F R) m k :
    substProg t impl p <> Vis m k.
  Proof.
    destruct p.
    - rewrite substProgVis. discriminate.
    - rewrite substProgRet. discriminate.
    - rewrite substProgTau. discriminate.
  Qed.

  Lemma bindSubstProg_not_ret {E F R R'} t (impl : ModuleImpl E F)
        (p : Prog E R) (k : R -> Prog F R') r :
    bindSubstProg t impl p k <> Ret r.
  Proof.
    destruct p.
    - rewrite bindSubstProgVis. discriminate.
    - rewrite bindSubstProgRet. discriminate.
    - rewrite bindSubstProgTau. discriminate.
  Qed.

  Section Composition.
    Context {E F G}
      {VE : @LTS E} {VF : @LTS F} {VG : @LTS G}.
    Context (implEF : ModuleImpl E F) (implFG : ModuleImpl F G).

    Definition pending_ok {R}
      (p : Prog E R) (b : option (Sig.op E)) : Prop :=
      match b with
      | None => True
      | Some m => exists k : Sig.ar m -> Prog E R, p = Vis m k
      end.

    Variant thread_comp t :
      option (@ThreadState E G) ->
      option (@ThreadState F G) ->
      option (@ThreadState E F) ->
      option (@LinState F) -> Prop :=
    | TC_None :
        thread_comp t None None None None
    | TC_Left q (p : Prog F (Sig.ar q)) :
        thread_comp t
          (Some (Build_ThreadState q (substProg t implEF p) None))
          (Some (Build_ThreadState q p None))
          None None
    | TC_Pre q m (k : Sig.ar m -> Prog F (Sig.ar q))
        (u : Prog E (Sig.ar m)) b
        (Hb : pending_ok u b) :
        thread_comp t
          (Some (Build_ThreadState q (bindSubstProg t implEF u k) b))
          (Some (Build_ThreadState q (Vis m k) None))
          (Some (Build_ThreadState m u b))
          (Some (ls_inv m))
    | TC_Run q m (k : Sig.ar m -> Prog F (Sig.ar q))
        (u : Prog E (Sig.ar m)) b
        (Hb : pending_ok u b) :
        thread_comp t
          (Some (Build_ThreadState q (bindSubstProg t implEF u k) b))
          (Some (Build_ThreadState q (Vis m k) (Some m)))
          (Some (Build_ThreadState m u b))
          (Some (ls_lini m))
    | TC_Done q m (k : Sig.ar m -> Prog F (Sig.ar q))
        (r : Sig.ar m) (u : Prog E (Sig.ar m)) b
        (Hb : pending_ok u b) :
        thread_comp t
          (Some (Build_ThreadState q (bindSubstProg t implEF u k) b))
          (Some (Build_ThreadState q (k r) None))
          (Some (Build_ThreadState m u b))
          (Some (ls_linr m r)).

    Definition pools_comp
      (c : @ThreadPoolState E G)
      (cFG : @ThreadPoolState F G)
      (cEF : @ThreadPoolState E F)
      (piF : tmap (@LinState F)) : Prop :=
      forall t,
        thread_comp t (TMap.find t c) (TMap.find t cFG)
          (TMap.find t cEF) (TMap.find t piF).

    Lemma pools_comp_set t c cFG cEF piF ec eFG eEF epi :
      pools_comp c cFG cEF piF ->
      thread_comp t ec eFG eEF epi ->
      pools_comp
        (match ec with
         | Some s => TMap.add t s c
         | None => TMap.remove t c
         end)
        (match eFG with
         | Some s => TMap.add t s cFG
         | None => TMap.remove t cFG
         end)
        (match eEF with
         | Some s => TMap.add t s cEF
         | None => TMap.remove t cEF
         end)
        (match epi with
         | Some s => TMap.add t s piF
         | None => TMap.remove t piF
         end).
    Proof.
      intros Hcomp Ht i.
      destruct (Pos.eq_dec i t); subst.
      - destruct ec, eFG, eEF, epi; simpl in *;
          repeat rewrite ?PositiveMap.gss, ?PositiveMap.grs; auto.
      - destruct ec, eFG, eEF, epi; simpl in *;
          repeat rewrite ?PositiveMap.gso, ?PositiveMap.gro by auto;
          apply Hcomp.
    Qed.

    Lemma pools_comp_empty :
      pools_comp (TMap.empty _) (TMap.empty _)
        (TMap.empty _) (TMap.empty _).
    Proof.
      intro t.
      repeat rewrite PositiveMap.gempty.
      constructor.
    Qed.

    Variant middle_result
      (c : @ThreadPoolState E G)
      (cEF : @ThreadPoolState E F)
      (mid : State VF) (piF : tmap (@LinState F))
      (rho : State VG) (piG : tmap (@LinState G)) : Prop :=
    | MR_Error
        (Herror : poss_steps (PossOk rho piG) PossError) :
        middle_result c cEF mid piF rho piG
    | MR_Continue
        (cFG : @ThreadPoolState F G)
        (rho' : State VG) (piG' : tmap (@LinState G))
        (Hsteps : poss_steps (PossOk rho piG) (PossOk rho' piG'))
        (Hsim : TPSimulation implFG mid cFG rho' piG')
        (Hcomp : pools_comp c cFG cEF piF) :
        middle_result c cEF mid piF rho piG.

    Lemma middle_one
      c cFG cEF mid piF mid' piF' rho piG
      (Hcomp : pools_comp c cFG cEF piF)
      (Hsim : TPSimulation implFG mid cFG rho piG)
      (Hstep : poss_step (PossOk mid piF) (PossOk mid' piF')) :
      middle_result c cEF mid' piF' rho piG.
    Proof.
      inversion Hstep as
          [t m s1 s2 pi HstepVF Hfind
          |t m r s1 s2 pi HstepVF Hfind
          |]; subst.
      - pose proof (Hcomp t) as Hthread.
        rewrite Hfind in Hthread.
        dependent destruction Hthread.
        dependent destruction Hsim.
        + constructor. assumption.
        + assert (Houter :
            ustep (Build_ThreadEvent t0 (InvEv m0)) mid cFG mid'
              (TMap.add t0
                (Build_ThreadState q (Vis m0 k) (Some m0)) cFG)).
          { econstructor.
            - symmetry. exact x1.
            - econstructor. exact HstepVF.
            - reflexivity. }
          specialize (tpsim_ustep _ _ _ Houter)
            as (rho' & piG' & Hsteps & Hsim').
          eapply MR_Continue with
            (cFG := TMap.add t0
              (Build_ThreadState q (Vis m0 k) (Some m0)) cFG);
            eauto.
          intro i.
          destruct (Pos.eq_dec i t0); subst.
          * rewrite PositiveMap.gss, PositiveMap.gss.
            rewrite <- x0, <- x.
            constructor. assumption.
          * rewrite PositiveMap.gso by auto.
            rewrite PositiveMap.gso by auto.
            apply Hcomp.
      - pose proof (Hcomp t) as Hthread.
        rewrite Hfind in Hthread.
        dependent destruction Hthread.
        dependent destruction Hsim.
        + constructor. assumption.
        + assert (Houter :
            ustep (Build_ThreadEvent t0 (ResEv m0 r)) mid cFG mid'
              (TMap.add t0 (Build_ThreadState q (k r) None) cFG)).
          { econstructor.
            - symmetry. exact x1.
            - econstructor. exact HstepVF.
            - reflexivity. }
          specialize (tpsim_ustep _ _ _ Houter)
            as (rho' & piG' & Hsteps & Hsim').
          eapply MR_Continue with
            (cFG := TMap.add t0 (Build_ThreadState q (k r) None) cFG);
            eauto.
          intro i.
          destruct (Pos.eq_dec i t0); subst.
          * rewrite PositiveMap.gss, PositiveMap.gss.
            rewrite <- x0, <- x.
            constructor. assumption.
          * rewrite PositiveMap.gso by auto.
            rewrite PositiveMap.gso by auto.
            apply Hcomp.
    Qed.

    Lemma middle_error_one
      c cFG cEF (mid : State VF) piF (rho : State VG) piG
      (Hcomp : pools_comp c cFG cEF piF)
      (Hsim : TPSimulation implFG mid cFG rho piG)
      (Hstep : poss_step (PossOk mid piF) PossError) :
      poss_steps (PossOk rho piG) PossError.
    Proof.
      inversion Hstep as [| |t m s pi Herror Hfind]; subst.
      pose proof (Hcomp t) as Hthread.
      rewrite Hfind in Hthread.
      dependent destruction Hthread.
      dependent destruction Hsim.
      - assumption.
      - exfalso.
        eapply (tpsim_noerror (Build_ThreadEvent t0 (InvEv m0))).
        econstructor.
        + symmetry. exact x1.
        + econstructor. exact Herror.
    Qed.

    Lemma middle_steps
      c cFG cEF mid piF mid' piF' rho piG
      (Hcomp : pools_comp c cFG cEF piF)
      (Hsim : TPSimulation implFG mid cFG rho piG)
      (Hsteps : poss_steps (PossOk mid piF) (PossOk mid' piF')) :
      middle_result c cEF mid' piF' rho piG.
    Proof.
      apply clos_rt_rt1n_iff in Hsteps.
      remember (PossOk mid piF) as x.
      remember (PossOk mid' piF') as z.
      revert mid piF mid' piF' Heqx Heqz cFG rho piG Hcomp Hsim.
      induction Hsteps; intros; subst.
      - inversion Heqz; subst.
        eapply MR_Continue with
          (cFG := cFG) (rho' := rho) (piG' := piG).
        + apply rt_refl.
        + exact Hsim.
        + exact Hcomp.
      - destruct y.
        2: inversion Hsteps.
        pose proof H as Hone.
        dependent destruction H.
        + pose proof
            (middle_one _ _ _ _ _ _ _ _ _ Hcomp Hsim Hone) as Hmiddle.
          dependent destruction Hmiddle.
          * constructor. assumption.
          * pose proof
              (IHHsteps _ _ _ _ eq_refl eq_refl
                cFG0 rho' piG' Hcomp0 Hsim0) as Hrest.
            dependent destruction Hrest.
            -- constructor.
               exact (@rt_trans Poss poss_step _ _ _ Hsteps0 Herror).
            -- eapply MR_Continue with
                 (cFG := cFG1) (rho' := rho'0) (piG' := piG'0).
               exact (@rt_trans Poss poss_step _ _ _ Hsteps0 Hsteps1).
               exact Hsim1.
               exact Hcomp1.
        + pose proof
            (middle_one _ _ _ _ _ _ _ _ _ Hcomp Hsim Hone) as Hmiddle.
          dependent destruction Hmiddle.
          * constructor. assumption.
          * pose proof
              (IHHsteps _ _ _ _ eq_refl eq_refl
                cFG0 rho' piG' Hcomp0 Hsim0) as Hrest.
            dependent destruction Hrest.
            -- constructor.
               exact (@rt_trans Poss poss_step _ _ _ Hsteps0 Herror).
            -- eapply MR_Continue with
                 (cFG := cFG1) (rho' := rho'0) (piG' := piG'0).
               exact (@rt_trans Poss poss_step _ _ _ Hsteps0 Hsteps1).
               exact Hsim1.
               exact Hcomp1.
        + constructor.
          eapply middle_error_one; eauto.
    Qed.

    Lemma middle_error
      c cFG cEF (mid : State VF) piF (rho : State VG) piG
      (Hcomp : pools_comp c cFG cEF piF)
      (Hsim : TPSimulation implFG mid cFG rho piG)
      (Hsteps : poss_steps (PossOk mid piF) PossError) :
      poss_steps (PossOk rho piG) PossError.
    Proof.
      apply clos_rt_rt1n_iff in Hsteps.
      remember (PossOk mid piF) as x.
      remember PossError as z.
      revert mid piF Heqx Heqz cFG rho piG Hcomp Hsim.
      induction Hsteps; intros; subst; try discriminate.
      destruct y.
      - pose proof H as Hone.
        dependent destruction H.
        + pose proof
            (middle_one _ _ _ _ _ _ _ _ _ Hcomp Hsim Hone) as Hmiddle.
          dependent destruction Hmiddle.
          * assumption.
          * pose proof
              (IHHsteps _ _ eq_refl eq_refl
                cFG0 rho' piG' Hcomp0 Hsim0) as Herror.
            exact (@rt_trans Poss poss_step _ _ _ Hsteps0 Herror).
        + pose proof
            (middle_one _ _ _ _ _ _ _ _ _ Hcomp Hsim Hone) as Hmiddle.
          dependent destruction Hmiddle.
          * assumption.
          * pose proof
              (IHHsteps _ _ eq_refl eq_refl
                cFG0 rho' piG' Hcomp0 Hsim0) as Herror.
            exact (@rt_trans Poss poss_step _ _ _ Hsteps0 Herror).
      - inversion Hsteps; subst.
        + eapply middle_error_one; eauto.
        + inversion H0.
    Qed.

    Lemma pools_comp_ustep
      (sigma : State VE) c cFG cEF piF (ev : ThreadEvent)
      (sigma' : State VE) c'
      (Hcomp : pools_comp c cFG cEF piF)
      (Hstep : ustep ev sigma c sigma' c') :
      exists cEF',
        ustep ev sigma cEF sigma' cEF' /\
        pools_comp c' cFG cEF' piF.
    Proof.
      destruct ev as [t ev].
      inversion Hstep; subst.
      pose proof (Hcomp t) as Hthread.
      simpl in Hfind.
      rewrite Hfind in Hthread.
      dependent destruction Hthread.
      - dependent destruction Hstep0.
        exfalso.
        eapply substProg_not_vis; eauto.
      - destruct u.
        + rewrite bindSubstProgVis in Hstep0.
          dependent destruction Hstep0.
          * exists (TMap.add t
              (Build_ThreadState m0 (Vis m1 k0) (Some m1)) cEF).
            split.
            { econstructor.
              - symmetry. exact x1.
              - econstructor. exact Hstep0.
              - reflexivity. }
            intro i. destruct (Pos.eq_dec i t); subst.
            { repeat rewrite PositiveMap.gss.
              rewrite <- x0, <- x.
              rewrite <- bindSubstProgVis.
              apply TC_Pre.
              exists k0. reflexivity. }
            repeat rewrite PositiveMap.gso by auto.
            apply Hcomp.
          * exists (TMap.add t
              (Build_ThreadState m0 (k0 ret) None) cEF).
            split.
            { econstructor.
              - symmetry. exact x1.
              - econstructor. exact Hstep0.
              - reflexivity. }
            intro i. destruct (Pos.eq_dec i t); subst.
            { repeat rewrite PositiveMap.gss.
              rewrite <- x0, <- x.
              apply TC_Pre. exact I. }
            repeat rewrite PositiveMap.gso by auto.
            apply Hcomp.
        + rewrite bindSubstProgRet in Hstep0. inversion Hstep0.
        + rewrite bindSubstProgTau in Hstep0. inversion Hstep0.
      - destruct u.
        + rewrite bindSubstProgVis in Hstep0.
          dependent destruction Hstep0.
          * exists (TMap.add t
              (Build_ThreadState m0 (Vis m1 k0) (Some m1)) cEF).
            split.
            { econstructor.
              - symmetry. exact x1.
              - econstructor. exact Hstep0.
              - reflexivity. }
            intro i. destruct (Pos.eq_dec i t); subst.
            { repeat rewrite PositiveMap.gss.
              rewrite <- x0, <- x.
              rewrite <- bindSubstProgVis.
              apply TC_Run.
              exists k0. reflexivity. }
            repeat rewrite PositiveMap.gso by auto.
            apply Hcomp.
          * exists (TMap.add t
              (Build_ThreadState m0 (k0 ret) None) cEF).
            split.
            { econstructor.
              - symmetry. exact x1.
              - econstructor. exact Hstep0.
              - reflexivity. }
            intro i. destruct (Pos.eq_dec i t); subst.
            { repeat rewrite PositiveMap.gss.
              rewrite <- x0, <- x.
              apply TC_Run. exact I. }
            repeat rewrite PositiveMap.gso by auto.
            apply Hcomp.
        + rewrite bindSubstProgRet in Hstep0. inversion Hstep0.
        + rewrite bindSubstProgTau in Hstep0. inversion Hstep0.
      - destruct u.
        + rewrite bindSubstProgVis in Hstep0.
          dependent destruction Hstep0.
          * exists (TMap.add t
              (Build_ThreadState m0 (Vis m1 k0) (Some m1)) cEF).
            split.
            { econstructor.
              - symmetry. exact x1.
              - econstructor. exact Hstep0.
              - reflexivity. }
            intro i. destruct (Pos.eq_dec i t); subst.
            { repeat rewrite PositiveMap.gss.
              rewrite <- x0, <- x.
              rewrite <- bindSubstProgVis.
              apply TC_Done.
              exists k0. reflexivity. }
            repeat rewrite PositiveMap.gso by auto.
            apply Hcomp.
          * exists (TMap.add t
              (Build_ThreadState m0 (k0 ret) None) cEF).
            split.
            { econstructor.
              - symmetry. exact x1.
              - econstructor. exact Hstep0.
              - reflexivity. }
            intro i. destruct (Pos.eq_dec i t); subst.
            { repeat rewrite PositiveMap.gss.
              rewrite <- x0, <- x.
              apply TC_Done. exact I. }
            repeat rewrite PositiveMap.gso by auto.
            apply Hcomp.
        + rewrite bindSubstProgRet in Hstep0. inversion Hstep0.
        + rewrite bindSubstProgTau in Hstep0. inversion Hstep0.
    Qed.

    Lemma pools_comp_uerror
      (sigma : State VE) c cFG cEF piF (ev : ThreadEvent)
      (Hcomp : pools_comp c cFG cEF piF)
      (Herror : uerror ev sigma c) :
      uerror ev sigma cEF.
    Proof.
      destruct ev as [t ev].
      inversion Herror; subst.
      pose proof (Hcomp t) as Hthread.
      simpl in Hfind.
      rewrite Hfind in Hthread.
      dependent destruction Hthread.
      - dependent destruction Herror0.
        exfalso.
        eapply substProg_not_vis; eauto.
      - destruct u.
        + rewrite bindSubstProgVis in Herror0.
          dependent destruction Herror0.
          econstructor.
          { symmetry. exact x1. }
          econstructor. exact Herror0.
        + rewrite bindSubstProgRet in Herror0. inversion Herror0.
        + rewrite bindSubstProgTau in Herror0. inversion Herror0.
      - destruct u.
        + rewrite bindSubstProgVis in Herror0.
          dependent destruction Herror0.
          econstructor.
          { symmetry. exact x1. }
          econstructor. exact Herror0.
        + rewrite bindSubstProgRet in Herror0. inversion Herror0.
        + rewrite bindSubstProgTau in Herror0. inversion Herror0.
      - destruct u.
        + rewrite bindSubstProgVis in Herror0.
          dependent destruction Herror0.
          econstructor.
          { symmetry. exact x1. }
          econstructor. exact Herror0.
        + rewrite bindSubstProgRet in Herror0. inversion Herror0.
        + rewrite bindSubstProgTau in Herror0. inversion Herror0.
    Qed.

  End Composition.

  Variant comp_inv {E G}
    {VE : @LTS E} {VG : @LTS G}
    (M : ModuleImpl E G)
    (X : State VE -> @ThreadPoolState E G ->
         State VG -> tmap (@LinState G) -> Prop)
    sigma c rho pi : Prop :=
  | CompInv_Error
      (Herror : poss_steps (PossOk rho pi) PossError) :
      comp_inv M X sigma c rho pi
  | CompInv_Continue
      (Hinv : forall t f c',
        invstep M t f c c' ->
        X sigma c' rho (TMap.add t (ls_inv f) pi))
      (Hret : forall t f r c',
        retstep t f r c c' ->
        TMap.find t pi = Some (ls_linr f r) /\
        X sigma c' rho (TMap.remove t pi))
      (Hustep : forall ev sigma' c',
        ustep ev sigma c sigma' c' ->
        exists rho' pi',
          poss_steps (PossOk rho pi) (PossOk rho' pi') /\
          X sigma' c' rho' pi')
      (Hlin : exists rho' pi',
        poss_steps (PossOk rho pi) (PossOk rho' pi') /\
        X sigma c rho' pi')
      (Htau : forall t c',
        taustep t c c' -> X sigma c' rho pi)
      (Hnoerror : forall ev, ~ uerror ev sigma c) :
      comp_inv M X sigma c rho pi.

  Lemma comp_inv_sound {E G}
    {VE : @LTS E} {VG : @LTS G}
    (M : ModuleImpl E G)
    (X : State VE -> @ThreadPoolState E G ->
         State VG -> tmap (@LinState G) -> Prop) :
    (forall sigma c rho pi,
      X sigma c rho pi ->
      comp_inv M X sigma c rho pi) ->
    forall sigma c rho pi,
      X sigma c rho pi ->
      TPSimulation M sigma c rho pi.
  Proof.
    intros Hbuild.
    cofix CIH.
    intros sigma c rho pi HX.
    pose proof (Hbuild _ _ _ _ HX) as Hcase.
    dependent destruction Hcase.
    - constructor. assumption.
    - apply TPSim_Continue; intros.
      + apply Hinv in Hstep.
        apply CIH. assumption.
      + apply Hret in Hstep as [Hpi HX'].
        split.
        * exact Hpi.
        * apply CIH. exact HX'.
      + apply Hustep in Hstep as (rho' & pi' & Hsteps & HX').
        exists rho', pi'. split.
        * exact Hsteps.
        * apply CIH. exact HX'.
      + destruct Hlin as (rho' & pi' & Hsteps & HX').
        exists rho', pi'. split.
        * exact Hsteps.
        * apply CIH. exact HX'.
      + apply Htau in Hstep.
        apply CIH. assumption.
      + exact (Hnoerror ev).
  Qed.

  Lemma vcompSim_gen {E F G}
    {VE : @LTS E} {VF : @LTS F} {VG : @LTS G}
    (implEF : ModuleImpl E F) (implFG : ModuleImpl F G) :
    forall
      (sigma : State VE) (c : @ThreadPoolState E G)
      (rho : State VG) (piG : tmap (@LinState G))
      (mid : State VF) (cFG : @ThreadPoolState F G)
      (cEF : @ThreadPoolState E F) (piF : tmap (@LinState F)),
      TPSimulation implEF sigma cEF mid piF ->
      TPSimulation implFG mid cFG rho piG ->
      pools_comp implEF c cFG cEF piF ->
      TPSimulation (implEF ▶ implFG) sigma c rho piG.
  Proof.
    intros sigma c rho piG mid cFG cEF piF
      HsimEF HsimFG Hcomp.
    eapply comp_inv_sound with
      (M := implEF ▶ implFG)
      (X := fun sigma c rho piG =>
        poss_steps (PossOk rho piG) PossError \/
        exists mid cFG cEF piF,
          TPSimulation implEF sigma cEF mid piF /\
          TPSimulation implFG mid cFG rho piG /\
          pools_comp implEF c cFG cEF piF).
    - clear sigma c rho piG mid cFG cEF piF
        HsimEF HsimFG Hcomp.
      intros sigma c rho piG HX.
      destruct HX as [Herror | HX].
      { apply CompInv_Error. exact Herror. }
      destruct HX as
        (mid & cFG & cEF & piF & HsimEF & HsimFG & Hcomp).
    pose proof HsimFG as HsimFG0.
    dependent destruction HsimFG.
    { apply CompInv_Error. assumption. }
    pose proof HsimEF as HsimEF0.
    dependent destruction HsimEF.
    { apply CompInv_Error.
      exact (middle_error implEF implFG
        c cFG cEF mid piF rho piG Hcomp HsimFG0 Herror). }
    apply CompInv_Continue.
        * intros t q c' Hstep.
          inversion Hstep; subst.
          pose proof (Hcomp t) as Hthread.
          rewrite Hfind in Hthread.
          dependent destruction Hthread.
          assert (HinvFG :
            invstep implFG t q cFG
              (TMap.add t
                (Build_ThreadState q (implFG q t) None) cFG)).
          { econstructor.
            - symmetry. exact x0.
            - reflexivity. }
          specialize (tpsim_invstep0 _ _ _ HinvFG) as HsimFG'.
          right. exists mid,
            (TMap.add t
              (Build_ThreadState q (implFG q t) None) cFG),
            cEF, piF.
          repeat split; try assumption.
          intro i.
          destruct (Pos.eq_dec i t); subst.
          ++ rewrite PositiveMap.gss, PositiveMap.gss.
             rewrite <- x1, <- x.
             constructor.
          ++ rewrite PositiveMap.gso by auto.
             rewrite PositiveMap.gso by auto.
             apply Hcomp.
        * intros t q r c' Hstep.
          inversion Hstep; subst.
          pose proof (Hcomp t) as Hthread.
          rewrite Hfind in Hthread.
          dependent destruction Hthread.
          -- apply substProg_ret_inv in x0. inversion x0; subst.
             assert (HretFG :
               retstep t q r cFG (TMap.remove t cFG)).
             { econstructor.
               - symmetry. exact x1.
               - reflexivity. }
             specialize (tpsim_retstep0 _ _ _ _ HretFG)
               as [HpiG HsimFG'].
             split; [exact HpiG|].
             right. exists mid, (TMap.remove t cFG), cEF, piF.
             repeat split; try assumption.
             intro i.
             destruct (Pos.eq_dec i t); subst.
             ++ repeat rewrite PositiveMap.grs.
                rewrite <- x, <- x2.
                constructor.
             ++ repeat rewrite PositiveMap.gro by auto.
                apply Hcomp.
          -- inversion x0.
             exfalso. eapply bindSubstProg_not_ret; eauto.
          -- inversion x0.
             exfalso. eapply bindSubstProg_not_ret; eauto.
          -- inversion x0.
             exfalso. eapply bindSubstProg_not_ret; eauto.
        * intros ev sigma' c' Hstep.
          pose proof
            (pools_comp_ustep implEF
              sigma c cFG cEF piF ev sigma' c' Hcomp Hstep)
            as (cEF' & Hinner & Hcomp').
          specialize (tpsim_ustep _ _ _ Hinner)
            as (mid' & piF' & HstepsF & HsimEF').
          pose proof
            (middle_steps implEF implFG
              c' cFG cEF' mid piF mid' piF' rho piG
              Hcomp' HsimFG0 HstepsF)
            as Hmiddle.
          dependent destruction Hmiddle.
          { exists rho, piG. split; [apply rt_refl|].
            left. assumption. }
          exists rho', piG'. split; auto.
          right. exists mid', cFG0, cEF', piF'.
          repeat split; assumption.
        * destruct tpsim_linstep as
            (mid' & piF' & HstepsF & HsimEF').
          pose proof
            (middle_steps implEF implFG
              c cFG cEF mid piF mid' piF' rho piG
              Hcomp HsimFG0 HstepsF)
            as Hmiddle.
          dependent destruction Hmiddle.
          { exists rho, piG. split; [apply rt_refl|].
            left. assumption. }
          exists rho', piG'. split; auto.
          right. exists mid', cFG0, cEF, piF'.
          repeat split; assumption.
        * intros t c' Hstep.
          inversion Hstep; subst.
          pose proof (Hcomp t) as Hthread.
          rewrite Hfind in Hthread.
          dependent destruction Hthread.
          -- destruct p.
             ++ rewrite substProgVis in Hstep0.
                dependent destruction Hstep0.
                assert (HinvEF :
                  invstep implEF t m0 cEF
                    (TMap.add t
                      (Build_ThreadState m0 (implEF m0 t) None) cEF)).
                { econstructor.
                  - symmetry. exact x1.
                  - reflexivity. }
                specialize (tpsim_invstep _ _ _ HinvEF) as HsimEF'.
                right. exists mid, cFG,
                  (TMap.add t
                    (Build_ThreadState m0 (implEF m0 t) None) cEF),
                  (TMap.add t (ls_inv m0) piF).
                repeat split; try assumption.
                intro i.
                destruct (Pos.eq_dec i t); subst.
                { repeat rewrite PositiveMap.gss.
                  rewrite <- x0.
                  apply TC_Pre. exact I. }
                repeat rewrite PositiveMap.gso by auto.
                apply Hcomp.
             ++ rewrite substProgRet in Hstep0. inversion Hstep0.
             ++ rewrite substProgTau in Hstep0.
                dependent destruction Hstep0.
                assert (HtauFG :
                  taustep t cFG
                    (TMap.add t (Build_ThreadState q p None) cFG)).
                { econstructor.
                  - symmetry. exact x0.
                  - constructor.
                  - reflexivity. }
                specialize (tpsim_taustep0 _ _ HtauFG) as HsimFG'.
                right. exists mid,
                  (TMap.add t (Build_ThreadState q p None) cFG),
                  cEF, piF.
                repeat split; try assumption.
                intro i.
                destruct (Pos.eq_dec i t); subst.
                { repeat rewrite PositiveMap.gss.
                  rewrite <- x1, <- x.
                  apply TC_Left. }
                repeat rewrite PositiveMap.gso by auto.
                apply Hcomp.
          -- destruct u.
             ++ rewrite bindSubstProgVis in Hstep0. inversion Hstep0.
             ++ rewrite bindSubstProgRet in Hstep0.
                dependent destruction Hstep0.
                destruct b.
                { simpl in Hb. destruct Hb as [? Hb]. discriminate Hb. }
                assert (HretEF :
                  retstep t m0 r cEF (TMap.remove t cEF)).
                { econstructor.
                  - symmetry. exact x1.
                  - reflexivity. }
                specialize (tpsim_retstep _ _ _ _ HretEF)
                  as [HpiF _].
                rewrite HpiF in x. discriminate.
             ++ rewrite bindSubstProgTau in Hstep0.
                dependent destruction Hstep0.
                destruct b.
                { simpl in Hb. destruct Hb as [? Hb]. discriminate Hb. }
                assert (HtauEF :
                  taustep t cEF
                    (TMap.add t (Build_ThreadState m0 u None) cEF)).
                { econstructor.
                  - symmetry. exact x1.
                  - constructor.
                  - reflexivity. }
                specialize (tpsim_taustep _ _ HtauEF) as HsimEF'.
                right. exists mid, cFG,
                  (TMap.add t (Build_ThreadState m0 u None) cEF),
                  piF.
                repeat split; try assumption.
                intro i.
                destruct (Pos.eq_dec i t); subst.
                { rewrite PositiveMap.gss, PositiveMap.gss.
                  rewrite <- x0, <- x.
                  apply TC_Pre. exact I. }
                rewrite PositiveMap.gso by auto.
                rewrite PositiveMap.gso by auto.
                apply Hcomp.
          -- destruct u.
             ++ rewrite bindSubstProgVis in Hstep0. inversion Hstep0.
             ++ rewrite bindSubstProgRet in Hstep0.
                dependent destruction Hstep0.
                destruct b.
                { simpl in Hb. destruct Hb as [? Hb]. discriminate Hb. }
                assert (HretEF :
                  retstep t m0 r cEF (TMap.remove t cEF)).
                { econstructor.
                  - symmetry. exact x1.
                  - reflexivity. }
                specialize (tpsim_retstep _ _ _ _ HretEF)
                  as [HpiF _].
                rewrite HpiF in x. discriminate.
             ++ rewrite bindSubstProgTau in Hstep0.
                dependent destruction Hstep0.
                destruct b.
                { simpl in Hb. destruct Hb as [? Hb]. discriminate Hb. }
                assert (HtauEF :
                  taustep t cEF
                    (TMap.add t (Build_ThreadState m0 u None) cEF)).
                { econstructor.
                  - symmetry. exact x1.
                  - constructor.
                  - reflexivity. }
                specialize (tpsim_taustep _ _ HtauEF) as HsimEF'.
                right. exists mid, cFG,
                  (TMap.add t (Build_ThreadState m0 u None) cEF),
                  piF.
                repeat split; try assumption.
                intro i.
                destruct (Pos.eq_dec i t); subst.
                { rewrite PositiveMap.gss, PositiveMap.gss.
                  rewrite <- x0, <- x.
                  apply TC_Run. exact I. }
                rewrite PositiveMap.gso by auto.
                rewrite PositiveMap.gso by auto.
                apply Hcomp.
          -- destruct u.
             ++ rewrite bindSubstProgVis in Hstep0. inversion Hstep0.
             ++ rewrite bindSubstProgRet in Hstep0.
                dependent destruction Hstep0.
                destruct b.
                { simpl in Hb. destruct Hb as [? Hb]. discriminate Hb. }
                assert (HretEF :
                  retstep t m0 r0 cEF (TMap.remove t cEF)).
                { econstructor.
                  - symmetry. exact x1.
                  - reflexivity. }
                specialize (tpsim_retstep _ _ _ _ HretEF)
                  as [HpiF HsimEF'].
                rewrite HpiF in x.
                dependent destruction x.
                right. exists mid, cFG,
                  (TMap.remove t cEF), (TMap.remove t piF).
                repeat split; try assumption.
                intro i.
                destruct (Pos.eq_dec i t); subst.
                { rewrite PositiveMap.gss.
                  repeat rewrite PositiveMap.grs.
                  rewrite <- x0.
                  apply TC_Left. }
                repeat rewrite PositiveMap.gso by auto.
                repeat rewrite PositiveMap.gro by auto.
                apply Hcomp.
             ++ rewrite bindSubstProgTau in Hstep0.
                dependent destruction Hstep0.
                destruct b.
                { simpl in Hb. destruct Hb as [? Hb]. discriminate Hb. }
                assert (HtauEF :
                  taustep t cEF
                    (TMap.add t (Build_ThreadState m0 u None) cEF)).
                { econstructor.
                  - symmetry. exact x1.
                  - constructor.
                  - reflexivity. }
                specialize (tpsim_taustep _ _ HtauEF) as HsimEF'.
                right. exists mid, cFG,
                  (TMap.add t (Build_ThreadState m0 u None) cEF),
                  piF.
                repeat split; try assumption.
                intro i.
                destruct (Pos.eq_dec i t); subst.
                { rewrite PositiveMap.gss, PositiveMap.gss.
                  rewrite <- x0, <- x.
                  apply TC_Done. exact I. }
                rewrite PositiveMap.gso by auto.
                rewrite PositiveMap.gso by auto.
                apply Hcomp.
        * intros ev Herror.
          eapply tpsim_noerror.
          eapply pools_comp_uerror; eauto.
    - right. exists mid, cFG, cEF, piF.
      repeat split; assumption.
  Qed.

  Lemma vcompSim {E F G} 
    {VE : @LTS E} {VF : @LTS F} {VG : @LTS G}
    (implEF : ModuleImpl E F) (implFG : ModuleImpl F G) :
    forall (σ0 : State VE) (ϱ0 : State VF) (ρ0 : State VG),
    cal implEF σ0 ϱ0 ->
    cal implFG ϱ0 ρ0 ->
    cal (implEF ▶ implFG) σ0 ρ0.
  Proof.
    intros sigma mid rho HsimEF HsimFG.
    unfold cal in *.
    eapply vcompSim_gen with
      (mid := mid)
      (cFG := TMap.empty _)
      (cEF := TMap.empty _)
      (piF := TMap.empty _); eauto.
    apply pools_comp_empty.
  Qed.

  Print Assumptions vcompSim.

End VCompTPSim.

Module HCompTPSim.
  Import LTSSpec.
  Import TPSimulation.TPSimulation.
  Import Semantics.

  Lemma liftLeftProgVis {E1 E2 R} m
      (k : Sig.ar m -> Prog E1 R) :
    liftLeftProg (E2 := E2) (Vis m k) =
    @Vis (Sig.Plus.omap E1 E2) R
      (@inl (Sig.op E1) (Sig.op E2) m)
      (fun r => liftLeftProg (E2 := E2) (k r)).
  Proof.
    rewrite (PPid (liftLeftProg (E2 := E2) (Vis m k))) at 1.
    unfold PP, liftLeftProg at 1.
    reflexivity.
  Qed.

  Lemma liftLeftProgRet {E1 E2 R} (r : R) :
    liftLeftProg (E1 := E1) (E2 := E2) (Ret r) = Ret r.
  Proof.
    rewrite (PPid (liftLeftProg (E1 := E1) (E2 := E2) (Ret r))) at 1.
    unfold PP, liftLeftProg at 1.
    reflexivity.
  Qed.

  Lemma liftLeftProgTau {E1 E2 R} (p : Prog E1 R) :
    liftLeftProg (E2 := E2) (Tau p) =
    Tau (liftLeftProg (E2 := E2) p).
  Proof.
    rewrite (PPid (liftLeftProg (E2 := E2) (Tau p))) at 1.
    unfold PP, liftLeftProg at 1.
    reflexivity.
  Qed.

  Lemma liftRightProgVis {E1 E2 R} m
      (k : Sig.ar m -> Prog E2 R) :
    liftRightProg (E1 := E1) (Vis m k) =
    @Vis (Sig.Plus.omap E1 E2) R
      (@inr (Sig.op E1) (Sig.op E2) m)
      (fun r => liftRightProg (E1 := E1) (k r)).
  Proof.
    rewrite (PPid (liftRightProg (E1 := E1) (Vis m k))) at 1.
    unfold PP, liftRightProg at 1.
    reflexivity.
  Qed.

  Lemma liftRightProgRet {E1 E2 R} (r : R) :
    liftRightProg (E1 := E1) (E2 := E2) (Ret r) = Ret r.
  Proof.
    rewrite (PPid (liftRightProg (E1 := E1) (E2 := E2) (Ret r))) at 1.
    unfold PP, liftRightProg at 1.
    reflexivity.
  Qed.

  Lemma liftRightProgTau {E1 E2 R} (p : Prog E2 R) :
    liftRightProg (E1 := E1) (Tau p) =
    Tau (liftRightProg (E1 := E1) p).
  Proof.
    rewrite (PPid (liftRightProg (E1 := E1) (Tau p))) at 1.
    unfold PP, liftRightProg at 1.
    reflexivity.
  Qed.

  Definition packThreadProg {E F} (ts : @ThreadState E F) :
      { q : Sig.op F & Prog E (Sig.ar q) } :=
    existT _ (ts_op ts) (ts_prog ts).

  Section Composition.
    Context {E1 F1 E2 F2}
      {VE1 : @LTS E1} {VF1 : @LTS F1}
      {VE2 : @LTS E2} {VF2 : @LTS F2}.
    Context (impl1 : ModuleImpl E1 F1) (impl2 : ModuleImpl E2 F2).

    Definition liftLeftLinState (s : @LinState F1) :
        @LinState (Sig.Plus.omap F1 F2) :=
      match s with
      | ls_inv f =>
          @ls_inv (Sig.Plus.omap F1 F2)
            (@inl (Sig.op F1) (Sig.op F2) f)
      | ls_lini f =>
          @ls_lini (Sig.Plus.omap F1 F2)
            (@inl (Sig.op F1) (Sig.op F2) f)
      | ls_linr f r =>
          @ls_linr (Sig.Plus.omap F1 F2)
            (@inl (Sig.op F1) (Sig.op F2) f) r
      end.

    Definition liftRightLinState (s : @LinState F2) :
        @LinState (Sig.Plus.omap F1 F2) :=
      match s with
      | ls_inv f =>
          @ls_inv (Sig.Plus.omap F1 F2)
            (@inr (Sig.op F1) (Sig.op F2) f)
      | ls_lini f =>
          @ls_lini (Sig.Plus.omap F1 F2)
            (@inr (Sig.op F1) (Sig.op F2) f)
      | ls_linr f r =>
          @ls_linr (Sig.Plus.omap F1 F2)
            (@inr (Sig.op F1) (Sig.op F2) f) r
      end.

    Variant hthread :
      option (@ThreadState (Sig.Plus.omap E1 E2)
        (Sig.Plus.omap F1 F2)) ->
      option (@ThreadState E1 F1) ->
      option (@ThreadState E2 F2) ->
      option (@LinState (Sig.Plus.omap F1 F2)) ->
      option (@LinState F1) ->
      option (@LinState F2) -> Prop :=
    | HT_None :
        hthread None None None None None None
    | HT_Left q (p : Prog E1 (Sig.ar q))
        (b : option (Sig.op E1)) (ls : option (@LinState F1))
        (pc : Prog (Sig.Plus.omap E1 E2) (Sig.ar q))
        (Hprog : pc = liftLeftProg (E2 := E2) p)
        (tc : @ThreadState (Sig.Plus.omap E1 E2)
          (Sig.Plus.omap F1 F2))
        (Htc : tc = @Build_ThreadState
          (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2)
          (@inl (Sig.op F1) (Sig.op F2) q) pc
          (option_map (@inl (Sig.op E1) (Sig.op E2)) b)) :
        hthread
          (Some tc)
          (Some (Build_ThreadState q p b))
          None
          (option_map liftLeftLinState ls)
          ls None
    | HT_Right q (p : Prog E2 (Sig.ar q))
        (b : option (Sig.op E2)) (ls : option (@LinState F2))
        (pc : Prog (Sig.Plus.omap E1 E2) (Sig.ar q))
        (Hprog : pc = liftRightProg (E1 := E1) p)
        (tc : @ThreadState (Sig.Plus.omap E1 E2)
          (Sig.Plus.omap F1 F2))
        (Htc : tc = @Build_ThreadState
          (Sig.Plus.omap E1 E2) (Sig.Plus.omap F1 F2)
          (@inr (Sig.op F1) (Sig.op F2) q) pc
          (option_map (@inr (Sig.op E1) (Sig.op E2)) b)) :
        hthread
          (Some tc)
          None
          (Some (Build_ThreadState q p b))
          (option_map liftRightLinState ls)
          None ls.

    Definition hpools
      (c : @ThreadPoolState (Sig.Plus.omap E1 E2)
        (Sig.Plus.omap F1 F2))
      (c1 : @ThreadPoolState E1 F1)
      (c2 : @ThreadPoolState E2 F2)
      (pi : tmap (@LinState (Sig.Plus.omap F1 F2)))
      (pi1 : tmap (@LinState F1))
      (pi2 : tmap (@LinState F2)) : Prop :=
      forall t, hthread
        (TMap.find t c) (TMap.find t c1) (TMap.find t c2)
        (TMap.find t pi) (TMap.find t pi1) (TMap.find t pi2).

    Lemma hpools_empty :
      hpools (TMap.empty _) (TMap.empty _) (TMap.empty _)
        (TMap.empty _) (TMap.empty _) (TMap.empty _).
    Proof.
      intro t. repeat rewrite PositiveMap.gempty. constructor.
    Qed.

    Lemma liftLeftProg_ret_inv {R} (p : Prog E1 R) r :
      liftLeftProg (E2 := E2) p = Ret r -> p = Ret r.
    Proof.
      destruct p.
      - rewrite liftLeftProgVis. discriminate.
      - rewrite liftLeftProgRet. inversion 1. reflexivity.
      - rewrite liftLeftProgTau. discriminate.
    Qed.

    Lemma liftRightProg_ret_inv {R} (p : Prog E2 R) r :
      liftRightProg (E1 := E1) p = Ret r -> p = Ret r.
    Proof.
      destruct p.
      - rewrite liftRightProgVis. discriminate.
      - rewrite liftRightProgRet. inversion 1. reflexivity.
      - rewrite liftRightProgTau. discriminate.
    Qed.

    Lemma hpools_update t c c1 c2 pi pi1 pi2
        ec ec1 ec2 epi epi1 epi2 :
      hpools c c1 c2 pi pi1 pi2 ->
      hthread ec ec1 ec2 epi epi1 epi2 ->
      hpools
        (match ec with Some x => TMap.add t x c | None => TMap.remove t c end)
        (match ec1 with Some x => TMap.add t x c1 | None => TMap.remove t c1 end)
        (match ec2 with Some x => TMap.add t x c2 | None => TMap.remove t c2 end)
        (match epi with Some x => TMap.add t x pi | None => TMap.remove t pi end)
        (match epi1 with Some x => TMap.add t x pi1 | None => TMap.remove t pi1 end)
        (match epi2 with Some x => TMap.add t x pi2 | None => TMap.remove t pi2 end).
    Proof.
      intros H Ht i. destruct (Pos.eq_dec i t); subst.
      - destruct ec, ec1, ec2, epi, epi1, epi2; simpl in *;
          repeat rewrite ?PositiveMap.gss, ?PositiveMap.grs; auto.
      - destruct ec, ec1, ec2, epi, epi1, epi2; simpl in *;
          repeat rewrite ?PositiveMap.gso, ?PositiveMap.gro by auto;
          apply H.
    Qed.

    Variant hmiddle
      (c : @ThreadPoolState (Sig.Plus.omap E1 E2)
        (Sig.Plus.omap F1 F2))
      (c1 : @ThreadPoolState E1 F1) (c2 : @ThreadPoolState E2 F2)
      (s1 : State VF1) (pi1 : tmap (@LinState F1))
      (s2 : State VF2) (pi2 : tmap (@LinState F2))
      (s : State (tens_lts VF1 VF2))
      (pi : tmap (@LinState (Sig.Plus.omap F1 F2))) : Prop :=
    | HM_Error
        (Herror : poss_steps (PossOk s pi) PossError) :
        hmiddle c c1 c2 s1 pi1 s2 pi2 s pi
    | HM_Continue
        (pi' : tmap (@LinState (Sig.Plus.omap F1 F2)))
        (Hsteps : @poss_steps _ (tens_lts VF1 VF2)
          (@PossOk _ (tens_lts VF1 VF2) s pi)
          (@PossOk _ (tens_lts VF1 VF2) (pair s1 s2) pi'))
        (Hpools : hpools c c1 c2 pi' pi1 pi2) :
        hmiddle c c1 c2 s1 pi1 s2 pi2 s pi.

    Lemma poss_left_one c c1 c2 s1 pi1 s1' pi1' s2 pi2 pi
      (Hpools : hpools c c1 c2 pi pi1 pi2)
      (Hstep : @poss_step _ VF1
        (PossOk s1 pi1) (PossOk s1' pi1')) :
      hmiddle c c1 c2 s1' pi1' s2 pi2
        (pair s1 s2) pi.
    Proof.
      inversion Hstep; subst.
      - pose proof (Hpools t0) as Ht. rewrite Hlin in Ht.
        dependent destruction Ht.
        eapply HM_Continue with
          (pi' := TMap.add t0
            (@ls_lini (Sig.Plus.omap F1 F2)
              (@inl (Sig.op F1) (Sig.op F2) f)) pi).
        + apply rt_step. constructor.
          * simpl. split; auto.
          * simpl in x3. symmetry. exact x3.
        + intro i. destruct (Pos.eq_dec i t0); subst.
          * repeat rewrite PositiveMap.gss.
            rewrite <- x0, <- x1, <- x2, <- x.
            replace
              (Some (@ls_lini (Sig.Plus.omap F1 F2)
                (@inl (Sig.op F1) (Sig.op F2) f)))
              with (option_map liftLeftLinState
                (Some (@ls_lini F1 f))) by reflexivity.
            eapply HT_Left; reflexivity.
          * repeat rewrite PositiveMap.gso by auto. apply Hpools.
      - pose proof (Hpools t0) as Ht. rewrite Hlin in Ht.
        dependent destruction Ht.
        eapply HM_Continue with
          (pi' := TMap.add t0
            (@ls_linr (Sig.Plus.omap F1 F2)
              (@inl (Sig.op F1) (Sig.op F2) f) ret) pi).
        + apply rt_step. constructor.
          * simpl. split; auto.
          * simpl in x3. symmetry. exact x3.
        + intro i. destruct (Pos.eq_dec i t0); subst.
          * repeat rewrite PositiveMap.gss.
            rewrite <- x0, <- x1, <- x2, <- x.
            replace
              (Some (@ls_linr (Sig.Plus.omap F1 F2)
                (@inl (Sig.op F1) (Sig.op F2) f) ret))
              with (option_map liftLeftLinState
                (Some (@ls_linr F1 f ret))) by reflexivity.
            eapply HT_Left; reflexivity.
          * repeat rewrite PositiveMap.gso by auto. apply Hpools.
    Qed.

    Lemma poss_right_one c c1 c2 s1 pi1 s2 pi2 s2' pi2' pi
      (Hpools : hpools c c1 c2 pi pi1 pi2)
      (Hstep : @poss_step _ VF2
        (PossOk s2 pi2) (PossOk s2' pi2')) :
      hmiddle c c1 c2 s1 pi1 s2' pi2'
        (pair s1 s2) pi.
    Proof.
      inversion Hstep; subst.
      - pose proof (Hpools t0) as Ht. rewrite Hlin in Ht.
        dependent destruction Ht.
        eapply HM_Continue with
          (pi' := TMap.add t0
            (@ls_lini (Sig.Plus.omap F1 F2)
              (@inr (Sig.op F1) (Sig.op F2) f)) pi).
        + apply rt_step. constructor.
          * simpl. split; auto.
          * simpl in x3. symmetry. exact x3.
        + intro i. destruct (Pos.eq_dec i t0); subst.
          * repeat rewrite PositiveMap.gss.
            rewrite <- x0, <- x1, <- x2, <- x.
            replace
              (Some (@ls_lini (Sig.Plus.omap F1 F2)
                (@inr (Sig.op F1) (Sig.op F2) f)))
              with (option_map liftRightLinState
                (Some (@ls_lini F2 f))) by reflexivity.
            eapply HT_Right; reflexivity.
          * repeat rewrite PositiveMap.gso by auto. apply Hpools.
      - pose proof (Hpools t0) as Ht. rewrite Hlin in Ht.
        dependent destruction Ht.
        eapply HM_Continue with
          (pi' := TMap.add t0
            (@ls_linr (Sig.Plus.omap F1 F2)
              (@inr (Sig.op F1) (Sig.op F2) f) ret) pi).
        + apply rt_step. constructor.
          * simpl. split; auto.
          * simpl in x3. symmetry. exact x3.
        + intro i. destruct (Pos.eq_dec i t0); subst.
          * repeat rewrite PositiveMap.gss.
            rewrite <- x0, <- x1, <- x2, <- x.
            replace
              (Some (@ls_linr (Sig.Plus.omap F1 F2)
                (@inr (Sig.op F1) (Sig.op F2) f) ret))
              with (option_map liftRightLinState
                (Some (@ls_linr F2 f ret))) by reflexivity.
            eapply HT_Right; reflexivity.
          * repeat rewrite PositiveMap.gso by auto. apply Hpools.
    Qed.

    Lemma poss_left_error_one c c1 c2 s1 pi1
        (s2 : State VF2) pi2 pi
      (Hpools : hpools c c1 c2 pi pi1 pi2)
      (Hstep : @poss_step _ VF1 (PossOk s1 pi1) PossError) :
      @poss_steps _ (tens_lts VF1 VF2)
        (@PossOk _ (tens_lts VF1 VF2) (pair s1 s2) pi)
        (@PossError _ (tens_lts VF1 VF2)).
    Proof.
      dependent destruction Hstep.
      pose proof (Hpools t0) as Ht. rewrite Hlin in Ht.
      dependent destruction Ht.
      apply rt_step.
      apply (@ps_error (Sig.Plus.omap F1 F2) (tens_lts VF1 VF2)
        t0 (@inl (Sig.op F1) (Sig.op F2) f) (pair s1 s2) pi).
      - simpl. exact Herror.
      - simpl in x3. symmetry. exact x3.
    Qed.

    Lemma poss_right_error_one c c1 c2
        (s1 : State VF1) pi1 s2 pi2 pi
      (Hpools : hpools c c1 c2 pi pi1 pi2)
      (Hstep : @poss_step _ VF2 (PossOk s2 pi2) PossError) :
      @poss_steps _ (tens_lts VF1 VF2)
        (@PossOk _ (tens_lts VF1 VF2) (pair s1 s2) pi)
        (@PossError _ (tens_lts VF1 VF2)).
    Proof.
      dependent destruction Hstep.
      pose proof (Hpools t0) as Ht. rewrite Hlin in Ht.
      dependent destruction Ht.
      apply rt_step.
      apply (@ps_error (Sig.Plus.omap F1 F2) (tens_lts VF1 VF2)
        t0 (@inr (Sig.op F1) (Sig.op F2) f) (pair s1 s2) pi).
      - simpl. exact Herror.
      - simpl in x3. symmetry. exact x3.
    Qed.

    Lemma poss_left_steps c c1 c2 s1 pi1 s1' pi1' s2 pi2 pi
      (Hpools : hpools c c1 c2 pi pi1 pi2)
      (Hsteps : @poss_steps _ VF1
        (PossOk s1 pi1) (PossOk s1' pi1')) :
      hmiddle c c1 c2 s1' pi1' s2 pi2 (pair s1 s2) pi.
    Proof.
      apply clos_rt_rt1n_iff in Hsteps.
      remember (PossOk s1 pi1) as x.
      remember (PossOk s1' pi1') as z.
      revert s1 pi1 s1' pi1' Heqx Heqz s2 pi2 pi Hpools.
      induction Hsteps; intros; subst.
      - inversion Heqz; subst.
        eapply HM_Continue; [apply rt_refl | exact Hpools].
      - destruct y; [|inversion Hsteps].
        pose proof H as Hone. dependent destruction H.
        + pose proof (poss_left_one
            c c1 c2 s1 pi1 s (TMap.add t0 (ls_lini f) pi1)
            s2 pi2 pi Hpools Hone)
            as Hmiddle.
          dependent destruction Hmiddle.
          * constructor. exact Herror.
          * pose proof (IHHsteps
              s (TMap.add t0 (ls_lini f) pi1) s1' pi1'
              eq_refl eq_refl s2 pi2 pi' Hpools0) as Hrest.
            dependent destruction Hrest.
            -- constructor.
               exact (@rt_trans Poss poss_step _ _ _ Hsteps0 Herror).
            -- eapply HM_Continue.
               ++ exact (@rt_trans Poss poss_step _ _ _ Hsteps0 Hsteps1).
               ++ exact Hpools1.
        + pose proof (poss_left_one
            c c1 c2 s1 pi1 s (TMap.add t0 (ls_linr f ret) pi1)
            s2 pi2 pi Hpools Hone)
            as Hmiddle.
          dependent destruction Hmiddle.
          * constructor. exact Herror.
          * pose proof (IHHsteps
              s (TMap.add t0 (ls_linr f ret) pi1) s1' pi1'
              eq_refl eq_refl s2 pi2 pi' Hpools0) as Hrest.
            dependent destruction Hrest.
            -- constructor.
               exact (@rt_trans Poss poss_step _ _ _ Hsteps0 Herror).
            -- eapply HM_Continue.
               ++ exact (@rt_trans Poss poss_step _ _ _ Hsteps0 Hsteps1).
               ++ exact Hpools1.
        + constructor. eapply poss_left_error_one; eauto.
    Qed.

    Lemma poss_right_steps c c1 c2 s1 pi1 s2 pi2 s2' pi2' pi
      (Hpools : hpools c c1 c2 pi pi1 pi2)
      (Hsteps : @poss_steps _ VF2
        (PossOk s2 pi2) (PossOk s2' pi2')) :
      hmiddle c c1 c2 s1 pi1 s2' pi2' (pair s1 s2) pi.
    Proof.
      apply clos_rt_rt1n_iff in Hsteps.
      remember (PossOk s2 pi2) as x.
      remember (PossOk s2' pi2') as z.
      revert s2 pi2 s2' pi2' Heqx Heqz s1 pi1 pi Hpools.
      induction Hsteps; intros; subst.
      - inversion Heqz; subst.
        eapply HM_Continue; [apply rt_refl | exact Hpools].
      - destruct y; [|inversion Hsteps].
        pose proof H as Hone. dependent destruction H.
        + pose proof (poss_right_one
            c c1 c2 s1 pi1 s2 pi2 s
            (TMap.add t0 (ls_lini f) pi2) pi Hpools Hone)
            as Hmiddle.
          dependent destruction Hmiddle.
          * constructor. exact Herror.
          * pose proof (IHHsteps
              s (TMap.add t0 (ls_lini f) pi2) s2' pi2'
              eq_refl eq_refl s1 pi1 pi' Hpools0) as Hrest.
            dependent destruction Hrest.
            -- constructor.
               exact (@rt_trans Poss poss_step _ _ _ Hsteps0 Herror).
            -- eapply HM_Continue.
               ++ exact (@rt_trans Poss poss_step _ _ _ Hsteps0 Hsteps1).
               ++ exact Hpools1.
        + pose proof (poss_right_one
            c c1 c2 s1 pi1 s2 pi2 s
            (TMap.add t0 (ls_linr f ret) pi2) pi Hpools Hone)
            as Hmiddle.
          dependent destruction Hmiddle.
          * constructor. exact Herror.
          * pose proof (IHHsteps
              s (TMap.add t0 (ls_linr f ret) pi2) s2' pi2'
              eq_refl eq_refl s1 pi1 pi' Hpools0) as Hrest.
            dependent destruction Hrest.
            -- constructor.
               exact (@rt_trans Poss poss_step _ _ _ Hsteps0 Herror).
            -- eapply HM_Continue.
               ++ exact (@rt_trans Poss poss_step _ _ _ Hsteps0 Hsteps1).
               ++ exact Hpools1.
        + constructor. eapply poss_right_error_one; eauto.
    Qed.

    Lemma poss_left_error c c1 c2 s1 pi1
        (s2 : State VF2) pi2 pi
      (Hpools : hpools c c1 c2 pi pi1 pi2)
      (Hsteps : @poss_steps _ VF1 (PossOk s1 pi1) PossError) :
      @poss_steps _ (tens_lts VF1 VF2)
        (@PossOk _ (tens_lts VF1 VF2) (pair s1 s2) pi)
        (@PossError _ (tens_lts VF1 VF2)).
    Proof.
      apply clos_rt_rt1n_iff in Hsteps.
      remember (PossOk s1 pi1) as x. remember PossError as z.
      revert s1 pi1 Heqx Heqz s2 pi2 pi Hpools.
      induction Hsteps; intros; subst; try discriminate.
      destruct y.
      - pose proof H as Hone. dependent destruction H.
        + pose proof (poss_left_one
            c c1 c2 s1 pi1 s (TMap.add t0 (ls_lini f) pi1)
            s2 pi2 pi Hpools Hone)
            as Hmiddle.
          dependent destruction Hmiddle.
          * exact Herror.
          * eapply rt_trans; [exact Hsteps0|].
            exact (IHHsteps s (TMap.add t0 (ls_lini f) pi1)
              eq_refl eq_refl s2 pi2 pi' Hpools0).
        + pose proof (poss_left_one
            c c1 c2 s1 pi1 s (TMap.add t0 (ls_linr f ret) pi1)
            s2 pi2 pi Hpools Hone)
            as Hmiddle.
          dependent destruction Hmiddle.
          * exact Herror.
          * eapply rt_trans; [exact Hsteps0|].
            exact (IHHsteps s (TMap.add t0 (ls_linr f ret) pi1)
              eq_refl eq_refl s2 pi2 pi' Hpools0).
      - inversion Hsteps; subst.
        + eapply poss_left_error_one; eauto.
        + inversion H0.
    Qed.

    Lemma poss_right_error c c1 c2
        (s1 : State VF1) pi1 s2 pi2 pi
      (Hpools : hpools c c1 c2 pi pi1 pi2)
      (Hsteps : @poss_steps _ VF2 (PossOk s2 pi2) PossError) :
      @poss_steps _ (tens_lts VF1 VF2)
        (@PossOk _ (tens_lts VF1 VF2) (pair s1 s2) pi)
        (@PossError _ (tens_lts VF1 VF2)).
    Proof.
      apply clos_rt_rt1n_iff in Hsteps.
      remember (PossOk s2 pi2) as x. remember PossError as z.
      revert s2 pi2 Heqx Heqz s1 pi1 pi Hpools.
      induction Hsteps; intros; subst; try discriminate.
      destruct y.
      - pose proof H as Hone. dependent destruction H.
        + pose proof (poss_right_one
            c c1 c2 s1 pi1 s2 pi2 s
            (TMap.add t0 (ls_lini f) pi2) pi Hpools Hone)
            as Hmiddle.
          dependent destruction Hmiddle.
          * exact Herror.
          * eapply rt_trans; [exact Hsteps0|].
            exact (IHHsteps s (TMap.add t0 (ls_lini f) pi2)
              eq_refl eq_refl s1 pi1 pi' Hpools0).
        + pose proof (poss_right_one
            c c1 c2 s1 pi1 s2 pi2 s
            (TMap.add t0 (ls_linr f ret) pi2) pi Hpools Hone)
            as Hmiddle.
          dependent destruction Hmiddle.
          * exact Herror.
          * eapply rt_trans; [exact Hsteps0|].
            exact (IHHsteps s (TMap.add t0 (ls_linr f ret) pi2)
              eq_refl eq_refl s1 pi1 pi' Hpools0).
      - inversion Hsteps; subst.
        + eapply poss_right_error_one; eauto.
        + inversion H0.
    Qed.

    Definition liftLeftEvent (ev : @ThreadEvent E1) :
        @ThreadEvent (Sig.Plus.omap E1 E2) :=
      match ev with
      | Build_ThreadEvent t (InvEv op) =>
          @Build_ThreadEvent (Sig.Plus.omap E1 E2) t
            (@InvEv (Sig.Plus.omap E1 E2)
              (@inl (Sig.op E1) (Sig.op E2) op))
      | Build_ThreadEvent t (ResEv op r) =>
          @Build_ThreadEvent (Sig.Plus.omap E1 E2) t
            (@ResEv (Sig.Plus.omap E1 E2)
              (@inl (Sig.op E1) (Sig.op E2) op) r)
      end.

    Definition liftRightEvent (ev : @ThreadEvent E2) :
        @ThreadEvent (Sig.Plus.omap E1 E2) :=
      match ev with
      | Build_ThreadEvent t (InvEv op) =>
          @Build_ThreadEvent (Sig.Plus.omap E1 E2) t
            (@InvEv (Sig.Plus.omap E1 E2)
              (@inr (Sig.op E1) (Sig.op E2) op))
      | Build_ThreadEvent t (ResEv op r) =>
          @Build_ThreadEvent (Sig.Plus.omap E1 E2) t
            (@ResEv (Sig.Plus.omap E1 E2)
              (@inr (Sig.op E1) (Sig.op E2) op) r)
      end.

    Variant hconcrete_result
      (c' : @ThreadPoolState (Sig.Plus.omap E1 E2)
        (Sig.Plus.omap F1 F2))
      (s1 : State VE1) (c1 : @ThreadPoolState E1 F1)
      (s2 : State VE2) (c2 : @ThreadPoolState E2 F2)
      (pi : tmap (@LinState (Sig.Plus.omap F1 F2)))
      (pi1 : tmap (@LinState F1)) (pi2 : tmap (@LinState F2))
      (sigma' : State (tens_lts VE1 VE2)) : Prop :=
    | HCR_Left ev s1' c1'
        (Hstep : ustep ev s1 c1 s1' c1')
        (Hstate : sigma' = pair s1' s2)
        (Hpools : hpools c' c1' c2 pi pi1 pi2) :
        hconcrete_result c' s1 c1 s2 c2 pi pi1 pi2 sigma'
    | HCR_Right ev s2' c2'
        (Hstep : ustep ev s2 c2 s2' c2')
        (Hstate : sigma' = pair s1 s2')
        (Hpools : hpools c' c1 c2' pi pi1 pi2) :
        hconcrete_result c' s1 c1 s2 c2 pi pi1 pi2 sigma'.

    Lemma hconcrete_step c c1 c2 pi pi1 pi2 s1 s2 ev sigma' c'
      (Hpools : hpools c c1 c2 pi pi1 pi2)
      (Hstep : @ustep _ _ (tens_lts VE1 VE2)
        ev (pair s1 s2) c sigma' c') :
      hconcrete_result c' s1 c1 s2 c2 pi pi1 pi2 sigma'.
    Proof.
      destruct sigma' as [sigma1' sigma2'].
      destruct ev as [t ev]. inversion Hstep; subst.
      pose proof (Hpools t) as Hthread.
      simpl in Hfind. rewrite Hfind in Hthread.
      dependent destruction Hthread.
      - dependent destruction Hstep0.
        + destruct p.
          * rewrite liftLeftProgVis in x.
            dependent destruction x.
            simpl in Hstep0. destruct Hstep0 as [Hs Hr]. subst.
            destruct b; inversion x0; subst.
            eapply HCR_Left with
              (ev := Build_ThreadEvent t (InvEv m0))
              (s1' := sigma1')
              (c1' := TMap.add t
                (Build_ThreadState q (Vis m0 k0) (Some m0)) c1).
            -- econstructor.
               ++ symmetry. exact x1.
               ++ econstructor. exact Hs.
               ++ reflexivity.
            -- reflexivity.
            -- intro i. destruct (Pos.eq_dec i t); subst.
               ++ repeat rewrite PositiveMap.gss.
                  rewrite <- x2, <- x3, <- x4.
                  pose proof
                    (HT_Left q (@Vis E1 (Sig.ar q) m0 k0)
                      (Some m0) (TMap.find t pi1)) as Hnew.
                  rewrite liftLeftProgVis in Hnew.
                  specialize (Hnew _ eq_refl).
                  specialize (Hnew _ eq_refl).
                  exact Hnew.
               ++ repeat rewrite PositiveMap.gso by auto. apply Hpools.
          * rewrite liftLeftProgRet in x. inversion x.
          * rewrite liftLeftProgTau in x. inversion x.
        + destruct p.
          * rewrite liftLeftProgVis in x.
            dependent destruction x.
            simpl in Hstep0. destruct Hstep0 as [Hs Hr]. subst.
            destruct b; inversion x0; subst.
            eapply HCR_Left with
              (ev := Build_ThreadEvent t (ResEv o ret))
              (s1' := sigma1')
              (c1' := TMap.add t
                (Build_ThreadState q (k0 ret) None) c1).
            -- econstructor.
               ++ symmetry. exact x1.
               ++ econstructor. exact Hs.
               ++ reflexivity.
            -- reflexivity.
            -- intro i. destruct (Pos.eq_dec i t); subst.
               ++ repeat rewrite PositiveMap.gss.
                  rewrite <- x2, <- x3, <- x4.
                  pose proof
                    (HT_Left q (k0 ret) None
                      (TMap.find t pi1)) as Hnew.
                  cbn in Hnew.
                  specialize (Hnew _ eq_refl).
                  specialize (Hnew _ eq_refl).
                  exact Hnew.
               ++ repeat rewrite PositiveMap.gso by auto. apply Hpools.
          * rewrite liftLeftProgRet in x. inversion x.
          * rewrite liftLeftProgTau in x. inversion x.
      - dependent destruction Hstep0.
        + destruct p.
          * rewrite liftRightProgVis in x.
            dependent destruction x.
            simpl in Hstep0. destruct Hstep0 as [Hs Hr]. subst.
            destruct b; inversion x0; subst.
            eapply HCR_Right with
              (ev := Build_ThreadEvent t (InvEv m0))
              (s2' := sigma2')
              (c2' := TMap.add t
                (Build_ThreadState q (Vis m0 k0) (Some m0)) c2).
            -- econstructor.
               ++ symmetry. exact x2.
               ++ econstructor. exact Hs.
               ++ reflexivity.
            -- reflexivity.
            -- intro i. destruct (Pos.eq_dec i t); subst.
               ++ repeat rewrite PositiveMap.gss.
                  rewrite <- x1, <- x3, <- x4.
                  pose proof
                    (HT_Right q (@Vis E2 (Sig.ar q) m0 k0)
                      (Some m0) (TMap.find t pi2)) as Hnew.
                  rewrite liftRightProgVis in Hnew.
                  specialize (Hnew _ eq_refl).
                  specialize (Hnew _ eq_refl).
                  exact Hnew.
               ++ repeat rewrite PositiveMap.gso by auto. apply Hpools.
          * rewrite liftRightProgRet in x. inversion x.
          * rewrite liftRightProgTau in x. inversion x.
        + destruct p.
          * rewrite liftRightProgVis in x.
            dependent destruction x.
            simpl in Hstep0. destruct Hstep0 as [Hs Hr]. subst.
            destruct b; inversion x0; subst.
            eapply HCR_Right with
              (ev := Build_ThreadEvent t (ResEv o ret))
              (s2' := sigma2')
              (c2' := TMap.add t
                (Build_ThreadState q (k0 ret) None) c2).
            -- econstructor.
               ++ symmetry. exact x2.
               ++ econstructor. exact Hs.
               ++ reflexivity.
            -- reflexivity.
            -- intro i. destruct (Pos.eq_dec i t); subst.
               ++ repeat rewrite PositiveMap.gss.
                  rewrite <- x1, <- x3, <- x4.
                  pose proof
                    (HT_Right q (k0 ret) None
                      (TMap.find t pi2)) as Hnew.
                  cbn in Hnew.
                  specialize (Hnew _ eq_refl).
                  specialize (Hnew _ eq_refl).
                  exact Hnew.
               ++ repeat rewrite PositiveMap.gso by auto. apply Hpools.
          * rewrite liftRightProgRet in x. inversion x.
          * rewrite liftRightProgTau in x. inversion x.
    Qed.

  End Composition.

  Lemma hcompSim {E1 F1 E2 F2} 
    {VE1 : @LTS E1} {VF1 : @LTS F1} {VE2 : @LTS E2} {VF2 : @LTS F2}
    (impl1 : ModuleImpl E1 F1) (impl2 : ModuleImpl E2 F2) :
    forall (σ01 : State VE1) (ρ01 : State VF1) (σ02 : State VE2) (ρ02 : State VF2),
    cal impl1 σ01 ρ01 ->
    cal impl2 σ02 ρ02 ->
    @cal _ _ (tens_lts VE1 VE2) (tens_lts VF1 VF2) (impl1 ⊗ impl2) (pair σ01 σ02) (pair ρ01 ρ02).
  Proof.
    intros sigma1 rho1 sigma2 rho2 Hsim1 Hsim2.
    unfold cal in Hsim1, Hsim2 |- *.
    eapply VCompTPSim.comp_inv_sound with
      (M := impl1 ⊗ impl2)
      (X := fun sigma c rho pi =>
        @poss_steps _ (tens_lts VF1 VF2)
          (PossOk rho pi) PossError \/
        match sigma, rho with
        | pair sigma1 sigma2, pair rho1 rho2 =>
            exists c1 c2 pi1 pi2,
              TPSimulation impl1 sigma1 c1 rho1 pi1 /\
              TPSimulation impl2 sigma2 c2 rho2 pi2 /\
              hpools c c1 c2 pi pi1 pi2
        end).
    - clear sigma1 rho1 sigma2 rho2 Hsim1 Hsim2.
      intros [sigma1 sigma2] c [rho1 rho2] pi HX.
      destruct HX as [Herror | HX].
      { apply VCompTPSim.CompInv_Error. exact Herror. }
      destruct HX as
        (c1 & c2 & pi1 & pi2 & Hsim1 & Hsim2 & Hpools).
      pose proof Hsim1 as Hsim1'.
      dependent destruction Hsim1.
      { apply VCompTPSim.CompInv_Error.
        eapply poss_left_error; eauto. }
      pose proof Hsim2 as Hsim2'.
      dependent destruction Hsim2.
      { apply VCompTPSim.CompInv_Error.
        eapply poss_right_error; eauto. }
      apply VCompTPSim.CompInv_Continue.
      + intros t f c' Hinv.
        inversion Hinv; subst.
        pose proof (Hpools t) as Hthread.
        rewrite Hfind in Hthread.
        dependent destruction Hthread.
        destruct f as [f1 | f2].
        * right. exists
            (TMap.add t
              (Build_ThreadState f1 (impl1 f1 t) None) c1),
            c2, (TMap.add t (ls_inv f1) pi1), pi2.
          repeat split.
          -- apply tpsim_invstep. constructor.
             ++ symmetry. exact x0.
             ++ reflexivity.
          -- exact Hsim2'.
          -- intro i. destruct (Pos.eq_dec i t); subst.
             ++ repeat rewrite PositiveMap.gss.
                rewrite <- x1, <- x.
                pose proof
                  (@HT_Left E1 F1 E2 F2 f1 (impl1 f1 t) None
                    (Some (ls_inv f1))) as Hnew.
                cbn in Hnew.
                specialize (Hnew _ eq_refl).
                specialize (Hnew _ eq_refl).
                exact Hnew.
             ++ repeat rewrite PositiveMap.gso by auto. apply Hpools.
        * right. exists c1,
            (TMap.add t
              (Build_ThreadState f2 (impl2 f2 t) None) c2),
            pi1, (TMap.add t (ls_inv f2) pi2).
          repeat split.
          -- exact Hsim1'.
          -- apply tpsim_invstep0. constructor.
             ++ symmetry. exact x1.
             ++ reflexivity.
          -- intro i. destruct (Pos.eq_dec i t); subst.
             ++ repeat rewrite PositiveMap.gss.
                rewrite <- x0, <- x3.
                pose proof
                  (@HT_Right E1 F1 E2 F2 f2 (impl2 f2 t) None
                    (Some (ls_inv f2))) as Hnew.
                cbn in Hnew.
                specialize (Hnew _ eq_refl).
                specialize (Hnew _ eq_refl).
                exact Hnew.
             ++ repeat rewrite PositiveMap.gso by auto. apply Hpools.
      + intros t f r c' Hret.
        inversion Hret; subst.
        pose proof (Hpools t) as Hthread.
        rewrite Hfind in Hthread.
        inversion Hthread.
        * pose proof (f_equal packThreadProg Htc) as Hpc.
          dependent destruction Hpc.
          symmetry in x.
          apply liftLeftProg_ret_inv in x.
          dependent destruction x.
          destruct b; inversion x0; subst.
          destruct (tpsim_retstep t q r
            (TMap.remove t c1)) as [Hpi Hnext].
          { constructor.
            - symmetry. exact H.
            - reflexivity. }
          split.
          -- rewrite Hpi. reflexivity.
          -- right. exists (TMap.remove t c1), c2,
               (TMap.remove t pi1), pi2.
             repeat split; auto.
             intro i. destruct (Pos.eq_dec i t); subst.
             ++ repeat rewrite PositiveMap.grs.
                rewrite <- H2, <- H5.
                apply HT_None.
             ++ repeat rewrite PositiveMap.gro by auto. apply Hpools.
        * pose proof (f_equal packThreadProg Htc) as Hpc.
          dependent destruction Hpc.
          symmetry in x.
          apply liftRightProg_ret_inv in x.
          dependent destruction x.
          destruct b; inversion x0; subst.
          destruct (tpsim_retstep0 t q r
            (TMap.remove t c2)) as [Hpi Hnext].
          { constructor.
            - symmetry. exact H2.
            - reflexivity. }
          split.
          -- rewrite Hpi. reflexivity.
          -- right. exists c1, (TMap.remove t c2),
               pi1, (TMap.remove t pi2).
             repeat split; auto.
             intro i. destruct (Pos.eq_dec i t); subst.
             ++ repeat rewrite PositiveMap.grs.
                rewrite <- H, <- H4.
                apply HT_None.
             ++ repeat rewrite PositiveMap.gro by auto. apply Hpools.
      + intros ev sigma' c' Hstep.
        pose proof (hconcrete_step
          c c1 c2 pi pi1 pi2 sigma1 sigma2 ev sigma' c'
          Hpools Hstep) as Hroute.
        dependent destruction Hroute.
        * destruct (tpsim_ustep ev0 s1' c1' Hstep0)
            as (rho1' & pi1' & Hsteps & Hnext).
          pose proof (poss_left_steps
            c' c1' c2 rho1 pi1 rho1' pi1'
            rho2 pi2 pi Hpools0 Hsteps) as Hmiddle.
          dependent destruction Hmiddle.
          -- exists (pair rho1 rho2), pi. split.
             ++ apply rt_refl.
             ++ left. exact Herror.
          -- exists (pair rho1' rho2), pi'. split.
             ++ exact Hsteps0.
             ++ right. rewrite Hstate.
                exists c1', c2, pi1', pi2.
                repeat split; auto.
        * destruct (tpsim_ustep0 ev0 s2' c2' Hstep0)
            as (rho2' & pi2' & Hsteps & Hnext).
          pose proof (poss_right_steps
            c' c1 c2' rho1 pi1 rho2 pi2 rho2' pi2'
            pi Hpools0 Hsteps) as Hmiddle.
          dependent destruction Hmiddle.
          -- exists (pair rho1 rho2), pi. split.
             ++ apply rt_refl.
             ++ left. exact Herror.
          -- exists (pair rho1 rho2'), pi'. split.
             ++ exact Hsteps0.
             ++ right. rewrite Hstate.
                exists c1, c2', pi1, pi2'.
                repeat split; auto.
      + destruct tpsim_linstep as
          (rho1' & pi1' & Hsteps & Hnext).
        pose proof (poss_left_steps
          c c1 c2 rho1 pi1 rho1' pi1'
          rho2 pi2 pi Hpools Hsteps) as Hmiddle.
        dependent destruction Hmiddle.
        * exists (pair rho1 rho2), pi. split.
          -- apply rt_refl.
          -- left. exact Herror.
        * exists (pair rho1' rho2), pi'. split.
          -- exact Hsteps0.
          -- right. exists c1, c2, pi1', pi2.
             repeat split; auto.
      + intros t c' Htau.
        inversion Htau; subst.
        pose proof (Hpools t) as Hthread.
        rewrite Hfind in Hthread.
        dependent destruction Hthread.
        * dependent destruction Hstep.
          destruct p.
          -- rewrite liftLeftProgVis in x. discriminate.
          -- rewrite liftLeftProgRet in x. discriminate.
          -- rewrite liftLeftProgTau in x.
             dependent destruction x.
             right. exists (TMap.add t
               (Build_ThreadState q p b) c1), c2, pi1, pi2.
             repeat split.
             ++ apply (tpsim_taustep t
                  (TMap.add t (Build_ThreadState q p b) c1)).
                eapply TauStep with
                  (ts1 := Build_ThreadState q (Tau p) b)
                  (ts2 := Build_ThreadState q p b).
                ** symmetry. exact x0.
                ** constructor.
                ** reflexivity.
             ++ exact Hsim2'.
             ++ intro i. destruct (Pos.eq_dec i t); subst.
                ** repeat rewrite PositiveMap.gss.
                   rewrite <- x1, <- x2, <- x3.
                   eapply HT_Left; reflexivity.
                ** repeat rewrite PositiveMap.gso by auto. apply Hpools.
        * dependent destruction Hstep.
          destruct p.
          -- rewrite liftRightProgVis in x. discriminate.
          -- rewrite liftRightProgRet in x. discriminate.
          -- rewrite liftRightProgTau in x.
             dependent destruction x.
             right. exists c1, (TMap.add t
               (Build_ThreadState q p b) c2), pi1, pi2.
             repeat split.
             ++ exact Hsim1'.
             ++ apply (tpsim_taustep0 t
                  (TMap.add t (Build_ThreadState q p b) c2)).
                eapply TauStep with
                  (ts1 := Build_ThreadState q (Tau p) b)
                  (ts2 := Build_ThreadState q p b).
                ** symmetry. exact x1.
                ** constructor.
                ** reflexivity.
             ++ intro i. destruct (Pos.eq_dec i t); subst.
                ** repeat rewrite PositiveMap.gss.
                   rewrite <- x0, <- x2, <- x3.
                   eapply HT_Right; reflexivity.
                ** repeat rewrite PositiveMap.gso by auto. apply Hpools.
      + intros ev Herror.
        destruct ev as [t ev]. inversion Herror; subst.
        pose proof (Hpools t) as Hthread.
        simpl in Hfind. rewrite Hfind in Hthread.
        dependent destruction Hthread.
        * dependent destruction Herror0.
          destruct p.
          -- rewrite liftLeftProgVis in x.
             dependent destruction x.
             destruct b; inversion x0; subst.
             apply (tpsim_noerror
               (Build_ThreadEvent t (InvEv m0))).
             econstructor.
             ++ symmetry. exact x1.
             ++ econstructor. simpl in Herror0. exact Herror0.
          -- rewrite liftLeftProgRet in x. discriminate.
          -- rewrite liftLeftProgTau in x. discriminate.
        * dependent destruction Herror0.
          destruct p.
          -- rewrite liftRightProgVis in x.
             dependent destruction x.
             destruct b; inversion x0; subst.
             apply (tpsim_noerror0
               (Build_ThreadEvent t (InvEv m0))).
             econstructor.
             ++ symmetry. exact x2.
             ++ econstructor. simpl in Herror0. exact Herror0.
          -- rewrite liftRightProgRet in x. discriminate.
          -- rewrite liftRightProgTau in x. discriminate.
    - right. exists (TMap.empty _), (TMap.empty _),
        (TMap.empty _), (TMap.empty _).
      repeat split; auto.
      apply hpools_empty.
  Qed.

  Print Assumptions hcompSim.
End HCompTPSim.

Module VCompTPSimSet.
  Import LTSSpec.
  Import TPSimulationSet.TPSimulation.
  Import Semantics.

  Lemma vcompSim {E F G} 
    {VE : @LTS E} {VF : @LTS F} {VG : @LTS G}
    (implEF : ModuleImpl E F) (implFG : ModuleImpl F G) :
    forall (σ0 : State VE) (ϱ0 : State VF) (ρ0 : State VG),
    cal implEF σ0 ϱ0 ->
    cal implFG ϱ0 ρ0 ->
    cal (implEF ▶ implFG) σ0 ρ0.
  Proof.
  Admitted.
End VCompTPSimSet.

Module HCompTPSimSet.
  Import LTSSpec.
  Import TPSimulationSet.TPSimulation.
  Import Semantics.

  Lemma hcompSim {E1 F1 E2 F2} 
    {VE1 : @LTS E1} {VF1 : @LTS F1} {VE2 : @LTS E2} {VF2 : @LTS F2}
    (impl1 : ModuleImpl E1 F1) (impl2 : ModuleImpl E2 F2) :
    forall (σ01 : State VE1) (ρ01 : State VF1) (σ02 : State VE2) (ρ02 : State VF2),
    cal impl1 σ01 ρ01 ->
    cal impl2 σ02 ρ02 ->
    @cal _ _ (tens_lts VE1 VE2) (tens_lts VF1 VF2) (impl1 ⊗ impl2) (pair σ01 σ02) (pair ρ01 ρ02).
  Proof.
  Admitted.
End HCompTPSimSet.
