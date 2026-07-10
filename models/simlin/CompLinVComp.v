Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.
Require Import Lia.
Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.Program.Equality.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import CompLin.

(** Vertical Compositionality of Compositional Linearizability (Lemma 4.3,
    §4.3): [CompLin] (Definition 4.1) composes vertically, when an
    implementation is stacked on top of another one.

    The composition operator on [ModuleImpl]s itself ([implVComp]/[▶]) is
    defined here fresh, independent of the [TPSimulationSet]/[AbstractConfig]
    machinery of Definition 5.2, since this file only needs it to state
    compositionality directly for the trace semantics of [CompLin.v].

    Horizontal compositionality (Lemma 4.2) is in [CompLinHComp.v]. *)
Module CompLinVComp.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.
  Import CompLin.CompLin.

  (** * Vertical composition of [ModuleImpl]s.

      [implEF ▶ implFG] stacks [implEF : E -> F] below [implFG : F -> G]:
      every F-operation [implFG] invokes is substituted, per-thread, by its
      implementation in [implEF]. *)
  CoFixpoint substProg
      {E F} (t : tid) (impl : ModuleImpl E F)
      {R} (p : Prog F R) : Prog E R :=
    match p with
    | Vis m k => Tau (bindSubstProg t impl (impl m t) k)
    | Ret r => Ret r
    | Tau p => Tau (substProg t impl p)
    end

  with bindSubstProg
      (t : tid) {E F} (impl : ModuleImpl E F)
      {R R'} (p : Prog E R) (k : R -> Prog F R') : Prog E R' :=
    match p with
    | Vis m' k' => Vis m' (fun r => bindSubstProg t impl (k' r) k)
    | Ret r => Tau (substProg t impl (k r))
    | Tau p => Tau (bindSubstProg t impl p k)
    end.

  Definition implVComp {E F G}
      (implEF : ModuleImpl E F) (implFG : ModuleImpl F G) : ModuleImpl E G :=
    fun g t => substProg t implEF (implFG g t).

  Notation "M ▶ N" := (implVComp M N) (at level 80, right associativity).

  (** Lemma 4.3 (Vertical Compositionality of Compositional
      Linearizability): if [M1 : VE { VF] and [M2 : VF { VG], then their
      vertical composition [M1 ▶ M2 : VE { VG]. *)
  Module VComp.
    Lemma CompLin_vcomp
        {E F G : Op.t}
        {VE : @LTS E} {VF : @LTS F} {VG : @LTS G}
        (M1 : ModuleImpl E F) (M2 : ModuleImpl F G)
        (sigma0 : State VE) (rho0 : State VF) (tau0 : State VG) :
      CompLin M1 sigma0 rho0 ->
      CompLin M2 rho0 tau0 ->
      CompLin (M1 ▶ M2) sigma0 tau0.
    Proof.
    Admitted.
  End VComp.

End CompLinVComp.
