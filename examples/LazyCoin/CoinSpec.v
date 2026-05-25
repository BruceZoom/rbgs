Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.

(* IMPORTANT *)
(*    
    It turns out Coq is more stupid than this. Doing the following cannot solve all similar problems.

    When a single thread event could have multiple transitions,
    must defined transitions in the following way:
    Variant Step : ... :=
    | rule_name params e:
        e = {| te_tid := t; te_ev := ev |} ->
        Step e s1 s2
    ...
    The event should not appear in the conclusion,
    otherwise inversion on the relation will not work.
    Doing so also make sure it will work with the current automation.
*)

Require Import examples.Common.AtomicLTS.

Module CoinSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  Variant ECoin_op :=
  | flip
  | read.

  Definition ECoin_ar (m : ECoin_op) : Type :=
    match m with
    | flip => unit
    | read => bool
    end.
  
  Canonical Structure ECoin :=
  {|
    Sig.op := ECoin_op;
    Sig.ar := ECoin_ar
  |}.

  Variant StepCoin : @ThreadEvent ECoin -> bool -> bool -> Prop :=
  | step_flip_inv e b t:
      e = {| te_tid := t; te_ev := InvEv flip |} ->
      StepCoin e b b
  | step_flip_res e t b b':
      e = {| te_tid := t; te_ev := ResEv flip tt |} ->
      StepCoin e b b'
  | step_read_inv b t:
      StepCoin {| te_tid := t; te_ev := InvEv read |} b b
  | step_read_res t b:
      StepCoin {| te_tid := t; te_ev := ResEv read b |} b b
  (* | step_read_inv e b t:
      e = {| te_tid := t; te_ev := InvEv read |} ->
      StepCoin e b b
  | step_read_res e t b:
      e = {| te_tid := t; te_ev := ResEv read b |} ->
      StepCoin e b b *)
  .

  Variant ErrorCoin : @ThreadEvent ECoin -> AState -> Prop :=
  | error_flip_racy t t' (b:bool) e:
      t <> t' ->
      e = {| te_tid := t; te_ev := InvEv flip |} ->
      ErrorCoin e (Pending b t' flip).

  Definition VCoin : @LTS ECoin := VAE StepCoin ErrorCoin.

End CoinSpec.


