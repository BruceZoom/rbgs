Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulation.
Require Import RGILogic.
Require Import examples.Common.AtomicLTS.
Require Import examples.Stacks.StackSpec.
Require Import examples.Exchanger.ExchangerSpec.


Module EBStackImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS TryStackSpec ExchSpec StackSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.

  Open Scope prog_scope.

  Context {A : Type}.

  Definition E : layer_interface :=
  {|
    li_sig := Sig.Plus.omap (ETryStack A) (EExch (option A));
    li_lts := tens_lts VTryStack VExch;
    li_init := (Idle nil, ExSIdle);
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := EStack A;
    li_lts := VStack;
    li_init := Idle nil
  |}.
  
  Definition push_impl (v : A) (_ : tid) : Prog (li_sig E) unit :=
    Do {
      inr (ExchSpec.exch (Some v)) >= other =>
      match other with
      | Some None => Ret (inr tt)
      | _ =>
        inl (TryStackSpec.push v) >= succ =>
        Ret (match succ with | FAIL => inl tt | _ => inr tt end)
      end
    } Loop.

  Definition pop_impl (_ : tid) : Prog (li_sig E) (option A) :=
    Do {
      inr (ExchSpec.exch None) >= other =>
      match other with
      | Some (Some v) => Ret (inr (Some v))
      | _ =>
        inl TryStackSpec.pop >= succ =>
        Ret (match succ with | FAIL => inl tt | OK v => inr v end)
      end
    } Loop.
    
  Program Definition Mebstack : layer_implementation E F := {|
    li_impl m :=
      match m with
      | push v => push_impl v
      | pop => pop_impl
      end
  |}.
  (* TODO: *)
End TreiberStackImpl.