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

Module TicketSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  Open Scope list.

  Variant ETicket_op :=
  | acq_ticket
  | cmp_ticket (t : nat)
  | rel_ticket.

  Definition ETicket_ar (m : ETicket_op) : Type :=
    match m with
    | acq_ticket => nat
    | cmp_ticket t => bool
    | rel_ticket => unit
    end.
  
  Canonical Structure ETicket :=
  {|
    Sig.op := ETicket_op;
    Sig.ar := ETicket_ar
  |}.

  Record TicketState : Type := TKS {
    ts_hd : nat;
    ts_q : list tid;
    ts_tl : nat
  }.

  Variant StepTicket : @ThreadEvent ETicket -> TicketState -> TicketState -> Prop :=
  | step_acq_inv e tks t :
      e = {| te_tid := t; te_ev := InvEv acq_ticket |} ->
      StepTicket e tks tks
  | step_acq_res e hd q tl t tks1 tks2 :
      e = {| te_tid := t; te_ev := ResEv acq_ticket tl |} ->
      tks1 = TKS hd q tl ->
      tks2 = TKS hd (q ++ t :: nil) (S tl) ->
      StepTicket e tks1 tks2

  | step_cmp_inv e tks t tk :
      e = {| te_tid := t; te_ev := InvEv (cmp_ticket tk) |} ->
      StepTicket e tks tks
  | step_cmp_res e t tk tks:
      e = {| te_tid := t; te_ev := ResEv (cmp_ticket tk) (tk =? (ts_hd tks))%bool |} ->
      StepTicket e tks tks
  
  | step_rel_inv e tks t :
      e = {| te_tid := t; te_ev := InvEv rel_ticket |} ->
      StepTicket e tks tks
  | step_rel_res e hd q tl t tks1 tks2:
      e = {| te_tid := t; te_ev := ResEv rel_ticket tt |} ->
      tks1 = TKS hd (t :: q) tl ->
      tks2 = TKS (S hd) q tl ->
      StepTicket e tks1 tks2
  .

  Variant ErrorTicket : @ThreadEvent ETicket -> TicketState -> Prop :=
  | error_jump_queue e hd q tl t t' tks:
      t <> t' ->
      e = {| te_tid := t; te_ev := InvEv rel_ticket |} ->
      tks = TKS hd (t' :: q) tl ->
      ErrorTicket e tks
  | error_empty_queue e hd tl t tks:
      e = {| te_tid := t; te_ev := InvEv rel_ticket |} ->
      tks = TKS hd nil tl ->
      ErrorTicket e tks.
  
  Definition VTicket : @LTS ETicket := VAE StepTicket (AError ErrorTicket).
End TicketSpec.

