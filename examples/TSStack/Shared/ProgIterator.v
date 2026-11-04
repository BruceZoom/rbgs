Require Import Coq.Lists.List.

Require Import Lang.


(** Structurally finite iteration without an accumulator.  The accumulating
    [foldM] combinator and its [ForEach] notation live in [Lang], where the
    production program logic can provide [provable_foreach]. *)
Module ProgIterator.
  Import Lang.

  Fixpoint iterM {E Item}
      (step : Item -> Prog E unit)
      (items : list Item) : Prog E unit :=
    match items with
    | nil => Ret tt
    | item :: items' =>
        bindProg (step item) (fun _ => iterM step items')
    end.

  Lemma iterM_nil {E Item} (step : Item -> Prog E unit) :
    iterM step nil = Ret tt.
  Proof. reflexivity. Qed.

  Lemma iterM_cons {E Item}
      (step : Item -> Prog E unit) item items :
    iterM step (item :: items) =
      bindProg (step item) (fun _ => iterM step items).
  Proof. reflexivity. Qed.

End ProgIterator.
