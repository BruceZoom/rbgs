Require Import Coq.Lists.List.

Require Import Lang.


(** Structurally finite iteration for interaction-tree programs.  Unlike
    [Lang.loop], these combinators terminate because they consume a list. *)
Module ProgIterator.
  Import Lang.

  Fixpoint foldM {E Item Acc}
      (step : Acc -> Item -> Prog E Acc)
      (items : list Item)
      (acc : Acc) : Prog E Acc :=
    match items with
    | nil => Ret acc
    | item :: items' =>
        bindProg (step acc item)
          (fun acc' => foldM step items' acc')
    end.

  Fixpoint iterM {E Item}
      (step : Item -> Prog E unit)
      (items : list Item) : Prog E unit :=
    match items with
    | nil => Ret tt
    | item :: items' =>
        bindProg (step item) (fun _ => iterM step items')
    end.

  Lemma foldM_nil {E Item Acc}
      (step : Acc -> Item -> Prog E Acc) acc :
    foldM step nil acc = Ret acc.
  Proof. reflexivity. Qed.

  Lemma foldM_cons {E Item Acc}
      (step : Acc -> Item -> Prog E Acc) item items acc :
    foldM step (item :: items) acc =
      bindProg (step acc item)
        (fun acc' => foldM step items acc').
  Proof. reflexivity. Qed.

  Lemma iterM_nil {E Item} (step : Item -> Prog E unit) :
    iterM step nil = Ret tt.
  Proof. reflexivity. Qed.

  Lemma iterM_cons {E Item}
      (step : Item -> Prog E unit) item items :
    iterM step (item :: items) =
      bindProg (step item) (fun _ => iterM step items).
  Proof. reflexivity. Qed.

End ProgIterator.
