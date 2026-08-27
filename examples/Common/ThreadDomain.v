Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.

Require Import LinCCAL.


Module ThreadDomain.
  Import LinCCALBase.

  (** A finite, non-empty thread domain with a deterministic traversal
      order.  The distinguished first element avoids introducing an
      artificial default thread when constructing non-empty families. *)
  Record t : Type := {
    first_thread : tid;
    other_threads : list tid;
    threads_nodup : NoDup (first_thread :: other_threads);
  }.

  Definition threads (D : t) : list tid :=
    first_thread D :: other_threads D.

  Definition contains (D : t) (thread : tid) : Prop :=
    In thread (threads D).

  Definition contains_dec (D : t) (thread : tid) :
      {contains D thread} + {~ contains D thread} :=
    In_dec Pos.eq_dec thread (threads D).

  Lemma contains_nodup (D : t) : NoDup (threads D).
  Proof. exact (threads_nodup D). Qed.

End ThreadDomain.
