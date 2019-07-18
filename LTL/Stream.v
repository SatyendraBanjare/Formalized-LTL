Set Implicit Arguments.

(* 

Stream used here is a set of infinite states that can be understood as a list.
Co-Inductive definitions are used to create termination proofs for the infinitely long streams.

This Section gives practical definitions of properties of Stream.

*)

Section Stream.
  Variable A : Type.

  CoInductive Stream : Type :=
  | Cons : A -> Stream -> Stream.

  Definition head (l : Stream) : A :=
    match l with
    | Cons x _ => x
    end.

  Definition tail (l : Stream) : Stream :=
    match l with
    | Cons _ l' => l'
    end.

  Definition frob (l : Stream) : Stream :=
    match l with
    | Cons x l' => Cons x l'
    end.

  Theorem frob_id :
    forall (l : Stream),
      l = frob l.
  Proof.
    intros; destruct l; auto.
  Qed.

  Fixpoint nth_tail (n : nat) (l : Stream) : Stream :=
    match n with
    | 0 => l
    | S n => nth_tail n (tail l)
    end.

End Stream.