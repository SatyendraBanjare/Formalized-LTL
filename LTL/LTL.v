Require Import Stream.
Require Import Coq.Logic.Classical Omega.


(*

This section contains the different definitions to be used for
the logic system. The understanding of these definitions can be 
inferred directly from the wikipedia page.

The used Logic Operators are And , Or , Not.

The used Modal operators are Until , Release , Eventually ,
WeakUntil , StrongRelease.

*)

Definition Stream_State (A : Type) : Type := Stream A -> Prop.

Section LTL.
  Variable A : Type.

  Inductive Atomic (At : A -> Prop) : Stream_State A :=
  | AtomicIntro : forall (a : A) (l : Stream A),
      At a -> Atomic At (Cons a l).

  Definition And (P Q : Stream_State A) : Stream_State A :=
    fun l => P l /\ Q l.

  Definition Or (P Q : Stream_State A) : Stream_State A :=
    fun l => P l \/ Q l.

  Definition Not (P : Stream_State A) : Stream_State A :=
    fun l => ~ (P l).

  Inductive Next (P : Stream_State A) : Stream_State A :=
  | NextIntro : forall (a : A) (l : Stream A),
      P l -> Next P (Cons a l).

  Inductive Until (P Q : Stream_State A) : Stream_State A :=
  | UntilHere : forall (l : Stream A),
      Q l -> Until P Q l
  | UntilLater : forall (a : A) (l : Stream A),
      P (Cons a l) -> Until P Q l -> Until P Q (Cons a l).

  CoInductive Release (P Q : Stream_State A) : Stream_State A :=
  | ReleaseHere : forall (l : Stream A),
      P l -> Q l -> Release P Q l
  | ReleaseLater : forall (a : A) (l : Stream A),
      Q (Cons a l) -> Release P Q l -> Release P Q (Cons a l).

  Inductive Eventually (P : Stream_State A) : Stream_State A :=
  | EventuallyHere : forall (a : A) (l : Stream A),
      P (Cons a l) -> Eventually P (Cons a l)
  | EventuallyLater : forall (a : A) (l : Stream A),
      Eventually P l -> Eventually P (Cons a l).

  CoInductive Always (P : Stream_State A) : Stream_State A :=
  | AlwaysIntro : forall (a : A) (l : Stream A),
      P (Cons a l) -> Always P l -> Always P (Cons a l).

  CoInductive WeakUntil (P Q: Stream_State A) : Stream_State A :=
  | WeakUntilHere : forall (l : Stream A),
    Q l -> WeakUntil P Q l
  | WeakUntilLater : forall (a : A) (l : Stream A),
    Q (Cons a l) -> WeakUntil P Q l -> WeakUntil P Q (Cons a l).

  CoInductive StrongRelease (P Q: Stream_State A) : Stream_State A :=
  | StrongReleaseHere : forall (l : Stream A),
    P l -> Q l -> StrongRelease P Q l
  | StrongReleaseLater : forall (a : A) (l : Stream A),
    P (Cons a l) -> StrongRelease P Q l -> StrongRelease P Q (Cons a l).

End LTL.