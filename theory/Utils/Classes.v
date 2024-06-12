(*** CLASSES ***)

(* I'm rolling my own version of lots of datatypes and using typeclasses
 * pervasively. Here are the typeclasses that support the hand-rolled datatype
 * definitions.
 *)
Class Ord (A : Type) := { ord_dec : A -> A -> comparison }.
#[export] Instance NatOrd : Ord nat := { ord_dec := Nat.compare }.

Class Monoid (A : Type) :=
  { null : A
  ; append : A -> A -> A
  }.

Module MonoidNotation.
  Notation "x ++ y " := (append x y) (at level 60, right associativity).
End MonoidNotation.
Import MonoidNotation.

Class Functor (T : Type -> Type) :=
  { map : forall {A B : Type}, (A -> B) -> T A -> T B
  }.

Class Monad (M : Type -> Type) :=
  { mreturn : forall {A : Type}, A -> M A
  ; mbind   : forall {A B : Type}, M A -> (A -> M B) -> M B
  }.

Module MonadNotation.
  Notation "x <- c1 ;; c2" := (mbind c1 (fun x => c2)) 
    (at level 100, c1 at next level, right associativity).

  Notation "e1 ;; e2" := (_ <- e1 ;; e2)
    (at level 100, right associativity).

  Infix ">>=" := mbind (at level 50, left associativity).
End MonadNotation.
Import MonadNotation.

Definition StateT (S : Type) (M : Type -> Type) (X : Type) : Type :=
  S -> M (X * S)%type.

Definition StateT_ret {S} {M} `{Monad M} {X} :
  X -> StateT S M X :=
  fun x s => mreturn (x, s).

Definition StateT_bind {S} {M} `{Monad M} {X Y} :
  StateT S M X ->
  (X -> StateT S M Y) ->
  StateT S M Y :=
  fun mx f s =>
    mbind (mx s) (fun '(x, s') => f x s').

Global Instance StateT_Monad {M} {S} `{Monad M} : Monad (StateT S M) := {|
  mreturn A := StateT_ret;
  mbind X Y := StateT_bind
  |}.

Definition get {S M} `{Monad M}: StateT S M S :=
  fun s => mreturn(s,s). 

Definition put {S M} `{Monad M} (st : S) :
  StateT S M unit := fun s => mreturn(tt, st).

Definition lift {S M} `{Monad M} {A} (m : M A) : StateT S M A :=
    fun st =>
    a <- m ;; mreturn (a, st).

(* user-defined well-formedness criteria for a datatype, e.g., that a dictionary
 * represented by an association-list has sorted and non-duplicate keys
 *)
Class WF (A : Type) := { wf : A -> Type }.

(* MISSING: correctness criteria, e.g., that `Ord` is an actual total order, etc.
 *)



