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

(* user-defined well-formedness criteria for a datatype, e.g., that a dictionary
 * represented by an association-list has sorted and non-duplicate keys
 *)
Class WF (A : Type) := { wf : A -> Type }.

(* MISSING: correctness criteria, e.g., that `Ord` is an actual total order, etc.
 *)

Class PredLift M `{Monad M} := {
  plift {X} : (X -> Prop) -> M X -> Prop;
  plift_ret {X} : forall x (P : X -> Prop), P x -> plift P (mreturn x);
  plift_bind {X Y} : forall (P : X -> Prop) (Q : Y -> Prop)
    (mx : M X) (f : X -> M Y), plift P mx ->
    (forall x, P x -> plift Q (f x)) ->
    plift Q (mbind mx f)
  }.

Definition has_weakening M `{PredLift M} : Prop :=
  forall X (P Q : X -> Prop),
    (forall x, P x -> Q x) ->
  forall m, plift P m -> plift Q m.
