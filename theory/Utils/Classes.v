Require Import Arith Lia.
Require Import POram.Utils.Vec.

Class Ord (A : Type) := {
  ord_dec : A -> A -> comparison;
  ord_refl : forall x, ord_dec x x = Eq;
  ord_eq : forall x y, ord_dec x y = Eq -> x = y;
  ord_lt_trans : forall x y z,
    ord_dec x y = Lt ->
    ord_dec y z = Lt ->
    ord_dec x z = Lt;
  }.

Lemma compare_lt_trans : forall x y z,
  x ?= y = Lt ->
  y ?= z = Lt ->
  x ?= z = Lt.
Proof.
  intros.
  rewrite Nat.compare_lt_iff in *.
  lia.
Qed.

Global Instance NatOrd : Ord nat := {
  ord_dec := Nat.compare;
  ord_refl := Nat.compare_refl;
  ord_eq := Nat.compare_eq;
  ord_lt_trans := compare_lt_trans
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

Definition monad_map {M} `{Monad M} {X Y} (f : X -> Y) (m : M X) : M Y :=
  x <- m;;
  mreturn (f x).

Lemma plift_map : forall {M} `{PredLift M} {X Y} (f : X -> Y) (m : M X) (P : Y -> Prop), 
    plift (fun x => P (f x)) m -> 
    plift P (monad_map f m).
Proof.
  intros.
  eapply plift_bind.
  - exact H1.
  - intros. 
    eapply plift_ret.
    apply H2; auto.
Qed.

Fixpoint constm_vec {A : Type} {M : Type -> Type} `{Monad M} (xM : M A) (n : nat) : M (vec n A) :=
  match n with
  | O => mreturn tt
  | S n' =>
      x <- xM ;;
      xs <- constm_vec xM n' ;;
      mreturn (x, xs)
  end.

(* TODO: refactor *)
Class PredLift2 M `{Monad M} := {
  plift2 {X Y} : (X -> Y -> Prop) -> M X -> M Y -> Prop;
  plift2_bind {X Y X' Y'} : forall (P : X -> Y -> Prop) (Q : X' -> Y' -> Prop)
    (m1 : M X) (m2 : M Y) (f1 : X -> M X') (f2 : Y -> M Y'),
    plift2 P m1 m2 ->
    (forall x y, P x y -> plift2 Q (f1 x) (f2 y)) ->
    plift2 Q (mbind m1 f1) (mbind m2 f2)
  }.
