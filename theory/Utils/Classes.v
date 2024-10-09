Require Import Arith Lia.

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
    plift Q (mbind mx f);
  plift_weaken {X} (P Q : X -> Prop) : (forall x, P x -> Q x) ->
    forall m, plift P m -> plift Q m;
  plift_true {X} : forall (m : M X), plift (fun _ => True) m;
  plift_split {X} (P Q : X -> Prop) : forall m,
    plift P m -> plift Q m -> plift (fun x => P x /\ Q x) m;
  plift_comm {X Y} (P : X -> Y -> Prop) (m1 : M X) (m2 : M Y) :
    plift (fun y => plift (fun x => P x y) m1) m2 ->
    plift (fun x => plift (P x) m2) m1
  }.

Lemma plift_triv {M} `{PredLift M} {X} (P : X -> Prop) (m : M X) :
  (forall x, P x) -> plift P m.
Proof.
  intros.
  apply plift_weaken with (P := fun _ => True).
  - intros; auto.
  - apply plift_true.
Qed.

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

Fixpoint constm_list {A : Type} {M : Type -> Type} `{Monad M} (xM : M A) (n : nat) : M (list A) :=
  match n with
  | O => mreturn (@nil A)
  | S n' =>
      x <- xM ;;
      xs <- constm_list xM n' ;;
      mreturn (cons x xs)
  end.

Lemma constm_list_length {A} {M} `{PredLift M} (m : M A) n :
  plift (fun _ => True) m ->
  plift (fun p => length p = n) (constm_list m n).
Proof.
  intro Hm.
  induction n.
  - apply plift_ret; auto.
  - eapply plift_bind; eauto.
    intros x _.
    eapply plift_bind; eauto.
    simpl.
    intros l Hl.
    apply plift_ret.
    simpl; auto.
Qed.

Definition plift2 {M} `{PredLift M} {X Y} (P : X -> Y -> Prop) :
  M X -> M Y -> Prop :=
  fun mx my =>
    plift (fun x => plift (P x) my) mx.

Lemma plift2_bind_l {M} `{PredLift M} {X Y Z}
  (P : X -> Z -> Prop) (Q : Y -> Z -> Prop)
  (m : M X) (f : X -> M Y) (n : M Z) :
  plift2 P m n ->
  (forall x, plift (P x) n -> plift2 Q (f x) n) ->
  plift2 Q (mbind m f) n.
Proof.
  apply plift_bind.
Qed.

Lemma plift2_bind_r {M} `{PredLift M} {X Y Z}
  (P : Z -> X -> Prop) (Q : Z -> Y -> Prop)
  (m : M X) (f : X -> M Y) (n : M Z) :
  plift2 P n m ->
  (forall x, plift (fun z => P z x) n -> plift2 Q n (f x)) ->
  plift2 Q n (mbind m f).
Proof.
  intros.
  apply plift_comm.
  eapply plift2_bind_l.
  - apply plift_comm in H1.
    exact H1.
  - intros.
    specialize (H2 x).
    apply plift_comm in H2; auto.
Qed.

Lemma plift2_bind {M} `{PredLift M} {X Y X' Y'} : forall (P : X -> Y -> Prop)
  (Q : X' -> Y' -> Prop) (m1 : M X) (m2 : M Y) (f1 : X -> M X') (f2 : Y -> M Y'),
  plift2 P m1 m2 ->
  (forall x y, P x y -> plift2 Q (f1 x) (f2 y)) ->
  plift2 Q (mbind m1 f1) (mbind m2 f2).
Proof.
  intros.
  apply plift2_bind_l with (P := fun x y' => plift (fun x' => Q x' y') (f1 x)).
  - apply plift2_bind_r with (P := P).
    + auto.
    + intros.
      eapply plift_weaken; [|exact H3].
      simpl; intros.
      apply H2 in H4.
      unfold plift2 in H4.
      apply plift_comm; auto.
  - intros.
    apply plift_comm.
    exact H3.
Qed.

Lemma plift2_ret_l {M} `{PredLift M} {X Y}
  (P : X -> Y -> Prop) (x : X) (m : M Y) :
  plift (P x) m ->
  plift2 P (mreturn x) m.
Proof.
  intros.
  eapply plift_ret.
  exact H1.
Qed.

Lemma plift2_ret_r {M} `{PredLift M} {X Y}
  (P : Y -> X -> Prop) (x : X) (m : M Y) :
  plift (fun y => P y x) m ->
  plift2 P m (mreturn x).
Proof.
  intros.
  apply plift_comm.
  apply plift2_ret_l.
  auto.
Qed.

