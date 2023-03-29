Require Import  ExtLib.Data.Monads.StateMonad ExtLib.Structures.Monads.
Require Import ZArith.
Import MonadLetNotation.
Open Scope monad_scope.
Require Import List.
Import ListNotations.

Definition counter : Type := nat.

Definition incr_counter : state nat unit :=
    let* curr := get in
    put (S curr).

Definition stateful_bubble : Z -> state nat Z :=
  fun x =>
    let* _ := incr_counter in
    ret (2 * x)%Z.

Fixpoint fold_left_m {M} `{Monad M} {A B} (f : B -> A -> M B)
         (b0 : B) (xs : list A) : M B :=
  match xs with
  | [] => ret b0
  | x :: ys => bind (f b0 x) (fun b' => fold_left_m f b' ys)
  end.

Definition fold_left_state {S A B} (f : B -> A -> state S B)
           (b0 : B) (xs : list A) : state S B :=
  fold_left_m f b0 xs.

Definition stateful_add : Z -> Z -> state nat Z :=
  fun x y =>
    let* _ := incr_counter in
    ret (x + y)%Z.

Lemma counter_simple: forall (init_counter: nat) (int_l : list Z),
    let res_counter :=
      (let st_add :=
         (let* curr_counter := get in
          fold_left_state stateful_add (0%Z) int_l) in
       snd (runState st_add init_counter)
      ) in 
    res_counter = init_counter + length(int_l).
Proof.
  intros.
  simpl in *.
  
