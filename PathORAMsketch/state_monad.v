Require Import  ExtLib.Data.Monads.StateMonad ExtLib.Structures.Monads.
Require Import ZArith.

(* Class Monad (M : Type -> Type) := { *)
(*   pure {X} : X -> M X; *)
(*   bind {X Y} : M X -> (X -> M Y) -> M Y *)
(*   }. *)

(* Definition State S X := S -> S * X. *)

(* a function that takes an input and returns twice that input,
   while also incrementing a global counter *)

Definition counter : Type := nat.

(* Definition stateful_double : Z -> State counter Z := (* Z -> M Z *) *)
(*   fun input_val old_counter => (S old_counter, 2 * input_val)%Z. *)
(* (* Import MonadNotation. *)
Open Scope monad_scope.
Definition incr_counter : state nat unit :=
  curr <- get;;
  _ <- put (S curr);;
  ret tt.

Definition stateful_double' : Z -> state nat Z :=
  fun x =>
    _ <- incr_counter;;
    ret (2 * x)%Z.
 *)

Import MonadLetNotation.
Open Scope monad_scope.

Definition incr_counter : state nat unit :=
    let* curr := get in
    put (S curr).

Definition stateful_bubble : Z -> state nat Z :=
  fun x =>
    let* _ := incr_counter in
    ret (2 * x)%Z.

(* adds the current counter val to an input val *)
(* Definition add_count : nat -> State counter nat := *)
(*   fun input_val old_counter => (old_counter, input_val + old_counter). *)

(* Definition state_pure {S} {X} : X -> State S X. *)
(* Proof. *)
(*   unfold State. *)
(*   intros x s. *)
(*   exact (s, x). *)
(* Defined. *)

(* Definition state_bind {S} {X Y} : State S X -> *)
(*   (X -> State S Y) -> State S Y. *)
(* Proof. *)
(*   unfold State. *)
(*   intros mx f. *)
(*   intro s0. *)
(*   destruct (mx s0) as [s1 x]. *)
(*   exact (f x s1). *)
(* Defined. *)

(* Compute state_bind (state_pure 7%Z) (stateful_double) 3. *)
(* Compute state_bind (state_pure 5%Z) (stateful_double) 0. *)


(* #[global] *)
(* Instance State_Monad (S : Type) : Monad (State S) := { *)
(*   pure := @state_pure S; *)
(*   bind := @state_bind S *)
(*   }. *)

Require Import List.
Import ListNotations.
Print Monad.
Fixpoint fold_left_m {M} `{Monad M} {A B} (f : B -> A -> M B)
         (b0 : B) (xs : list A) : M B :=
  match xs with
  | [] => ret b0
  | x :: ys => bind (f b0 x) (fun b' => fold_left_m f b' ys)
  end.
Print bind.

Definition fold_left_state {S A B} (f : B -> A -> state S B)
           (b0 : B) (xs : list A) : state S B :=
  
  fold_left_m f b0 xs.

Print fold_left_state.

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







Class Point (X : Type) :=
  { point : X }.

Definition pointy {X Y} `{Point X} (f : X -> Y) : Y :=
  f point.

#[global]
 Instance Point_nat : Point nat :=
  { point := 7 }.

Compute pointy S.
