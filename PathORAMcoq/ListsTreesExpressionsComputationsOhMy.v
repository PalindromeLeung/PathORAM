(***************)
(* EXPRESSIONS *)
(***************)

(* This is an expression tree with one binary operation `+` and
 * embedded literals in ℕ
 *)
Inductive expression_tree : Set :=
  | Plus_ET : expression_tree -> expression_tree -> expression_tree
  | Lit_ET : nat -> expression_tree.

(* This is an interpretation of the expression language, giving every
 * expression a denotation into ℕ
 *)
Fixpoint interp_expression_tree (e : expression_tree) : nat :=
  match e with
  | Plus_ET e1 e2 => interp_expression_tree e1 + interp_expression_tree e2
  | Lit_ET n => n
  end.

(* An equivalent way to represent these expression trees is by
 * flattening them into lists. This is ok to do because plus is
 * associative, and the zero literal is a unit for plus
 *)
Inductive expression_list : Set :=
  | Plus_EL : nat -> expression_list -> expression_list
  | Zero_EL : expression_list.

(* This "list-y" version of things also has an interpretation *)
Fixpoint interp_expression_list (e : expression_list) : nat :=
  match e with
  | Plus_EL n e' => n + interp_expression_list e'
  | Zero_EL => 0
  end.

(* A helper we need for the next thing... *)
Fixpoint append_expression_list (e1 : expression_list) (e2 : expression_list) : expression_list :=
  match e1 with
  | Plus_EL n e1' => Plus_EL n (append_expression_list e1' e2)
  | Zero_EL => e2
  end.

(* This is a constructive definition to support the claim that
 * expression trees can be compiled into expression lists. In fact, we
 * could prove a theorem than the denotation of `e` and `compile(e)`
 * are equal, and you will notice that in the proof you have to use
 * associativity and unit laws for plus.
 *)
Fixpoint compile_expression_tree (e : expression_tree) : expression_list :=
  match e with
  | Plus_ET e1 e2 => append_expression_list (compile_expression_tree e1) (compile_expression_tree e2)
  | Lit_ET n => Plus_EL n Zero_EL
  end.

Require Import Coq.Arith.PeanoNat.


Axiom interp_list: forall l1 l2, interp_expression_list l1 + interp_expression_list l2 = interp_expression_list (append_expression_list l1 l2).
Axiom there_must_be_such_a_theorem: forall n m1 m2, m1 = m2 -> n + m1 = n + m2.
  
Theorem compiletree_correct : forall (e : expression_tree),
    interp_expression_tree e =
      interp_expression_list (compile_expression_tree e).
Proof. 
  intros.
  induction e. 
  - destruct e1, e2; simpl in *.
    + rewrite IHe1. rewrite IHe2. rewrite interp_list. auto.
    + rewrite <- interp_list. simpl. rewrite <- IHe2. auto.
    + rewrite IHe2. eapply there_must_be_such_a_theorem. auto.
    +  rewrite <- IHe2. reflexivity.
  - induction n.
    + simpl in *. reflexivity.
    + simpl. rewrite Nat.add_0_r. reflexivity.
Qed.

(****************)
(* COMPUTATIONS *)
(****************)

(* This is a computation language intended to be interpreted into the
 * state monad. It has `get` and `put` operations, a way to combine
 * computations via `bind`, and a way to conclude with a literal value
 * via `return`. A neat thing about monads is that all of our
 * intuitions about `+` and expression languages from above can be
 * carried over. `bind` is actually associative (like `+`), `return`
 * is a unit for `bind` (just like `0` was for `+`). Most
 * importantly, we can compile this tree-structured thing into an
 * equivalent list-structured thing, and the ability to do so
 * crucially relies on associativity and unit laws.
 *)
Inductive computation_tree : Set :=
  | Bind_CT : computation_tree -> (nat -> computation_tree) -> computation_tree
  | Return_CT : nat -> computation_tree
  | Get_CT : computation_tree
  | Put_CT : nat -> computation_tree.

(* This is an interpretation of computation trees in terms of
 * functions that manipulate a single cell of state
 *)
(*                                                                output state              *)
(*                                                                       ↓↓↓                *)
Fixpoint interp_computation_tree (e : computation_tree) (state : nat) : (nat * nat) :=
(*                                                                             ↑↑↑          *)
(*                                                                             return value *)

  match e with
  | Bind_CT e' f => 
    match interp_computation_tree e' state with
    | (state', n) => interp_computation_tree (f n) state'
    end
  | Return_CT n => (state, n)
  | Get_CT => (state, state)
  | Put_CT n => (n, n)
  end.

(* This is our "first try" at list-ifying the computation tree. This
 * is just like a list that has two different types of "cons cells":
 * one for `get` and one for `put`. We can fold these together into a
 * single "cons cell" using a helper definition, so let's do that.
 *)
Inductive computation_list_first_try : Set :=
  | Get_CLFT : (nat -> computation_list_first_try) -> computation_list_first_try
  | Put_CLFT : nat -> (nat -> computation_list_first_try) -> computation_list_first_try
  | Done_CLFT : computation_list_first_try.

(* This is the inductive type for "commands" in our language *)
Inductive computation_op : Set :=
  | Get_OP : computation_op
  | Put_OP : nat -> computation_op.

(* This is the inductive type for computations in our language. It's
 * just a list, but where the cons cells allow for the tail of the
 * list to depend on a "return value". The tail of the list also holds
 * a final value.
 *)
Inductive computation_list : Set :=
  | Op_CL : computation_op -> (nat -> computation_list) -> computation_list
  | Done_CL : nat -> computation_list.

(* This is an interpretation of these computation lists in terms of
 * the same state monad semantics
 *)
(*                                                                       state              *)
(*                                                                       ↓↓↓                *)
Fixpoint interp_computation_list (e : computation_list) (state : nat) : (nat * nat) :=
(*                                                                             ↑↑↑          *)
(*                                                                             return value *)
  match e with
  | Op_CL o f => 
      match o with
      | Get_OP => interp_computation_list (f state) state
      | Put_OP n => interp_computation_list (f n) n
      end
  | Done_CL n => (state, n)
  end.

(* And finally, we have the compiler from computation trees to
 * computation lists.
 *)

(* Magically, we need an append operation for our computation lists
 * before defining our compiler for computation trees, just like we
 * needed an append operation on expression lists before defining our
 * compiler for expression trees.
 *)
Fixpoint append_computation_list (e : computation_list) (f : nat -> computation_list) : computation_list :=
  match e with
  | Op_CL o f1 => Op_CL o (fun x => append_computation_list (f1 x) f)
  | Done_CL n => f n
  end.

(* And now we have the compiler from computation trees to computation
 * lists. We should be able to prove that the denotations of
 * computation trees and computation lists (via compilation) are
 * equal, and you'll notice that doing so relies on associativity and
 * unit laws for the denotation space (the state monad).
 *)
Fixpoint compile_computation_tree (e : computation_tree) : computation_list :=
  match e with
  | Bind_CT e f => append_computation_list (compile_computation_tree e) (fun n => compile_computation_tree (f n))
  | Return_CT n => Done_CL n
  | Get_CT => Op_CL Get_OP (fun n => Done_CL n)
  | Put_CT n => Op_CL (Put_OP n) (fun n' => Done_CL n')
  end.


Axiom interp_comp_list: forall e1 (c : nat -> computation_tree),
    interp_computation_list
      (append_computation_list
         (compile_computation_tree e1)
         (fun n:nat => compile_computation_tree (c n))
      ) =
      (fun state : nat =>
         let (state', n) := interp_computation_tree e1 state in
         interp_computation_tree (c n) state').

Theorem comp_tree_correct: forall e , interp_computation_list(compile_computation_tree e) = interp_computation_tree e.
Proof.
  intros. 
  induction e.
  - simpl. rewrite interp_comp_list. auto. 
  - induction n; simpl; auto.
  - simpl. auto.
  - induction n; simpl; auto.
Qed.
