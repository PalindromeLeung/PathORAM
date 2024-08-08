Require Coq.Bool.Bool.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.QArith.QArith.
Require Import Coq.Classes.EquivDec.
Require Import Lia.
Require Import POram.Utils.Classes.
Import MonadNotation.
Require Import POram.Utils.Lists.
Require Import POram.Utils.Vectors.
Require Import POram.Utils.Tree.
Require Import POram.Utils.Rationals.
Require Import POram.Utils.Distributions.
Require Import POram.System.PathORAMDef.
Require Import POram.System.PathORAMFunCorrect.
(* assume that the tree has one node and 2 leaves, then the path is 1 bit long *)
(**
                 / [ ID | PAYLOAD ] \
                 | [ ID | PAYLOAD ] |
                 \ [ ID | PAYLOAD ] /
                  /               \
                 /                 \
                /                   \
   / [ ID | PAYLOAD ] \   / [ ID | PAYLOAD ] \  ←
   | [ ID | PAYLOAD ] |   | [ ID | PAYLOAD ] |  ← A BUCKET = N BLOCKS (example: N=3)
   \ [ ID | PAYLOAD ] /   \ [ ID | PAYLOAD ] /  ←
                            ↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑
 **)

(*
  Z = 3
  N = 3
  addr space = Z * N = 3 * 3
  path_len = 1 bit 
  |acc_list| = Len = 5
  Len_AP = 1 * 5 = 5 bits
 *)

(*TODO : define 2 random variables from a coin_flip, show that the probability of the conjuction of them is true is 1/4 *)

(*
  p <- coin_flip
  q <- coin_flip
  Pr[ p /\ q ] = 1/4
 *)

(* Pr(A /\ B) = Pr(A) * Pr(B) *)

Definition coin_flip_two :=
  p <- coin_flip ;;
  q <- coin_flip ;;
  mreturn (p, q).

Definition eval_dist {X} (mu : dist X) (f : X -> bool) : Q :=
  sum_dist (filter_dist (dist_pmf mu) f).

Goal eval_dist coin_flip_two (fun '(p,q) => andb p q) = 1 / 4.
  reflexivity.
Qed. 

(* mapM :: Monad m => (a -> m b) -> t a -> m (t b) *)

Definition mapM {A B M} `{Monad M} (f : A -> M B) (l : list (M A)) 
    :list (M B) := 
  (List.map
     (fun s => mbind s f) l).


Definition distr_eqv {X} d d' : Prop :=
  forall (E : X -> bool), 
  Qeq (eval_dist d E) (eval_dist d' E).

(* sequence :: (Traversable t, Monad m) => t (m a) -> m (t a) *)
Fixpoint sequence {A M} `{Monad M} (l : list (M A)) : M (list A) :=
  match l with
  | [] => mreturn []
  | h :: t =>
      x <- h ;;
      xs <- sequence t ;;
      mreturn (x :: xs)
  end.

Definition monad_map {A B M} `{Monad M} (f : A -> B) (a : M A) : M B := 
  x <- a ;;
  mreturn (f x).

(* Definition acc_list_1 {C : Config} (arg_list : list (block_id * operation)) (s : state) : *)
(*   list (dist path). *)
(*   pose (List.map (fun '(bid, op) => access bid op) arg_list). *)
(*   refine (List.map _ l). *)
(*   intros prm. *)
(*   specialize (prm s). *)
(*   pose (monad_map fst prm). *)
(*   pose (monad_map fst d). *)
(*   exact d0. *)
(* Defined. *)

Definition acc_dist_list {C : Config}
  (arg_list : list (block_id * operation)) (s : state) : dist (list path) :=
  let l := List.map (fun '(bid, op) => access bid op) arg_list in
  let p := sequence l in
  let p_l := monad_map (List.map fst) p in
  monad_map fst (p_l s).


Definition acc_list_dist {C : Config}
  (arg_list : list (block_id * operation)) (s : state)  : list (dist path) := 
  let l := List.map (fun '(bid, op) => access bid op) arg_list in
  let d_tuple := List.map (fun prm => monad_map fst (monad_map fst (prm s))) l in
  d_tuple.

Theorem acc_list_len_preservation :
  forall {C : Config} (arg_list : list (block_id * operation)) (s : state),
    List.length arg_list =
       List.length (acc_list_dist arg_list s).
Proof.
  intros.
  induction arg_list; simpl; auto.
Qed. 

Definition path_pred {C : Config} (l : list (dist path)) : Prop :=
  Forall (plift (fun p => (List.length p = LOP))%nat) l. 

Lemma plift_monad_map : forall {X Y} (f : X -> Y) (d : dist X) (P : Y -> Prop), 
    plift (fun x => P (f x)) d -> 
    plift P (monad_map f d).
Admitted. 

Theorem acc_list_len_inner_preservation :
  forall {C : Config} (arg_list : list (block_id * operation)) (s : state),
    path_pred (acc_list_dist arg_list s).
Proof.
  intros.
  unfold path_pred, acc_list_dist.
  do 2 apply Forall_map.
  rewrite Forall_forall.
  intros [id op].
  intro Inp.
  do 2 apply plift_monad_map.
Admitted.

(* Dubious, extremely dubious *)
Definition coin_flip_path : dist (list path) := 
  {| dist_pmf := [([[true]], 1/2); ([[false]], 1/2)];
    dist_law := eq_refl                   
  |}.

(* top level security theorem says that when we have a list of accesses, the distribution of the final list of paths as output observes the same distribution of the source of the randomness *)
Theorem access_dist_preservation :
  forall {C : Config} (arg_list : list (block_id * operation)) (s : state),
    distr_eqv coin_flip (acc_list_dist arg_list s).
Admitted.


(* Theorem stat_ind : forall (n > 0), *)
(*     len(access_list_1) = len(access_list_2) -> *)
(*     Pr(access_list_1 == AP /\ access_list_2 == AP) *)
(*   = Pr(access_list_1 == AP) * Pr (access_list_2 == AP).  *)
