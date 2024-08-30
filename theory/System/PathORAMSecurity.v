Require Coq.Bool.Bool.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.QArith.QArith.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import POram.Utils.Classes.
Import MonadNotation.
Require Import POram.Utils.Lists.
Require Import POram.Utils.Vectors.
Require Import POram.Utils.Tree.
Require Import POram.Utils.Rationals.
Require Import POram.Utils.StateT.
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
  (arg_list : list (block_id * operation)) : Poram (list path) :=
  let l := List.map (fun '(bid, op) => access bid op) arg_list in
  let p := sequence l in
  monad_map (List.map fst) p.

Definition get_dist_list_bool {C : Config}
  (arg_list : list (block_id * operation))(s : state) : dist (list bool) :=
  monad_map (@List.concat bool) (monad_map fst ((acc_dist_list arg_list) s)).

Lemma plift_monad_map : forall {X Y} (f : X -> Y) (d : dist X) (P : Y -> Prop), 
    plift (fun x => P (f x)) d -> 
    plift P (monad_map f d).
Proof.
  intros.
  eapply plift_bind.
  - exact H.
  - intros. 
    eapply plift_ret.
    apply H0; auto.
Qed.

Lemma state_plift_monad_map :
  forall {X Y} (Pre Post: state -> Prop) (P : Y -> Prop)
    (f : X -> Y) (m : Poram X),
    state_plift Pre Post (fun x => P (f x)) m ->
    state_plift Pre Post P (monad_map f m).
Proof.
  intros.
  eapply state_plift_bind.
  - exact H.
  - intros. 
    eapply state_plift_ret.
    apply H0; auto.
Qed.

Lemma sequence_length :
  forall {S A M} `{PredLift M} (Pre : S -> Prop)(l : list (StateT S M A)) ,
    let n := List.length l in 
    state_plift Pre Pre (fun l' => List.length l' = n) (sequence l).
Admitted.


Lemma state_plift_Forall :
  forall {S A M} `{PredLift M} (Pre : S -> Prop)
    (P : A -> Prop) (l : list (StateT S M A)),
    Forall (state_plift Pre Pre P) l ->
    state_plift Pre Pre (Forall P) (sequence l).
Admitted.

Lemma state_plift_P_weakening :
  forall {S A M} `{PredLift M} (Pre : S -> Prop)(P Q: A -> Prop) s,
    (forall x, P x -> Q x) -> 
    state_plift Pre Pre P s -> 
    state_plift Pre Pre Q s.
Admitted.

Lemma state_plift_P_split :
  forall {C : Config} {S M X} `{PredLift M}
    (P Q : X -> Prop) (Pre Post: S -> Prop)
    (s : StateT S M X),
    state_plift Pre Post P s /\  
      state_plift Pre Post Q s ->
    state_plift Pre Post (fun x => (P x /\ Q x)) s.
Admitted. 
    
Lemma acc_dist_list_length :
  forall {C : Config} (arg_list : list (block_id * operation)),
    state_plift well_formed well_formed 
      (fun l => List.length l = List.length arg_list /\
               (Forall (fun l' => List.length l' = LOP) l))
      (acc_dist_list arg_list).
Proof. 
  intros.
  unfold acc_dist_list.
  apply state_plift_monad_map.
  apply state_plift_P_split; split.
  - apply state_plift_P_weakening with
      (P := fun l => length l = length (List.map (fun '(bid, op) => access bid op) arg_list)).
    + intros.
      rewrite map_length in *; auto.
    + apply sequence_length.
  - apply state_plift_P_weakening with
      (P := Forall (fun pn : (path * nat) => length (fst pn) = LOP)).
    + intros. rewrite Forall_map; auto.
    + apply state_plift_Forall.
      rewrite Forall_map.
      rewrite Forall_forall.
      intros; simpl.
      admit.
Admitted. 
    
Fixpoint replicate {X} (n : nat) (m : X) : list X :=
  match n with
  | O => []
  | S n' => cons m (replicate n' m)
  end.

Lemma Forall_replicate :
  forall {X Y} (l : list X) (f : X -> Y) (y : Y),
    Forall (fun x => f x = y) l ->
    List.map f l = replicate (List.length l) y.
Proof.
  induction l; simpl; auto.
  intros.
  pose proof (Forall_inv H). simpl in H0. rewrite H0.
  pose proof (Forall_inv_tail H). 
  specialize (IHl f y H1).
  rewrite IHl.
  auto.
Qed.

Lemma concat_list_sum : 
  forall {X} (l : list (list X)),
  List.length (concat l) = List.list_sum (List.map (@List.length X) l).
Proof.
  induction l; simpl; auto.
  rewrite app_length.
  rewrite IHl. auto.
Qed.

Lemma list_sum_rep :
  forall (n m : nat),
    List.list_sum (replicate n m) = (n * m)%nat.
Proof.
  induction n; simpl; auto.
Qed.
  
Theorem arg_list_len_rel :
  forall {C : Config} (arg_list : list (block_id * operation))(s : state),
    well_formed s -> 
    plift (fun l => List.length l = List.length arg_list * LOP)%nat
      (get_dist_list_bool arg_list s).
Proof.
  intros c ag s Hwf.
  do 2 apply plift_monad_map.
  pose proof (acc_dist_list_length ag s Hwf).
  eapply dist_has_weakening; [ | exact H].
  intros.
  simpl in H0. destruct x. destruct H0. simpl.
  destruct H0.
  apply Forall_replicate in H2.
  rewrite concat_list_sum.
  rewrite H2.
  rewrite list_sum_rep.
  rewrite H0.
  auto.
Qed.
  
Definition uniform (n : nat) (d : dist (list bool)) :=
  forall l, (List.length l = n)%nat ->
      Qeq (eval_dist d (list_beq bool eqb l)) ((1 / 2) ^ (Z.of_nat n)).
    

(* top level security theorem says that when we have a list of accesses, the distribution of the final list of paths as output observes the same distribution of the source of the randomness *)
Theorem access_dist_preservation :
  forall {C : Config} (arg_list : list (block_id * operation)) (s : state),
    uniform ((List.length arg_list) * LOP)
      (get_dist_list_bool arg_list s).
Admitted.


(* Theorem stat_ind : forall (n > 0), *)
(*     len(access_list_1) = len(access_list_2) -> *)
(*     Pr(access_list_1 == AP /\ access_list_2 == AP) *)
(*   = Pr(access_list_1 == AP) * Pr (access_list_2 == AP).  *)
