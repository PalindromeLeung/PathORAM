Require Import POram.Utils.Classes.
Import MonadNotation.
Require Import Coq.QArith.QArith.
Require Import Coq.Lists.List.
Import ListNotations.
(*** DISTRIBUTIONS ***)

(* You may need to just roll your own on this one, and it will be a pain. This
 * representation is mostly just a placeholder. This representation represents
 * the distribution as an association list, so must be a discrete distribution
 * with finite support. We allow multiple keys in the association list (so a
 * multimap) because to restrict otherwise would require an `Ord` restraint on
 * the value type, which makes it more painful to use things like the `Monad`
 * typeclass and notation. Another way to go is to use `dict` instead of a raw
 * association list, which has the dual trade-offs.
 *
 * These are extensional distributions, which make reasoning about conditional
 * probabilities and distribution independence a pain. consider moving to
 * intensional distributions a la the "A Language for Probabilistically
 * Oblivious Computation" paper (Fig 10). 
 *)

Fixpoint fold_l {X Y: Type} (f : X -> Y -> Y) (b : Y) (l : list X) : Y :=
  match l with
  | [] => b
  | h ::t => f h (fold_l f b t)
  end.

Definition sum_dist {A} (l : list (A * Q)) : Q := fold_l Qplus 0 (List.map snd l).

Record dist (A : Type) : Type :=
  Dist
    { dist_pmf : list (A * Q); 
      dist_law : Qeq (sum_dist dist_pmf) 1
    }.
Arguments Dist {A} _.
Arguments dist_pmf {A} _.

Definition mreturn_dist {A : Type} (x : A) : dist A.
  refine (Dist [ (x, 1 / 1) ] _ ).
  Proof.
    unfold sum_dist. simpl.
    unfold Qeq. simpl. reflexivity.
  Defined.

Lemma refold_sum_dist:
  forall {A} (a : A) (q : Q) (l : list (A * Q)),
    sum_dist ((a, q) :: l) = q + sum_dist l.
Proof.
  intros. reflexivity.
Defined.

Lemma sum_dist_app:
  forall {A} (l1 l2 : list (A * Q)),
    Qeq (sum_dist (l1 ++ l2)) (sum_dist l1 + sum_dist l2).
Proof.
  induction l1; intros.
  - rewrite Qplus_0_l. reflexivity.
  - simpl. destruct a. rewrite refold_sum_dist. rewrite refold_sum_dist.
    rewrite IHl1. apply Qplus_assoc.
Defined.

Definition update_probs {B} q l :=
  List.map
    (fun yq' : B * Q => let (y, q') := yq' in (y, q * q'))
    l.

Lemma update_probs_OK:
  forall {B} q l,
    Qeq (sum_dist (@update_probs B q l)) (q * sum_dist l).
Proof.
  intros. induction l.
  - unfold sum_dist. simpl. ring.
  - destruct a. simpl. 
    rewrite refold_sum_dist. rewrite refold_sum_dist.
    rewrite IHl. ring.
Defined.

Definition mbind_dist_pmf {A B : Type} (xM : dist A) (f : A -> dist B) : list (B * Q) :=
  flat_map
   (fun (xq : A * Q) => 
     let (x , q) := xq in 
     (update_probs q (dist_pmf (f x))))
   (dist_pmf xM).

Definition mbind_dist {A B : Type} (xM : dist A) (f : A -> dist B) : dist B.
 refine (Dist (mbind_dist_pmf xM f) _ ).
Proof.
  destruct xM. unfold mbind_dist_pmf. simpl. rewrite <- dist_law0. generalize dist_pmf0 as l. induction l.
  - reflexivity.
  - simpl. destruct a. rewrite refold_sum_dist. rewrite sum_dist_app.
    remember (f a). destruct d. simpl. rewrite IHl.
    rewrite update_probs_OK. rewrite dist_law1. ring.
Defined.
 
#[export] Instance Monad_dist : Monad dist := { mreturn {_} x := mreturn_dist x ; mbind {_ _} := mbind_dist }.

Definition coin_flip : dist bool := Dist [ (true, 1 / 2) ; (false , 1 / 2) ] eq_refl.

(* Definition norm_dist {A} (d: dist A) : dist A := *)
(*   let supp := dist_pmf d in *)
(*   let sum_tot := sum_dist d in *)
(*   Dist(map_alist (fun x : Q => x / sum_tot) supp). *)

Definition event (A : Type) := A -> bool.

(* might collide when you import the List Lib. *)

Fixpoint filter {A} (l: list A) (f: A -> bool): list A :=
  match l with
  | [] => []
  | x :: l => if f x then x::(filter l f) else filter l f 
  end.

Fixpoint takeL {A} n (l : list A) : list A :=
  match n with
  | O => []
  | S m => match l with
          | [] => []
          | h :: t => h :: takeL m t 
          end
  end.

(* The goal of evalDist is to evaluate the probability when given an event under a certain distribution.      *)

(* 1. get the list -- dist_pmf *)
(* 2. filter a, construct the new list (A, rat) which satisfies event predicate *)
(* 3. reconstruct/repack a dist using this one *)
(* 4. sum it up -- sum_dist *)

 
Fixpoint filter_dist {A} (l: list (A * Q))
  (f: A -> bool): list (A * Q) :=
  match l with
  | [] => []
  | h :: t => 
      match h with
        | pair k v => 
            if f k
            then h :: (filter_dist t f)
            else filter_dist t f
      end
  end.
    
(* Definition evalDist {A} (x: event A) (d: dist A): Q := *)
(*    sum_dist(Dist(filter_dist (dist_pmf d) x)). *)

(* Definition uniform_dist {A} (l: list A) :dist A:= *)
(*  norm_dist(Dist(map_l (fun x => (x, 1)) l)). *)

Fixpoint mk_n_list (n: nat):list nat :=
  match n with
  | O => []
  | S n' => [n'] ++ mk_n_list n'
  end.

Lemma zero_one_neq : ~ (0 == 1)%Q.
Proof.
  intro pf.
  inversion pf.
Qed.

(* extract a value from a distribution arbitrarily, in this case
   taking the first elt of the underlying list *)
Definition peek {X} (d : dist X) : X :=
  match d with
  | {| dist_pmf := dist; dist_law := law |} =>
    match dist as l return ((sum_dist l == 1)%Q -> X) with
    | [] => fun law => 
      match zero_one_neq law with end
    | (x,_) :: _ => fun _ => x
       end law
  end.
