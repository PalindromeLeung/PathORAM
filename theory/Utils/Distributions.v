Require Import POram.Utils.Classes.
Import MonadNotation.
Require Import Coq.QArith.QArith.
Require Import Coq.Lists.List.
Import ListNotations.

Definition sum_dist {A} (l : list (A * Q)) : Q :=
  List.fold_right Qplus 0 (List.map snd l).

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

(* might collide when you import the List Lib. *)

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

(* WARNING: distribution should contain non-zero weighted support *)
Definition dist_lift {X} (P : X -> Prop) (d : dist X) : Prop.
Proof.   
  destruct d.
  eapply (Forall P (List.map fst dist_pmf0)).
Defined.

Lemma dist_lift_peek {X} (P : X -> Prop) (dx : dist X) :
  dist_lift P dx ->
  P (peek dx).
Proof.
  intro Hdx.
  destruct dx as [dist law]; simpl.
  destruct dist as [|p dist].
  - destruct zero_one_neq.
  - destruct p.
    inversion Hdx; auto.
Qed.

Lemma dist_lift_ret : forall (X : Type) (x : X) (P : X -> Prop), P x -> dist_lift P (mreturn x).
Proof.
  intros; simpl.
  repeat constructor; auto.
Qed.

Lemma dist_lift_bind :
forall (X Y : Type) (P : X -> Prop)
  (Q : Y -> Prop) (mx : dist X)
  (f : X -> dist Y),
dist_lift P mx ->
(forall x : X, P x -> dist_lift Q (f x)) ->
dist_lift Q (x <- mx;; f x).
Proof.
  intros. simpl mbind. unfold mbind_dist.
    unfold dist_lift. rewrite Forall_map. unfold mbind_dist_pmf. rewrite flat_map_concat_map. rewrite Forall_concat. rewrite Forall_map.
    eapply Forall_impl.
    2:{destruct mx. simpl in *. rewrite Forall_map in H. exact H. }
    intros (k,v) pk. simpl. unfold update_probs. rewrite Forall_map.
    specialize (H0 k pk). destruct (f k). simpl in *. rewrite Forall_map in H0. eapply Forall_impl.
    2:{exact H0. }
    intros (a, b) pa. exact pa.
Qed.

Lemma dist_lift_weaken {X} (P Q : X -> Prop) :
  (forall x, P x -> Q x) -> forall d,
  dist_lift P d -> dist_lift Q d.
Proof.
  intros.
  unfold dist_lift in *.
  destruct d.
  eapply Forall_impl; eauto.
Qed.

Lemma dist_split {X} (P Q : X -> Prop) d :
  dist_lift P d ->
  dist_lift Q d ->
  dist_lift (fun x => P x /\ Q x) d.
Proof.
  destruct d; simpl.
  repeat rewrite Forall_forall.
  intros; auto.
Qed.

Lemma dist_true {X} (d : dist X) : dist_lift (fun _ => True) d.
Proof.
  destruct d; simpl.
  rewrite Forall_forall.
  auto.
Qed.

Global Instance Pred_Dist_Lift : PredLift dist :=
  {|
    plift := @dist_lift;
    plift_ret := dist_lift_ret;
    plift_bind := dist_lift_bind;
    plift_weaken := @dist_lift_weaken;
    plift_split := @dist_split;
    plift_true := @dist_true;
  |}.

Lemma coin_flip_triv :
  plift (fun _ => True) coin_flip.
Proof.
  repeat constructor.
Qed.

Definition coin_flips (n : nat) : dist (list bool) :=
  constm_list coin_flip n.

Lemma coin_flips_length (n : nat):
  plift (fun p => length p = n) (coin_flips n).
Proof.
  apply constm_list_length.
  exact coin_flip_triv.
Qed.

Definition dist_lift2 X Y (P : X -> Y -> Prop)
  (dx : dist X) (dy : dist Y) : Prop :=
  plift (fun x => plift (P x) dy) dx.
