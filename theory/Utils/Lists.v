Require Import POram.Utils.Classes.
Require Import Coq.Lists.List.
Import ListNotations.
(*** LISTS ***)

(* #[export] Instance Functor_list : Functor list := { map := List.map }. *)
#[export] Instance Monoid_list {A : Type} : Monoid (list A) := { null := nil ; append := @List.app A }.

Definition disjoint_list {A} (l1 l2 : list A) :=
  forall a, ~ (In a l1 /\ In a l2).

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

Fixpoint remove_list {A : Type} (p : A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => [] 
  | x' :: xs' =>
      if p x'
      then remove_list p xs'
      else
        x' :: remove_list p xs'
  end.

Lemma takeL_in : forall {X} (x : X) n l,
   In x (takeL n l) -> In x l. 
Proof.
  induction n; intros; simpl in *.
  - exfalso; auto.
  - destruct l.
    + auto.
    + destruct H.
      * rewrite H. left; auto.
      * right. apply IHn. auto.
Qed.

Lemma In_remove_list_In {A} (p : A -> bool) (xs : list A) : forall x,
    In x (remove_list p xs) -> In x xs.
Proof.
  intros x Hx.
  induction xs as [|y xs].
  - destruct Hx.
  - simpl in Hx.
    destruct (p y).
    + right; auto.
    + simpl in *; tauto.
Qed.

Lemma In_remove_list_p {A} (p : A -> bool) (xs : list A) : forall x,
    In x (remove_list p xs) -> p x = false.
Proof.
  intros x Hx.
  induction xs as [|y xs].
  - destruct Hx.
  - simpl in Hx.
    destruct (p y) eqn:Hy; auto.
    destruct Hx; auto.
    congruence.
Qed.

Lemma In_remove_list {A} (p : A -> bool) (xs : list A) : forall x,
    In x xs -> p x = false -> In x (remove_list p xs).
Proof.
  intros x Hx1 Hx2.
  induction xs as [|y xs].
  - destruct Hx1.
  - simpl.
    destruct Hx1; subst.
    + rewrite Hx2.
      left; auto.
    + destruct (p y); auto.
      right; auto.
Qed.

Lemma In_remove_list_iff {A} (p : A -> bool) (xs : list A) : forall x,
    In x (remove_list p xs) <-> In x xs /\ p x = false.
Proof.
  intros; split; intros.
  - split.
    + eapply In_remove_list_In; eauto.
    + eapply In_remove_list_p; eauto.
  - destruct H; eapply In_remove_list; eauto.
Qed.

(* TODO: move this somewhere*)
Definition eqb_correct {A} (A_eqb : A -> A -> bool) : Prop :=
  forall a a', A_eqb a a' = true <-> a = a'.

Lemma eqb_correct_refl {A} (A_eqb : A -> A -> bool) :
 eqb_correct A_eqb -> forall a, A_eqb a a = true.
Proof.
  intros A_eqb_correct a.
  rewrite (A_eqb_correct a a); auto.
Qed.

Fixpoint remove_aux {A} (A_eqb : A -> A -> bool) (lst : list A) (x : A) : list A :=
  match lst with
  | [] => []
  | h :: t => 
      if A_eqb h x then t else h :: remove_aux A_eqb t x
  end.

Fixpoint remove_list_sub {A} (A_eqb : A -> A -> bool) (sublist : list A) (lst : list A) : list A :=
  match sublist with
  | [] => lst
  | h :: t => remove_list_sub A_eqb t (remove_aux A_eqb lst h)
  end.

Lemma remove_aux_lemma {A} (A_eqb : A -> A -> bool)
  (A_eqb_correct : eqb_correct A_eqb) : forall (lst : list A) (a a' : A),
    In a' lst ->
    In a' (remove_aux A_eqb lst a) \/ a = a'.
Proof.
  intros.
  induction lst; intuition.
  simpl.
  destruct A_eqb eqn: eq_cond; simpl.
  - destruct H.
    + right.
      rewrite (A_eqb_correct a0 a) in eq_cond; congruence.
    + tauto.
  - destruct H.
    + do 2 left; auto.
    + apply IHlst in H. tauto.
Qed.

Lemma remove_list_sub_lemma {A} (A_eqb : A -> A -> bool)
  (A_eqb_correct : eqb_correct A_eqb) : forall (a : A) (sub : list A) (lst : list A),
      In a lst ->
      In a (remove_list_sub A_eqb sub lst) \/ In a sub.
Proof.
  intros a sub.
  induction sub. 
  - simpl.  intros. left; auto.
  - intros. simpl remove_list_sub.
    pose proof (IHsub (remove_aux A_eqb lst a0))%list.
    destruct (remove_aux_lemma A_eqb A_eqb_correct _ a0 _ H).
    + apply H0 in H1. destruct H1.
      * left. auto.
      * right. right; auto.
    + right. left; auto.
Qed.

Lemma In_remove_aux {A} (A_eqb : A -> A -> bool) :
  forall (lst : list A) (x a : A),
    In x (remove_aux A_eqb lst a) ->
    In x lst.
Proof.
  induction lst; simpl; intros; auto.
  destruct A_eqb eqn: eq_cond; simpl.
  - right; auto.
  - destruct H; auto. right.
    apply IHlst with (a := a0). auto.
Qed.

Lemma remove_list_sub_weaken {A} (A_eqb : A -> A -> bool) : forall dlt lst b,
    In b (remove_list_sub A_eqb dlt lst) -> In b lst.
Proof.
  induction dlt; simpl; intros; auto.
  apply IHdlt in H.
  apply In_remove_aux in H; auto.
Qed.
