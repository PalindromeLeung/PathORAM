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
