Require Import POram.Utils.Classes.
Require Import Coq.Lists.List.
Import ListNotations.
(*** LISTS ***)

(* #[export] Instance Functor_list : Functor list := { map := List.map }. *)
#[export] Instance Monoid_list {A : Type} : Monoid (list A) := { null := nil ; append := @List.app A }.

Fixpoint remove_list {A : Type} (p : A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => [] 
  | x' :: xs' =>
      if p x'
      then remove_list p xs'
      else
        x' :: remove_list p xs'
  end.

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
