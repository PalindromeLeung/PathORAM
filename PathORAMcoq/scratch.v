Require Import List.
Import ListNotations.

Class Bifunctor (F : Type -> Type -> Type) := {
    bimap {A B C D} : (A -> C) -> (B -> D) -> F A B -> F C D;
    first {A B C} : (A -> C) -> F A B -> F C B;
    second {A B D} : (B -> D) -> F A B -> F A D;

    bimap_first_second {A B C D} (g : A -> C) (h : B -> D) :
    forall x, bimap g h x = first g (second h x);
    first_bimap {A B C} (g : A -> C) :
    forall x, first g x = bimap g (fun (x : B) => x) x;
    second_bimap {A B D} (h : B -> D) :
    forall x, second h x = bimap (fun (x : A) => x) h x
  }.

#[export]
Instance Prod_BF : Bifunctor prod.
Proof.
  refine ( {|
             bimap _ _ _ _ := fun g h '(x,y) => (g x, h y);
             first _ _ _ := fun g '(x,y) => (g x, y);
             second _ _ _ := fun h '(x,y) => (x, h y);
             bimap_first_second :=  _;
             first_bimap := _;
             second_bimap := _
           |} ).
  - intros A B C D g h [a b]. reflexivity.
  - intros A B C g [a b]. reflexivity.
  - intros A B D h [a b]. reflexivity.
Defined.

Definition list_sum (A B : Type) : Type :=
  list (A + B).

Definition list_sum_bimap {A B C D} :
  (A -> C) -> (B -> D) -> list_sum A B -> list_sum C D :=
  fun g h xs =>
    List.map (fun (s : A + B) =>
                     match s with
                     | inl a => inl (g a)
                     | inr b => inr (h b)
                     end) xs.

Definition list_sum_first {A B C} : (A -> C) -> (list_sum A B) -> list_sum C B :=
  fun g xs =>
    List.map (fun (s : A + B) =>
                match s with
                | inl a => inl (g a)
                | inr b => inr b
                end) xs.

Definition list_sum_second {A B D} : (B -> D) -> list_sum A B -> list_sum A D :=
  fun h xs =>
    List.map (fun (s : A + B) =>
                match s with
                | inl a => inl a
                | inr b => inr (h b)
                end) xs.

#[export]
Instance ls_BF : Bifunctor list_sum.
Proof.
  refine ( {|
             bimap _ _ _ _ := list_sum_bimap;
             first _ _ _ := list_sum_first;
             second _ _ _ := list_sum_second;
             bimap_first_second :=  _;
             first_bimap := _;
             second_bimap := _
           |} ).
  - intros.
    induction x.
    + trivial.
    + simpl.
      destruct a;
      now rewrite IHx.
  - intros.
    admit.
  - admit.
Admitted.
