Require Import List.
Import ListNotations.
From Coq Require Import Lia.
Require Import Coq.Bool.Bool.

Section Utils.
  Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true 
  | S n' => 
      match m with
      | O =>  false
      | S m' => leb n' m'
      end
  end.
  
End Utils.

Section Tree.

  
  Inductive PBTree (A: Type) : Type :=
  | Leaf (idx: nat) (val: list A)
  | Node (idx: nat) (val: list A) (l r: PBTree A).

  Fixpoint getHeight (A: Type) (root: PBTree A) : nat :=
    match root with
    | Leaf _  _ _ => 1
    | Node _ _ _ l r => if(leb (getHeight A l) (getHeight A r))then S(getHeight A r) else S(getHeight A l)
    end.

  (*TODO getPath & clearPath*)
  
End Tree.


Section Fold.
  Fixpoint foldr {A : Type} {B : Type} (f : A -> B -> B) (v : B) (l : list A) := 
  match l with
  | nil => v
  | x :: xs => f x (foldr f v xs)
  end.

  Fixpoint foldl {A : Type} {B : Type} (f : B -> A -> B) (v : B) (l : list A) :=
  match l with
  | nil => v
  | x :: xs => foldl f (f v x) xs
  end.

End Fold.


Section PathORAM.
  Definition nodesTotal := 28.
  Definition nodecap := 4.

  Inductive Operation :=
  | Rd
  | Wr.
  
 End PathORAM.
