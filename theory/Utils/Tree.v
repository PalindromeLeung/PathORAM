Require Import Lia.
Require Import List.
Import ListNotations.

Inductive tree X : Type :=
  | leaf
  | node (data: X) (o_l o_r : tree X). 

Arguments leaf {_}.
Arguments node {_} _ _ _.

Fixpoint get_height {X} (o : tree X) : nat :=
  match o with
  | leaf => 0
  | node  _ l r => S (max (get_height l) (get_height r))
  end.

Fixpoint is_p_b_tr {X} (o : tree X) (l : nat) : Prop :=
  match o, l with
  | leaf, O => True
  | node _ o_l o_r, S l' =>
      is_p_b_tr o_l l' /\ is_p_b_tr o_r l'
  | _, _ => False
  end.

Definition path := list bool.

Fixpoint coord_in_bound {X} (o : tree X) (p : path) (stop: nat) : Prop :=
  match o with
  | leaf => False 
  | node d_o o_l o_r =>
      match stop with
      | 0%nat => True 
      | S stop' =>
          match p with
          | [] => False 
          | true :: xs => coord_in_bound o_l xs stop' 
          | false :: xs => coord_in_bound o_r xs stop'
          end
      end
  end.

Lemma pb_coord_in_bound {X} : forall (o : tree X) (p : path) (k lvl : nat), 
    is_p_b_tr o (S k) ->
    (length p) = k -> 
    lvl <= k ->
    coord_in_bound o p lvl.
Proof.
  intro o.
  induction o; simpl.
  - intros. inversion H.
  - intros. destruct lvl; simpl; auto.
    destruct p; simpl in *; try lia.
    destruct b; simpl in *.
    + apply IHo1 with (k := (length p)); try rewrite H0.
      tauto. reflexivity.
      rewrite <- H0 in H1. lia.
    + apply IHo2 with (k := (length p)); try lia.
      destruct H. rewrite H0. auto.
Qed.

Fixpoint update_tree {X} (o : tree X) (stop : nat) (x : X) :
  path -> tree X :=
  match o in tree _ return path -> tree X with
  | leaf => fun _ => leaf
  | node d_o o_l o_r =>
      fun p =>
        match stop with
        | O => node x o_l o_r
        | S stop' =>
            match p with
            | [] => node d_o o_l o_r
            | b :: xs =>
                match b with
                | true => node d_o (update_tree o_l stop' x xs ) o_r
                | false => node d_o o_l(update_tree o_r stop' x xs)
                end
            end
        end
  end.

Fixpoint lookup_tree {X} (o : tree X) (lvl : nat) : path -> option X:=
  match o with
  | leaf => fun _ => None
  | node d o_l o_r =>
      fun p =>
        match lvl with
        | O => Some d
        | S lv =>
            match p with
            | [] => None
            | x :: xs =>
                match x with
                | true => lookup_tree o_l lv xs
                | false => lookup_tree o_r lv xs
                end
            end
        end
  end.

Lemma lookup_tree_update_tree {X} (o : tree X) : forall
  (lvl lvl' : nat) (p p' : path) (x : X),
  lvl < lvl' ->
  lookup_tree (update_tree o lvl x p') lvl' p =
  lookup_tree o lvl' p.
Proof.
  induction o; intros; simpl; auto.
  destruct lvl'.
  - lia.
  - destruct lvl; simpl in *; auto.
    destruct p; simpl in *. 
    + destruct p'; simpl in *; auto.
      destruct b; simpl in *; auto.
    + apply Arith_prebase.lt_S_n in H.
      destruct p'; simpl; auto.
      destruct b0, b; simpl; auto.
Qed.

Lemma update_tree_preserves_pb {X} (o : tree X) :
  forall n lvl x p,
  is_p_b_tr o n ->
  is_p_b_tr (update_tree o lvl x p) n.
Proof.
  induction o; simpl; intros; auto.
  destruct lvl; simpl; auto.
  destruct p; simpl; auto.
  destruct b; simpl; auto.
  destruct n; simpl; auto.
  - split; try tauto.
    apply IHo1; tauto.
  - destruct n; simpl; auto.
    +  split; try tauto.
       apply IHo2; tauto.
Qed.
