Require Import Lia.
Require Import List.
Import ListNotations.

Inductive tree X : Type :=
  | leaf
  | node (data: X) (o_l o_r : tree X). 

Arguments leaf {_}.
Arguments node {_} _ _ _.

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

Fixpoint lookup_path {X} (t : tree X) (p : path) : list X :=
  match t with
  | leaf => []
  | node x t1 t2 =>
    match p with
    | [] => [x]
    | true :: p' => x :: lookup_path t1 p'
    | false :: p' => x :: lookup_path t2 p'
    end
  end.

Fixpoint flatten_tree {X} (t : tree X) : list X :=
  match t with
  | leaf => []
  | node x t1 t2 => x :: flatten_tree t1 ++ flatten_tree t2
  end.

Lemma In_flatten_update {X} (t : tree X) : forall (lvl : nat) (x x' : X) (p : path),
  In x (flatten_tree (update_tree t lvl x' p)) ->
  In x (flatten_tree t) \/ x = x'.
Proof.
  induction t; intros lvl x x' p pf.
  - destruct pf.
  - destruct lvl.
    + destruct pf.
      * right; auto.
      * left; right; auto.
    + destruct p as [|[] p'].
      * left; destruct pf.
        -- left; auto.
        -- right; auto.
      * destruct pf.
        -- left; left; auto.
        -- apply in_app_or in H.
           destruct H.
           ++ apply IHt1 in H.
              destruct H; [|tauto].
              left; right.
              apply in_or_app; now left.
           ++ left; right.
              apply in_or_app; now right.
      * destruct pf.
        -- left; left; auto.
        -- apply in_app_or in H.
           destruct H.
           ++ left; right.
              apply in_or_app; now left.
           ++ apply IHt2 in H.
              destruct H; [|tauto].
              left; right.
              apply in_or_app; now right.
Qed.

Lemma lookup_path_flatten_tree {X} (t : tree X) : forall (p : path ) (x : X), In x (lookup_path t p) -> In x (flatten_tree t).
Proof.
  induction t; intros p x pf.
  - destruct pf.
  - destruct p as [|[|] p'].
    + destruct pf; [|contradiction].
      now left.
    + destruct pf; [now left|].
      right; apply in_or_app; left.
      eapply IHt1; eauto.
    + destruct pf; [now left|].
      right; apply in_or_app; right.
      eapply IHt2; eauto.
Qed.


