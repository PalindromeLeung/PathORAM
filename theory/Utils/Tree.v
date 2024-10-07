Require Import Lia.
Require Import List.
Import ListNotations.

Require Import POram.Utils.Fin.
Require Import POram.Utils.Vec.

Fixpoint pb_tree n X : Type :=
  match n with
  | 0 => unit
  | S m => X * pb_tree m X * pb_tree m X
  end.

Definition path n := vec n bool.

Fixpoint update_tree {X} {n} : pb_tree (S n) X -> Fin (S n) -> X -> path n -> pb_tree (S n) X :=
  match n with
  | 0 => fun t _ x _ =>
    match t with
    | (_, t1, t2) => (x, t1, t2)
    end
  | S m => fun t i x p =>
    match t with
    | (x_nd, t_l, t_r) =>
      match i with
      (* i=0 *)
      | inl _ => (x, t_l, t_r)
      (* i=j+1 *)
      | inr j =>
        match p with
        (* path begins with left *)
        | (true, p') => (x_nd, update_tree t_l j x p', t_r)
        (* path begins with right *)
        | (false, p') => (x_nd, t_l, update_tree t_r j x p')
        end
      end
    end
  end.

Fixpoint lookup_tree {X} {n} : pb_tree (S n) X -> Fin (S n) -> path n -> X :=
  match n with
  | 0 => fun t _ _ =>
    match t with
    | (x, _, _) => x
    end
  | S m => fun t i p =>
    match t with
    | (x, t_l, t_r) =>
      match i with
      (* i=0 *)
      | inl _ => x
      (* i=j+1 *)
      | inr j =>
        match p with
        (* path begins with left *)
        | (true, p') => lookup_tree t_l j p'
        (* path begins with right *)
        | (false, p') => lookup_tree t_r j p'
        end
      end
    end
  end.

Fixpoint Fin_lt {n} : Fin n -> Fin n -> Prop :=
  match n with
  | 0 => fun _ _ => True
  | S m => fun i j =>
    match i,j with
    | inl _, inl _ => False
    | inl _, inr _ => True
    | inr _, inl _ => False
    | inr i', inr j' => Fin_lt i' j'
    end
  end.

Infix "<f" := Fin_lt (at level 10).

Lemma Fin_lt_1_contra : forall i j : Fin 1,
  ~ i <f j.
Proof.
  intros [|[]] [|[]] [].
Qed.

(* TODO: change name *)
Lemma lookup_tree_update_tree {X} {n} (o : pb_tree (S n) X) :
  forall (lvl lvl' : Fin (S n)) (p p' : path n) (x : X),
    lvl <f lvl' ->
    lookup_tree (update_tree o lvl x p') lvl' p =
    lookup_tree o lvl' p.
Proof.
  induction n; intros lvl lvl' p p' x Hlvls.
  - apply Fin_lt_1_contra in Hlvls.
    contradiction.
  - destruct o as [[x' o_l] o_r].
    destruct lvl, lvl'.
    + simpl in Hlvls; contradiction.
    + reflexivity.
    + simpl in Hlvls; contradiction.
    + destruct p' as [[|] p'_tl].
      * destruct p; simpl.
        rewrite IHn; auto.
      * destruct p; simpl.
        rewrite IHn; auto.
Qed.
