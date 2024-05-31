(* --- BEGIN Talia's equivalent definition of nth to reuse later --- *)
Require Import Coq.Vectors.Vector.
Require Import Coq.QArith.QArith.
Fixpoint nth_error_opt {A : Type} {m : nat} (v : Vector.t A m) (n : nat) : option A :=
  match n with
  | O =>
    match v with
    | Vector.nil _ => None
    | Vector.cons _ h _ _ => Some h
    end
  | S p =>
    match v with
    | Vector.nil _ => None
    | Vector.cons _ _ n1 t0 => nth_error_opt t0 p
    end
  end.

Lemma nth_error_opt_some:
  forall {A : Type} {m : nat} (v : Vector.t A m) (n : nat) (a : A),
    nth_error_opt v n = Some a -> Nat.lt n m.
Proof.
  intros A m v n. revert A m v.
  induction n; destruct v; intros; inversion H.
  - auto with arith.
  - specialize (IHn A n0 v a H1). auto with arith.
Qed.

Lemma fin_of_lt_irrel:
  forall {m n : nat} (H1 H2 : Nat.lt n m), Fin.of_nat_lt H1 = Fin.of_nat_lt H2.
Proof.
  induction m; destruct n; intros; auto.
  - inversion H1.
  - inversion H1.
  - simpl. f_equal. apply IHm.
Qed.

Lemma nth_error_OK:
  forall {A : Type} {m : nat} (v : Vector.t A m) (n : nat) (a : A) (H : nth_error_opt v n = Some a),
    nth_order v (nth_error_opt_some v n a H) = a.
Proof.
  intros A m v n. revert A m v. induction n; destruct v; intros; inversion H.
  - subst. reflexivity.
  - specialize (IHn A n0 v a H).
    unfold nth_order in *. simpl in *. rewrite <- IHn. 
    f_equal. apply fin_of_lt_irrel.
Qed.
(* --- END Talia's equivalent definition of nth to reuse later --- *)
