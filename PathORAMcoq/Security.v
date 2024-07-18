Require Import FCF.FCF.

Definition bool_eq_dec : eq_dec bool.
Proof.
  unfold eq_dec.
  decide equality.
Defined. 

Definition coin_flip : Comp bool.
  pose (rnd_bv := Rnd 1).
  exact (Bind rnd_bv (fun bv => Ret bool_eq_dec (Vector.hd bv))).
Defined.

Compute evalDist coin_flip true.
Print Rat.
Print posnat.
Print sig.
Definition Rat_to_nums (r : Rat) : nat * nat :=
  match r with
  | RatIntro numerator (exist _ denominator _) => (numerator, denominator)
  end.

Compute Rat_to_nums (evalDist coin_flip false).

(* uniform distribution.  *)

Definition uniform_comp(l : nat): Comp (Bvector l) := Rnd l.

Definition uniform_dist (l : nat) := evalDist (uniform_comp l).

Definition sampleBV1 := Vector.cons _ false _ (Vector.cons _ true _ (Vector.nil _)).
Compute uniform_dist 2 sampleBV1.

Definition sampleBV2 := Vector.cons _ false _ (Vector.cons _ true _ (Vector.nil _)).
Compute uniform_dist 2 sampleBV2.

#[export] Instance bool_eqb : EqDec bool :=
  {
    eqb := Bool.eqb;
    eqb_leibniz := eqb_true_iff
  }.
Lemma Bv12Equiv : eqb_vector bool_eqb sampleBV1 sampleBV2 = true.
Proof.
  unfold eqb_vector.
  simpl.
  reflexivity.
Qed.

(* assume that the tree has one node and 2 leaves, then the path is 1 bit long *)
(**
                 / [ ID | PAYLOAD ] \
                 | [ ID | PAYLOAD ] |
                 \ [ ID | PAYLOAD ] /
                  /               \
                 /                 \
                /                   \
   / [ ID | PAYLOAD ] \   / [ ID | PAYLOAD ] \  ←
   | [ ID | PAYLOAD ] |   | [ ID | PAYLOAD ] |  ← A BUCKET = N BLOCKS (example: N=3)
   \ [ ID | PAYLOAD ] /   \ [ ID | PAYLOAD ] /  ←
                            ↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑
 **)

(*
  Z = 3
  N = 3
  addr space = Z * N = 3 * 3
  path_len = 1 bit 
  |acc_list| = Len = 5
  Len_AP = 1 * 5 = 5 bits
 *)

(*TODO : define 2 random variables from a coin_flip, show that the probability of the conjuction of them is true is 1/4 *)
(*
  p <- coin_flip
  q <- coin_flip
  Pr[p /\ q ] = 1/4
 *)












