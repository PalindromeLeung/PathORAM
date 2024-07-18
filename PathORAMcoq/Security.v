Require Import FCF.FCF.

Definition  bool_eq_dec : eq_dec bool.
Proof.
  unfold eq_dec.
  decide equality.
Defined. 

Definition coin_flip : Comp bool.
  pose (rnd_bv := Rnd 1).
  exact (Bind rnd_bv (fun bv => Ret bool_eq_dec (Vector.hd bv))).
Defined.



(* uniform distribution.  *)

Definition uniform_comp(l : nat): Comp (Bvector l) := Rnd l.

Definition uniform_dist (l : nat) := evalDist (uniform_comp l).

Definition sampleBV := Vector.cons _ false _ (Vector.cons _ true _ (Vector.nil _)).
Compute uniform_dist 2 sampleBV.
Definition sampleBV' := Vector.cons _ true _ (Vector.nil _).
Compute uniform_dist 1 sampleBV'.


(* conditional probability *)




 
