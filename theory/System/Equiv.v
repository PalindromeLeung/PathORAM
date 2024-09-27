Require Import List.
Import ListNotations.

Require Import POram.Utils.Tree.
Require Import POram.System.PathORAMDef.
Require Import POram.System.PathORAMFunCorrect.
Require Import POram.Utils.Distributions.
Require Import POram.Utils.Classes.

(* for any x in xs and y in ys, P x y holds. *)
Definition All2 {X Y} (P : X -> Y -> Prop)
  (xs : list X) (ys : list Y) : Prop :=
  Forall (fun x => Forall (P x) ys) xs.

Section Equiv.

Context `{C : Config}.

Definition kv_rel (id : block_id) (v : nat) (st : state) : Prop :=
    blk_in_state id v st \/ (undef id st /\ v = 0).

Definition state_equiv (s s' : state) : Prop :=
  forall k v,
    kv_rel k v s <-> kv_rel k v s'. 

Definition dist_equiv {X} (eqv : X -> X -> Prop)
  (d d' : dist X) : Prop :=
  All2 eqv
    (List.map fst (dist_pmf d))
    (List.map fst (dist_pmf d')).

Definition prod_rel {X X' Y Y'} (P : X -> X' -> Prop) (Q : Y -> Y' -> Prop) :
  X * Y -> X' * Y' -> Prop :=
  fun p1 p2 =>
    P (fst p1) (fst p2) /\
    Q (snd p1) (snd p2).

Definition poram_equiv {X} (eqv : X -> X -> Prop)
  (m m' : Poram X) : Prop :=
  forall s s' : state,
    state_equiv s s' ->
    well_formed s ->
    well_formed s' ->
    dist_equiv (prod_rel eqv state_equiv) (m s) (m' s').

End Equiv.
