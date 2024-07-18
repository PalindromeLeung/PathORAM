Require Import List.
Import ListNotations.

Require Import POram.System.PathORAMDef.
Require Import POram.Utils.Distributions.
Require Import POram.Utils.Classes.

(* for any x in xs and y in ys, P x y holds. *)
Definition All2 {X Y} (P : X -> Y -> Prop)
  (xs : list X) (ys : list Y) : Prop :=
  Forall (fun x => Forall (P x) ys) xs.

Section Equiv.

Context `{C : Config}.

Definition state_equiv (s s' : state) : Prop :=
  forall k v,
    kv_rel k v s <-> kv_rel k v s'.

Definition state_val_equiv {X} (p p' : X * state) : Prop :=
  fst p = fst p' /\
  state_equiv (snd p) (snd p').

Definition dist_equiv {X} (eqv : X -> X -> Prop)
  (d d' : dist X) : Prop :=
  All2 eqv
    (List.map fst (dist_pmf d))
    (List.map fst (dist_pmf d')).

Definition poram_equiv {X} (m m' : Poram X) : Prop :=
  forall s s' : state,
    state_equiv s s' ->
    dist_equiv state_val_equiv (m s) (m' s').

End Equiv.
