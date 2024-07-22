Require Import List.
Import ListNotations.

Require Import POram.System.PathORAMDef.
Require Import POram.Utils.Distributions.
Require Import POram.Utils.Classes.
Import MonadNotation.
Require Import POram.System.PathORAMFunCorrect.
Require Import POram.System.Equiv.

Section EquivProofs.

Context `{C : Config}.

Definition snd_eq {X Y} (p1 p2 : X * Y) : Prop :=
  snd p1 = snd p2.

Lemma read_access_lawful (id : block_id) :
  lawful snd_eq (read_access id).
Proof.
Admitted.

Lemma write_access_lawful (id : block_id) (v : nat) :
  lawful snd_eq (write_access id v).
Proof.
Admitted.

Definition read id : Poram nat :=
  map snd (read_access id).

Definition write id v : Poram nat :=
  map snd (write_access id v).

Theorem write_read : forall k v,
  poram_equiv
  eq
  (write k v;; read k) 
  (write k v;; mreturn v).
Proof.
Admitted.

End EquivProofs.

