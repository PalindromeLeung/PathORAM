Require Import List.
Import ListNotations.
Require Import  POram.System.PathORAM_typeclass.
Require Import  ExtLib.Data.Monads.StateMonad ExtLib.Structures.Monads.

Definition state_lift {S X} (Pre Post : S -> Prop)
  (P : X -> Prop) : state S X -> Prop :=
  fun f => forall s, Pre s ->
    P (fst (runState f s)) /\ Post (snd (runState f s)).

Lemma weaken_lemma {S X}
  {Pre : S -> Prop}
  (Post : S -> Prop)
  {Post' : S -> Prop}
  (P : X -> Prop)
  {P' : X -> Prop}
  (m : state S X) :
  (forall s, Post s -> Post' s) ->
  (forall x, P x -> P' x) ->
  state_lift Pre Post P m ->
  state_lift Pre Post' P' m.
Proof.
  intros HPostPost' HPP' Hm s Hs.
  split.
  - apply HPP'.
    now apply Hm.
  - apply HPostPost'.
    now apply Hm.
Qed.

Lemma ret_lemma {S X}
  {Pre : S -> Prop}
  {P : X -> Prop}
  {x : X} :
  P x ->
  state_lift Pre Pre P (ret x).
Proof.
  simpl.
  intros p st; simpl.
  tauto.
Qed.

Lemma bind_lemma {S X Y}
  {Pre : S -> Prop}
  (Mid : S -> Prop)
  {Post : S -> Prop}
  (P : X -> Prop)
  {Q : Y -> Prop}
  {mx : state S X}
  {f : X -> state S Y} :
  state_lift Pre Mid P mx ->
  (forall x, P x -> state_lift Mid Post Q (f x)) ->
  state_lift Pre Post Q (bind mx f).
Proof.
  intros Hmx Hf s Hs.
  destruct (Hmx s Hs) as [HP HMid].
  destruct (Hf _ HP _ HMid).
  unfold bind.
  simpl; destruct (runState mx s); simpl in *; now split.
Qed.

Lemma get_lemma {S}
  {Pre : S -> Prop} :
  state_lift Pre Pre Pre get.
Proof.
  intros s; simpl.
  tauto.
Qed.

Lemma put_lemma {S}
  {Pre Pre' : S -> Prop}
  {s : S} :
  Pre' s ->
  state_lift Pre Pre' (fun _ => True) (put s).
Proof.
  intros Hs s' _; simpl.
  tauto.
Qed.

Section ORAM_STATE.

Record orState (n l : nat) : Type := ORState
  { state_position_map : position_map
  ; state_stash : stash
  ; state_oram : oram
  }.

End ORAM_STATE.
