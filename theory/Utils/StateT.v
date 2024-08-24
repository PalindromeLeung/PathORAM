Require Import POram.Utils.Classes.
Import MonadNotation.

Definition StateT (S : Type) (M : Type -> Type) (X : Type) : Type :=
  S -> M (X * S)%type.

Definition StateT_ret {S} {M} `{Monad M} {X} :
  X -> StateT S M X :=
  fun x s => mreturn (x, s).

Definition StateT_bind {S} {M} `{Monad M} {X Y} :
  StateT S M X ->
  (X -> StateT S M Y) ->
  StateT S M Y :=
  fun mx f s =>
    mbind (mx s) (fun '(x, s') => f x s').

Global Instance StateT_Monad {M} {S} `{Monad M} : Monad (StateT S M) := {|
  mreturn A := StateT_ret;
  mbind X Y := StateT_bind
  |}.

Definition get {S M} `{Monad M}: StateT S M S :=
  fun s => mreturn(s,s). 

Definition put {S M} `{Monad M} (st : S) :
  StateT S M unit := fun s => mreturn(tt, st).

Definition liftT {S M} `{Monad M} {A} (m : M A) : StateT S M A :=
    fun st =>
    a <- m ;; mreturn (a, st).

Definition state_plift {S} {M} `{Monad M} `{PredLift M} {X} (Pre Post : S -> Prop) (P : X -> Prop) :
  StateT S M X -> Prop :=
  fun mx =>
    forall s, Pre s -> plift (fun '(x, s') => P x /\ Post s') (mx s).

(* similar but relates state to value *)
Definition state_plift_val {S} {M} `{Monad M} `{PredLift M} {X} (Pre : S -> Prop)
  (Post : S -> X -> Prop) :
  StateT S M X -> Prop :=
  fun mx =>
    forall s, Pre s -> plift (fun '(x, s') => Post s' x) (mx s).

(*
 * state_prob_bind is analogous to the sequencing rule in Hoare Logic
 *)
Lemma state_plift_bind {S X Y} {M} `{Monad M} `{PredLift M} {Pre : S -> Prop}
      (Mid : S -> Prop) {Post : S -> Prop} (P: X -> Prop) {Q: Y -> Prop}
      {mx : StateT S M X} {f : X -> StateT S M Y} : 
  state_plift Pre Mid P mx ->
  (forall x, P x -> state_plift Mid Post Q (f x)) ->
  state_plift Pre Post Q (mbind mx f).
Proof.
  intros.
  unfold state_plift. intros.
  eapply plift_bind; eauto.
  intros.
  destruct x.
  apply H3; tauto.
Qed.

Lemma state_plift_ret {S X} {M} `{Monad M} `{PredLift M} {Pre : S -> Prop} {P : X -> Prop} {x : X}:
  P x -> state_plift Pre Pre P (mreturn x).
Proof.
  intros.
  unfold state_plift. intros.
  apply plift_ret.
  split; auto.
Qed.

Lemma state_plift_get {S} {M} `{Monad M} `{PredLift M} {Pre : S-> Prop} :
  state_plift Pre Pre Pre get.
Proof.
  intros s Hs.
  apply plift_ret.
  split; auto.
Qed.

Lemma state_plift_put {S} {M} `{PredLift M} {Pre Pre' : S -> Prop} : forall s,
  Pre' s -> state_plift Pre Pre' (fun _ => True) (put s).
Proof.
  intros s Hs ? ?.
  apply plift_ret.
  split; auto.
Qed.

Lemma state_plift_liftT {S} {M} `{PredLift M} {Pre : S -> Prop}
  {X} {P : X -> Prop} : forall (m : M X),
  plift P m ->
  state_plift Pre Pre P (liftT m).
Proof.
  intros m Hm.
  intros s Hs.
  eapply plift_bind; eauto.
  intros x Hx.
  apply plift_ret.
  split; auto.
Qed.

Lemma state_plift_weaken {S} {M} `{PredLift M} {X}
  {Pre : S -> Prop} (Post : S -> Prop) {Post' : S -> Prop}
  (P : X -> Prop) :
  has_weakening M -> forall m,
  (forall s, Post s -> Post' s) ->
  state_plift Pre Post P m ->
  state_plift Pre Post' P m.
Proof.
  intros HM m HPostPost' Hm s Hs.
  eapply HM; [| apply Hm; auto].
  intros [x s'] [Hx Hs']; auto.
Qed.
