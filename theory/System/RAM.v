Require Import Coq.Logic.Eqdep_dec.

Module Type StateMonad.

  Parameter state : forall (S X : Type), Type.

  Definition State (S X : Type) := S -> state S X.

  Parameter ret : forall {S X : Type}, X -> State S X.

  Parameter bind : forall {S X Y}, State S X -> (X -> State S Y) -> State S Y. 

  Parameter get : forall {S}, State S S.

  Parameter put : forall {S}, S -> State S unit.

End StateMonad.

Module Type RAM (M : StateMonad).
  Parameter K : Type.
  Parameter V : Type.

  (* Inner implementation of RAM (TODO move or something) *)
  Parameter S : Type.

  (* Well-formedness over inner implementation (TODO move or remove from interface if possible) *)
  Parameter well_formed : S -> Prop.

  (* Read and write operations *)
  Parameter read : K -> M.State S V.
  Parameter write : K -> V -> M.State S unit.

  Parameter equiv : forall {X},
    M.State S X -> M.State S X -> Prop.

  (* I *)
  Axiom read_write : forall k ,
    equiv
      (M.ret tt)
      (M.bind (read k) (fun v => write k v)).

  (* II *)
  Axiom write_read : forall k v,
    equiv
      (M.bind (write k v) (fun _ => M.ret v))
      (M.bind (write k v) (fun _ => read k)).

  (* III *)
  Axiom read_read : forall (k : K),
    equiv
      (M.bind (read k) (fun v => M.ret v))
      (M.bind (read k) (fun _ => read k)).

  (* IV *)
  Axiom read_commute : forall (k1 k2 : K),
    equiv
      (M.bind (read k1) (fun v1 =>
        M.bind (read k2) (fun v2 =>
        M.ret (v1, v2))))
      (M.bind (read k2) (fun v2 =>
        M.bind (read k1) (fun v1 =>
        M.ret (v1, v2)))).

  (* V *)
  Axiom read_write_commute : forall (k1 k2 : K) (v2 : V),
    k1 <> k2 ->
    equiv
      (M.bind (read k1) (fun v1 =>
        M.bind (write k2 v2) (fun _ =>
        M.ret v1)))
      (M.bind (write k2 v2) (fun _ =>
        M.bind (read k1) (fun v1 =>
        M.ret v1))).

  (* VI *)
  Axiom write_commute : forall (k1 k2 : K) (v1 v2 : V),
    k1 <> k2 ->
    equiv
      (M.bind (write k1 v1) (fun _ =>
        write k2 v2))
      (M.bind (write k2 v2) (fun _ =>
        write k1 v1)).

  (* VII *)
  Axiom write_absorb : forall (k : K) (v v' : V),
    equiv
      (M.bind (write k v) (fun _ => write k v'))
      (write k v').

End RAM.
