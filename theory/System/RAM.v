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

  (* Wrapped value type, specific to implementation *)
  Parameter Vw : Type -> Type.

  (* Inner implementation of RAM (TODO move or something) *)
  Parameter S : Type.

  (* Well-formedness over inner implementation (TODO move or remove from interface if possible) *)
  Parameter well_formed : S -> Prop.

  (* Read and write operations *)
  Parameter read : K -> M.State S (Vw V).
  Parameter write : K -> V -> M.State S (Vw V).

  (* Get payload *)
  Parameter get_payload : M.state S (Vw V) -> option V.

  (* Wrap value *)
  Parameter wrap : V -> Vw V.

  (* --- RAM laws (TODO maybe add uniform syntax here, and maybe change if not quite right) --- *)
  Axiom read_read :
    forall (k : K) (s : S), 
      well_formed s ->
      get_payload ((M.bind (read k) (fun _ => read k)) s) =
      get_payload ((M.bind (read k) (fun v => M.ret v)) s). 

  Axiom read_write :
    forall (k : K) (v : V) (s : S),
      well_formed s ->
      get_payload ((M.bind (write k v) (fun _ => read k)) s) =
      get_payload ((M.bind (write k v) (fun _ => M.ret (wrap v))) s).

  Axiom read_write_commute :
    forall (k1 k2 : K) (v : V) f (s : S),
      well_formed s ->
      k1 <> k2 ->
      get_payload (M.bind (read k1) (fun v' => M.bind (write k2 v) (fun _ => f v')) s) =
      get_payload (M.bind (write k2 v) (fun _ => M.bind (read k1) f) s).

  (* TODO remaining laws
v1 <- read(key1) ; v2 <- read(key2) ; f(v1,v2) == v2 <- read(key2) ; v1 <- read(key1) ; f(v1,v2) -- read-commute law (doesn't require key1 =/= key2)
write(key1,value1) ; write(key2,value2) == write(key2,value2) ; write(key1,value1) -- write-commute law (requires key1 =/= key2)
  *)

  (* TODO how does it relate to lens laws? *)
End RAM.