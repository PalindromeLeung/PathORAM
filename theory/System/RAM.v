Require Import Coq.Logic.Eqdep_dec.

Module Type StateMonad.

  Parameter State : forall (S X : Type), Type.

  Parameter ret : forall {S X}, X -> State S X.

  Parameter bind : forall {S X Y}, State S X -> (X -> State S Y) -> State S Y. 

  Parameter get : forall {S}, State S S.

  Parameter put : forall {S}, S -> State S unit.

End StateMonad.

Module Type RAM (M : StateMonad).
  Parameter K : Type.
  Parameter V : Type.

  (* Inner state, specific to implementation *)
  Parameter St : Type.

  (* Wrapped value type, specific to implementation *)
  Parameter Vw : Type -> Type.

  (* Read and write operations *)
  Parameter read : K -> M.State St (Vw V).
  Parameter write : K -> V -> M.State St (Vw V).

  (* RAM laws (TODO maybe add uniform syntax here) *)
  Axiom read_read :
    forall (k : K), 
      M.bind (read k) (fun _ => read k) =
      M.bind (read k) (fun v => M.ret v). 

  (* TODO remaining laws
write(key,value) ; read(key)  == write(key,value) ; return(value) -- read-write law
v1 <- read(key1) ; v2 <- read(key2) ; f(v1,v2) == v2 <- read(key2) ; v1 <- read(key1) ; f(v1,v2) -- read-commute law (doesn't require key1 =/= key2)
v <- read(key1); write(key2,value); f(v) == write(key2,value) ; v <- read(key1) ; f(v) -- read-write-commute law (requires key1 =/= key2)
write(key1,value1) ; write(key2,value2) == write(key2,value2) ; write(key1,value1) -- write-commute law (requires key1 =/= key2)
  *)

  (* TODO how does it relate to lens laws? *)
End RAM.