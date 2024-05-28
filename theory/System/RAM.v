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

  Parameter read : K -> M.State St (Vw V).
  Parameter write : K -> V -> M.State St (Vw V).

  (* TODO laws
  Axiom read_read : ...
  Axiom read_write : ... 
  *)

  (* TODO how does it relate to lens laws? *)
End RAM.