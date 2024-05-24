Require Import Coq.Logic.Eqdep_dec.

Module Type RAM.
  (* TODO tweak to have monadic stuff 
     so we can reference in the spec *)
  Parameter K : Type.
  Parameter V : Type.
  Parameter state : Type -> Type.

  Parameter read : K -> state V.
  Parameter write : K -> V -> state V.

  (* TODO laws
  Axiom read_read : ...
  Axiom read_write : ... 
  *)
End RAM.