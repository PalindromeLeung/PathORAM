Require Import Coq.Logic.Eqdep_dec.

Module Type RAM.
  Parameter K : Type.
  Parameter V : Type.
  Parameter state : Type -> Type.

  Parameter read : K -> state V.
  Parameter write : K -> V -> state V.
End RAM.