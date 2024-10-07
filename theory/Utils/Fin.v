
Fixpoint Fin n : Type :=
  match n with
  | 0 => Empty_set
  | S m => unit + Fin m
  end.

Fixpoint Fin_iterate {n} {X} : (Fin n -> X -> X) -> X -> X :=
  match n with
  | 0 => fun f x => x
  | S m => fun f x => f (inl tt) (Fin_iterate (fun j => f (inr j)) x)
  end.
