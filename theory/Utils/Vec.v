
Fixpoint vec n X : Type :=
  match n with
  | 0 => unit
  | S m => X * vec m X
  end.
