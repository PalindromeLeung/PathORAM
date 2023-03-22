Class Monad(M : Type -> Type) := {
    pure {X} : X -> M X;
    bind {X Y} : M X -> (X -> M Y) -> M Y
  }.



Definition State S X := S * X.
Definition statePure {S} {X} : State S X := fun sigma => (sigma, X).

