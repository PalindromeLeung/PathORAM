Class Monad (M : Type -> Type) := {
  pure {X} : X -> M X;
  bind {X Y} : M X -> (X -> M Y) -> M Y
  }.

Definition State S X := S -> S * X.

Definition state_pure {S} {X} : X -> State S X :=
  fun x s => (s, x).

Definition state_bind {S} {X Y} : State S X ->
  (X -> State S Y) -> State S Y :=
  fun mx f s =>
    let '(s', x) := mx s in
    f x s'.

Global Instance State_Monad (S : Type) : Monad (State S) := {
  pure := @state_pure S;
  bind := @state_bind S
  }.

Fixpoint Vec X n : Type :=
  match n with
  | 0 => unit
  | S m => X * Vec X m
  end.

(* old-fashioned zipWith for comparison *)
Fixpoint zipWith {X Y Z} {n} (f : X -> Y -> Z) :
  Vec X n -> Vec Y n -> Vec Z n :=
  match n with
  | 0 => fun _ _ => tt
  | S m => fun '(x, xs) '(y, ys) =>
      (f x y, zipWith f xs ys)
  end.

Fixpoint zipWithM {M} `{Monad M} {X Y Z} {n}
  (f : X -> Y -> M Z) {struct n} : Vec X n -> Vec Y n -> M (Vec Z n) :=
  match n with
  | 0 => fun _ _ => pure tt
  | S m => fun '(x, xs) '(y, ys) =>
      bind (f x y) (fun z =>
      bind (zipWithM f xs ys) (fun zs =>
      pure (z, zs)
      ))
  end.

(* alias to distinguish from inputs *)
Definition carry : Type := bool.

Definition full_adder : bool -> bool -> State carry bool :=
  fun b1 b2 c =>
  (orb (andb b1 b2) (andb c (xorb b1 b2)),
   xorb b1 (xorb b2 c)).

Definition adder {n} : Vec bool n -> Vec bool n -> State carry (Vec bool n) :=
  zipWithM full_adder.

Definition test1 : Vec bool 4 := (true, (true, (true, (false, tt)))).
Definition test2 : Vec bool 4 := (true, (false, (false, (false, tt)))).

Compute adder test1 test2 false.