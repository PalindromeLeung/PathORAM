
Module Type Magic.
  Parameter LEVEL : nat.
  Parameter nodesTotal : nat.
  Parameter nodeCap : nat.
End Magic.

Module MyModule (m : Magic).
  Definition foo := S m.LEVEL.

  Lemma foo_is_OK: foo > 0.
  Proof.
    intros. unfold foo. auto with arith.
  Qed.
    
End MyModule.

Module Magic3 <: Magic.
  Definition LEVEL := 3.
  Definition nodesTotal := 60.
  Definition nodeCap := 4.
End Magic3.

Module MyModule3 := MyModule(Magic3).

Eval compute in MyModule3.foo.
Check MyModule3.foo_is_OK.
