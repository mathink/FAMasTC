(****************************************************************

   Utilities.

 ****************************************************************)

Definition compose {A B C: Set}(g: B -> C)(f: A -> B) := fun x => g (f x).
Notation "A '(.)' B" := (compose A B) (at level 50, left associativity).

