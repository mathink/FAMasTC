(****************************************************************

   TypeModifier.v

 ****************************************************************)

Require Export "./Relations".
Export Relation.

Set Implicit Arguments.

Record TypeModifier: Type :=
  {
    tm_modify:> Set -> Set;
    tm_equivalence {A: Set}: Equivalence (tm_modify A)
  }.

Notation "A =t= B" := (equiv_eq (Equivalence:=tm_equivalence _) A B)
  (at level 70, no associativity).

