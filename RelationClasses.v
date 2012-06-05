(****************************************************************

   RelationClasses.v

 ****************************************************************)


Module Relation.

  Definition relation (A: Set) := A -> A -> Prop.

  Section BasicProperties.

    Class Reflexive {A: Set}(R: relation A) :=
      Reflexivity: forall x: A, R x x.
    
    Class Symmetric {A: Set}(R: relation A) :=
      Symmetry: forall x y: A, R x y -> R y x.
    
    Class Transitive {A: Set}(R: relation A) :=
      Transitivity: forall x y z: A, R x y -> R y z -> R x z.

    Class Antisymmetric {A: Set}(R: relation A) :=
      Antisymmetry: forall x y: A, R x y -> R y x -> x = y.


    Class PreOrder (A: Set) :=
      {
        preord_ord: relation A;
        preord_refl:> Reflexive preord_ord;
        preord_trans:> Transitive preord_ord
      }.
    Definition PseudoOrder := PreOrder.
    
    Class PartialOrder (A: Set) :=
      {
        pord_ord: relation A;
        pord_refl:> Reflexive pord_ord;
        pord_trans:> Transitive pord_ord;
        pord_antisym:> Antisymmetric pord_ord
      }.
    
    Class Equivalence (A: Set) :=
      {
        equiv_eq: relation A;
        equiv_refl:> Reflexive equiv_eq;
        equiv_sym:> Symmetric equiv_eq;
        equiv_trans:> Transitive equiv_eq
      }.

  End BasicProperties.
  
  Implicit Arguments pord_ord [[A] [PartialOrder]].
  Notation "A <= B" := (pord_ord A B) (at level 70, no associativity).

  Implicit Arguments equiv_eq [[A] [Equivalence]].
  Notation "A == B" := (equiv_eq A B) (at level 80, no associativity).

End Relation.

Section eq_Equivalence.
  Import Relation.

  Program Instance eq_Reflexive (A: Set): Reflexive (eq (A:=A)).
  Next Obligation.
    reflexivity.
  Qed.
  
  Program Instance eq_Symmetric (A: Set): Symmetric (eq (A:=A)).
  Next Obligation.
    intros A x y Heq; subst.
    reflexivity.
  Qed.
  
  Program Instance eq_Transitive (A: Set): Transitive (eq (A:=A)).
  Next Obligation.
    intros A x y z Heqxy Heqyz; subst.
    reflexivity.
  Qed.
  
  Program Instance eq_Equivalence (A: Set): Equivalence A :=
    {
      equiv_eq := eq (A:=A)
    }.
End eq_Equivalence.  
