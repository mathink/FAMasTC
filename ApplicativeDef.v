(****************************************************************

   ApplicativeDef.v

 ****************************************************************)

Require Import Util.
Require Export TypeModifier.

Set Implicit Arguments.

Module Applicative.
  Section ApplicativeDef.
  
    Variable T: TypeModifier.
    
    Reserved Notation "A (#) B" (at level 50, left associativity).
    Class Applicative :=
      {
        pure {A: Set}: A -> T A;
        flift {A B: Set}: T (A -> B) -> T A -> T B
          where "A (#) B" := (flift A B);
        
    (* Applicative's law *)
        pure_identity:
          forall {A: Set}(u: T A),
            (pure (id (A:=A))) (#) u =t= u;
        
        pure_composition:
          forall {A B C: Set}(u: T (B -> C))(v: T (A -> B))(w: T A),
            (pure compose) (#) u (#) v (#) w =t= u (#) (v (#) w);

        pure_hom:
          forall {A B: Set}(f: A -> B)(x: A),
            (pure f) (#) (pure x) =t= pure (f x);

        pure_interchange:
          forall {A B: Set}(u: T (A -> B))(x: A),
            u (#) (pure x) =t= (pure (fun f => f x)) (#) u;

        flift_f_subst:
          forall {A B: Set}(u v: T (A -> B))(m: T A),
            u =t= v ->
            u(#)m =t= v(#)m;

        flift_x_subst:
          forall {A B: Set}(u: T (A -> B))(m n: T A),
            m =t= n ->
            u(#)m =t= u(#)n
      }.

  End ApplicativeDef.

  Notation "A (#) B" := (flift A B)
    (at level 50, left associativity).
  Notation "[ F | X , .. , Y ]" := ( .. ((pure F) (#) X) .. (#) Y)
    (at level 50, left associativity).

End Applicative.


