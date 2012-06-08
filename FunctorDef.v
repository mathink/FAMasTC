(****************************************************************

   FunctorDef.v

 ****************************************************************)

Require Import "./Util".
Require Export "./TypeModifier".

Set Implicit Arguments.

Module Functor.
  Section FunctorDef.
  
    Variable T: TypeModifier.
    
    Class Functor :=
      {
        fmap {A B: Set}: (A -> B) -> T A -> T B;
        
        fmap_id:
          forall {A: Set}(x: T A),
            fmap (id (A:=A)) x =t= x;
        
        fmap_compose:
          forall {A B C: Set}(f: A -> B)(g: B -> C)(x: T A),
            fmap (g(.)f) x =t= (fmap g (.) fmap f) x
      }.

  End FunctorDef.
End Functor.

