(****************************************************************

   MonadDef.v

 ****************************************************************)

Require Import Util.
Require Export TypeModifier.

Set Implicit Arguments.

Module Monad.
  Section MonadDef.
  
    Variable T: TypeModifier.

    Reserved Notation "x >>= y" (at level 60, no associativity).
    Class Monad :=
      {
        ret {A: Set}: A -> T A;
        
        bind {A B: Set}: (A -> T B) -> T A -> T B
          where "x >>= y" := (bind y x);
        
        unit_left:
          forall (A B: Set)(f: A -> T B)(a: A),
            (ret a) >>= f =t= f a;
        unit_right:
          forall (A: Set)(m: T A),
            m >>= ret =t= m;
        assoc:
          forall (A B C: Set)(f: A -> T B)(g: B -> T C)(m: T A),
            (m >>= f >>= g) =t= m >>= (fun x => (f x) >>= g);

        bind_subst:
          forall (A B: Set)(m m': T A)(f f': A -> T B),
            m =t= m' ->
            (forall a: A, f a =t= f' a) ->
            m >>= f =t= m' >>= f'
      }.

    Implicit Arguments ret [Monad [A]].
    Implicit Arguments bind [Monad A B].

  End MonadDef.

  Notation "^| A" := (ret A)
    (at level 0, no associativity): monad_scope.
  Notation "x >>= y" := (bind y x)
    (at level 60): monad_scope.
  
  Open Scope monad_scope.
  
  Notation "x >> y" := (x >>= fun _ => y)
    (at level 55, right associativity): monad_scope.
  Notation "x <- y ; z" := (y >>= (fun x => z))
    (at level 60, right associativity): monad_scope.
  Notation " x :[ A ] <- y ; z" := (y >>= (fun x: A => z))
    (at level 60, right associativity): monad_scope.


  Ltac apply_sym e := apply Symmetry; apply e.
  Ltac eapply_sym e := apply Symmetry; eapply e.
  Ltac rewrite_assoc_l :=
    eapply Transitivity; [apply assoc |].
  Ltac rewrite_assoc_r :=
    eapply Transitivity; [| apply assoc].
  Ltac rewrite_assoc_inv_l :=
    eapply Transitivity; [apply Symmetry; apply assoc |].
  Ltac rewrite_assoc_inv_r :=
    eapply Transitivity; [| apply Symmetry; apply assoc].

End Monad.

Section MonadProp.
  Import Monad.

  Context `{mon: Monad}.
  
  Definition skip: T unit := ret tt.
  
  Lemma skip_inv:
    forall {A: Set}(m: T A),
      skip >> m =t= m.
  Proof.
    unfold skip.
    intros.
    apply unit_left.
  Qed.
  
  Lemma ret_bind:
    forall {A B: Set}(a: A)(f: A -> T B),
      x:[A] <- ret a; f x =t= (fun x: A => f x) a.
  Proof.
    intros.
    apply unit_left.
  Qed.

  Lemma bind_ret:
    forall {A B: Set}(m: T A)(a: A)(f: A -> T B),
      ret a =t= m ->
      x <- m; f x =t= f a.
  Proof.
    intros A B m a f Heq.
    apply Symmetry in Heq.
    eapply Transitivity.
    apply bind_subst.
    apply Heq.
    intro; apply Reflexivity.
    apply unit_left.
  Qed.

  Corollary bind_m_subst:
    forall (A B: Set)(m m': T A)(f: A -> T B),
      m =t= m' ->
      m >>= f =t= m' >>= f.
  Proof.
    intros.
    apply bind_subst with (f':=f);
      [| intro; apply Reflexivity].
    apply H.
  Qed.

  Corollary bind_f_subst:
    forall (A B: Set)(m: T A)(f f': A -> T B),
      (forall a: A, f a =t= f' a) ->
      m >>= f =t= m >>= f'.
  Proof.
    intros.
    apply bind_subst with (m':=m);
      [apply Reflexivity |].
    apply H.
  Qed.

End MonadProp.
