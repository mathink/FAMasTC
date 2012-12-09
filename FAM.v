(****************************************************************

   FAM.v
   -- Functor > Applicative > Monad

 ****************************************************************)

Add LoadPath "." as FAM.

Require Import "./Util".
Require Import "./FunctorDef".
Require Import "./ApplicativeDef".
Require Import "./MonadDef".

Set Implicit Arguments.

Section FAM.
  Import Functor.
  Import Applicative.
  Import Monad.

  Program Instance ApplicativeFunctor `(ap: Applicative): Functor T :=
    {
      fmap A B f x := [f | x]
    }.
  Next Obligation.
    intros T ap A x.
    apply pure_identity.
  Qed.
  Next Obligation.
    intros T ap A B C f g x.
    unfold compose.
    eapply Transitivity; [| apply pure_composition].
    eapply Transitivity.
     eapply flift_f_subst.
     replace (fun x0: A => g (f x0)) with ((compose g) f).
      apply Symmetry.
      apply pure_hom.

      unfold compose.
      reflexivity.
     eapply Transitivity.
      eapply flift_f_subst.
      eapply flift_f_subst.
      apply Symmetry.
      apply pure_hom.

      apply Reflexivity.
  Qed.


  Program Instance MonadApplicative `(mon: Monad): Applicative T :=
    {
      pure A a := ret a;
      flift A B mf ma := a <- ma; f <- mf; ^|(f a)
    }.
  Next Obligation.
    intros T mon A u.
    eapply Transitivity; [apply bind_f_subst; intro |].
     eapply Transitivity; [apply unit_left |].
     unfold id.
     apply Reflexivity.

     apply unit_right.
  Qed.
  Next Obligation.
    intros T mon A B C u v w.
    rewrite_assoc_inv_r.
    simpl.
    apply bind_f_subst; intro a.
    rewrite_assoc_l.
    simpl.
    rewrite_assoc_inv_r.
    simpl.
    apply bind_f_subst; intro f.
    rewrite_assoc_l.
    simpl.
    apply Symmetry.
    eapply Transitivity; [apply unit_left |].
    rewrite_assoc_inv_r.
    simpl.
    apply bind_f_subst; intro g.
    rewrite_assoc_inv_r.
    simpl.
    apply Symmetry.
    eapply Transitivity; [apply unit_left |].
    eapply Transitivity; [apply unit_left |].
    eapply Transitivity; [apply unit_left |].
    unfold compose.
    apply Reflexivity.
  Qed.
  Next Obligation.
    intros T mon A B f x.
    eapply Transitivity; [apply unit_left |].
    eapply Transitivity; [apply unit_left |].
    apply Reflexivity.
  Qed.
  Next Obligation.
    intros T mon A B u x.
    eapply Transitivity; [apply unit_left |].
    apply bind_f_subst; intro f.
    apply Symmetry.
    eapply Transitivity; [apply unit_left |].
    simpl.
    apply Reflexivity.
  Qed.
  Next Obligation.
    intros T mon A B u v m Heq.
    apply bind_f_subst; intro.
    apply (bind_m_subst _ _ _ _ Heq).
  Qed.
  Next Obligation.
    intros T mon A B u m n Heq.
    apply (bind_m_subst _ _ _ _ Heq).
  Qed.
  
  
  Program Instance MonadFunctor `(monad: Monad): Functor T :=
    {
      fmap A B f x := a <- x; ret (f a)
    }.
  Next Obligation.
    intros T mon A x.
    unfold id.
    eapply Transitivity; [apply bind_f_subst; intro |].
     apply Reflexivity.
     
     apply unit_right.
  Qed.
  Next Obligation.
    intros T mon A B C f g x.
    unfold compose.
    rewrite_assoc_inv_r.
    simpl.
    apply Symmetry.
    eapply Transitivity; [apply bind_f_subst; intro |].
    eapply Transitivity.
     apply unit_left.
     apply Reflexivity.
   
     simpl.
     apply Reflexivity.
  Qed.


  Program Instance MonadApplicativeFunctor `(monad: Monad): Functor T :=
    ApplicativeFunctor (MonadApplicative monad).


  Lemma MF_MAF_equiv:
    forall `(monad: Monad){A B: Set}(f: A -> B)(m: T A),
      fmap (Functor:=MonadFunctor monad) f m =t= fmap (Functor:=MonadApplicativeFunctor monad) f m.
  Proof.
    unfold fmap.
    simpl.
    intros.
    apply bind_f_subst; intro a.
    apply Symmetry.
    eapply Transitivity.
     apply unit_left.
     
     apply Reflexivity.
  Qed.

End FAM.

