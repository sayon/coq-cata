From mathcomp.ssreflect Require Import ssreflect ssrfun seq.
Require Import Coq.Logic.FunctionalExtensionality.
 
Require Import Functor.
Require Import Applicative.

Program Definition seq_functor_mixin : Functor.mixin_of seq . 
refine (FunctorMixin seq (@map) _ _ ) =>//=.
- move=> A B C f g.
  extensionality s.
  elim s =>//=.
  move=> a l IH.
  by rewrite IH.
Defined.

Canonical ListFunctor := Functor seq seq_functor_mixin.

Definition example := [:: 1; 2; 3].
