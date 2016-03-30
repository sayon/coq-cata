From mathcomp.ssreflect Require Import ssreflect eqtype.
Require Import Common Functor.
Require Import Coq.Logic.FunctionalExtensionality.

Inductive expr a :=
| add : a -> a -> expr a
| lit: a -> expr a.
(*


Axiom atfix: exists t, expr t = t.

Fixpoint algebra (e: expr nat) : nat :=
  match e with
    | add  x y => x + y
    | lit x => x
  end.*)


Definition Algebra (F:functor) (a:Type)  := F a -> a.
Definition CoAlgebra (F:functor) (a:Type)  := F a -> a.

Definition expr_fmap {A B} (f: A->B) (e: expr A) :expr B :=
  match e with
                 | add x x0 => add _ (f x) (f x0)
                 | lit x => lit _ $ f x
  end.

Definition functor_expr_mixin : Functor.mixin_of expr.
  refine ( FunctorMixin expr (@expr_fmap) _ _ ).
  done.
  move=> A B C f g.
  extensionality e.
  elim: e f g; by intros.
Defined.

Canonical ExprFunctor := Functor expr functor_expr_mixin.

Definition eval: Algebra expr.
  

               
  

CoFixpoint tfix {a: Type} (t:a->expr a) : a := t (tfix t).

                               | 
CoInductive iterate (f:Type->Type): 
Fixpoint Mu (f:forall A: A->A) := f (Mu f).