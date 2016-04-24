From mathcomp.ssreflect Require Import ssreflect eqtype.
Require Import Common Functor.
Require Import Coq.Logic.FunctionalExtensionality.

Inductive exprf a :=
| add : a -> a -> exprf a
| lit: nat -> exprf a.


Definition Algebra (F:functor) (a:Type)  := F a -> a.
Definition CoAlgebra (F:functor) (a:Type)  := F a -> a.

Definition exprf_fmap {A B} (f: A->B) (e: exprf A) :exprf B :=
  match e with
                 | add x x0 => add _ (f x) (f x0)
                 | lit x => lit _ x
  end.

Definition functor_exprf_mixin : Functor.mixin_of exprf.  refine ( FunctorMixin exprf (@exprf_fmap) _ _ ).  done.  move=> A B C f g.  extensionality e.  elim: e f g; by intros.  Defined.

Canonical ExprFFunctor := Functor exprf functor_exprf_mixin.

Definition eval: Algebra ExprFFunctor nat := 
  fun e=> match e with
            | add x y => x + y
            | lit x => x
          end.

(* I can't think of another way of expressing fixpoint *)

Inductive expr := In { Out: exprf expr }.
Definition Expr := In.
Definition ex := Expr ( add _ (Expr $ lit _ 4) (Expr $ lit _ 8)).

Definition expr_cata {T} (e: expr) (alg:Algebra ExprFFunctor T) : T :=
  
  