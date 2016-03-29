From mathcomp.ssreflect Require Import ssrfun.
Require Import Functor.
Require Import Common.
Module Applicative.
  Section RawMixin.
    
    Record mixin_of (F:functor) :=
      Mixin {
          op_pure {A}:
            A -> F A;
          op_star {A B}:
            F (A->B) -> F A -> F B;

          law_identity {A}:
            @op_star A A (op_pure id) = id;

          law_homomorphism A B (f:A->B) (x:A):
            op_star (op_pure f) (op_pure x) = op_pure (f x);
          
          law_intercharge A B (u: F (A -> B) ) (y : A) :
            op_star u (op_pure y) = op_star (op_pure  (fun f=> f y) ) u;

          law_composition a c b (u: F (c -> b))  (v: F (a -> c)) (w:  F a ):
            op_star (
                op_star (
                    op_star (
                        op_pure (fun f g x=> f (g x)))
                            u)
                        v)
                    w = op_star u (op_star v w)
        }.
  End RawMixin.

  Section Packing.
    Structure pack_applicative: Type := Pack {type: functor ; _ : mixin_of type}.
    Local Coercion type: pack_applicative >-> Functor.pack_functor.

  End Packing.


  Module Exports.
    Notation applicative := pack_applicative.
    Notation ApplicativeMixin := Mixin.
    Notation Applicative T m := (@Pack T m).
    Notation "x <*> y" := (op_star x y) (at level 43, left associativity) .
    Notation pure := op_pure.
    Notation star := op_star.
    Local Coercion type: pack_applicative >-> Functor.pack_functor.
  End Exports.
End Applicative.

Export Applicative.Exports. 