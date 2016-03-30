From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun.

Module Functor.
  Section RawMixin.
  Variable F:Type->Type.

  Record mixin_of:=
    Mixin {
        fmap_op {A B}: (A->B)-> F A -> F B;
        _ T: @fmap_op T T \o id = @fmap_op T T;
        _ {A B C: Type} (f:A->B) (g:B->C): (fmap_op g) \o (fmap_op f) = fmap_op (g \o f)
      }
  .
  End RawMixin.

  Section Packing.
    Structure pack_functor: Type := Pack {type:Type->Type; _ : mixin_of type}.
    Local Coercion type: pack_functor >-> Funclass.

    Variable Pk: pack_functor.
    Parameter F:Type->Type.

    Definition functor_struct : mixin_of Pk :=
      let: Pack _ c := Pk return mixin_of Pk in c.

    Definition fmap := @fmap_op _ functor_struct.
  End Packing.

  Module Exports.

    Notation functor := pack_functor.
    Notation FunctorMixin := Mixin.
    Notation Functor T m := (@Pack T m).
    Notation "f <$> x" := (fmap f x) (at level 43, left associativity).
    Coercion type: pack_functor >-> Funclass.
    Notation fmap := (fmap _ _ _).
  End Exports.

  End Functor.

Export Functor.Exports.
