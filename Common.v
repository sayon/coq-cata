From mathcomp.ssreflect Require Import ssreflect ssrnat ssrbool eqtype seq ssrnat.
From mathcomp.algebra Require Import ssrint.


(*** Quality of life *)
Definition _dollar {Tx Ty} (x:Tx->Ty) (v:Tx) := x v.
Transparent _dollar.

Notation "x $ y" := (@_dollar _ _ x y) (at level 100, right associativity) :core_scope.
Hint Transparent _dollar.
Hint Unfold _dollar.

Definition cast {A B : Type} (a: A ) (H: A= B ) : B. rewrite <- H. exact a. Defined.
Notation "/! x" := (cast x _) (at level 100, no associativity).




(*** Decidable quality and reflect *)
Definition eq_dec T := forall x y: T, {x = y} + {~ x = y}.
Scheme Equality for nat.
Scheme Equality for unit.

Definition reflect_from_dec {T} (cmp: eq_dec T): (@Equality.axiom T (fun x y => if cmp x y then true else false) ).
  rewrite /Equality.axiom. move=> x y.  
  move: (cmp x y) => [] //=; by constructor.
Qed.

Definition to_cmp {T} {E:eqType} (f: T-> E) (x y: T) := f x == f y .
Notation "//= f , .. , z // " := ( cons (to_cmp f) .. (cons  (to_cmp z) nil)  .. ).
Definition cmp_with {T:Type} (fs: seq (T->T->bool) ) (x y: T) := all (fun f=> f x y) fs.

Definition dec_from_reflect {T:eqType} (Hr: forall (x y:T), reflect (x=y) (x==y)) : eq_dec T.
  rewrite /eq_dec.
  move=> x y.  case: ( Hr x y ); by [apply left | apply right]. Defined.

Definition int_eq_dec := @dec_from_reflect int_eqType (@eqP int_eqType).



(*** seq helpers *)
Fixpoint  zipwith_when_eqlength {A B} (f: A->B->bool) (x: seq A) (y: seq B) : bool :=
  match x,y with
    | x::xs, y::ys => f x y &&  zipwith_when_eqlength f xs ys
    | nil, nil => true
    | nil, _ | _, nil => false
  end.     