module Logic

import Basics
import Data.Nat
import Induction
import Prelude

%hide Basics.Numbers.pred
%hide Basics.Playground2.plus
%hide Prelude.Not

%default total

Injective : {a, b : Type} -> (f : a -> b) -> Type
Injective {a} {b} f = (x, y : a) -> f x = f y -> x = y

succ_inj : Injective S
succ_inj x x Refl = Refl

-- ||| Cojunction
infixl 8 /\
data (/\) : Type -> Type -> Type where
  Conj : p -> q -> p /\ q

and_intro : a -> b -> a /\ b
and_intro = Conj

and_exercise : (n, m : Nat) -> n + m = 0 -> (n = 0) /\ (m = 0)
and_exercise 0 0 prf = Conj prf prf

and_example2 : (n, m : Nat) -> (n = 0) /\ (m = 0) -> n + m = 0
and_example2 Z Z (Conj Refl Refl) = Refl
and_example2 (S _) _ (Conj Refl _) impossible
and_example2 _ (S _) (Conj _ Refl) impossible

and_example2' : (n, m : Nat) -> n = 0 -> m = 0 -> n + m = 0
and_example2' Z Z Refl Refl = Refl
and_example2' (S _) _ Refl _ impossible
and_example2' _ (S _) _ Refl impossible

and_example3 : (n, m : Nat) -> n + m = 0 -> n * m = 0
and_example3 n m prf =
  let (Conj nz _) = and_exercise n m prf in
  rewrite nz in Refl

proj1 : p /\ q -> p
proj1 (Conj x _) = x

proj2 : p /\ q -> q
proj2 (Conj _ y) = y

and_commut : p /\ q -> q /\ p
and_commut (Conj p q) = (Conj q p)

and_assoc : p /\ (q /\ r) -> (p /\ q) /\ r
and_assoc (Conj p (Conj q r)) = (Conj (Conj p q) r)

-- ||| Disjunction
infixl 7 \/
data (\/) : Type -> Type -> Type where
  OrL :  p -> p \/ q
  OrR :  q -> p \/ q

or_example : (n, m : Nat) -> (n = 0) \/ (m = 0) -> n * m = 0
or_example Z _ (OrL Refl) = Refl
or_example (S _) _ (OrL Refl) impossible
or_example n Z (OrR Refl) = multZeroRightZero n
or_example _ (S _) (OrR Refl) impossible

or_intro : a -> a \/ b
or_intro = OrL

zero_or_succ : (n : Nat) -> (n = 0) \/ (n = S (pred n))
zero_or_succ Z = OrL Refl
zero_or_succ (S _) = OrR Refl

mult_eq_0 : {n, m : Nat} -> n * m = 0 -> (n = 0) \/ (m = 0)
mult_eq_0 {n = 0} prf = OrL prf
mult_eq_0 {m = 0} prf = OrR (rewrite sym prf in Refl)
mult_eq_0 {n = S k} {m = S j} prf impossible -- this line is not actually required

or_commut : p \/ q -> q \/ p
or_commut (OrL p) = OrR p
or_commut (OrR q) = OrL q

Not : Type -> Type
Not a = a -> Void

ex_falso_quodlibet : (0 _ : Void) -> p
ex_falso_quodlibet = void

not_implies_our_not : Not p -> (q -> (p -> q))
not_implies_our_not q p = \_ => p

zero_not_one : Not (Z = S _)
zero_not_one = uninhabited

not_False : Not Void
not_False = absurd

contradiction_implies_anything : p /\ Not p -> q
contradiction_implies_anything (Conj p notp) = absurd $ notp p

double_neg : p -> Not $ Not p
double_neg p notp = notp p

contrapositive : (p -> q) -> (Not q -> Not p)
contrapositive pq qv = qv . pq

not_both_true_and_false : Not (p /\ Not p)
not_both_true_and_false (Conj p pv) = pv p

not_true_is_false : (b : Bool) -> Not (b = True) -> b = False
not_true_is_false False h = Refl
not_true_is_false True h = absurd $ h Refl

True_is_true : Unit
True_is_true = ()

namespace MyIff

  public export
  (<->) : (p, q : Type) -> Type
  (<->) p q = (p -> q) /\ (q -> p)
  infixl 3 <->

  iff_sym : (p <-> q) -> (q <-> p)
  iff_sym (Conj pq qp) = (Conj qp pq)

  iff_refl : p <-> p
  iff_refl = (Conj id id)

  iff_trans : (p <-> q) -> (q <-> r) -> (p <-> r)
  iff_trans (Conj pq qp) (Conj qr rq) = Conj (qr . pq) (qp . rq)

  or_distributes_over_and1 : (p \/ (q /\ r)) -> (p \/ q) /\ (p \/ r)
  or_distributes_over_and1 (OrL p) = Conj (OrL p) (OrL p)
  or_distributes_over_and1 (OrR (Conj q r)) = Conj (OrR q) (OrR r)

  or_distributes_over_and2 : (p \/ q) /\ (p \/ r) -> (p \/ (q /\ r))
  or_distributes_over_and2 (Conj (OrL _) (OrL p)) = OrL p
  or_distributes_over_and2 (Conj (OrL p) (OrR _)) = OrL p
  or_distributes_over_and2 (Conj (OrR _) (OrL p)) = OrL p
  or_distributes_over_and2 (Conj (OrR q) (OrR r)) = OrR (Conj q r)

  or_distributes_over_and : (p \/ (q /\ r)) <-> (p \/ q) /\ (p \/ r)
  or_distributes_over_and = Conj or_distributes_over_and1 or_distributes_over_and2

-- ||| Existential Quantification
four_is_even : (n : Nat ** 4 = n + n)
four_is_even = (2 ** Refl)

exists_example_2 : (m : Nat ** n = 4 + m) -> (o : Nat ** n = 2 + o)
exists_example_2 (m ** pf) = (2 + m ** pf)

dist_not_exists : {p : a -> Type} -> ((x : a) -> p x) -> Not (x ** Not $ p x)
dist_not_exists f (x ** pxv) = pxv (f x)

dist_exists_or : {p, q : a -> Type} -> (x ** (p x \/ q x)) <-> ((x ** p x) \/ (x ** q x))
dist_exists_or = Conj dist_exists_or1 ?r
  where
    dist_exists_or1 : (x : a ** p x \/ q x) -> (x : a ** p x) \/ (x : a ** q x)
    dist_exists_or1 (x ** (OrL px)) = OrL (x ** px)
    dist_exists_or1 (x ** (OrR qx)) = OrR (x ** qx)
    dist_exists_or2 : (x : a ** p x) \/ (x : a ** q x) -> (x : a ** p x \/ q x)
    dist_exists_or2 (OrL (x ** px)) = (x ** (OrL px))
    dist_exists_or2 (OrR (x ** qx)) = (x ** (OrR qx))
