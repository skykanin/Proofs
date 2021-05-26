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

and_intro : a -> b -> (a, b)
and_intro = MkPair

and_exercise : (n, m : Nat) -> n + m = 0 -> (n = 0, m = 0)
and_exercise 0 0 prf = (prf, prf)

and_example2 : (n, m : Nat) -> (n = 0, m = 0) -> n + m = 0
and_example2 Z Z (Refl, Refl) = Refl
and_example2 (S _) _ (Refl, _) impossible
and_example2 _ (S _) (_ , Refl) impossible

and_example2' : (n, m : Nat) -> n = 0 -> m = 0 -> n + m = 0
and_example2' Z Z Refl Refl = Refl
and_example2' (S _) _ Refl _ impossible
and_example2' _ (S _) _ Refl impossible

and_example3 : (n, m : Nat) -> n + m = 0 -> n * m = 0
and_example3 n m prf =
  let (nz, _) = and_exercise n m prf in
  rewrite nz in Refl

proj1 : (p, q) -> p
proj1 = fst

and_commut : (p, q) -> (q, p)
and_commut (p, q) = (q, p)

and_assoc : (p, (q, r)) -> ((p, q), r)
and_assoc (p, (q, r)) = ((p, q), r)

or_example : (n, m : Nat) -> (n = 0) `Either` (m = 0) -> n * m = 0
or_example Z _ (Left Refl) = Refl
or_example (S _) _ (Left Refl) impossible
or_example n Z (Right Refl) = multZeroRightZero n
or_example _ (S _) (Right Refl) impossible

or_intro : a -> a `Either` b
or_intro = Left

zero_or_succ : (n : Nat) -> (n = 0) `Either` (n = S (pred n))
zero_or_succ Z = Left Refl
zero_or_succ (S _) = Right Refl

mult_eq_0 : {n, m : Nat} -> n * m = 0 -> (n = 0) `Either` (m = 0)
mult_eq_0 {n = 0} prf = Left prf
mult_eq_0 {m = 0} prf = Right (rewrite sym prf in Refl)
mult_eq_0 {n = S k} {m = S j} prf impossible -- this line is not actually required

or_commut : p `Either` q -> q `Either` p
or_commut (Left p) = Right p
or_commut (Right q) = Left q

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

contradiction_implies_anything : (p, Not p) -> q
contradiction_implies_anything (p, notp) = absurd $ notp p

double_neg : p -> Not $ Not p
double_neg p notp = notp p

contrapositive : (p -> q) -> (Not q -> Not p)
contrapositive pq qv = qv . pq

not_both_true_and_false : Not (p, Not p)
not_both_true_and_false (p, pv) = pv p
