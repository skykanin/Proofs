module Induction

import Basics as B
import Prelude.Interfaces
import Prelude.Nat

%access public export
%default total

plus_n_Z : (n : Nat) -> n = n + 0
plus_n_Z Z = Refl
plus_n_Z (S k) = 
  let inductiveHypothesis = plus_n_Z k in
    rewrite inductiveHypothesis in Refl

minus_diag : (n : Nat) -> minus n n = 0
minus_diag Z = Refl
minus_diag (S k) = minus_diag k

mult_0_r : (n : Nat) -> n * 0 = 0
mult_0_r Z = Refl
mult_0_r (S k) =
  let iH = mult_0_r k in
    rewrite iH in Refl
    
plus_n_Sm : (n, m : Nat) -> S (n + m) = n + (S m)
plus_n_Sm Z m = Refl
plus_n_Sm (S k) m =
  let iH = plus_n_Sm k m in 
  rewrite iH in 
  rewrite plus_n_Z k in Refl

plus_comm : (n, m : Nat) -> n + m = m + n
plus_comm Z m = rewrite plus_n_Z m in Refl
plus_comm (S k) m =
  let iH = plus_comm k m in
    rewrite iH in
    rewrite plus_n_Sm m k in Refl
