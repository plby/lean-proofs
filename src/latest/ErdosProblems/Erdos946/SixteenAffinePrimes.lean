/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SixteenAffineCommonMultiplier

open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega

namespace Erdos946.SixteenAffine

open Erdos946.SixteenKey


lemma keyAuxPrime16_coprime_keyNumber16 (i j : Fin 16) :
    (keyAuxPrime16 i).Coprime (keyNumber16 j) := by
  exact SixteenKey.keyAuxPrime16_coprime_keyNumber i j

lemma keyPower16_pairwise_coprime :
    ((Finset.univ : Finset (Fin 16)) : Set (Fin 16)).Pairwise
      (fun i j => (keyPower16 i).Coprime (keyPower16 j)) := by
  intro i _ j _ hij
  apply Nat.Coprime.pow
  exact (Nat.coprime_primes (keyAuxPrime16_prime i) (keyAuxPrime16_prime j)).2
    (by
      intro h
      exact hij (keyAuxPrime16_injective h))


lemma keyPower16_coprime_commonMultiplier (i : Fin 16) :
    (keyPower16 i).Coprime keyCommonMultiplier16 := by
  exact Nat.Coprime.pow_left _ (keyAuxPrime16_coprime_commonMultiplier i)

lemma keyPower16_coprime_keyNumber16 (i j : Fin 16) :
    (keyPower16 i).Coprime (keyNumber16 j) := by
  exact Nat.Coprime.pow_left _ (keyAuxPrime16_coprime_keyNumber16 i j)


end Erdos946.SixteenAffine
