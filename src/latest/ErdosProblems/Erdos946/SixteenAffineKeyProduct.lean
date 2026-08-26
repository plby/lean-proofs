/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SixteenAffinePrimePowerSigma

open scoped BigOperators

namespace Erdos946.SixteenAffine

open Erdos946.SixteenKey

lemma keyAuxPrime16_coprime_keyProduct (i : Fin 16) :
    (keyAuxPrime16 i).Coprime (∏ j : Fin 16, keyNumber16 j) := by
  exact Nat.Coprime.prod_right fun j _ ↦
    SixteenKey.keyAuxPrime16_coprime_keyNumber i j

end Erdos946.SixteenAffine
