/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SixteenAffinePrimePowerSigma

namespace Erdos946.SixteenAffine

open Erdos946.SixteenKey

lemma keyAuxPrime16_coprime_factorial (i : Fin 16) :
    (keyAuxPrime16 i).Coprime (Nat.factorial 16) := by
  decide +kernel +revert

end Erdos946.SixteenAffine
