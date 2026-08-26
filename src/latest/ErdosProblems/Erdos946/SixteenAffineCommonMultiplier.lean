/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SixteenAffineFactorial
import ErdosProblems.Erdos946.SixteenAffineKeyProduct

open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega

namespace Erdos946.SixteenAffine

open Erdos946.SixteenKey


lemma keyAuxPrime16_coprime_commonMultiplier (i : Fin 16) :
    (keyAuxPrime16 i).Coprime keyCommonMultiplier16 := by
  rw [keyCommonMultiplier16]
  exact (keyAuxPrime16_coprime_factorial i).mul_right
    (keyAuxPrime16_coprime_keyProduct i)

end Erdos946.SixteenAffine
