/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SixteenAffineDefinitions

open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega

namespace Erdos946.SixteenAffine

open Erdos946.SixteenKey

lemma keyPower16_gt_one (i : Fin 16) : 1 < keyPower16 i := by
  rw [keyPower16]
  exact one_lt_pow₀ (keyAuxPrime16_prime i).one_lt
    (Nat.sub_ne_zero_of_lt (sigma_zero_keyNumber16_ge_two i))

lemma sigma_zero_keyPower16 (i : Fin 16) :
    σ 0 (keyPower16 i) = σ 0 (keyNumber16 i) := by
  rw [keyPower16, ArithmeticFunction.sigma_zero_apply_prime_pow
    (keyAuxPrime16_prime i)]
  exact Nat.sub_add_cancel (by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (ArithmeticFunction.sigma_pos 0 _
        (Nat.ne_of_gt (Nat.zero_lt_one.trans (keyNumber16_gt_one i))))))


end Erdos946.SixteenAffine
