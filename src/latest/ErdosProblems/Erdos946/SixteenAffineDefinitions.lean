/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SixteenResidues

open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega

namespace Erdos946.SixteenAffine

open Erdos946.SixteenKey

noncomputable def keyCommonMultiplier16 : ℕ :=
  Nat.factorial 16 * ∏ i : Fin 16, keyNumber16 i

/-- The prime power attached to the `i`th key number. -/
noncomputable def keyPower16 (i : Fin 16) : ℕ :=
  keyAuxPrime16 i ^ (σ 0 (keyNumber16 i) - 1)


lemma keyAuxPrime16_prime (i : Fin 16) : (keyAuxPrime16 i).Prime := by
  exact SixteenKey.keyAuxPrime16_prime i

lemma keyNumber16_gt_one (i : Fin 16) : 1 < keyNumber16 i := by
  exact SixteenKey.keyNumber16_gt_one i

lemma sigma_zero_keyNumber16_ge_two (i : Fin 16) : 2 ≤ σ 0 (keyNumber16 i) := by
  have hn1 : 1 < keyNumber16 i := keyNumber16_gt_one i
  have hpos : 0 < σ 0 (keyNumber16 i) :=
    ArithmeticFunction.sigma_pos 0 _ (Nat.ne_of_gt (Nat.zero_lt_one.trans hn1))
  have hne : σ 0 (keyNumber16 i) ≠ 1 := by
    intro h
    have := (ArithmeticFunction.sigma_eq_one_iff 0 (keyNumber16 i)).mp h
    omega
  omega


end Erdos946.SixteenAffine
