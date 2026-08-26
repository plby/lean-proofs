/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SixteenAffinePrimes

open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega

namespace Erdos946.SixteenAffine

open Erdos946.SixteenKey

/-- Coefficient in the simultaneous congruence which defines the affine
parameter. -/
noncomputable def keyCongruence16Coefficient (i : Fin 16) : ℕ :=
  keyNumber16 i * keyCommonMultiplier16

lemma keyCongruence16Coefficient_coprime (i : Fin 16) :
    (keyCongruence16Coefficient i).Coprime ((keyPower16 i) ^ 2) := by
  apply Nat.Coprime.pow_right
  exact ((keyPower16_coprime_keyNumber16 i i).mul_right
    (keyPower16_coprime_commonMultiplier i)).symm

/-- Each individual congruence
`(aᵢ A) X ≡ rᵢ - 1 (mod rᵢ²)` has a solution because its coefficient is a
unit modulo `rᵢ²`. -/
lemma exists_keyCongruence16Residue (i : Fin 16) : ∃ x : ℕ,
    keyCongruence16Coefficient i * x ≡ keyPower16 i - 1
      [MOD (keyPower16 i) ^ 2] := by
  have hm0 : (keyPower16 i) ^ 2 ≠ 0 :=
    Nat.ne_of_gt (pow_pos (Nat.zero_lt_one.trans (keyPower16_gt_one i)) 2)
  obtain ⟨x, _hxlt, hx⟩ :=
    Nat.exists_mul_mod_eq_of_coprime (keyPower16 i - 1)
      (keyCongruence16Coefficient_coprime i) hm0
  exact ⟨x, hx⟩

/-- A selected solution of the `i`th congruence. -/
noncomputable def keyCongruence16Residue (i : Fin 16) : ℕ :=
  Classical.choose (exists_keyCongruence16Residue i)

lemma keyCongruence16Residue_spec (i : Fin 16) :
    keyCongruence16Coefficient i * keyCongruence16Residue i ≡
      keyPower16 i - 1 [MOD (keyPower16 i) ^ 2] :=
  Classical.choose_spec (exists_keyCongruence16Residue i)

lemma keyPower16Sq_ne_zero (i : Fin 16) : (keyPower16 i) ^ 2 ≠ 0 := by
  exact Nat.ne_of_gt
    (pow_pos (Nat.zero_lt_one.trans (keyPower16_gt_one i)) 2)

lemma keyPower16Sq_pairwise_coprime :
    ((Finset.univ : Finset (Fin 16)) : Set (Fin 16)).Pairwise
      (fun i j => ((keyPower16 i) ^ 2).Coprime ((keyPower16 j) ^ 2)) := by
  intro i hi j hj hij
  exact Nat.Coprime.pow 2 2 (keyPower16_pairwise_coprime hi hj hij)


end Erdos946.SixteenAffine
