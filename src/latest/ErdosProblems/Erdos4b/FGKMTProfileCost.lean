/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTProfileMass

/-!
# The polynomial Abel cost of the actual squared profile

The constant depends only on the fixed cutoff. In particular it does
not depend on the sieve dimension, the modulus, or either scale.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem sieveFactor_sq_unit_mass_eq {U : ℝ} (hU : 0 < U) (hU1 : U ≤ 1) (T : ℝ) :
    (∫ t in (0 : ℝ)..1, sieveFactor T U t ^ 2) =
      ∫ t in (0 : ℝ)..U, sieveFactor T U t ^ 2 :=
  sieveFactor_pow_integral_eq hU hU1 T 1

theorem sieveFactor_sq_unit_mass_pos {T U : ℝ} (hT : 0 ≤ T) (hU : 0 < U) (hU1 : U ≤ 1) :
    0 < (∫ t in (0 : ℝ)..1, sieveFactor T U t ^ 2) := by
  rw [sieveFactor_sq_unit_mass_eq hU hU1]
  exact sieveFactor_sq_mass_pos hT hU

theorem sieveFactor_sq_endpoint_le_one {T : ℝ} (hT : 0 ≤ T) (U : ℝ) :
    |sieveFactor T U 1 ^ 2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  have h0 := sieveFactor_nonneg T U 1
  have h1 := sieveFactor_le_one hT zero_le_one U
  nlinarith

theorem sieveFactor_sq_cost {T U K : ℝ} (hT : 1 ≤ T) (hU : 0 < U) (hU1 : U ≤ 1)
    (hTU : 2 ≤ T * U) (hψ : BoundedCutoff sieveCutoff K) :
    |sieveFactor T U 1 ^ 2| + 2 * (K / U + T) ≤
      ((4 * K + 6) * T ^ 2) * (∫ t in (0 : ℝ)..1, sieveFactor T U t ^ 2) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hK0 := hψ.constant_nonneg
  have hInv : 1 / U ≤ T := (div_le_iff₀ hU).mpr (by nlinarith)
  have hKu : K / U ≤ K * T := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hInv hK0
  have hmass : 1 / (2 * T) ≤ (∫ t in (0 : ℝ)..1, sieveFactor T U t ^ 2) := by
    rw [sieveFactor_sq_unit_mass_eq hU hU1]
    exact sieveFactor_sq_mass_ge_half_inv hT0 hU hTU
  calc
    _ ≤ (2 * K + 3) * T := by
      nlinarith [sieveFactor_sq_endpoint_le_one hT0.le U]
    _ = ((4 * K + 6) * T ^ 2) * (1 / (2 * T)) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveFactor_sq_cost
