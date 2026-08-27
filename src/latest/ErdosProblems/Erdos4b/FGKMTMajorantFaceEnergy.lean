/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTMajorantFace

/-!
# Quadratic face-energy loss for the full error majorant

The positive-ray face integral is compared to the actual profile face
energy with an absolute constant and a quadratic dimension factor.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory
open scoped BigOperators

theorem dimensionLongFirstMass_sq_le {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    dimensionLongFirstMass k ^ 2 ≤ 16 * dimensionProfileFirstMass k ^ 2 := by
  have hd0 : 0 ≤ dimensionLongFirstMass k :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (dimensionLongFactor_nonneg k)
  have h := pow_le_pow_left₀ hd0 (dimensionLongFirstMass_le_four hk hlog) 2
  nlinarith

theorem integral_majorantFaceValue_sq_tensor_bound {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    (∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)), majorantFaceValue k j t ^ 2) ≤
      36 * ((j : ℝ) + 1) ^ 2 * dimensionProfileFirstMass k ^ 2 * dimensionProfileMass k ^ j := by
  have ha := (dimensionProfileMass_pos hk hlog).le
  have hpow : 0 ≤ dimensionProfileMass k ^ j := pow_nonneg ha j
  have hA : 0 ≤ dimensionProfileFirstMass k ^ 2 := sq_nonneg _
  calc
    _ ≤ 2 * dimensionLongFirstMass k ^ 2 * dimensionProfileMass k ^ j +
        2 * dimensionProfileFirstMass k ^ 2 *
          (∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)),
            sieveProfileMajorant k j t ^ 2) := integral_majorantFaceValue_sq_le hk hlog
    _ ≤ 2 * (16 * dimensionProfileFirstMass k ^ 2) * dimensionProfileMass k ^ j +
        2 * dimensionProfileFirstMass k ^ 2 *
          (2 * (j : ℝ) ^ 2 * dimensionProfileMass k ^ j) :=
      add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (dimensionLongFirstMass_sq_le hk hlog) (by norm_num)) hpow)
        (mul_le_mul_of_nonneg_left (integral_sieveProfileMajorant_sq_tensor_bound hk hlog)
          (by positivity))
    _ = (32 + 4 * (j : ℝ) ^ 2) * dimensionProfileFirstMass k ^ 2 * dimensionProfileMass k ^ j := by
      ring
    _ ≤ _ := by
      have hc : 32 + 4 * (j : ℝ) ^ 2 ≤ 36 * ((j : ℝ) + 1) ^ 2 := by
        nlinarith [sq_nonneg (j : ℝ), (show (0 : ℝ) ≤ j from Nat.cast_nonneg j)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hA) hpow

theorem integral_majorantFaceValue_sq_energy_bound {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hj : j ≤ k) :
    (∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)), majorantFaceValue k j t ^ 2) ≤
      144 * ((j : ℝ) + 1) ^ 2 * dimensionFaceEnergy k j := by
  have hJ := (dimensionFaceEnergy_bounds hk hlog hj).1
  have hmass : dimensionProfileFirstMass k ^ 2 * dimensionProfileMass k ^ j ≤
      4 * dimensionFaceEnergy k j := by linarith
  calc
    _ ≤ 36 * ((j : ℝ) + 1) ^ 2 * dimensionProfileFirstMass k ^ 2 * dimensionProfileMass k ^ j :=
      integral_majorantFaceValue_sq_tensor_bound hk hlog
    _ = (36 * ((j : ℝ) + 1) ^ 2) *
        (dimensionProfileFirstMass k ^ 2 * dimensionProfileMass k ^ j) := by ring
    _ ≤ (36 * ((j : ℝ) + 1) ^ 2) * (4 * dimensionFaceEnergy k j) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

theorem sieveProfileMajorant_orthant_face_energy_bound {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hj : j ≤ k) :
    (∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)),
        (∫ x in Set.Ioi (0 : ℝ), sieveProfileMajorant k (j + 1) (Fin.cons x t)) ^ 2) ≤
      144 * ((j : ℝ) + 1) ^ 2 * dimensionFaceEnergy k j := by
  simp_rw [← majorantFaceValue_eq_integral hk hlog]
  exact integral_majorantFaceValue_sq_energy_bound hk hlog hj

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.integral_majorantFaceValue_sq_energy_bound
#print axioms Erdos4b.FGKMT.sieveProfileMajorant_orthant_face_energy_bound
