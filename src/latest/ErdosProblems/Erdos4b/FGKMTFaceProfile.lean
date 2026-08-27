/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTMajorantSliceCost

/-! # The actual face profile, its majorant, and its exact product support -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def sieveFaceProfile (k m : ℕ) (t : Fin m → ℝ) : ℝ :=
  (∏ i, dimensionProfileFactor k (t i)) * dimensionFaceCutoff k (∑ i, t i)

theorem sieveFaceProfile_eq_integral (k m : ℕ) (t : Fin m → ℝ) :
    sieveFaceProfile k m t =
      ∫ x in (0 : ℝ)..1, sieveProfile k (m + 1) (Fin.cons x t) :=
  (sieveProfile_face_integral k m t).symm

theorem sieveFaceProfile_nonneg (k m : ℕ) (t : Fin m → ℝ) :
    0 ≤ sieveFaceProfile k m t :=
  mul_nonneg (Finset.prod_nonneg fun i _hi => dimensionProfileFactor_nonneg k (t i))
    (dimensionFaceCutoff_nonneg k _)

theorem sieveFaceProfile_le_majorant {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (m : ℕ) (t : Fin m → ℝ) :
    sieveFaceProfile k m t ≤ majorantFaceValue k m t := by
  have hP : 0 ≤ ∏ i, dimensionProfileFactor k (t i) :=
    Finset.prod_nonneg fun i _hi => dimensionProfileFactor_nonneg k (t i)
  calc
    _ ≤ (∏ i, dimensionProfileFactor k (t i)) * dimensionProfileFirstMass k :=
      mul_le_mul_of_nonneg_left (dimensionFaceCutoff_le_mass k _) hP
    _ ≤ (∏ i, dimensionProfileFactor k (t i)) * dimensionLongFirstMass k :=
      mul_le_mul_of_nonneg_left (dimensionProfileFirstMass_le_long hk hlog) hP
    _ ≤ majorantFaceValue k m t := by
      unfold majorantFaceValue
      have hQ := mul_nonneg (dimensionProfileFirstMass_nonneg k)
        (sieveProfileMajorant_nonneg k m t)
      nlinarith

theorem sieveFaceProfile_zero_of_sum_ge_one {k m : ℕ} {t : Fin m → ℝ}
    (ht : 1 ≤ ∑ i, t i) : sieveFaceProfile k m t = 0 := by
  rw [sieveFaceProfile_eq_integral]
  calc
    _ = ∫ _x in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx0 : 0 ≤ x := (show x ∈ Set.Icc (0 : ℝ) 1 from by
        simpa only [Set.uIcc_of_le zero_le_one] using hx).1
      apply sieveProfile_zero_of_sum_ge_one
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      linarith
    _ = 0 := by simp

theorem sieveFaceProfile_logTuple_zero_of_product_ge {k m R : ℕ} (hR : 1 < R)
    (r : Fin m → ℕ) (hr : ∀ i, 0 < r i) (hprod : R ≤ ∏ i, r i) :
    sieveFaceProfile k m (sieveLogTuple R r) = 0 := by
  apply sieveFaceProfile_zero_of_sum_ge_one
  rw [sum_sieveLogTuple R r hr]
  apply (le_div_iff₀ (Real.log_pos (by exact_mod_cast hR))).mpr
  rw [one_mul]
  exact Real.log_le_log (by exact_mod_cast (by omega : 0 < R)) (by exact_mod_cast hprod)

theorem majorantFaceValue_zero_of_coord_ge_two {k m : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (i : Fin m) {t : Fin m → ℝ} (ht : 2 ≤ t i) :
    majorantFaceValue k m t = 0 := by
  have hA := dimensionProfileFactor_zero_of_one_le hk hlog (by linarith : 1 ≤ t i)
  have hQ := sieveProfileMajorant_zero_of_coord_ge_two hk hlog i ht
  unfold majorantFaceValue
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hA, hQ, mul_zero, mul_zero, add_zero]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveFaceProfile_le_majorant
#print axioms Erdos4b.FGKMT.sieveFaceProfile_logTuple_zero_of_product_ge
