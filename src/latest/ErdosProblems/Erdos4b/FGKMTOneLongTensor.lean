/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTOrthantMass

/-!
# One-long-factor tensors

These are the individual summands of the actual error majorant.
Their square energies are exact products of full positive-ray masses.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory
open scoped BigOperators

def oneLongFactor (k : ℕ) {j : ℕ} (i q : Fin j) : ℝ → ℝ :=
  if q = i then dimensionLongFactor k else dimensionProfileFactor k

def oneLongTensor (k j : ℕ) (i : Fin j) (t : Fin j → ℝ) : ℝ :=
  ∏ q, oneLongFactor k i q (t q)

theorem oneLongFactor_nonneg (k : ℕ) {j : ℕ} (i q : Fin j) (x : ℝ) :
    0 ≤ oneLongFactor k i q x := by
  unfold oneLongFactor
  split_ifs
  · exact dimensionLongFactor_nonneg k x
  · exact dimensionProfileFactor_nonneg k x

theorem oneLongTensor_nonneg (k j : ℕ) (i : Fin j) (t : Fin j → ℝ) :
    0 ≤ oneLongTensor k j i t := Finset.prod_nonneg fun q _ => oneLongFactor_nonneg k i q (t q)

theorem oneLongTensor_continuous (k j : ℕ) (i : Fin j) : Continuous (oneLongTensor k j i) := by
  unfold oneLongTensor
  apply continuous_finsetProd
  intro q _hq
  unfold oneLongFactor
  split_ifs
  · exact (dimensionLongFactor_contDiff k (n := 1)).continuous.comp (continuous_apply q)
  · exact (dimensionProfileFactor_contDiff k (n := 1)).continuous.comp (continuous_apply q)

theorem oneLongTensor_eq (k j : ℕ) (i : Fin j) (t : Fin j → ℝ) :
    oneLongTensor k j i t = dimensionLongFactor k (t i) *
      ∏ q ∈ Finset.univ.erase i, dimensionProfileFactor k (t q) := by
  classical
  rw [oneLongTensor, ← Finset.mul_prod_erase Finset.univ
    (fun q => oneLongFactor k i q (t q)) (Finset.mem_univ i)]
  simp only [oneLongFactor]
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  rw [if_neg (Finset.mem_erase.mp hq).1]

theorem oneLongTensor_pow_integrableOn {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (i : Fin j) (m : ℕ) :
    IntegrableOn (fun t => oneLongTensor k j i t ^ (m + 1))
      (Set.univ.pi (fun _ : Fin j => Set.Ioi (0 : ℝ))) := by
  simp_rw [oneLongTensor, ← Finset.prod_pow]
  apply integrableOn_orthant_tensor (f := fun q x => oneLongFactor k i q x ^ (m + 1))
  intro q
  unfold oneLongFactor
  split_ifs
  · exact sieveFactor_pow_integrableOn_positiveRay (by norm_num) (sieveProfileScale k) m
  · exact sieveFactor_pow_integrableOn_positiveRay
      (profile_scales_bounds hk hlog).2.1 (sieveProfileScale k) m

theorem integral_oneLongTensor_pow (k j : ℕ) (i : Fin j) (m : ℕ) :
    (∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)),
        oneLongTensor k j i t ^ (m + 1)) =
      (∫ x in Set.Ioi (0 : ℝ), dimensionLongFactor k x ^ (m + 1)) *
        (∫ x in Set.Ioi (0 : ℝ), dimensionProfileFactor k x ^ (m + 1)) ^ (j - 1) := by
  classical
  simp_rw [oneLongTensor, ← Finset.prod_pow]
  rw [integral_orthant_tensor (fun q x => oneLongFactor k i q x ^ (m + 1)),
    ← Finset.mul_prod_erase Finset.univ
    (fun q : Fin j => ∫ x in Set.Ioi (0 : ℝ), oneLongFactor k i q x ^ (m + 1))
    (Finset.mem_univ i)]
  simp only [oneLongFactor]
  congr 1
  calc
    _ = ∏ _q ∈ Finset.univ.erase i,
        (∫ x in Set.Ioi (0 : ℝ), dimensionProfileFactor k x ^ (m + 1)) := by
      apply Finset.prod_congr rfl
      intro q hq
      simp only [if_neg (Finset.mem_erase.mp hq).1]
    _ = _ := by simp

theorem integral_oneLongTensor_sq {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (i : Fin j) :
    (∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)),
        oneLongTensor k j i t ^ 2) = dimensionLongMass k * dimensionProfileMass k ^ (j - 1) := by
  rw [integral_oneLongTensor_pow k j i 1,
    ← dimensionLongMass_eq_positiveRay, ← dimensionProfileMass_eq_positiveRay hk hlog]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.oneLongTensor_pow_integrableOn
#print axioms Erdos4b.FGKMT.integral_oneLongTensor_sq
