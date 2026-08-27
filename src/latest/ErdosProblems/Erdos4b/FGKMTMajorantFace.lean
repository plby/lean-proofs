/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTMajorantEnergy
import ErdosProblems.Erdos4b.FGKMTFaceEnergy

/-!
# The exact inner face integral of the error majorant

The distinguished long factor may occur in the integrated coordinate
or in one of the remaining coordinates. Both cases are retained.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory
open scoped BigOperators

theorem oneLongTensor_cons_zero (k j : ℕ) (x : ℝ) (t : Fin j → ℝ) :
    oneLongTensor k (j + 1) 0 (Fin.cons x t) =
      dimensionLongFactor k x * ∏ i, dimensionProfileFactor k (t i) := by
  simp [oneLongTensor, oneLongFactor, Fin.prod_univ_succ]

theorem oneLongTensor_cons_succ (k j : ℕ) (i : Fin j) (x : ℝ) (t : Fin j → ℝ) :
    oneLongTensor k (j + 1) i.succ (Fin.cons x t) =
      dimensionProfileFactor k x * oneLongTensor k j i t := by
  have hzero : (0 : Fin (j + 1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero i)
  simp [oneLongTensor, oneLongFactor, Fin.prod_univ_succ, hzero]

theorem sieveProfileMajorant_cons (k j : ℕ) (x : ℝ) (t : Fin j → ℝ) :
    sieveProfileMajorant k (j + 1) (Fin.cons x t) =
      dimensionLongFactor k x * (∏ i, dimensionProfileFactor k (t i)) +
        dimensionProfileFactor k x * sieveProfileMajorant k j t := by
  rw [sieveProfileMajorant, Fin.sum_univ_succ, oneLongTensor_cons_zero]
  simp_rw [oneLongTensor_cons_succ]
  rw [← Finset.mul_sum]
  rfl

def majorantFaceValue (k j : ℕ) (t : Fin j → ℝ) : ℝ :=
  dimensionLongFirstMass k * (∏ i, dimensionProfileFactor k (t i)) +
    dimensionProfileFirstMass k * sieveProfileMajorant k j t

theorem majorantFaceValue_eq_integral {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k)
    (j : ℕ) (t : Fin j → ℝ) :
    majorantFaceValue k j t =
      ∫ x in Set.Ioi (0 : ℝ), sieveProfileMajorant k (j + 1) (Fin.cons x t) := by
  simp_rw [sieveProfileMajorant_cons]
  rw [integral_add ((dimensionLongFactor_integrableOn_positiveRay k).mul_const _)
      ((dimensionProfileFactor_integrableOn_positiveRay hk hlog).mul_const _),
    integral_mul_const, integral_mul_const,
    ← dimensionLongFirstMass_eq_positiveRay, ← dimensionProfileFirstMass_eq_positiveRay hk hlog]
  rfl

theorem majorantFaceValue_continuous (k j : ℕ) : Continuous (majorantFaceValue k j) := by
  apply Continuous.add
  · apply continuous_const.mul
    apply continuous_finsetProd
    intro i _hi
    exact (dimensionProfileFactor_contDiff k (n := 1)).continuous.comp (continuous_apply i)
  · exact continuous_const.mul (sieveProfileMajorant_continuous k j)

theorem shortTensor_sq_integrableOn {k j : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) :
    IntegrableOn (fun t : Fin j → ℝ => (∏ i, dimensionProfileFactor k (t i)) ^ 2)
      (Set.univ.pi (fun _ : Fin j => Set.Ioi (0 : ℝ))) := by
  simp_rw [← Finset.prod_pow]
  exact integrableOn_orthant_tensor (f := fun _ : Fin j => fun x => dimensionProfileFactor k x ^ 2)
    (fun _ => dimensionProfileFactor_sq_integrableOn_positiveRay hk hlog)

theorem integral_shortTensor_sq {k j : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) :
    (∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)),
        (∏ i, dimensionProfileFactor k (t i)) ^ 2) = dimensionProfileMass k ^ j := by
  simp_rw [← Finset.prod_pow]
  rw [integral_orthant_tensor (fun _ : Fin j => fun x => dimensionProfileFactor k x ^ 2)]
  simp only [← dimensionProfileMass_eq_positiveRay hk hlog, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem majorantFaceValue_sq_bound (k j : ℕ) (t : Fin j → ℝ) :
    majorantFaceValue k j t ^ 2 ≤
      (2 * dimensionLongFirstMass k ^ 2) * (∏ i, dimensionProfileFactor k (t i)) ^ 2 +
        (2 * dimensionProfileFirstMass k ^ 2) * sieveProfileMajorant k j t ^ 2 := by
  unfold majorantFaceValue
  nlinarith [sq_nonneg (dimensionLongFirstMass k * (∏ i, dimensionProfileFactor k (t i)) -
    dimensionProfileFirstMass k * sieveProfileMajorant k j t)]

theorem majorantFaceValue_sq_integrableOn {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    IntegrableOn (fun t => majorantFaceValue k j t ^ 2)
      (Set.univ.pi (fun _ : Fin j => Set.Ioi (0 : ℝ))) := by
  have hmaj := ((shortTensor_sq_integrableOn hk hlog (j := j)).const_mul
    (2 * dimensionLongFirstMass k ^ 2)).add
      ((sieveProfileMajorant_sq_integrableOn hk hlog (j := j)).const_mul
        (2 * dimensionProfileFirstMass k ^ 2))
  apply hmaj.mono' ((majorantFaceValue_continuous k j).pow 2).aestronglyMeasurable
  exact ae_of_all _ fun t => by
    change |majorantFaceValue k j t ^ 2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact majorantFaceValue_sq_bound k j t

theorem integral_majorantFaceValue_sq_le {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    (∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)), majorantFaceValue k j t ^ 2) ≤
      2 * dimensionLongFirstMass k ^ 2 * dimensionProfileMass k ^ j +
        2 * dimensionProfileFirstMass k ^ 2 *
          (∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)),
            sieveProfileMajorant k j t ^ 2) := by
  have hfirst := (shortTensor_sq_integrableOn hk hlog (j := j)).const_mul
    (2 * dimensionLongFirstMass k ^ 2)
  have hsecond := (sieveProfileMajorant_sq_integrableOn hk hlog (j := j)).const_mul
    (2 * dimensionProfileFirstMass k ^ 2)
  calc
    _ ≤ ∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)),
        (2 * dimensionLongFirstMass k ^ 2) * (∏ i, dimensionProfileFactor k (t i)) ^ 2 +
          (2 * dimensionProfileFirstMass k ^ 2) * sieveProfileMajorant k j t ^ 2 :=
      integral_mono (majorantFaceValue_sq_integrableOn hk hlog) (hfirst.add hsecond)
        (fun t => majorantFaceValue_sq_bound k j t)
    _ = _ := by
      rw [integral_add hfirst hsecond, integral_const_mul, integral_const_mul,
        integral_shortTensor_sq hk hlog]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.majorantFaceValue_eq_integral
#print axioms Erdos4b.FGKMT.integral_majorantFaceValue_sq_le
