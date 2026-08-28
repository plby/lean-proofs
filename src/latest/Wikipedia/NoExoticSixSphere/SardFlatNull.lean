import Wikipedia.NoExoticSixSphere.SardFlatHolder
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The high-order vanishing part of Sard's theorem

The local Hölder estimate bounds the image's Hausdorff dimension by the
source dimension divided by the vanishing order plus one. If this is
strictly below the target dimension, the image has zero additive Haar
measure. This handles the high-order vanishing part, not the remaining
critical strata.
-/

open scoped ContDiff NNReal ENNReal
open Set Module MeasureTheory MeasureTheory.Measure

namespace NoExoticSixSphere.Sard

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem dimH_image_flatPoints_lt {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (k : ℕ)
    (hk : finrank ℝ E < (k + 1) * finrank ℝ F) :
    dimH (f '' (U ∩ flatPoints f k)) < finrank ℝ F := by
  calc
    dimH (f '' (U ∩ flatPoints f k)) ≤ dimH (U ∩ flatPoints f k) / (k + 1 : ℕ) :=
      dimH_image_flatPoints_le hU hf k
    _ ≤ (finrank ℝ E : ℝ≥0∞) / (k + 1 : ℕ) := by
      apply ENNReal.div_le_div_right
      exact (dimH_mono (subset_univ _)).trans_eq (Real.dimH_univ_eq_finrank E)
    _ < finrank ℝ F := by
      rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp))]
      exact_mod_cast (show finrank ℝ E < finrank ℝ F * (k + 1) by
        simpa only [Nat.mul_comm] using hk)

theorem measure_image_flatPoints_eq_zero [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [IsAddHaarMeasure μ] {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (k : ℕ)
    (hk : finrank ℝ E < (k + 1) * finrank ℝ F) :
    μ (f '' (U ∩ flatPoints f k)) = 0 := by
  have hμ : μ ≪ (μH[((finrank ℝ F : ℝ≥0) : ℝ)] : Measure F) := by
    simpa only [NNReal.coe_natCast] using
      (Measure.absolutelyContinuous_isAddHaarMeasure μ (μH[(finrank ℝ F : ℝ)] : Measure F))
  apply measure_zero_of_dimH_lt hμ
  simpa using dimH_image_flatPoints_lt hU hf k hk

theorem dense_compl_image_flatPoints {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (k : ℕ)
    (hk : finrank ℝ E < (k + 1) * finrank ℝ F) :
    Dense (f '' (U ∩ flatPoints f k))ᶜ :=
  dense_compl_of_dimH_lt_finrank (dimH_image_flatPoints_lt hU hf k hk)

end NoExoticSixSphere.Sard
