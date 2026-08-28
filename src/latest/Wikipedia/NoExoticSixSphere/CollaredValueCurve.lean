import Wikipedia.NoExoticSixSphere.RelativeSphereNormalization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# A smooth, collared path of nearby sphere values

The value is the original point before one eighth and after seven eighths,
and the chosen nearby point throughout the middle half. Normalized affine
interpolation stays quantitatively close to the original point.
-/

open scoped Manifold ContDiff
open Set Metric

namespace NoExoticSixSphere.CollaredValueCurve

noncomputable def cutoff : ContDiffBump (1 / 2 : ℝ) where
  rIn := 1 / 4
  rOut := 3 / 8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem cutoff_left {t : ℝ} (ht : t ≤ 1 / 8) : cutoff t = 0 := by
  apply cutoff.zero_of_le_dist
  change 3 / 8 ≤ dist t (1 / 2 : ℝ)
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

theorem cutoff_right {t : ℝ} (ht : 7 / 8 ≤ t) : cutoff t = 0 := by
  apply cutoff.zero_of_le_dist
  change 3 / 8 ≤ dist t (1 / 2 : ℝ)
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

theorem cutoff_middle {t : ℝ} (ht : t ∈ Icc (1 / 4 : ℝ) (3 / 4)) : cutoff t = 1 := by
  apply cutoff.one_of_mem_closedBall
  change dist t (1 / 2 : ℝ) ≤ 1 / 4
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [ht.1, ht.2]

variable {n : ℕ} (b c : Sphere n) (hc : dist c b < 1)

noncomputable def ambient : C(ℝ, EuclideanSpace ℝ (Fin (n + 1))) where
  toFun t := (b : EuclideanSpace ℝ (Fin (n + 1))) +
    cutoff t • ((c : EuclideanSpace ℝ (Fin (n + 1))) - b)
  continuous_toFun := continuous_const.add (cutoff.continuous.smul continuous_const)

include hc in
theorem ambient_ne_zero (t : ℝ) : ambient b c t ≠ 0 :=
  nearby_segment_ne_zero b c hc ⟨cutoff t, cutoff.nonneg, cutoff.le_one⟩

noncomputable def curve : C(ℝ, Sphere n) :=
  normalizedSphereMap (ambient b c) (ambient_ne_zero b c hc)

theorem contMDiff_curve : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (curve b c hc) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have h : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ (ambient b c) :=
    contMDiff_const.add (cutoff.contDiff.contMDiff.smul contMDiff_const)
  exact (contMDiff_normalize h (ambient_ne_zero b c hc)).codRestrict_sphere _

theorem curve_of_cutoff_zero {t : ℝ} (ht : cutoff t = 0) : curve b c hc t = b := by
  apply Subtype.ext
  change NormedSpace.normalize ((b : EuclideanSpace ℝ (Fin (n + 1))) +
    cutoff t • ((c : EuclideanSpace ℝ (Fin (n + 1))) - b)) = b
  rw [ht, zero_smul, add_zero]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm b)

theorem curve_middle {t : ℝ} (ht : t ∈ Icc (1 / 4 : ℝ) (3 / 4)) : curve b c hc t = c := by
  apply Subtype.ext
  change NormedSpace.normalize ((b : EuclideanSpace ℝ (Fin (n + 1))) +
    cutoff t • ((c : EuclideanSpace ℝ (Fin (n + 1))) - b)) = c
  rw [cutoff_middle ht, one_smul, ← add_sub_assoc, add_sub_cancel_left]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm c)

theorem ambient_dist_le (t : ℝ) :
    dist (ambient b c t) (b : EuclideanSpace ℝ (Fin (n + 1))) ≤ dist c b := by
  change dist ((b : EuclideanSpace ℝ (Fin (n + 1))) +
    cutoff t • ((c : EuclideanSpace ℝ (Fin (n + 1))) - b)) b ≤ dist c b
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg cutoff.nonneg]
  exact mul_le_of_le_one_left (norm_nonneg _) cutoff.le_one

theorem dist_curve_le (t : ℝ) : dist (curve b c hc t) b ≤ 2 * dist c b := by
  exact (dist_normalize_unit_le b (ambient_ne_zero b c hc t)).trans
    (mul_le_mul_of_nonneg_left (ambient_dist_le b c t) (by norm_num))

noncomputable def homotopy : (ContinuousMap.const ℝ b).Homotopy (curve b c hc) :=
  nearbyNormalizationHomotopy (ContinuousMap.const ℝ b) (ambient b c)
    (fun t ↦ (ambient_dist_le b c t).trans_lt hc)

theorem homotopy_dist_le (u : unitInterval) (t : ℝ) :
    dist (homotopy b c hc (u, t)) b ≤ 2 * dist c b := by
  let v := (b : EuclideanSpace ℝ (Fin (n + 1))) +
    (u : ℝ) • (ambient b c t - b)
  have hn : v ≠ 0 := nearby_segment_ne_zero b (ambient b c t)
    ((ambient_dist_le b c t).trans_lt hc) u
  have hv : dist v (b : EuclideanSpace ℝ (Fin (n + 1))) ≤ dist c b := by
    calc
      dist v (b : EuclideanSpace ℝ (Fin (n + 1))) ≤ dist (ambient b c t) b := by
        change ‖(b : EuclideanSpace ℝ (Fin (n + 1))) +
          (u : ℝ) • (ambient b c t - b) - b‖ ≤ ‖ambient b c t - b‖
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg u.property.1]
        exact mul_le_of_le_one_left (norm_nonneg _) u.property.2
      _ ≤ dist c b := ambient_dist_le b c t
  exact (dist_normalize_unit_le b hn).trans (mul_le_mul_of_nonneg_left hv (by norm_num))

theorem homotopy_of_cutoff_zero (u : unitInterval) {t : ℝ} (ht : cutoff t = 0) :
    homotopy b c hc (u, t) = b := by
  apply Subtype.ext
  change NormedSpace.normalize ((b : EuclideanSpace ℝ (Fin (n + 1))) +
    (u : ℝ) • ((b + cutoff t • ((c : EuclideanSpace ℝ (Fin (n + 1))) - b)) - b)) = b
  rw [ht, zero_smul, add_zero, sub_self, smul_zero, add_zero]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm b)

end NoExoticSixSphere.CollaredValueCurve
