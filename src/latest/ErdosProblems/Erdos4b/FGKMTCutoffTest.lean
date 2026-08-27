/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCutoffAverage
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The cost of a frozen sum-dependent cutoff

The supremum of a profile on the unit interval is bounded by its
endpoint value plus its derivative bound. Consequently multiplying by
a translated bounded cutoff has a uniform endpoint-plus-derivative
cost, independent of the frozen sum of the other coordinates.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem profile_abs_le_endpoint_add_deriv {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {V : ℝ} (hV : ∀ t ∈ Set.Icc (0 : ℝ) 1, |deriv G t| ≤ V)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : |G t| ≤ |G 1| + V := by
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV 0 ⟨le_rfl, zero_le_one⟩)
  have hdiff := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x (_hx : x ∈ Set.Icc (0 : ℝ) 1) => hG.differentiable_one x)
    (fun x hx => by simpa only [Real.norm_eq_abs] using hV x hx)
    (convex_Icc (0 : ℝ) 1) (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩) ht
  simp only [Real.norm_eq_abs] at hdiff
  have hdist : |t - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hbound : |G t - G 1| ≤ V := hdiff.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hdist hV0)
  calc
    _ = |G 1 + (G t - G 1)| := by congr 1; ring
    _ ≤ |G 1| + |G t - G 1| := abs_add_le _ _
    _ ≤ _ := add_le_add le_rfl hbound

def cutoffTest (G Φ : ℝ → ℝ) (u t : ℝ) : ℝ := G t * Φ (u + t)

theorem cutoffTest_contDiff {G Φ : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    (hΦ : ContDiff ℝ 1 Φ) (u : ℝ) : ContDiff ℝ 1 (cutoffTest G Φ u) :=
  hG.mul (hΦ.comp (contDiff_const.add contDiff_id))

theorem cutoffTest_deriv {G Φ : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    (hΦ : ContDiff ℝ 1 Φ) (u t : ℝ) :
    deriv (cutoffTest G Φ u) t = deriv G t * Φ (u + t) + G t * deriv Φ (u + t) := by
  have h := (hG.differentiable_one t).hasDerivAt.mul
    ((hΦ.differentiable_one (u + t)).hasDerivAt.comp t ((hasDerivAt_id t).const_add u))
  simpa only [cutoffTest, Function.comp_apply, id_eq, mul_one] using! h.deriv

theorem cutoffTest_cost {G Φ : ℝ → ℝ} {K V : ℝ} (hG : ContDiff ℝ 1 G)
    (hΦ : BoundedCutoff Φ K)
    (hV : ∀ t ∈ Set.Icc (0 : ℝ) 1, |deriv G t| ≤ V) (u : ℝ) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      |deriv (cutoffTest G Φ u) t| ≤ K * (|G 1| + 2 * V)) ∧
    |cutoffTest G Φ u 1| + K * (|G 1| + 2 * V) ≤ 2 * K * (|G 1| + V) := by
  have hK := hΦ.constant_nonneg
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV 0 ⟨le_rfl, zero_le_one⟩)
  constructor
  · intro t ht
    rw [cutoffTest_deriv hG hΦ.smooth]
    calc
      _ ≤ |deriv G t * Φ (u + t)| + |G t * deriv Φ (u + t)| := abs_add_le _ _
      _ = |deriv G t| * |Φ (u + t)| + |G t| * |deriv Φ (u + t)| := by
        rw [abs_mul, abs_mul]
      _ ≤ V * K + (|G 1| + V) * K := add_le_add
        (mul_le_mul (hV t ht) (hΦ.value_bound (u + t)) (abs_nonneg _) (by
          exact (abs_nonneg _).trans (hV t ht)))
        (mul_le_mul (profile_abs_le_endpoint_add_deriv hG hV ht)
          (hΦ.deriv_bound (u + t)) (abs_nonneg _) (by positivity))
      _ = _ := by ring
  · have hendpoint : |cutoffTest G Φ u 1| ≤ |G 1| * K := by
      rw [cutoffTest, abs_mul]
      exact mul_le_mul_of_nonneg_left (hΦ.value_bound (u + 1)) (abs_nonneg _)
    nlinarith

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.cutoffTest_cost
