import Wikipedia.NoExoticSixSphere.NormalGraphPlane

/-!
# The spatial column after making a graph normal time-vertical

Its coefficient has the opposite sign to the outward time slope. This sign
is retained explicitly instead of being hidden by normalization.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.NormalGraphPlane

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def verticalCoefficient (ν : F) (s : ℝ) : ℝ := -(‖normalRaw ν s‖⁻¹ * (s + s⁻¹))

theorem vertical_normalColumn (ν : F) {s : ℝ} (hs : s ≠ 0) :
    normalColumn ν s - (normalColumn ν s).fst • (s⁻¹ • outwardRaw ν s) =
      WithLp.toLp 2 ((0 : ℝ), verticalCoefficient ν s • ν) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).injective
  apply Prod.ext
  · change ‖normalRaw ν s‖⁻¹ * 1 - (‖normalRaw ν s‖⁻¹ * 1) * (s⁻¹ * s) = 0
    rw [inv_mul_cancel₀ hs, mul_one, mul_one, sub_self]
  · change ‖normalRaw ν s‖⁻¹ • -(s • ν) -
      (‖normalRaw ν s‖⁻¹ * 1) • (s⁻¹ • ν) = verticalCoefficient ν s • ν
    rw [smul_neg, smul_smul, mul_one, smul_smul, ← neg_smul, ← sub_smul]
    apply congrArg (fun c : ℝ ↦ c • ν)
    unfold verticalCoefficient
    ring

theorem verticalCoefficient_pos (ν : F) {s : ℝ} (hs : s < 0) :
    0 < verticalCoefficient ν s := by
  unfold verticalCoefficient
  apply neg_pos.mpr
  exact mul_neg_of_pos_of_neg (inv_pos.mpr (norm_pos_iff.mpr (normalRaw_ne_zero ν s)))
    (add_neg hs (inv_lt_zero.mpr hs))

theorem verticalCoefficient_neg (ν : F) {s : ℝ} (hs : 0 < s) :
    verticalCoefficient ν s < 0 := by
  unfold verticalCoefficient
  apply neg_lt_zero.mpr
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (normalRaw_ne_zero ν s)))
    (add_pos hs (inv_pos.mpr hs))

theorem verticalCoefficient_ne_zero (ν : F) {s : ℝ} (hs : s ≠ 0) :
    verticalCoefficient ν s ≠ 0 := by
  rcases lt_or_gt_of_ne hs with hn | hp
  · exact ne_of_gt (verticalCoefficient_pos ν hn)
  · exact ne_of_lt (verticalCoefficient_neg ν hp)

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]

theorem contMDiff_verticalCoefficient {ν : X → F} {s : X → ℝ}
    (hν : ContMDiff I 𝓘(ℝ, F) ∞ ν) (hs : ContMDiff I 𝓘(ℝ, ℝ) ∞ s)
    (hn : ∀ x, s x ≠ 0) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ verticalCoefficient (ν x) (s x)) := by
  have hraw := contMDiff_normalRaw hν hs
  have hnorm : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ ‖normalRaw (ν x) (s x)‖) := by
    intro x
    exact (contDiffAt_norm ℝ (normalRaw_ne_zero (ν x) (s x))).comp_contMDiffAt
      (f := fun y ↦ normalRaw (ν y) (s y)) (x := x) (hraw x)
  exact ((hnorm.inv₀ (fun x ↦ norm_ne_zero_iff.mpr (normalRaw_ne_zero (ν x) (s x)))).mul
    (hs.add (hs.inv₀ hn))).neg

end NoExoticSixSphere.NormalGraphPlane
