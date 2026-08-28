import Wikipedia.SmoothSixDPoincare.SphereNormalChartJacobian
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction
import Wikipedia.SmoothSixDPoincare.ComplementCoefficientSigns

/-!
# Constant radial orientation along an actual sphere chart

The actual ambient derivative of a sphere chart, augmented by the outward
radial vector, is a smooth field of invertible maps. Its determinant therefore
has the same sign at both ends of any continuous path in the chart source.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates

variable {V N : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
  (c : PartialDiffeomorph 𝓘(ℝ, N) (𝓡 n) N (Metric.sphere (0 : V) 1) ∞)

/-- The actual ambient differential of the sphere chart, augmented by its outward vector. -/
def chartRadialFrame (z : N) : (ℝ × N) →L[ℝ] V :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (c z : V)).coprod
    (fderiv ℝ (fun w => (c w : V)) z)

theorem chartRadialFrame_eq {z : N} (hz : z ∈ c.source) :
    chartRadialFrame c z = radialFrame (N := N) (c z)
      (mfderiv 𝓘(ℝ, N) (𝓡 n) c z : N →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
  have hchain : fderiv ℝ (fun w => (c w : V)) z =
      (inclusionDerivative (c z)).comp
        (mfderiv 𝓘(ℝ, N) (𝓡 n) c z : N →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
    have h := mfderiv_comp z
      ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).mdifferentiableAt (by simp))
      (c.mdifferentiableAt (by simp) hz)
    rw [mfderiv_eq_fderiv] at h
    exact h
  unfold chartRadialFrame radialFrame
  rw [hchain]
  rfl

theorem contDiffOn_chartRadialFrame : ContDiffOn ℝ ∞ (chartRadialFrame c) c.source := by
  have hc : ContDiffOn ℝ ∞ (fun w => (c w : V)) c.source :=
    ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).comp_contMDiffOn c.contMDiffOn_toFun).contDiffOn
  exact FrameField.contDiffOn_coprod (contDiffOn_const.smulRight hc)
    (hc.fderiv_of_isOpen c.open_source (m := ∞) (by simp))

variable [FiniteDimensional ℝ N]

theorem bijective_chartRadialFrame {z : N} (hz : z ∈ c.source) :
    Bijective (chartRadialFrame c z) := by
  rw [chartRadialFrame_eq c hz]
  let C : N →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, N) (𝓡 n) c z
  have hC : C.IsInvertible :=
    ⟨(LinearEquiv.ofBijective C.toLinearMap
      (PartialChart.bijective_mfderiv c hz)).toContinuousLinearEquiv, rfl⟩
  exact bijective_radialFrame (c z) C hC

variable [FiniteDimensional ℝ V]

/-- The same actual chart supplies compatible outward orientations at both ends of a path. -/
theorem chartRadialFrame_det_mul_endpoints_pos (j : (ℝ × N) ≃L[ℝ] V)
    (a : ℝ → N) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (haS : MapsTo a (Icc (0 : ℝ) 1) c.source) :
    0 < ((chartRadialFrame c (a 0)).comp j.symm.toContinuousLinearMap).det *
      ((chartRadialFrame c (a 1)).comp j.symm.toContinuousLinearMap).det := by
  have hF := (contDiffOn_chartRadialFrame c).continuousOn.comp ha haS
  exact FrameField.det_mul_endpoints_pos (hF.clm_comp continuousOn_const)
    (fun t ht => (bijective_chartRadialFrame c (haS ht)).comp j.symm.bijective)

/-- Along one actual sphere chart, opposite fixed normal signs are exactly opposite
normal-coordinate determinants. The chart orientation is proved consistent, not assumed. -/
theorem opposite_normalJacobians_iff_chartDet (j : (ℝ × N) ≃L[ℝ] V)
    (a : ℝ → N) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (haS : MapsTo a (Icc (0 : ℝ) 1) c.source)
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) (hB : B.IsInvertible) :
    normalJacobian j (c (a 0)) A * normalJacobian j (c (a 1)) B < 0 ↔
      (A.comp (mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 0) : N →L[ℝ] EuclideanSpace ℝ (Fin n))).det *
        (B.comp (mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 1) : N →L[ℝ] EuclideanSpace ℝ (Fin n))).det < 0 := by
  let C₀ : N →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 0)
  let C₁ : N →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, N) (𝓡 n) c (a 1)
  have h₀ : normalJacobian j (c (a 0)) A * (A.comp C₀).det =
      ((chartRadialFrame c (a 0)).comp j.symm.toContinuousLinearMap).det := by
    rw [chartRadialFrame_eq c (haS (by simp))]
    exact normalJacobian_mul_chartDet j (c (a 0)) A hA C₀
  have h₁ : normalJacobian j (c (a 1)) B * (B.comp C₁).det =
      ((chartRadialFrame c (a 1)).comp j.symm.toContinuousLinearMap).det := by
    rw [chartRadialFrame_eq c (haS (by simp))]
    exact normalJacobian_mul_chartDet j (c (a 1)) B hB C₁
  have hp : 0 < (normalJacobian j (c (a 0)) A * normalJacobian j (c (a 1)) B) *
      ((A.comp C₀).det * (B.comp C₁).det) := by
    have heq : (normalJacobian j (c (a 0)) A * normalJacobian j (c (a 1)) B) *
        ((A.comp C₀).det * (B.comp C₁).det) =
        (normalJacobian j (c (a 0)) A * (A.comp C₀).det) *
          (normalJacobian j (c (a 1)) B * (B.comp C₁).det) := by ring
    rw [heq, h₀, h₁]
    exact chartRadialFrame_det_mul_endpoints_pos c j a ha haS
  change _ ↔ (A.comp C₀).det * (B.comp C₁).det < 0
  rcases mul_pos_iff.mp hp with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact iff_of_false (not_lt_of_gt hp) (not_lt_of_gt hq)
  · exact iff_of_true hp hq

end Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates
