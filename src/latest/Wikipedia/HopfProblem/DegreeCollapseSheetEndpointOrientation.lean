import Wikipedia.HopfProblem.DegreeCollapseLinearTransverseChart
import Wikipedia.HopfProblem.DegreeCollapseCubicEndpointOrientation

/-!
# Endpoint orientation correction preserving the two sheet factors

Change only the second transverse factor of the terminal chart. The
longitudinal axis and the first transverse factor remain fixed, so the
terminal sheet's coordinate equation is preserved. The determinant is
chosen from the actual native transitions, without a parity hypothesis.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {A B E M ι : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem exists_compatible_sheet_endpoint_orientation (basis : Module.Basis ι ℝ B) (i : ι)
    (Ψ Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × (A × B)) 𝓘(ℝ, E) (ℝ × (A × B)) M ∞)
    {p q : ℝ} (hΨ₀ : (p, (0 : A × B)) ∈ Ψ.source)
    (hΨ₁ : (q, (0 : A × B)) ∈ Ψ.source)
    (hΦ₀ : (p, (0 : A × B)) ∈ Φ₀.source) (hΦ₁ : (q, (0 : A × B)) ∈ Φ₁.source)
    (haxis₀ : (fun s : ℝ => Φ₀ (s, 0)) =ᶠ[𝓝 p] (fun s => Ψ (s, 0)))
    (haxis₁ : (fun s : ℝ => Φ₁ (s, 0)) =ᶠ[𝓝 q] (fun s => Ψ (s, 0))) :
    ∃ R : B ≃L[ℝ] B,
      0 < (AxisCoordinates.transverseBlock
        (fderiv ℝ (Ψ.symm ∘ Φ₀) (p, 0))).toLinearMap.det *
        (AxisCoordinates.transverseBlock
          (fderiv ℝ (Ψ.symm ∘ linearTransverseChart
            ((ContinuousLinearEquiv.refl ℝ A).prodCongr R) Φ₁) (q, 0))).toLinearMap.det := by
  obtain ⟨U₀, -, hp, -, -, -, -, hi₀, -⟩ :=
    AxisCoordinates.exists_native_axis_transition_data Φ₀ Ψ hΦ₀ hΨ₀ haxis₀
  obtain ⟨U₁, -, hq, hs₁, -, -, -, hi₁, -⟩ :=
    AxisCoordinates.exists_native_axis_transition_data Φ₁ Ψ hΦ₁ hΨ₁ haxis₁
  let d₀ := (AxisCoordinates.transverseBlock
    (fderiv ℝ (Ψ.symm ∘ Φ₀) (p, 0))).toLinearMap.det
  let d₁ := (AxisCoordinates.transverseBlock
    (fderiv ℝ (Ψ.symm ∘ Φ₁) (q, 0))).toLinearMap.det
  have h₀ : d₀ ≠ 0 := det_ne_zero_of_isInvertible _ (hi₀ p hp)
  have h₁ : d₁ ≠ 0 := det_ne_zero_of_isInvertible _ (hi₁ q hq)
  obtain ⟨R, hR⟩ := SupportedGerms.exists_linearEquiv_with_det basis i
    (inv_ne_zero (mul_ne_zero h₀ h₁))
  refine ⟨R, ?_⟩
  rw [det_transition_linearTransverseChart _ Φ₁ Ψ (hs₁ q hq)]
  have hdet : ((ContinuousLinearEquiv.refl ℝ A).prodCongr R).toLinearMap.det =
      (d₀ * d₁)⁻¹ := by
    change ((LinearMap.id : A →ₗ[ℝ] A).prodMap R.toLinearMap).det = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul, hR]
  rw [hdet]
  change 0 < d₀ * (d₁ * (d₀ * d₁)⁻¹)
  have hone : d₀ * (d₁ * (d₀ * d₁)⁻¹) = 1 := by
    rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero h₀ h₁)]
  rw [hone]
  exact zero_lt_one

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
