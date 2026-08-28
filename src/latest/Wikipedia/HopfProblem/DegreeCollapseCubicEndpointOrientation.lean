import Wikipedia.HopfProblem.DegreeCollapseCubicTransverseNegation

/-!
# Constructing compatible endpoint orientations in odd transverse rank

Invertibility of the actual transition blocks makes their determinants
nonzero. Keep the right endpoint chart if the signs already agree; otherwise
negate its transverse coordinates. This preserves its axis and every signed
cubic equation, while supplying the sign condition for native chart gluing.
-/

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

omit [FiniteDimensional ℝ V] in
theorem det_ne_zero_of_isInvertible (T : V →L[ℝ] V) (hT : T.IsInvertible) :
    T.toLinearMap.det ≠ 0 := by
  obtain ⟨e, he⟩ := hT
  rw [← he]
  exact e.toLinearEquiv.isUnit_det'.ne_zero

/-- The compatible right endpoint is selected from two explicit native charts. -/
theorem exists_compatible_endpoint_orientation
    (Ψ Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞)
    (hodd : Odd (Module.finrank ℝ V)) {p q : ℝ}
    (hΨ₀ : (p, (0 : V)) ∈ Ψ.source) (hΨ₁ : (q, (0 : V)) ∈ Ψ.source)
    (hΦ₀ : (p, (0 : V)) ∈ Φ₀.source) (hΦ₁ : (q, (0 : V)) ∈ Φ₁.source)
    (haxis₀ : (fun s : ℝ => Φ₀ (s, 0)) =ᶠ[𝓝 p] (fun s => Ψ (s, 0)))
    (haxis₁ : (fun s : ℝ => Φ₁ (s, 0)) =ᶠ[𝓝 q] (fun s => Ψ (s, 0))) :
    ∃ Φ₂ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞,
      (Φ₂ = Φ₁ ∨ Φ₂ = negateTransverseChart Φ₁) ∧
      (q, (0 : V)) ∈ Φ₂.source ∧
      (∀ s : ℝ, Φ₂ (s, 0) = Φ₁ (s, 0)) ∧
      0 < (AxisCoordinates.transverseBlock
        (fderiv ℝ (Ψ.symm ∘ Φ₀) (p, 0))).toLinearMap.det *
        (AxisCoordinates.transverseBlock
          (fderiv ℝ (Ψ.symm ∘ Φ₂) (q, 0))).toLinearMap.det := by
  obtain ⟨U₀, -, hp, -, -, -, -, hi₀, -⟩ :=
    AxisCoordinates.exists_native_axis_transition_data Φ₀ Ψ hΦ₀ hΨ₀ haxis₀
  obtain ⟨U₁, -, hq, hs₁, -, -, -, hi₁, -⟩ :=
    AxisCoordinates.exists_native_axis_transition_data Φ₁ Ψ hΦ₁ hΨ₁ haxis₁
  let d₀ := (AxisCoordinates.transverseBlock
    (fderiv ℝ (Ψ.symm ∘ Φ₀) (p, 0))).toLinearMap.det
  let d₁ := (AxisCoordinates.transverseBlock
    (fderiv ℝ (Ψ.symm ∘ Φ₁) (q, 0))).toLinearMap.det
  have hn₀ : d₀ ≠ 0 := det_ne_zero_of_isInvertible _ (hi₀ p hp)
  have hn₁ : d₁ ≠ 0 := det_ne_zero_of_isInvertible _ (hi₁ q hq)
  by_cases hpos : 0 < d₀ * d₁
  · exact ⟨Φ₁, Or.inl rfl, hΦ₁, fun _ => rfl, hpos⟩
  · refine ⟨negateTransverseChart Φ₁, Or.inr rfl,
      (negateTransverseChart_axis_source Φ₁ q).mpr hΦ₁,
      negateTransverseChart_axis Φ₁, ?_⟩
    rw [det_transition_negateTransverseChart Φ₁ Ψ hodd (hs₁ q hq)]
    change 0 < d₀ * -d₁
    have hneg : d₀ * d₁ < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (mul_ne_zero hn₀ hn₁)
    nlinarith

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
