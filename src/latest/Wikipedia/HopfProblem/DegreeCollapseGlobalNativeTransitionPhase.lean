import Wikipedia.HopfProblem.DegreeCollapseNativeTransitionPhase
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransportCutoff
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# A globally smooth phase for the actual native transition

Extend the proved local scalar phase near the closed reference point and
restrict the actual transverse chart to the agreement neighborhood. The
exact native transition formula is retained, and the scalar phase is now
globally smooth and vanishes at the reference orbit, as required by the
compact positive phase realization theorem.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z E M : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The actual native chart transition constructs a globally smooth phase
with zero reference value and retains its exact formula on a smaller genuine
transverse chart. No global smooth extension is assumed. -/
theorem exists_global_native_transition_phase
    (A C : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hA : ∀ x ∈ A.target, V x = FlowConstruction.partialChartField A.symm
      (fun _ : ℝ × Z => (1, 0)) x)
    (hC : ∀ x ∈ C.target, V x = FlowConstruction.partialChartField C.symm
      (fun _ : ℝ × Z => (1, 0)) x)
    {t₀ : ℝ} (hpA : (t₀, (0 : Z)) ∈ A.source) (hpC : (t₀, (0 : Z)) ∈ C.source)
    (hpoint : A (t₀, 0) = C (t₀, 0)) :
    ∃ (ε : ℝ) (P : PartialDiffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞) (v : Z → ℝ),
      0 < ε ∧ (0 : Z) ∈ P.source ∧ P 0 = 0 ∧ v 0 = 0 ∧ ContDiff ℝ ∞ v ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), ∀ z ∈ P.source,
        (t, z) ∈ A.source ∧ (t + v z, P z) ∈ C.source ∧
          A (t, z) = C (t + v z, P z) := by
  obtain ⟨ε, P, v, hε, hP0, hPzero, hv0, hv, hformula⟩ :=
    exists_native_transition_phase A C V hA hC hpA hpC hpoint
  have hzero : ({0} : Set Z) ⊆ P.source := singleton_subset_iff.mpr hP0
  obtain ⟨g, hg, W, hW, h0W, hWsub, heq⟩ :=
    PeriodTorusLineBundleClassificationTransport.exists_smooth_extension_near_closed
      isClosed_singleton P.open_source hzero hv
  let Q := PartialChart.restrictSource P hW
  have hQ0 : (0 : Z) ∈ Q.source := ⟨hP0, h0W (mem_singleton 0)⟩
  have hg0 : g 0 = 0 := (heq (h0W (mem_singleton 0))).trans hv0
  refine ⟨ε, Q, g, hε, hQ0, hPzero, hg0, hg, ?_⟩
  intro t ht z hz
  have hh := hformula t ht z hz.1
  change (t, z) ∈ A.source ∧ (t + g z, P z) ∈ C.source ∧ A (t, z) = C (t + g z, P z)
  rw [heq hz.2]
  exact hh

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
