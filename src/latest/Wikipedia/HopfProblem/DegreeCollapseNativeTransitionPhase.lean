import Wikipedia.HopfProblem.DegreeCollapseTransverseTransitionChart

/-!
# Extracting transverse holonomy and phase from the actual native charts

Two native charts of the same vertical field, with one common axis point,
construct a genuine transverse partial diffeomorphism and smooth phase.
The exact native map identity and membership in both actual chart domains
are retained. No derivative, holonomy, or phase data are supplied separately.
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

/-- Extract the actual transverse chart and scalar phase solely from native
field charts meeting at the same axis point. -/
theorem exists_native_transition_phase
    (A C : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hA : ∀ x ∈ A.target, V x = FlowConstruction.partialChartField A.symm
      (fun _ : ℝ × Z => (1, 0)) x)
    (hC : ∀ x ∈ C.target, V x = FlowConstruction.partialChartField C.symm
      (fun _ : ℝ × Z => (1, 0)) x)
    {t₀ : ℝ} (hpA : (t₀, (0 : Z)) ∈ A.source) (hpC : (t₀, (0 : Z)) ∈ C.source)
    (hpoint : A (t₀, 0) = C (t₀, 0)) :
    ∃ (ε : ℝ) (P : PartialDiffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞) (v : Z → ℝ),
      0 < ε ∧ (0 : Z) ∈ P.source ∧ P 0 = 0 ∧ v 0 = 0 ∧
      ContDiffOn ℝ ∞ v P.source ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), ∀ z ∈ P.source,
        (t, z) ∈ A.source ∧ (t + v z, P z) ∈ C.source ∧
          A (t, z) = C (t + v z, P z) := by
  let R := A.trans C.symm
  have hp : (t₀, (0 : Z)) ∈ R.source := by
    refine ⟨hpA, ?_⟩
    change A (t₀, 0) ∈ C.target
    rw [hpoint]
    exact C.map_source' hpC
  have hfix : R (t₀, 0) = (t₀, 0) := by
    change C.symm (A (t₀, 0)) = (t₀, 0)
    rw [hpoint]
    exact C.left_inv' hpC
  have hvertical (p : ℝ × Z) (hp : p ∈ R.source) : fderiv ℝ R p (1, 0) = (1, 0) :=
    native_vertical_transition_derivative A C V hA hC hp
  obtain ⟨ε, P, v, hε, hP0, hPzero, hv0, hv, hsub, hformula⟩ :=
    exists_transverse_transition_chart R hvertical hp hfix
  refine ⟨ε, P, v, hε, hP0, hPzero, hv0, hv, ?_⟩
  intro t ht z hz
  have hpR : (t, z) ∈ R.source := hsub ⟨ht, hz⟩
  have hmap : C.symm (A (t, z)) = (t + v z, P z) := hformula t ht z hz
  refine ⟨hpR.1, ?_, ?_⟩
  · have hh : C.symm (A (t, z)) ∈ C.source := C.map_target' hpR.2
    rwa [hmap] at hh
  · have hh : C (C.symm (A (t, z))) = A (t, z) := C.right_inv' hpR.2
    rw [hmap] at hh
    exact hh.symm

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
