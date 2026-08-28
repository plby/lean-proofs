import Wikipedia.HopfProblem.DegreeCollapseEndpointVerticalChart

/-!
# The actual transition between two native field charts

The original native field determines the derivative of the real
coordinate transition. Two charts representing vertical velocity have a
transition whose derivative fixes vertical velocity on its entire domain.
This is derived from the original manifold derivatives and inverse maps.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {D B E M : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The true coordinate transition intertwines the two represented fields. -/
theorem native_field_transition_pushforward
    (A : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞)
    (C : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, E) B M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (WA : D → D) (WC : B → B)
    (hA : ∀ x ∈ A.target, V x = FlowConstruction.partialChartField A.symm WA x)
    (hC : ∀ x ∈ C.target, V x = FlowConstruction.partialChartField C.symm WC x)
    {p : D} (hp : p ∈ (A.trans C.symm).source) :
    fderiv ℝ (C.symm ∘ A) p (WA p) = WC (C.symm (A p)) := by
  have hpA : p ∈ A.source := hp.1
  have hpC : A p ∈ C.target := hp.2
  have hpushA : mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) A p
      ((NormedSpace.fromTangentSpace p).symm (WA p)) = V (A p) := by
    have hh := hA (A p) (A.map_source' hpA)
    rw [FlowConstruction.partialChartField_eq_mfderiv_symm A.symm WA (A.map_source' hpA)] at hh
    have hi : A.symm (A p) = p := A.left_inv' hpA
    rw [hi] at hh
    exact hh.symm
  have hdiff : C.symm.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, B) :=
    ⟨C.symm.mdifferentiableOn (by simp), C.mdifferentiableOn (by simp)⟩
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) C.symm (A p)).IsInvertible :=
    ⟨hdiff.mfderiv hpC, rfl⟩
  have hpushC : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) C.symm (A p) (V (A p)) =
      (NormedSpace.fromTangentSpace (C.symm (A p))).symm (WC (C.symm (A p))) := by
    rw [hC (A p) hpC]
    unfold FlowConstruction.partialChartField
    rw [VectorField.mpullback_apply]
    exact hinv.self_apply_inverse _
  rw [← mfderiv_eq_fderiv, mfderiv_comp p
    (C.symm.mdifferentiableAt (by simp) hpC) (A.mdifferentiableAt (by simp) hpA)]
  change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) C.symm (A p))
    ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) A p)
      ((NormedSpace.fromTangentSpace p).symm (WA p))) = _
  rw [hpushA]
  exact hpushC

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- On its entire source, an actual transition between vertical field
charts has exactly unit vertical derivative and zero transverse derivative. -/
theorem native_vertical_transition_derivative
    (A C : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hA : ∀ x ∈ A.target, V x = FlowConstruction.partialChartField A.symm
      (fun _ : ℝ × Z => (1, 0)) x)
    (hC : ∀ x ∈ C.target, V x = FlowConstruction.partialChartField C.symm
      (fun _ : ℝ × Z => (1, 0)) x)
    {p : ℝ × Z} (hp : p ∈ (A.trans C.symm).source) :
    fderiv ℝ (C.symm ∘ A) p (1, 0) = (1, 0) :=
  native_field_transition_pushforward A C V (fun _ => (1, 0)) (fun _ => (1, 0)) hA hC hp

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
