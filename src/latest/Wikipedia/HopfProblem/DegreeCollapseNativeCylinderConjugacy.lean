import Wikipedia.HopfProblem.DegreeCollapseNativeRationalFieldChart
import Wikipedia.HopfProblem.DegreeCollapseSuspensionVectorField

/-!
# Native cylinders under an actual coordinate-flow conjugacy

Any genuine model diffeomorphism preserving the working base region
gives a native chart with exactly the old source and target. Its actual
conjugated vertical field is the native pullback of vertical translation.
The time coordinate need not be preserved.
-/

noncomputable section

open Set Function Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z E M : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem exists_native_cylinder_conjugacy
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    {U : Set Z} (hsource : Φ.source = U ×ˢ univ)
    (D : Diffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, Z × ℝ) (Z × ℝ) (Z × ℝ) ∞)
    (hbase : ∀ p, (D p).1 ∈ U ↔ p.1 ∈ U)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hmodel : ∀ y ∈ Φ.target,
      V y = FlowConstruction.partialChartField Φ.symm (suspensionField D) y) :
    ∃ Ω : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞,
      Ω.source = U ×ˢ univ ∧ Ω.target = Φ.target ∧
      (∀ p, Ω p = Φ (D p)) ∧
      ∀ y ∈ Ω.target, V y =
        FlowConstruction.partialChartField Ω.symm (fun _ : Z × ℝ => (0, 1)) y := by
  let Ω := D.toPartialDiffeomorph.trans Φ
  have hΩsource : Ω.source = U ×ˢ univ := by
    ext p
    change (p ∈ (univ : Set (Z × ℝ)) ∧ D p ∈ Φ.source) ↔ p ∈ U ×ˢ univ
    rw [hsource]
    simp only [mem_univ, true_and, mem_prod, and_true, hbase]
  have hΩtarget : Ω.target = Φ.target := by
    ext y
    change (y ∈ Φ.target ∧ Φ.symm y ∈ (univ : Set (Z × ℝ))) ↔ y ∈ Φ.target
    simp only [mem_univ, and_true]
  have hpush (p : Z × ℝ) (_ : p ∈ D.toPartialDiffeomorph.source) :
      fderiv ℝ D.toPartialDiffeomorph p (0, 1) = suspensionField D (D p) := by
    simp only [suspensionField, D.symm_apply_apply]
    rfl
  refine ⟨Ω, hΩsource, hΩtarget, fun _ => rfl, ?_⟩
  intro y hy
  rw [hmodel y (hΩtarget ▸ hy)]
  exact (MorseCancellation.partialChartField_of_model_conjugacy
    D.toPartialDiffeomorph Φ (fun _ : Z × ℝ => (0, 1)) (suspensionField D) hpush hy).symm

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
