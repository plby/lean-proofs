import Wikipedia.HopfProblem.DegreeCollapseCompactIsotopySuspension
import Wikipedia.HopfProblem.DegreeCollapseNativeRationalFieldChart

/-!
# An actual native full flow chart after supported suspension

Compose the original native cylinder with the retained suspension
diffeomorphism. The source and target remain exactly the original ones,
and native pullback composition identifies the new field with vertical
translation. Both exterior coordinate formulas are exact.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {E B M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace M] [ChartedSpace B M]

/-- The complete suspension gives a genuine native vertical chart,
retaining both exterior formulas and the exact original chart domain. -/
theorem exists_native_suspension_chart
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    {U : Set E} (hsource : Φ.source = U ×ˢ univ)
    {D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞} {K : Set E} (hKU : K ⊆ U)
    {W : (E × ℝ) → E × ℝ} {F : Flow ℝ (E × ℝ)}
    (C : SuspensionCoordinates D K W F)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hmodel : ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y) :
    ∃ Ω : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞,
      Ω.source = Φ.source ∧ Ω.target = Φ.target ∧
      (∀ p, Ω p = Φ (C.chart p)) ∧
      (∀ y ∈ Ω.target, V y =
        FlowConstruction.partialChartField Ω.symm (fun _ : E × ℝ => (0, 1)) y) ∧
      (∀ p, p.2 ≤ 0 → Ω p = Φ p) ∧
      (∀ p, 1 ≤ p.2 → Ω p = Φ (D p.1, p.2)) := by
  let Ω := C.chart.toPartialDiffeomorph.trans Φ
  have hΩsource : Ω.source = Φ.source := by
    ext p
    change (p ∈ (univ : Set (E × ℝ)) ∧ C.chart p ∈ Φ.source) ↔ p ∈ Φ.source
    rw [hsource]
    simp only [mem_univ, true_and, mem_prod, and_true, C.base_iff U hKU]
  have hΩtarget : Ω.target = Φ.target := by
    ext y
    change (y ∈ Φ.target ∧ Φ.symm y ∈ (univ : Set (E × ℝ))) ↔ y ∈ Φ.target
    simp only [mem_univ, and_true]
  have hpush (p : E × ℝ) (_ : p ∈ C.chart.toPartialDiffeomorph.source) :
      fderiv ℝ C.chart.toPartialDiffeomorph p (0, 1) = W (C.chart p) := by
    calc
      fderiv ℝ C.chart.toPartialDiffeomorph p (0, 1) =
          suspensionField C.chart (C.chart p) := by
        simp only [suspensionField, C.chart.symm_apply_apply]
        rfl
      _ = W (C.chart p) := (congrArg (fun w => w (C.chart p)) C.field_eq).symm
  refine ⟨Ω, hΩsource, hΩtarget, fun _ => rfl, ?_, ?_, ?_⟩
  · intro y hy
    have hyt : y ∈ Φ.target := hΩtarget ▸ hy
    rw [hmodel y hyt]
    exact (MorseCancellation.partialChartField_of_model_conjugacy
      C.chart.toPartialDiffeomorph Φ (fun _ : E × ℝ => (0, 1)) W hpush hy).symm
  · intro p hp
    change Φ (C.chart p) = Φ p
    rw [C.lower p hp]
  · intro p hp
    change Φ (C.chart p) = Φ (D p.1, p.2)
    rw [C.upper p hp]

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
