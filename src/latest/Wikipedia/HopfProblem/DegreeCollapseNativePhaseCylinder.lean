import Wikipedia.HopfProblem.DegreeCollapsePhaseCylinderChart
import Wikipedia.HopfProblem.DegreeCollapseNativeRationalFieldChart

/-!
# Native flow cylinders in endpoint transverse and phase coordinates

The actual common transverse chart and scalar phase reparametrize the
whole native cylinder without changing its field or target. The source
is exactly the transverse chart source times the entire time axis.
-/

noncomputable section

open Set Function Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z E B M : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace M] [ChartedSpace B M]

theorem exists_native_phase_cylinder
    (Φ : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, B) (Z × ℝ) M ∞)
    {U : Set Z} (hsource : Φ.source = U ×ˢ univ)
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞) (hQtarget : Q.target = U)
    (v : E → ℝ) (hv : ContDiff ℝ ∞ v)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hmodel : ∀ y ∈ Φ.target, V y =
      FlowConstruction.partialChartField Φ.symm (fun _ : Z × ℝ => (0, 1)) y) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞,
      Ψ.source = Q.source ×ˢ univ ∧ Ψ.target = Φ.target ∧
      (∀ p, Ψ p = Φ (Q p.1, p.2 + v p.1)) ∧
      ∀ y ∈ Ψ.target, V y =
        FlowConstruction.partialChartField Ψ.symm (fun _ : E × ℝ => (0, 1)) y := by
  let R := phaseCylinderChart Q v hv
  let Ψ := R.trans Φ
  have hRtarget : R.target = Φ.source := by
    rw [phaseCylinderChart_target, hQtarget, hsource]
  have hΨsource : Ψ.source = Q.source ×ˢ univ := by
    ext p
    change (p ∈ R.source ∧ R p ∈ Φ.source) ↔ p ∈ Q.source ×ˢ univ
    constructor
    · exact fun hp => hp.1
    · intro hp
      exact ⟨hp, hRtarget ▸ R.map_source' hp⟩
  have hΨtarget : Ψ.target = Φ.target := by
    ext y
    change (y ∈ Φ.target ∧ Φ.symm y ∈ R.target) ↔ y ∈ Φ.target
    constructor
    · exact And.left
    · exact fun hy => ⟨hy, hRtarget.symm ▸ Φ.map_target' hy⟩
  refine ⟨Ψ, hΨsource, hΨtarget, fun _ => rfl, ?_⟩
  intro y hy
  rw [hmodel y (hΨtarget ▸ hy)]
  exact (MorseCancellation.partialChartField_of_model_conjugacy R Φ
    (fun _ : E × ℝ => (0, 1)) (fun _ : Z × ℝ => (0, 1))
    (fun p hp => phaseCylinderChart_vertical Q v hv hp) hy).symm

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
