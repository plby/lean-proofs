import Wikipedia.HopfProblem.DegreeCollapseFlowSheetImmersion

/-!
# Actual native charts with exact flow-invariant basin planes

The phase chart composed with the original cylinder is a native partial
diffeomorphism. Its full coordinate formula is the actual endpoint slice
flow, so any flow-invariant basin equation on that slice is an exact
coordinate equation throughout the chart source.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {D Z E M : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem exists_phase_flow_basin_chart
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    {U : Set Z} (hsource : A.source = U ×ˢ univ)
    (F : Flow ℝ M)
    (hflow : ∀ z ∈ U, ∀ s t : ℝ, F t (A (z, s)) = A (z, s + t))
    (Q : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, Z) D Z ∞) (hQU : Q.target ⊆ U)
    (h0 : (0 : D) ∈ Q.source) (hQ0 : Q 0 = 0)
    (S : D → M) (v : D → ℝ) (T : ℝ)
    (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0)
    (hphase : ∀ u ∈ Q.source, S u = A (Q u, T + v u))
    (Basin : M → Prop) (hshift : ∀ t x, Basin (F t x) ↔ Basin x)
    (R : D → Prop) (hbasin : ∀ u ∈ Q.source, Basin (S u) ↔ R u) :
    ∃ P : PartialDiffeomorph 𝓘(ℝ, D × ℝ) 𝓘(ℝ, E) (D × ℝ) M ∞,
      P.source = Q.source ×ˢ univ ∧ (0 : D × ℝ) ∈ P.source ∧ P 0 = A 0 ∧
      (∀ u ∈ Q.source, ∀ t, P (u, t) = F (t - T) (S u)) ∧
      ∀ w ∈ P.source, Basin (P w) ↔ R w.1 := by
  let C := phaseCylinderChart Q v hv
  let P := C.trans A
  have hPsource : P.source = Q.source ×ˢ univ := by
    ext w
    change (w ∈ Q.source ×ˢ univ ∧ (Q w.1, w.2 + v w.1) ∈ A.source) ↔
      w ∈ Q.source ×ˢ univ
    constructor
    · exact And.left
    · intro hw
      refine ⟨hw, ?_⟩
      rw [hsource]
      exact ⟨hQU (Q.map_source' hw.1), mem_univ _⟩
  have hP0 : (0 : D × ℝ) ∈ P.source := by
    rw [hPsource]
    exact ⟨h0, mem_univ _⟩
  have hPzero : P 0 = A 0 := by
    change A (Q 0, 0 + v 0) = A (0, 0)
    rw [hQ0, hv0, zero_add]
  have hPflow (u : D) (hu : u ∈ Q.source) (t : ℝ) : P (u, t) = F (t - T) (S u) :=
    (phase_slice_flow_coordinates A hsource F hflow Q hQU S v T hphase u hu t).1.symm
  refine ⟨P, hPsource, hP0, hPzero, hPflow, ?_⟩
  intro w hw
  rw [hPsource] at hw
  rw [show P w = F (w.2 - T) (S w.1) from hPflow w.1 hw.1 w.2]
  exact (hshift (w.2 - T) (S w.1)).trans (hbasin w.1 hw.1)

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem phase_flow_chart_subsheet_germ
    (P : PartialDiffeomorph 𝓘(ℝ, D × ℝ) 𝓘(ℝ, E) (D × ℝ) M ∞)
    {O : Set D} (hO : IsOpen O) (h0 : (0 : D) ∈ O)
    (F : Flow ℝ M) (S : D → M) (T : ℝ)
    (hformula : ∀ u ∈ O, ∀ t, P (u, t) = F (t - T) (S u)) (L : B →L[ℝ] D) :
    (fun w : ℝ × B => F (w.1 - T) (S (L w.2))) =ᶠ[𝓝 0]
      (fun w : ℝ × B => P (L w.2, w.1)) := by
  have hnear : ∀ᶠ w : ℝ × B in 𝓝 0, L w.2 ∈ O :=
    (L.continuous.comp continuous_snd).continuousAt.eventually
      (hO.mem_nhds (by simpa only [Function.comp_apply, Prod.snd_zero, map_zero] using h0))
  filter_upwards [hnear] with w hw
  exact (hformula (L w.2) hw w.1).symm

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
