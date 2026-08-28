import Wikipedia.HopfProblem.DegreeCollapseFlowSheetCoordinates
import Wikipedia.HopfProblem.DegreeCollapsePhaseCylinderChart

/-!
# Native immersions of the actual endpoint flow sheets

The transverse phase chart and original cylinder form a genuine native
partial diffeomorphism. Its restriction along an injective linear sheet
has injective native derivative. The exact flow-coordinate germ transfers
this to the actual complete-flow sheet.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {B D Z E M : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem native_partial_chart_linear_immersion
    (P : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞)
    (h0 : (0 : D) ∈ P.source) (L : B →L[ℝ] D) (hL : Injective L) :
    Injective (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) (fun x => P (L x)) 0) := by
  have hp : L (0 : B) ∈ P.source := by simpa only [map_zero] using h0
  have hd : MDifferentiableAt 𝓘(ℝ, B) 𝓘(ℝ, D) L 0 := L.differentiableAt.mdifferentiableAt
  change Injective (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) (P ∘ L) 0)
  rw [mfderiv_comp 0 (P.mdifferentiableAt (by simp) hp) hd, map_zero,
    mfderiv_eq_fderiv, L.fderiv]
  exact (PartialChart.bijective_mfderiv P h0).injective.comp hL

theorem phase_flow_subsheet_immersion
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    {U : Set Z} (hsource : A.source = U ×ˢ univ)
    (F : Flow ℝ M)
    (hflow : ∀ z ∈ U, ∀ s t : ℝ, F t (A (z, s)) = A (z, s + t))
    (Q : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, Z) D Z ∞) (hQU : Q.target ⊆ U)
    (h0 : (0 : D) ∈ Q.source) (hQ0 : Q 0 = 0)
    (S : D → M) (v : D → ℝ) (T : ℝ)
    (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 0)
    (hphase : ∀ u ∈ Q.source, S u = A (Q u, T + v u))
    (L : B →L[ℝ] D) (hL : Injective L) :
    Injective (mfderiv 𝓘(ℝ, ℝ × B) 𝓘(ℝ, E)
      (fun w : ℝ × B => F (w.1 - T) (S (L w.2))) 0) := by
  let C := phaseCylinderChart Q v hv
  let P := C.trans A
  let J : (ℝ × B) →L[ℝ] (D × ℝ) :=
    (L.comp (ContinuousLinearMap.snd ℝ ℝ B)).prod (ContinuousLinearMap.fst ℝ ℝ B)
  have hJ : Injective J := by
    intro u w huw
    exact Prod.ext (congrArg Prod.snd huw) (hL (congrArg Prod.fst huw))
  have h0U : (0 : Z) ∈ U := hQ0 ▸ hQU (Q.map_source' h0)
  have hP0 : (0 : D × ℝ) ∈ P.source := by
    refine ⟨⟨h0, mem_univ _⟩, ?_⟩
    change (Q 0, 0 + v 0) ∈ A.source
    rw [hQ0, hv0, zero_add, hsource]
    exact ⟨h0U, mem_univ _⟩
  have hi := native_partial_chart_linear_immersion P hP0 J hJ
  have hnear : ∀ᶠ w : ℝ × B in 𝓝 0, L w.2 ∈ Q.source :=
    (L.continuous.comp continuous_snd).continuousAt.eventually
      (Q.open_source.mem_nhds (by simpa using h0))
  have heq : (fun w : ℝ × B => F (w.1 - T) (S (L w.2))) =ᶠ[𝓝 0]
      (fun w : ℝ × B => P (J w)) := by
    filter_upwards [hnear] with w hw
    exact (phase_slice_flow_coordinates A hsource F hflow Q hQU S v T hphase (L w.2) hw w.1).1
  rw [heq.mfderiv_eq]
  exact hi

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
