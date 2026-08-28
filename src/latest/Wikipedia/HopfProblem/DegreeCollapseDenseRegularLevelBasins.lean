import Wikipedia.HopfProblem.DegreeCollapseDenseMinimumBasins
import Wikipedia.HopfProblem.DegreeCollapseNativeFlowCylinder

/-!
# Minimum basins are dense on each actual regular level

An open subset of a cylinder section sweeps out an open subset of the
original manifold. Density there and flow invariance give density on the
section. The native cylinder is constructed from the original regular level
and the same complete flow, so the conclusion retains both.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem dense_section_of_flow_cylinder {N X : Type*}
    [TopologicalSpace N] [TopologicalSpace X]
    (A : OpenPartialHomeomorph (N × ℝ) X) (hsource : A.source = univ)
    (F : Flow ℝ X) (ι : N → X) (hformula : ∀ z, A z = F z.2 (ι z.1))
    {B : Set X} (hB : Dense B) (hinv : ∀ t x, F t x ∈ B ↔ x ∈ B) :
    Dense (ι ⁻¹' B) := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  have hdom : U ×ˢ (univ : Set ℝ) ⊆ A.source := by rw [hsource]; exact subset_univ _
  have hopen : IsOpen (A '' (U ×ˢ (univ : Set ℝ))) :=
    A.isOpen_image_of_subset_source (hU.prod isOpen_univ) hdom
  obtain ⟨z, hz⟩ := hne
  have himage : (A '' (U ×ˢ (univ : Set ℝ))).Nonempty :=
    ⟨A (z, 0), (z, 0), ⟨hz, mem_univ _⟩, rfl⟩
  obtain ⟨x, hx, hxB⟩ := hB.inter_open_nonempty _ hopen himage
  obtain ⟨⟨w, t⟩, ⟨hw, -⟩, rfl⟩ := hx
  refine ⟨w, hw, ?_⟩
  apply (hinv t (ι w)).mp
  rwa [hformula] at hxB

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.dense_regular_level_minimum_basins
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (hreg : ∀ x, f x = a → x ∉ criticalPoints E f) :
    Dense {x : {y : M // f y = a} | ∃ p : criticalPoints E f,
      nativeMorseIndex E f p = 0 ∧ Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)} := by
  let L := {y : M // f y = a}
  rcases isEmpty_or_nonempty L with h | h
  · exact fun x => isEmptyElim x
  · let _ := RegularLevel.chartedSpace hf hreg
    obtain ⟨A, hsource, -, hformula, -⟩ := FlowCancellation.exists_native_level_flow_cylinder
      hf hreg S.smooth S.flow S.integral (fun x hx => S.descent x (hreg x hx))
      (Classical.arbitrary L)
    apply dense_section_of_flow_cylinder A.toOpenPartialHomeomorph hsource S.flow
      Subtype.val hformula (S.dense_minimum_forward_basins hf)
    intro t x
    constructor
    · rintro ⟨p, hp, hlim⟩
      exact ⟨p, hp, (flow_time_atTop_limit_iff S.flow t x p.val).mp hlim⟩
    · rintro ⟨p, hp, hlim⟩
      exact ⟨p, hp, (flow_time_atTop_limit_iff S.flow t x p.val).mpr hlim⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
