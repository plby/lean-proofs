import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenDolbeaultResolution

/-!
# Literal global differential equations on an actual open domain

The two solvability properties refer only to actual ambient functions,
their genuine smoothness on the given open, and their actual coordinate
antiholomorphic derivatives there. They make the true global-section
complex exact and its top map surjective. They are not cohomology,
comparison, or local Poincaré-lemma assumptions.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault

open PeriodTorusLineBundleClassification PeriodTorusLineBundleClassificationCousin

/-- Actual global solvability of the two coordinate equations for closed pairs. -/
def ClosedOneSolvable (Ω : Opens (ℂ × ℂ)) : Prop :=
  ∀ f g : ℂ × ℂ → ℂ, ContDiffOn ℝ ∞ f Ω → ContDiffOn ℝ ∞ g Ω →
    (∀ q ∈ Ω, dbarFirst g q = dbarSecond f q) →
    ∃ u : ℂ × ℂ → ℂ, ContDiffOn ℝ ∞ u Ω ∧
      ∀ q ∈ Ω, dbarFirst u q = f q ∧ dbarSecond u q = g q

/-- Actual global solvability of the literal top coordinate equation. -/
def TopSolvable (Ω : Opens (ℂ × ℂ)) : Prop :=
  ∀ w : ℂ × ℂ → ℂ, ContDiffOn ℝ ∞ w Ω →
    ∃ a b : ℂ × ℂ → ℂ, ContDiffOn ℝ ∞ a Ω ∧ ContDiffOn ℝ ∞ b Ω ∧
      ∀ q ∈ Ω, dbarFirst b q - dbarSecond a q = w q

/-- Actual coefficient primitives are actual section primitives. -/
theorem exists_section_primitive (Ω : Opens (ℂ × ℂ)) (hOne : ClosedOneSolvable Ω)
    (s : AffineDolbeault.PairSection Ω) (hs : AffineDolbeault.topSection Ω s = 0) :
    ∃ t : AffineDolbeault.SmoothSection Ω, AffineDolbeault.differentialSection Ω t = s := by
  obtain ⟨u, hu, he⟩ := hOne _ _
    (AffineDolbeault.smoothExtend_contDiffOn Ω s.1)
    (AffineDolbeault.smoothExtend_contDiffOn Ω s.2)
    (AffineDolbeault.closed_of_topSection_zero Ω s hs)
  let t := AffineDolbeault.sectionOfSmooth Ω u hu
  refine ⟨t, ?_⟩
  apply Prod.ext
  · apply ContMDiffMap.ext
    intro q
    change dbarFirst (AffineDolbeault.smoothExtend Ω t) q = s.1 q
    rw [dbarFirst_congr (AffineDolbeault.smoothExtend_sectionOfSmooth_germ Ω u hu q q.property)]
    exact (he q q.property).1.trans (AffineDolbeault.smoothExtend_apply Ω s.1 q q.property)
  · apply ContMDiffMap.ext
    intro q
    change dbarSecond (AffineDolbeault.smoothExtend Ω t) q = s.2 q
    rw [dbarSecond_congr (AffineDolbeault.smoothExtend_sectionOfSmooth_germ Ω u hu q q.property)]
    exact (he q q.property).2.trans (AffineDolbeault.smoothExtend_apply Ω s.2 q q.property)

/-- An actual top coefficient primitive gives a genuine smooth pair section. -/
theorem exists_section_top_primitive (Ω : Opens (ℂ × ℂ)) (hTop : TopSolvable Ω)
    (s : AffineDolbeault.SmoothSection Ω) :
    ∃ t : AffineDolbeault.PairSection Ω, AffineDolbeault.topSection Ω t = s := by
  obtain ⟨a, b, ha, hb, he⟩ := hTop _ (AffineDolbeault.smoothExtend_contDiffOn Ω s)
  let sa := AffineDolbeault.sectionOfSmooth Ω a ha
  let sb := AffineDolbeault.sectionOfSmooth Ω b hb
  refine ⟨(sa, sb), ?_⟩
  apply ContMDiffMap.ext
  intro q
  change dbarFirst (AffineDolbeault.smoothExtend Ω sb) q -
    dbarSecond (AffineDolbeault.smoothExtend Ω sa) q = s q
  rw [dbarFirst_congr (AffineDolbeault.smoothExtend_sectionOfSmooth_germ Ω b hb q q.property),
    dbarSecond_congr (AffineDolbeault.smoothExtend_sectionOfSmooth_germ Ω a ha q q.property)]
  exact (he q q.property).trans (AffineDolbeault.smoothExtend_apply Ω s q q.property)

theorem sectionComplex_exact (Ω : Opens (ℂ × ℂ)) (hOne : ClosedOneSolvable Ω) :
    (sectionComplex Ω).Exact := by
  apply (ShortComplex.ab_exact_iff_function_exact (sectionComplex Ω)).mpr
  intro s
  constructor
  · exact exists_section_primitive Ω hOne s
  · rintro ⟨t, rfl⟩
    exact AffineDolbeault.topSection_differentialSection Ω t

theorem sectionComplex_top_epi (Ω : Opens (ℂ × ℂ)) (hTop : TopSolvable Ω) :
    Epi (sectionComplex Ω).g := by
  apply ConcreteCategory.epi_of_surjective
  intro s
  obtain ⟨t, ht⟩ := exists_section_top_primitive Ω hTop s
  exact ⟨t, ht⟩

/-- The genuine global complex of the restricted resolution is exact. -/
theorem globalComplex_exact (Ω : Opens (ℂ × ℂ)) (hOne : ClosedOneSolvable Ω) :
    (restrictedResolution Ω).globalComplex.Exact :=
  ShortComplex.exact_of_iso (globalComplexIso Ω).symm (sectionComplex_exact Ω hOne)

/-- Actual top solvability makes the genuine last global-sections map epic. -/
theorem globalComplex_top_epi (Ω : Opens (ℂ × ℂ)) (hTop : TopSolvable Ω) :
    Epi (restrictedResolution Ω).globalComplex.g := by
  let : Epi (sectionComplex Ω).g := sectionComplex_top_epi Ω hTop
  have : Epi ((sectionComplex Ω).g ≫ (globalComplexIso Ω).inv.τ₃) := by infer_instance
  exact epi_of_epi_fac (globalComplexIso Ω).inv.comm₂₃

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault
