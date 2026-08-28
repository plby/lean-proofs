import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultExact
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalDbar
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDbarTwo
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionSections

/-!
# Exactness of the actual global affine Dolbeault section complex

The globally constructed `(0,1)` primitive and the exact-stabilization
top-degree primitive apply to the literal global smooth coefficients.
They prove exactness and surjectivity on genuine global sections. These
are analytic proofs, not consequences of a presumed cohomology vanishing.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault

open PeriodTorusLineBundleClassification PeriodTorusLineBundleClassificationCousin

/-- The ambient representative of a global smooth section is smooth everywhere. -/
theorem smoothExtend_top_contDiff (s : SmoothSection ⊤) :
    ContDiff ℝ ∞ (smoothExtend ⊤ s) :=
  contDiffOn_univ.mp (smoothExtend_contDiffOn ⊤ s)

/-- Every genuine closed global coefficient pair has a genuine global
smooth primitive, using the proved global two-variable integral solver. -/
theorem exists_global_primitive (s : PairSection ⊤) (hs : topSection ⊤ s = 0) :
    ∃ t : SmoothSection ⊤, differentialSection ⊤ t = s := by
  obtain ⟨u, hu, hfirst, hsecond⟩ := exists_smooth_global_dbar_primitive
    (smoothExtend_top_contDiff s.1) (smoothExtend_top_contDiff s.2)
    (fun q => closed_of_topSection_zero ⊤ s hs q (by trivial))
  let t := sectionOfSmooth ⊤ u hu.contDiffOn
  refine ⟨t, ?_⟩
  apply Prod.ext
  · apply ContMDiffMap.ext
    intro q
    change dbarFirst (smoothExtend ⊤ t) q = s.1 q
    rw [dbarFirst_congr (smoothExtend_sectionOfSmooth_germ ⊤ u hu.contDiffOn q q.property)]
    exact (hfirst q).trans (smoothExtend_apply ⊤ s.1 q q.property)
  · apply ContMDiffMap.ext
    intro q
    change dbarSecond (smoothExtend ⊤ t) q = s.2 q
    rw [dbarSecond_congr (smoothExtend_sectionOfSmooth_germ ⊤ u hu.contDiffOn q q.property)]
    exact (hsecond q).trans (smoothExtend_apply ⊤ s.2 q q.property)

/-- Every genuine global top coefficient is the actual top derivative
of a genuine smooth pair, using the proved exact-stabilization solver. -/
theorem exists_global_top_primitive (s : SmoothSection ⊤) :
    ∃ t : PairSection ⊤, topSection ⊤ t = s := by
  obtain ⟨a, b, ha, hb, he⟩ := DbarTwo.exists_smooth_top_primitive (smoothExtend_top_contDiff s)
  let sa := sectionOfSmooth ⊤ a ha.contDiffOn
  let sb := sectionOfSmooth ⊤ b hb.contDiffOn
  refine ⟨(sa, sb), ?_⟩
  apply ContMDiffMap.ext
  intro q
  change dbarFirst (smoothExtend ⊤ sb) q - dbarSecond (smoothExtend ⊤ sa) q = s q
  rw [dbarFirst_congr (smoothExtend_sectionOfSmooth_germ ⊤ b hb.contDiffOn q q.property),
    dbarSecond_congr (smoothExtend_sectionOfSmooth_germ ⊤ a ha.contDiffOn q q.property)]
  exact (he q).trans (smoothExtend_apply ⊤ s q q.property)

/-- The literal global-sections complex of the genuine resolution is exact. -/
theorem globalComplex_exact : resolution.globalComplex.Exact := by
  apply (ShortComplex.ab_exact_iff_function_exact resolution.globalComplex).mpr
  intro s
  constructor
  · exact exists_global_primitive s
  · rintro ⟨t, rfl⟩
    exact topSection_differentialSection ⊤ t

/-- The last actual global-sections map is surjective, not just stalkwise epic. -/
instance globalTop_epi : Epi resolution.globalComplex.g := by
  apply ConcreteCategory.epi_of_surjective
  intro s
  obtain ⟨t, ht⟩ := exists_global_top_primitive s
  exact ⟨t, ht⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault
