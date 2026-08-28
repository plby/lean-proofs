import Wikipedia.HopfProblem.CoveringImmersion

/-!
# Descent of immersions through an analytic covering of the source

The source chart downstairs is a local covering inverse followed by the
source chart of the immersion upstairs.  Its analytic inverse is the
upstairs inverse chart followed by the covering projection.  Thus the
coordinate inclusion normal form descends without changing the complement.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CoveringQuotient

variable {E E' F M N Q G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace E' N]
    [TopologicalSpace Q] [Group G] [MulAction G M]
    [IsManifold (modelWithCornersSelf ℂ E) ω M]
    {q : M → Q} (hq : IsQuotientCoveringMap q G)
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (fun x : M => g • x))

include hG in
/-- A continuous map from the analytic quotient is an immersion whenever
its composition with the covering projection is an immersion. -/
theorem immersion_of_comp_project {f : Q → N} (hc : Continuous f)
    (hi : Manifold.IsImmersionOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E') ω (f ∘ q)) :
    letI := chartedSpace (E := E) hq
    Manifold.IsImmersionOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E') ω f := by
  let := chartedSpace (E := E) hq
  let := isManifold (E := E) hq ω hG
  intro x
  let a := representative hq x
  let c := localInverse hq a
  have hcx : x ∈ c.source := by
    have h := hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source (x := a)
    simpa only [c, localInverse, a, project_representative] using h
  have hqx : q (c x) = x := project_localInverse hq a hcx
  let h := hi (c x)
  let d := c.trans h.domChart
  have hdSymm : (d.symm : E → Q) = q ∘ h.domChart.symm := by
    change (localInverse hq a).symm ∘ h.domChart.symm = _
    rw [localInverse_symm]
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt hc.continuousAt
    h.equiv d h.codChart ⟨hcx, h.mem_domChart_source⟩ ?_ ?_
    h.codChart_mem_maximalAtlas ?_
  · simpa only [Function.comp_apply, hqx] using h.mem_codChart_source
  · apply d.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).comp
        ((localInverse_holomorphic hq ω hG a).mono inter_subset_left) (fun _ hw => hw.2)
    · rw [hdSymm]
      exact (contMDiff_project hq ω hG).comp_contMDiffOn
        ((contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mono inter_subset_left)
  · intro z hz
    have hz' : z ∈ d.target := by simpa [OpenPartialHomeomorph.extend] using hz
    change h.codChart (f (d.symm z)) = h.equiv (z, 0)
    rw [hdSymm]
    exact h.writtenInCharts (by simpa [OpenPartialHomeomorph.extend] using hz'.1)

end Wikipedia.HopfProblem.CoveringQuotient
