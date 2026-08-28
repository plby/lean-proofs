import Wikipedia.HopfProblem.CoveringManifold

/-!
# Local deck transformations in quotient coordinates

A transition between covering-quotient charts is locally the coordinate
expression of one fixed deck transformation.  The statement is an equality
of actual maps near the point, and can therefore be used for derivatives.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CoveringQuotient

variable {E M Q G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q]
    [Group G] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G)

/-- A continuous local lift differs locally from the identity lift by one
fixed element of the covering group. -/
theorem localInverse_eventually_deck (hG : ∀ g : G, Continuous (fun x : M => g • x))
    (a x : M) (hx : q x ∈ (localInverse hq a).source) :
    ∃ g : G, localInverse hq a (q x) = g • x ∧
      (localInverse hq a ∘ q) =ᶠ[𝓝 x] (fun y => g • y) := by
  have hc : ContinuousAt (localInverse hq a ∘ q) x :=
    ((localInverse hq a).continuousAt hx).comp hq.continuous.continuousAt
  obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp (project_localInverse hq a hx)
  refine ⟨g, hg.symm, ?_⟩
  apply eventuallyEq_of_localHomeomorph_comp_eq hq.isCoveringMap.isLocalHomeomorph
    hc (hG g).continuousAt hg.symm
  have hs : ∀ᶠ y in 𝓝 x, q y ∈ (localInverse hq a).source :=
    hq.continuous.continuousAt ((localInverse hq a).open_source.mem_nhds hx)
  exact hs.mono fun y hy => (project_localInverse hq a hy).trans (hq.map_smul g).symm

omit [NormedSpace ℂ E] in
/-- Every quotient-coordinate transition agrees near every point of its
source with the source and target charts around a single deck map. -/
theorem transition_eventually_deck
    (hG : ∀ g : G, Continuous (fun x : M => g • x)) (x y : Q) {z : E}
    (hz : z ∈ ((chart (E := E) hq x).symm.trans (chart (E := E) hq y)).source) :
    ∃ g : G,
      g • (chartAt E (representative hq x)).symm z ∈
        (chartAt E (representative hq y)).source ∧
      (((chart (E := E) hq x).symm.trans (chart (E := E) hq y)) : E → E) =ᶠ[𝓝 z]
        (chartAt E (representative hq y) ∘ (fun a : M => g • a) ∘
          (chartAt E (representative hq x)).symm) := by
  have hza : z ∈ (chartAt E (representative hq x)).target := hz.1.1
  have hy : q ((chartAt E (representative hq x)).symm z) ∈
      (chart (E := E) hq y).source := by
    simpa only [OpenPartialHomeomorph.symm_symm, chart_symm, Function.comp_apply,
      Set.mem_preimage] using hz.2
  obtain ⟨g, hg, he⟩ := localInverse_eventually_deck hq hG (representative hq y)
    ((chartAt E (representative hq x)).symm z) hy.1
  refine ⟨g, ?_, ?_⟩
  · rw [← hg]
    exact hy.2
  · rw [transition_eq]
    exact (he.comp_tendsto ((chartAt E (representative hq x)).symm.continuousAt hza)).fun_comp
      (chartAt E (representative hq y))

end Wikipedia.HopfProblem.CoveringQuotient
