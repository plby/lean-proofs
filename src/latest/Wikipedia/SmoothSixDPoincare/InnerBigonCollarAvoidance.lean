import Wikipedia.SmoothSixDPoincare.InnerBigonComplementFilling

/-!
# An inner filling disjoint from the whole remaining native collar

Use the original smooth boundary map on its actual open domain as the obstacle
parametrization. Only the compact collar subset of that domain is forbidden.
Relative perturbation retains the shared boundary germ and all existing
avoidance of the original compact sheet.
-/

noncomputable section

open Set Function Filter Topology ContinuousMap TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

open WhitneyPairModel

variable {E M D Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [TopologicalSpace Y] [ChartedSpace D Y] [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y]

/-- The inner disk can be chosen to miss the entire remaining collar in its interior,
without losing embeddedness, native immersion, the boundary germ, or sheet avoidance. -/
theorem CleanBigonBoundary.exists_collar_disjoint_inner_extension_in_open
    (g : C(Y, M)) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) (range g) T a b k l h)
    (U : Opens M) (hU : (range g ∪ T)ᶜ ⊆ U)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, U),
      ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E)
    (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E) :
    ∃ r : ℝ, r ∈ Ioo (0 : ℝ) 1 ∧ innerBigonCollar h r ⊆ d.domain ∧
      ∃ F : C(ℝ × ℝ, U), ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
        IsClosedEmbedding (fun p : bigon h => F p) ∧
        (∀ p ∈ bigon h, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p)) ∧
        (∀ p ∈ bigon h, (F p : M) ∉ range g) ∧
        (∀ p ∈ interior (bigon h), (F p : M) ∉ d.map '' innerBigonCollar h r) ∧
        ∃ W : Set (ℝ × ℝ), IsOpen W ∧ frontier (bigon h) ⊆ W ∧
          EqOn (Subtype.val ∘ F) (d.map ∘ innerBigonMap h r) W := by
  obtain ⟨r, hr, hcollar, F, hF, hemb, hi, havoid, V, hV, hfrontV, hEq⟩ :=
    d.exists_embedded_inner_extension_in_open g hg U hU hnull hdim hobstacle
  let Q : Opens (ℝ × ℝ) := ⟨d.domain, d.open_domain⟩
  let q : C(Q, M) := ⟨fun p => d.map p,
    continuousOn_iff_continuous_domRestrict.mp d.smooth.continuousOn⟩
  have hq : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ q := by
    intro p
    apply contMDiffAt_subtype_iff.mpr
    exact d.smooth.contMDiffAt (d.open_domain.mem_nhds p.property)
  let A : Set Q := Subtype.val ⁻¹' innerBigonCollar h r
  have himage : q '' A = d.map '' innerBigonCollar h r := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hcollar hp⟩, hp, rfl⟩
  have hclosed : IsClosed (q '' A) := by
    rw [himage]
    exact ((isCompact_innerBigonCollar d.height_pos hr.1.ne').image_of_continuousOn
      (d.smooth.continuousOn.mono hcollar)).isClosed
  have hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (innerBigonMap h r) :=
    (innerBigonDiffeomorph h r hr.1.ne').contMDiff
  let V' : Set (ℝ × ℝ) := V ∩ innerBigonMap h r ⁻¹' d.domain
  have hV' : IsOpen V' := hV.inter (d.open_domain.preimage hs.continuous)
  have hfrontV' : frontier (bigon h) ⊆ V' := by
    intro p hp
    refine ⟨hfrontV hp, hcollar ?_⟩
    exact (innerBigonMap_mem_collar_iff d.height_pos hr
      ((mem_frontier_bigon_iff h p).mp hp).1).mpr hp
  have hfrontCompact : IsCompact (frontier (bigon h)) :=
    (isCompact_bigon d.height_pos).of_isClosed_subset isClosed_frontier
      (fun p hp => ((mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, -, hC, hfrontC, hCV⟩ :=
    exists_compact_closed_between hfrontCompact hV' hfrontV'
  have hinj : InjOn F (bigon h) := by
    intro p hp z hz heq
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨z, hz⟩) heq)
  have hclean : ∀ p ∈ bigon h ∩ C, p ∉ frontier (bigon h) → (F p : M) ∉ q '' A := by
    intro p hp hpB hmem
    rw [himage] at hmem
    obtain ⟨z, hz, heq⟩ := hmem
    have hzp : z = innerBigonMap h r p :=
      d.injective (hcollar hz) (hCV hp.2).2 (heq.trans (hEq (hCV hp.2).1))
    exact hpB ((innerBigonMap_mem_collar_iff d.height_pos hr hp.1).mp (hzp ▸ hz))
  let O : Set U := (Subtype.val : U → M) ⁻¹' (range g)ᶜ
  have hO : IsOpen O := (isCompact_range g.continuous).isClosed.isOpen_compl.preimage
    continuous_subtype_val
  have hmaps : MapsTo F (bigon h) O := fun p hp => havoid p hp
  have hdim' : 2 * Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ E := by
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  have hobstacle' : Module.finrank ℝ (ℝ × ℝ) + Module.finrank ℝ (ℝ × ℝ) <
      Module.finrank ℝ E := by
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨G, hG, hhom, hembG, hiG, hmapsG, havoidG⟩ :=
    ManifoldImmersion.exists_embedded_image_avoidance_relative_neighborhood_in_open
      U F q A hF hq hclosed hdim' hobstacle' (isCompact_bigon d.height_pos) hC hfrontC
      hinj hi hclean hO hmaps
  refine ⟨r, hr, hcollar, G, hG, hembG, hiG, hmapsG, ?_,
    interior C, isOpen_interior, hfrontC, ?_⟩
  · intro p hp hmem
    have hpB : p ∉ frontier (bigon h) := by
      intro hfront
      rw [frontier] at hfront
      exact hfront.2 hp
    exact havoidG p ⟨interior_subset hp, hpB⟩ (by rwa [himage])
  · intro p hp
    have hpC : p ∈ C := interior_subset hp
    exact (congrArg Subtype.val (hhom.fst_eq_snd hpC)).symm.trans (hEq (hCV hpC).1)

end Wikipedia.SmoothSixDPoincare
