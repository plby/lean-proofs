import Wikipedia.SmoothSixDPoincare.CleanStarConvexTubularNeighborhood

/-!
# Clean ambient coordinates along a native embedded sheet

A genuine partial chart inside the sheet, together with its native immersive
embedding, determines ambient tubular coordinates along any compact star-convex
source region. The embedding topology excludes the rest of the full sheet,
not just the part parametrized by that chart.
-/

noncomputable section

open Set Function Module Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.SmoothSixDPoincare

variable {E M D G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace N] [ChartedSpace G N]

/-- Ambient tubular coordinates are clean relative to the entire native sheet image. -/
theorem exists_clean_embedded_sheet_neighborhood {F : N → M}
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F) (hembF : IsEmbedding F)
    (c : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, G) D N ∞) {K : Set D}
    (hK : IsCompact K) (hz : (0 : D) ∈ K) (hstar : StarConvex ℝ (0 : D) K)
    (hKc : K ⊆ c.source)
    (hiF : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F (c x)))
    (n : ℕ) (hcodim : finrank ℝ D + n = finrank ℝ E)
    {O : Set M} (hO : IsOpen O) (hFO : MapsTo (F ∘ c) K O) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
          (D × EuclideanSpace ℝ (Fin n)) M ∞,
        K ×ˢ closedBall 0 ε ⊆ Φ.source ∧
        Φ.source ⊆ c.source ×ˢ univ ∧ Φ.target ⊆ O ∧
        (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = F (c x)) ∧
        (∀ q ∈ Φ.source, Φ q ∈ range F ↔ q.2 = 0) := by
  let f := F ∘ c
  have hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f c.source :=
    hF.comp_contMDiffOn c.contMDiffOn_toFun
  have hembf : IsEmbedding (fun x : c.source => f x) :=
    hembF.comp c.toOpenPartialHomeomorph.isEmbedding_restrict
  have hi : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x) := by
    intro x hx
    rw [mfderiv_comp x (hF.mdifferentiableAt (by simp))
      (c.mdifferentiableAt (by simp) (hKc hx))]
    exact (hiF x hx).comp (PartialChart.bijective_mfderiv c (hKc hx)).1
  obtain ⟨A, hA, hpreA⟩ := hembF.isInducing.isOpen_iff.mp c.open_target
  have hfA : MapsTo f K A := by
    intro x hx
    change c x ∈ F ⁻¹' A
    rw [hpreA]
    exact c.map_source' (hKc hx)
  obtain ⟨ε, hε, Φ, hprod, hsource, htarget, hzero, himage⟩ :=
    exists_clean_tubularNeighborhood_of_embedded_starConvex hf hK hz hstar c.open_source
      hKc hembf hi n hcodim (hO.inter hA) (fun x hx => ⟨hFO hx, hfA hx⟩)
  refine ⟨ε, hε, Φ, hprod, hsource, fun _ hy => (htarget hy).1, hzero, ?_⟩
  intro q hq
  have hqA := (htarget (Φ.map_source' hq)).2
  have hrange : Φ q ∈ range F ↔ Φ q ∈ f '' c.source := by
    constructor
    · rintro ⟨y, hy⟩
      have hyA : F y ∈ A := hy ▸ hqA
      have hyT : y ∈ c.target := by
        change y ∈ F ⁻¹' A at hyA
        rwa [hpreA] at hyA
      exact ⟨c.invFun y, c.map_target' hyT, (congrArg F (c.right_inv' hyT)).trans hy⟩
    · rintro ⟨u, _, hu⟩
      exact ⟨c u, hu⟩
  exact hrange.trans (himage q hq)

end Wikipedia.SmoothSixDPoincare
