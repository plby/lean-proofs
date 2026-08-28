import Wikipedia.SmoothSixDPoincare.StarConvexTubularNeighborhood
import Wikipedia.SmoothSixDPoincare.TwoDimensionalEmbedding

/-!
# Star-convex tubular charts in the original normed source

An explicit continuous linear equivalence transports the constructed tubular
chart back from a Euclidean source. This includes the product-norm plane used
by the cornered Whitney bigon. Neither the original source topology nor the
original manifold's atlas is changed.
-/

noncomputable section

open Set Function Module
open scoped Manifold ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare

variable {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

/-- Constructed positive-radius tubular coordinates for any finite-dimensional normed source. -/
theorem exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero
    {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D}
    (hK : IsCompact K) (hz : (0 : D) ∈ K) (hstar : StarConvex ℝ (0 : D) K)
    (hinj : InjOn f K)
    (hi : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hcodim : finrank ℝ D + n = finrank ℝ E)
    {O : Set M} (hO : IsOpen O) (hfO : MapsTo f K O) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
          (D × EuclideanSpace ℝ (Fin n)) M ∞,
        K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
        (∀ x, Φ (x, 0) = f x) ∧ Φ.target ⊆ O := by
  let D₀ := EuclideanSpace ℝ (Fin (finrank ℝ D))
  let e : D₀ ≃L[ℝ] D := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin
  let f₀ := f ∘ e
  let K₀ := e ⁻¹' K
  have hf₀ : ContMDiff 𝓘(ℝ, D₀) 𝓘(ℝ, E) ∞ f₀ := hf.comp e.contDiff.contMDiff
  have hK₀ : IsCompact K₀ := e.toHomeomorph.isCompact_preimage.mpr hK
  have hz₀ : (0 : D₀) ∈ K₀ := by
    change e 0 ∈ K
    simpa only [map_zero] using hz
  have hstar₀ : StarConvex ℝ (0 : D₀) K₀ := by
    apply StarConvex.linear_preimage e.toLinearMap
    simpa only [ContinuousLinearEquiv.coe_coe, map_zero] using hstar
  have hinj₀ : InjOn f₀ K₀ := fun _ hx _ hy hxy => e.injective (hinj hx hy hxy)
  have hi₀ : ∀ x ∈ K₀, Injective (mfderiv 𝓘(ℝ, D₀) 𝓘(ℝ, E) f₀ x) := by
    intro x hx
    exact (ManifoldImmersion.injective_mfderiv_comp_linearEquiv_iff e
      (hf.mdifferentiableAt (by simp))).mpr (hi (e x) hx)
  have hcodim₀ : finrank ℝ D₀ + n = finrank ℝ E := by
    simpa only [D₀, finrank_euclideanSpace_fin] using hcodim
  obtain ⟨ε, hε, Φ, hsource, hzero, htarget⟩ :=
    exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf₀ hK₀ hz₀ hstar₀
      hinj₀ hi₀ n hcodim₀ hO (fun _ hx => hfO hx)
  let eprod := e.symm.prodCongr (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)))
  let c := eprod.toDiffeomorph
  let Ψ := c.toPartialDiffeomorph.trans Φ
  have hpre (x : D) (hx : x ∈ K) : e.symm x ∈ K₀ := by
    change e (e.symm x) ∈ K
    simpa only [e.apply_symm_apply] using hx
  refine ⟨ε, hε, Ψ, ?_, ?_, ?_⟩
  · rintro ⟨x, v⟩ ⟨hx, hv⟩
    exact ⟨mem_univ _, hsource ⟨hpre x hx, hv⟩⟩
  · intro x
    change Φ (e.symm x, 0) = f x
    rw [hzero (e.symm x)]
    exact congrArg f (e.apply_symm_apply x)
  · intro y hy
    exact htarget hy.1

/-- The zero-section identity restricted to the specified compact source region. -/
theorem exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D}
    (hK : IsCompact K) (hz : (0 : D) ∈ K) (hstar : StarConvex ℝ (0 : D) K)
    (hinj : InjOn f K)
    (hi : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hcodim : finrank ℝ D + n = finrank ℝ E)
    {O : Set M} (hO : IsOpen O) (hfO : MapsTo f K O) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
          (D × EuclideanSpace ℝ (Fin n)) M ∞,
        K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
        (∀ x ∈ K, Φ (x, 0) = f x) ∧ Φ.target ⊆ O := by
  obtain ⟨ε, hε, Φ, hsource, hzero, htarget⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero
      hf hK hz hstar hinj hi n hcodim hO hfO
  exact ⟨ε, hε, Φ, hsource, fun x _ => hzero x, htarget⟩

end Wikipedia.SmoothSixDPoincare
