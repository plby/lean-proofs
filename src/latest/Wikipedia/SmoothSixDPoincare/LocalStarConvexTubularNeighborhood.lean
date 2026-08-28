import Wikipedia.SmoothSixDPoincare.StarConvexSmoothExtension
import Wikipedia.SmoothSixDPoincare.NormedStarConvexTubularNeighborhood
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Tubular coordinates for locally smooth parametrizations

The parametrization is only required to be smooth on its actual open domain.
The constructed chart retains the original parametrization on every point of
its zero section, and its base projection stays in that domain.
-/

noncomputable section

open Set Function Module
open scoped Manifold ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare

variable {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

/-- An actual tubular chart for a locally smooth compact star-convex embedded region. -/
theorem exists_local_tubularNeighborhood_of_embedded_starConvex {f : D → M} {K U : Set D}
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hK : IsCompact K) (hz : (0 : D) ∈ K) (hstar : StarConvex ℝ (0 : D) K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hinj : InjOn f K)
    (hi : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hcodim : finrank ℝ D + n = finrank ℝ E)
    {O : Set M} (hO : IsOpen O) (hfO : MapsTo f K O) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
          (D × EuclideanSpace ℝ (Fin n)) M ∞,
        K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
        Φ.source ⊆ U ×ˢ univ ∧
        (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧ Φ.target ⊆ O := by
  obtain ⟨g, hg, V, hV, hKV, hVU, heq⟩ :=
    exists_smooth_extension_near_starConvex hK hz hstar hU hKU hf
  have hinjg : InjOn g K := by
    intro x hx y hy hxy
    apply hinj hx hy
    simpa only [heq (hKV hx), heq (hKV hy)] using hxy
  have hig : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x) := by
    intro x hx
    have hnear : g =ᶠ[𝓝 x] f := Filter.Eventually.mono (hV.mem_nhds (hKV hx)) heq
    rw [hnear.mfderiv_eq]
    exact hi x hx
  have hgO : MapsTo g K O := by
    intro x hx
    rw [heq (hKV hx)]
    exact hfO hx
  obtain ⟨ε, hε, Φ, hsource, hzero, htarget⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero
      hg hK hz hstar hinjg hig n hcodim hO hgO
  let Ψ := PartialChart.restrictSource Φ (hV.preimage
    (continuous_fst : Continuous (Prod.fst : D × EuclideanSpace ℝ (Fin n) → D)))
  refine ⟨ε, hε, Ψ, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨hsource hp, hKV hp.1⟩
  · intro p hp
    exact ⟨hVU hp.2, mem_univ _⟩
  · intro x hx
    change Φ (x, 0) = f x
    exact (hzero x).trans (heq hx.2)
  · intro y hy
    exact htarget hy.1

end Wikipedia.SmoothSixDPoincare
