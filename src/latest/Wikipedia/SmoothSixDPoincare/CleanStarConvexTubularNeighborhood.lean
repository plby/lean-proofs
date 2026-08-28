import Wikipedia.SmoothSixDPoincare.LocalStarConvexTubularNeighborhood

/-!
# Clean tubular coordinates along an embedded sheet patch

The embedding topology excludes other branches of the entire patch image.
Consequently, inside the constructed chart, membership in that image is
equivalent to vanishing of the normal coordinate.
-/

noncomputable section

open Set Function Module Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.SmoothSixDPoincare

variable {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

/-- The entire embedded patch image meets the tubular chart exactly in its zero section. -/
theorem exists_clean_tubularNeighborhood_of_embedded_starConvex {f : D → M} {K U : Set D}
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hK : IsCompact K) (hz : (0 : D) ∈ K) (hstar : StarConvex ℝ (0 : D) K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hemb : IsEmbedding (fun x : U => f x))
    (hi : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hcodim : finrank ℝ D + n = finrank ℝ E)
    {O : Set M} (hO : IsOpen O) (hfO : MapsTo f K O) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
          (D × EuclideanSpace ℝ (Fin n)) M ∞,
        K ×ˢ closedBall 0 ε ⊆ Φ.source ∧
        Φ.source ⊆ U ×ˢ univ ∧ Φ.target ⊆ O ∧
        (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧
        (∀ q ∈ Φ.source, Φ q ∈ f '' U ↔ q.2 = 0) := by
  have hinj : InjOn f K := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hemb.injective
      (show (fun u : U => f u) ⟨x, hKU hx⟩ = (fun u : U => f u) ⟨y, hKU hy⟩ from hxy))
  obtain ⟨a, ha, Φ, hprod, hsource, hzero, htarget⟩ :=
    exists_local_tubularNeighborhood_of_embedded_starConvex
      hf hK hz hstar hU hKU hinj hi n hcodim hO hfO
  have hbase : IsOpen {x : U | ((x : D), (0 : EuclideanSpace ℝ (Fin n))) ∈ Φ.source} :=
    Φ.open_source.preimage (continuous_subtype_val.prodMk continuous_const)
  obtain ⟨A, hA, hpreA⟩ := hemb.isInducing.isOpen_iff.mp hbase
  have haxis {x : D} (hx : x ∈ U) (hxA : f x ∈ A) : (x, 0) ∈ Φ.source := by
    have hx' : (⟨x, hx⟩ : U) ∈ (fun u : U => f u) ⁻¹' A := hxA
    rw [hpreA] at hx'
    exact hx'
  have hKA : MapsTo f K A := by
    intro x hx
    have hx' : (⟨x, hKU hx⟩ : U) ∈
        {u : U | ((u : D), (0 : EuclideanSpace ℝ (Fin n))) ∈ Φ.source} :=
      hprod ⟨hx, mem_closedBall_self ha.le⟩
    rw [← hpreA] at hx'
    exact hx'
  let Ψ := PartialChart.restrictTarget Φ hA
  have hKzero : K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Ψ.source := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    have hxΦ := hprod ⟨hx, mem_closedBall_self ha.le⟩
    refine ⟨hxΦ, ?_⟩
    change Φ (x, 0) ∈ A
    rw [hzero x hxΦ]
    exact hKA hx
  obtain ⟨ε, hε, hεprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset hK Ψ.open_source hKzero
  refine ⟨ε, hε, Ψ, hεprod, fun _ hq => hsource hq.1,
    fun _ hy => htarget hy.1, fun x hx => hzero x hx.1, ?_⟩
  rintro ⟨x, z⟩ hq
  constructor
  · rintro ⟨u, hu, heq⟩
    have huA : f u ∈ A := heq ▸ hq.2
    have huΦ := haxis hu huA
    have hpair : (x, z) = (u, 0) := Φ.toPartialEquiv.injOn hq.1 huΦ
      (heq.symm.trans (hzero u huΦ).symm)
    exact congrArg Prod.snd hpair
  · intro hz
    change z = 0 at hz
    subst z
    exact ⟨x, (hsource hq.1).1, (hzero x hq.1).symm⟩

end Wikipedia.SmoothSixDPoincare
