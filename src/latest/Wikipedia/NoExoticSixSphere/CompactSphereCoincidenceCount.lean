import Wikipedia.NoExoticSixSphere.CompactSphereCoincidenceChart

/-!
# Stability of the actual coincidence-pair count in a compact region

If all zero-time coincidences lie in the region interior and are spatially
transverse, the genuine compact trace has actual time charts along its
zero fiber. The covering-neighborhood theorem then compares its nearby
fiber cardinalities, and the exact pair bijections give the asserted count.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CompactPairTrace

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (f g : ℝ → Sphere 3 → M) (K : Set (Sphere 3 × Sphere 3))
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
  (hK : IsCompact K)
  (hinter : ∀ p ∈ K, f 0 p.1 = g 0 p.2 → p ∈ interior K)
  (ht : ∀ p ∈ K, f 0 p.1 = g 0 p.2 → Surjective
    ((mfderiv (𝓡 3) (𝓡 6) (f 0) p.1).coprod (mfderiv (𝓡 3) (𝓡 6) (g 0) p.2)))

include hf hg hK hinter ht in
theorem eventually_pair_equiv :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      Nonempty (↥(K ∩ MapIntersections.pairs (f 0) (g 0)) ≃
        ↥(K ∩ MapIntersections.pairs (f t) (g t))) := by
  let : CompactSpace (space f g K) :=
    isCompact_iff_compactSpace.mp (isCompact_space f g K hf.continuous hg.continuous hK)
  have hlocal : ∀ a ∈ (time f g K) ⁻¹' {0},
      ∃ d : OpenPartialHomeomorph (space f g K) ℝ,
        a ∈ d.source ∧ EqOn (time f g K) d d.source := by
    intro a ha
    have hat : a.val.1 = 0 := ha
    have hap : a.val.2 ∈ K := a.property.1.2
    have hae : f 0 a.val.2.1 = g 0 a.val.2.2 := by
      have he : f a.val.1 a.val.2.1 = g a.val.1 a.val.2.2 := a.property.2
      rwa [hat] at he
    have haint : a.val.1 ∈ Ioo (-1 : ℝ) 1 := by rw [hat]; norm_num
    have hatr : Surjective
        ((mfderiv (𝓡 3) (𝓡 6) (f a.val.1) a.val.2.1).coprod
          (mfderiv (𝓡 3) (𝓡 6) (g a.val.1) a.val.2.2)) := by
      rw [hat]
      exact ht a.val.2 hap hae
    obtain ⟨d, had, hde⟩ := exists_time_chart f g K hf hg a haint (hinter a.val.2 hap hae) hatr
    exact ⟨d, had, fun q hq ↦ (hde q hq).symm⟩
  have hcover := CompactFiber.eventually_homeomorphic_fibers
    (time f g K) (time f g K).continuous 0 hlocal
  have htime : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [hcover, htime] with t hcover ht
  obtain ⟨e⟩ := hcover
  exact ⟨(fiberPairEquiv f g K 0 (by constructor <;> norm_num)).symm.trans
    (e.toEquiv.trans (fiberPairEquiv f g K t (Ioo_subset_Icc_self ht)))⟩

include hf hg hK hinter ht in
theorem eventually_pair_ncard_eq :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      (K ∩ MapIntersections.pairs (f t) (g t)).ncard =
        (K ∩ MapIntersections.pairs (f 0) (g 0)).ncard := by
  filter_upwards [eventually_pair_equiv f g K hf hg hK hinter ht] with t h
  obtain ⟨e⟩ := h
  exact (Nat.card_congr e).symm

end NoExoticSixSphere.CompactPairTrace
