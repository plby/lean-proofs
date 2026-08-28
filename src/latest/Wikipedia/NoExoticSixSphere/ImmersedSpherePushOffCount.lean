import Wikipedia.NoExoticSixSphere.ImmersedSpherePushOffFamily
import Wikipedia.NoExoticSixSphere.CompactSphereCoincidenceCount
import Wikipedia.NoExoticSixSphere.CompactSphereCoincidenceTransversality
import Wikipedia.NoExoticSixSphere.SphereDoublePointParity

/-!
# An actual bijection between small push-off intersections and double-point pairs

The compact source-pair container and the actual time charts give an evenly
covered neighborhood of zero time. Its fiber equivalences identify every
sufficiently small nonzero-time coincidence set with the ordered double-point
set. Openness of native transversality on the same compact region proves
that these finite, even-count pushed-off intersections are transverse.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
  (ht : ∀ s t, s ≠ t → f s = f t → Surjective
    ((mfderiv (𝓡 3) (𝓡 6) f s).coprod (mfderiv (𝓡 3) (𝓡 6) f t)))

include e a r hf hd ht in
theorem exists_transverse_pushOff_pair_equivalences :
    ∃ G : ℝ → Sphere 3 → M,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry G) ∧ (∀ s, G 0 s = f s) ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), t ≠ 0 →
        Nonempty (↥(SphereSelfIntersections.pairs f) ≃ ↥(MapIntersections.pairs f (G t))) ∧
        ∀ x y, f x = G t y → Surjective
          ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) (G t) y)) := by
  obtain ⟨G, hG, hG₀, K, hK, hKE, hself, hother⟩ := e.exists_immersed_pushOff_family a r f hf hd
  have hGzero : G 0 = f := funext hG₀
  have hzero : K ∩ MapIntersections.pairs f (G 0) = SphereSelfIntersections.pairs f := by
    rw [hGzero, hKE]
  have hinter : ∀ p ∈ K, f p.1 = G 0 p.2 → p ∈ interior K := by
    intro p hp he
    apply hself
    rw [← hzero]
    exact ⟨hp, he⟩
  have htrans : ∀ p ∈ K, f p.1 = G 0 p.2 → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f p.1).coprod (mfderiv (𝓡 3) (𝓡 6) (G 0) p.2)) := by
    intro p hp he
    have hpair : p ∈ SphereSelfIntersections.pairs f := by
      rw [← hzero]
      exact ⟨hp, he⟩
    rw [hGzero]
    exact ht p.1 p.2 hpair.1 hpair.2
  have hE := CompactPairTrace.eventually_pair_equiv (fun _ ↦ f) G K
    (hf.comp contMDiff_snd) hG hK hinter htrans
  have hT := CompactPairTrace.eventually_transverse (fun _ ↦ f) G K
    (hf.comp contMDiff_snd) hG hK htrans
  refine ⟨G, hG, hG₀, ?_⟩
  filter_upwards [hE, hT] with t hE hT
  intro ht
  obtain ⟨E⟩ := hE
  have hInt : K ∩ MapIntersections.pairs f (G t) = MapIntersections.pairs f (G t) :=
    inter_eq_right.mpr ((hother t ht).trans interior_subset)
  refine ⟨⟨(Equiv.setCongr hzero.symm).trans (E.trans (Equiv.setCongr hInt))⟩, ?_⟩
  intro x y he
  exact hT (x, y) (interior_subset (hother t ht he)) he

include e a r hf hd ht in
theorem exists_pushOff_pair_equivalences :
    ∃ G : ℝ → Sphere 3 → M,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry G) ∧ (∀ s, G 0 s = f s) ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), t ≠ 0 →
        Nonempty (↥(SphereSelfIntersections.pairs f) ≃ ↥(MapIntersections.pairs f (G t))) := by
  obtain ⟨G, hG, hG₀, hnear⟩ := e.exists_transverse_pushOff_pair_equivalences a r f hf hd ht
  refine ⟨G, hG, hG₀, ?_⟩
  filter_upwards [hnear] with t ht
  exact fun hn ↦ (ht hn).1

include e a r hf hd ht in
theorem exists_even_transverse_pushOff_intersections :
    ∃ G : ℝ → Sphere 3 → M,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry G) ∧ (∀ s, G 0 s = f s) ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), t ≠ 0 →
        (MapIntersections.pairs f (G t)).Finite ∧ MapIntersections.parity f (G t) = 0 ∧
        ∀ x y, f x = G t y → Surjective
          ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) (G t) y)) := by
  obtain ⟨G, hG, hG₀, hE⟩ := e.exists_transverse_pushOff_pair_equivalences a r f hf hd ht
  have hfin := SphereSelfIntersections.finite_pairs hf ht hd
  refine ⟨G, hG, hG₀, ?_⟩
  filter_upwards [hE] with t hE
  intro htn
  obtain ⟨⟨E⟩, hT⟩ := hE htn
  have hpairfin : (MapIntersections.pairs f (G t)).Finite := by
    let := hfin.to_subtype
    exact finite_coe_iff.mp (Finite.of_equiv _ E)
  refine ⟨hpairfin, ?_, hT⟩
  have hn : (MapIntersections.pairs f (G t)).ncard = (SphereSelfIntersections.pairs f).ncard :=
    (Nat.card_congr E).symm
  change ((MapIntersections.pairs f (G t)).ncard : ZMod 2) = 0
  rw [hn]
  exact SphereSelfIntersections.ncard_cast_eq_zero f hfin

include e a r hf hd ht in
theorem exists_even_finite_pushOff_intersections :
    ∃ G : ℝ → Sphere 3 → M,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry G) ∧ (∀ s, G 0 s = f s) ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), t ≠ 0 →
        (MapIntersections.pairs f (G t)).Finite ∧ MapIntersections.parity f (G t) = 0 := by
  obtain ⟨G, hG, hG₀, hnear⟩ := e.exists_even_transverse_pushOff_intersections a r f hf hd ht
  refine ⟨G, hG, hG₀, ?_⟩
  filter_upwards [hnear] with t ht
  exact fun hn ↦ ⟨(ht hn).1, (ht hn).2.1⟩

end NoExoticSixSphere.EuclideanEmbedding
