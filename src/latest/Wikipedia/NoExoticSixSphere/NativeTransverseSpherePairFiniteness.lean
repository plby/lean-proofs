import Wikipedia.NoExoticSixSphere.SphereNativeDerivativeCoordinates
import Wikipedia.NoExoticSixSphere.SelfTransverseSphereDoublePoints
import Wikipedia.NoExoticSixSphere.TransverseSphereIntersections

/-!
# Finiteness of transverse mutual pairs without embedding hypotheses

The actual coincidence set is closed in the compact product of source
spheres. Transversality makes its chart difference locally injective, so
each coincidence is isolated. Neither map needs to be globally injective.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.MapIntersections

open GLOrthonormalization IntersectionTrace SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] {f g : Sphere 3 → M}
  (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
  (ht : NativeSpherePairTransverse f g)

include hf hg ht in
theorem isDiscrete_pairs_of_nativeTransverse : IsDiscrete (pairs f g) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  rintro ⟨x, y⟩ hxy
  let F : ℝ → Sphere 3 → M := fun _ ↦ f
  let G : ℝ → Sphere 3 → M := fun _ ↦ g
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry F) :=
    hf.comp contMDiff_snd
  have hG : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry G) :=
    hg.comp contMDiff_snd
  let s : SphereChart := modelChartPartialDiffeomorph (I := 𝓡 3) x
  let z : SphereChart := modelChartPartialDiffeomorph (I := 𝓡 3) y
  let c : ManifoldChart M := modelChartPartialDiffeomorph (I := 𝓡 6) (f x)
  have hx : x ∈ s.source := mem_extChartAt_source x
  have hy : y ∈ z.source := mem_extChartAt_source y
  have hc : f x ∈ c.source := mem_extChartAt_source (f x)
  have hcy : g y ∈ c.source := hxy ▸ hc
  have hx' : s.symm (s x) = x := s.left_inv hx
  have hy' : z.symm (z y) = y := z.left_inv hy
  let T := s.toOpenPartialHomeomorph.prod z.toOpenPartialHomeomorph
  let D : Vector 3 × Vector 3 → Vector 6 := fun q ↦ coordinateDifference F G s z c (0, q)
  have hdomain : (0, (s x, z y)) ∈ fullCoordinateDomain F G s z c := by
    refine ⟨⟨s.map_source hx, z.map_source hy⟩, ?_, ?_⟩
    · change f (s.symm (s x)) ∈ c.source
      rwa [hx']
    · change g (z.symm (z y)) ∈ c.source
      rwa [hy']
  have hD : ContDiffAt ℝ ∞ D (s x, z y) :=
    ((contDiffOn_coordinateDifference_full F G hF hG s z c).contDiffAt
      ((isOpen_fullCoordinateDomain F G hF hG s z c).mem_nhds hdomain)).comp (s x, z y)
        (contDiffAt_const.prodMk contDiffAt_id)
  have hDi : Injective (fderiv ℝ D (s x, z y)) :=
    (bijective_fderiv_spatial_difference F G hF hG 0 x y s z c hx hy hc hxy
      (ht x y hxy)).1
  obtain ⟨V, hV, hVp, hVi⟩ := CompactCoreImmersion.exists_open_injOn_at hD hDi
  have hTp : (x, y) ∈ T.source := ⟨hx, hy⟩
  have hzero : D (T (x, y)) = 0 := by
    change c (f (s.symm (s x))) - c (g (z.symm (z y))) = 0
    rw [hx', hy', hxy, sub_self]
  refine ⟨T.source ∩ T ⁻¹' V,
    T.continuousOn.isOpen_inter_preimage T.open_source hV, ?_⟩
  ext q
  constructor
  · rintro ⟨⟨hqT, hqV⟩, hq⟩
    have hqzero : D (T q) = 0 := by
      change c (f (s.symm (s q.1))) - c (g (z.symm (z q.2))) = 0
      have hqs : s.symm (s q.1) = q.1 := s.left_inv hqT.1
      have hqz : z.symm (z q.2) = q.2 := z.left_inv hqT.2
      rw [hqs, hqz, hq, sub_self]
    have heT : T q = T (x, y) := hVi hqV hVp (hqzero.trans hzero.symm)
    exact mem_singleton_iff.mpr (T.injOn hqT hTp heT)
  · rintro rfl
    exact ⟨⟨hTp, hVp⟩, hxy⟩

include hf hg ht in
theorem finite_pairs_of_nativeTransverse : (pairs f g).Finite := by
  have hc : IsClosed (pairs f g) :=
    isClosed_eq (hf.continuous.comp continuous_fst) (hg.continuous.comp continuous_snd)
  exact hc.isCompact.finite (isDiscrete_pairs_of_nativeTransverse hf hg ht)

end NoExoticSixSphere.MapIntersections
