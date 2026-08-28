import Wikipedia.NoExoticSixSphere.ImmersedSphereDoublePoints
import Wikipedia.NoExoticSixSphere.TransverseSphereChartDifference
import Wikipedia.NoExoticSixSphere.CompactCoreImmersion

/-!
# Finitely many ordered double points of a self-transverse immersed sphere

At a transverse pair, the actual chart coincidence map has bijective spatial
derivative. The inverse-function theorem isolates that original source pair.
The compact off-diagonal set of an immersion is therefore finite. Neither
the number of double points nor an embedding is assumed.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereSelfIntersections

open GLOrthonormalization IntersectionTrace

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] {f : Sphere 3 → M}
  (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (ht : ∀ x y, x ≠ y → f x = f y → Surjective
    ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))

include hf ht in
theorem isDiscrete_pairs : IsDiscrete (pairs f) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  rintro ⟨x, y⟩ ⟨hne, hxy⟩
  let G : ℝ → Sphere 3 → M := fun _ ↦ f
  have hG : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry G) :=
    hf.comp contMDiff_snd
  let s : SphereChart := modelChartPartialDiffeomorph (I := 𝓡 3) x
  let z : SphereChart := modelChartPartialDiffeomorph (I := 𝓡 3) y
  let c : ManifoldChart M := modelChartPartialDiffeomorph (I := 𝓡 6) (f x)
  have hx : x ∈ s.source := mem_extChartAt_source x
  have hy : y ∈ z.source := mem_extChartAt_source y
  have hc : f x ∈ c.source := mem_extChartAt_source (f x)
  have hcy : f y ∈ c.source := hxy ▸ hc
  have hx' : s.symm (s x) = x := s.left_inv hx
  have hy' : z.symm (z y) = y := z.left_inv hy
  let T := s.toOpenPartialHomeomorph.prod z.toOpenPartialHomeomorph
  let D : Vector 3 × Vector 3 → Vector 6 := fun q ↦ coordinateDifference G G s z c (0, q)
  have hdomain : (0, (s x, z y)) ∈ fullCoordinateDomain G G s z c := by
    refine ⟨⟨s.map_source hx, z.map_source hy⟩, ?_, ?_⟩
    · change f (s.symm (s x)) ∈ c.source
      rwa [hx']
    · change f (z.symm (z y)) ∈ c.source
      rwa [hy']
  have hD : ContDiffAt ℝ ∞ D (s x, z y) :=
    ((contDiffOn_coordinateDifference_full G G hG hG s z c).contDiffAt
      ((isOpen_fullCoordinateDomain G G hG hG s z c).mem_nhds hdomain)).comp (s x, z y)
        (contDiffAt_const.prodMk contDiffAt_id)
  have hDi : Injective (fderiv ℝ D (s x, z y)) :=
    (bijective_fderiv_spatial_difference G G hG hG 0 x y s z c hx hy hc hxy
      (ht x y hne hxy)).1
  obtain ⟨V, hV, hVp, hVi⟩ := CompactCoreImmersion.exists_open_injOn_at hD hDi
  have hTp : (x, y) ∈ T.source := ⟨hx, hy⟩
  have hzero : D (T (x, y)) = 0 := by
    change c (f (s.symm (s x))) - c (f (z.symm (z y))) = 0
    rw [hx', hy', hxy, sub_self]
  refine ⟨T.source ∩ T ⁻¹' V,
    T.continuousOn.isOpen_inter_preimage T.open_source hV, ?_⟩
  ext q
  constructor
  · rintro ⟨⟨hqT, hqV⟩, hq⟩
    have hqzero : D (T q) = 0 := by
      change c (f (s.symm (s q.1))) - c (f (z.symm (z q.2))) = 0
      have hqs : s.symm (s q.1) = q.1 := s.left_inv hqT.1
      have hqz : z.symm (z q.2) = q.2 := z.left_inv hqT.2
      rw [hqs, hqz, hq.2, sub_self]
    have heT : T q = T (x, y) := hVi hqV hVp (hqzero.trans hzero.symm)
    exact mem_singleton_iff.mpr (T.injOn hqT hTp heT)
  · rintro rfl
    exact ⟨⟨hTp, hVp⟩, hne, hxy⟩

include hf ht in
theorem finite_pairs (hi : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    (pairs f).Finite := (isCompact_pairs hf hi).finite (isDiscrete_pairs hf ht)

end NoExoticSixSphere.SphereSelfIntersections
