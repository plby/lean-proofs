import Wikipedia.NoExoticSixSphere.SmoothSphereCollapse

/-!
# Regularity of the distinguished value on the actual spheres

Both stereographic coordinate changes have invertible differential. The
surjective finite collapse differential therefore gives a surjective manifold
differential on its sphere neighborhood. Relative smoothing preserves this
differential along the distinguished fiber.
-/

open scoped Manifold ContDiff Topology
open Set Filter

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)

theorem mfderiv_sphereMap_surjective {y : Sphere e.ambientDimension}
    (hy : y ∈ d.sphereNeighborhood) :
    Function.Surjective (mfderiv (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - n))
      d.sphereMap y) := by
  let c := sphereProjection e.ambientDimension
  let t := (sphereProjection (e.ambientDimension - n)).symm
  have hc : IsLocalDiffeomorphAt (𝓡 e.ambientDimension) (𝓡 e.ambientDimension) ∞ c y :=
    ⟨sphereProjectionDiffeomorph e.ambientDimension, d.sphereNeighborhood_subset_source hy,
      fun _ _ ↦ rfl⟩
  have ht : IsLocalDiffeomorphAt (𝓡 (e.ambientDimension - n))
      (𝓡 (e.ambientDimension - n)) ∞ t (d.coordinates (c y)) := by
    refine ⟨(sphereProjectionDiffeomorph (e.ambientDimension - n)).symm, ?_, fun _ _ ↦ rfl⟩
    change d.coordinates (c y) ∈ (sphereProjection (e.ambientDimension - n)).target
    rw [sphereProjection_target]
    trivial
  have hq := (d.contDiffAt_coordinates (d.sphereProjection_mapsTo_neighborhood hy)).differentiableAt
    (by simp)
  have hc' := hc.mdifferentiableAt (by simp)
  have ht' := ht.mdifferentiableAt (by simp)
  have hq' := hq.mdifferentiableAt
  have hcs : Function.Surjective (mfderiv (𝓡 e.ambientDimension) (𝓡 e.ambientDimension) c y) :=
    (hc.mfderivToContinuousLinearEquiv (by simp)).surjective
  have hts : Function.Surjective (mfderiv (𝓡 (e.ambientDimension - n))
      (𝓡 (e.ambientDimension - n)) t (d.coordinates (c y))) :=
    (ht.mfderivToContinuousLinearEquiv (by simp)).surjective
  have hqs : Function.Surjective (mfderiv (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - n))
      d.coordinates (c y)) := by
    rw [mfderiv_eq_fderiv]
    exact d.surjective_differential _ (d.sphereProjection_mapsTo_neighborhood hy)
  have heq : (d.sphereMap : Sphere e.ambientDimension → Sphere (e.ambientDimension - n))
      =ᶠ[𝓝 y] (fun z ↦ t (d.coordinates (c z))) := by
    filter_upwards [d.isOpen_sphereNeighborhood.mem_nhds hy] with z hz
    simpa only [euclideanOnePointSphere_coe] using d.sphereMap_eq_local hz
  rw [heq.mfderiv_eq]
  change Function.Surjective (mfderiv (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - n))
    (t ∘ (d.coordinates ∘ c)) y)
  rw [mfderiv_comp y ht' (hq'.comp y hc'), mfderiv_comp y hq' hc']
  exact hts.comp (hqs.comp hcs)

theorem mfderiv_smoothRepresentative_surjective
    (g : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - n))) (x : M)
    (heq : (g : Sphere e.ambientDimension → Sphere (e.ambientDimension - n))
      =ᶠ[𝓝 (e.compactifiedEmbedding x)] d.sphereMap) :
    Function.Surjective (mfderiv (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - n))
      g (e.compactifiedEmbedding x)) := by
  rw [heq.mfderiv_eq]
  exact d.mfderiv_sphereMap_surjective (d.zero_fiber_subset_sphereNeighborhood
    ((d.sphereMap_zero_iff _).mpr ⟨x, rfl⟩))

theorem exists_smoothSphereMap_regular :
    ∃ g : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - n)),
      ContMDiff (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - n)) ∞ g ∧
      d.sphereMap.Homotopic g ∧
      (∀ y, g y = sphereZero (e.ambientDimension - n) ↔ ∃ x, e.compactifiedEmbedding x = y) ∧
      (∀ y, g y = sphereZero (e.ambientDimension - n) →
        Function.Surjective (mfderiv (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - n)) g y)) ∧
      ∀ x, (g : Sphere e.ambientDimension → Sphere (e.ambientDimension - n))
        =ᶠ[𝓝 (e.compactifiedEmbedding x)] d.sphereMap := by
  obtain ⟨g, hg, hhom, hfiber, heq⟩ := d.exists_smoothSphereMap
  refine ⟨g, hg, hhom, hfiber, ?_, heq⟩
  intro y hy
  obtain ⟨x, rfl⟩ := (hfiber y).mp hy
  exact d.mfderiv_smoothRepresentative_surjective g x (heq x)

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

namespace NoExoticSixSphere

theorem exists_sixSphereRegularCollapse {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
    (h : M ≃ₜ Sphere 6) :
    ∃ e : EuclideanEmbedding 6 M,
      ∃ g : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - 6)),
        ContMDiff (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - 6)) ∞ g ∧
        (∀ y, g y = sphereZero (e.ambientDimension - 6) ↔
          ∃ x, e.compactifiedEmbedding x = y) ∧
        ∀ y, g y = sphereZero (e.ambientDimension - 6) →
          Function.Surjective
            (mfderiv (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - 6)) g y) := by
  obtain ⟨e, a, ⟨d⟩⟩ := exists_sixSphereFramedCollapseData h
  obtain ⟨g, hg, _, hfiber, hregular, _⟩ := d.exists_smoothSphereMap_regular
  exact ⟨e, g, hg, hfiber, hregular⟩

end NoExoticSixSphere
