import Wikipedia.NoExoticSixSphere.SphereCollapse

/-!
# Smoothness of the sphere-valued collapse near its distinguished fiber

The compactification homeomorphisms use the actual stereographic atlas.
In these charts the continuous sphere map is the previously checked smooth
finite collapse coordinate, so it is smooth on an open neighborhood of the
embedded candidate.
-/

open scoped Manifold ContDiff
open Set Topology

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)

noncomputable def sphereMap : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - n)) :=
  ⟨fun y ↦ euclideanOnePointSphere (e.ambientDimension - n)
      (d.map ((euclideanOnePointSphere e.ambientDimension).symm y)),
    (euclideanOnePointSphere (e.ambientDimension - n)).continuous.comp
      (d.map.continuous.comp (euclideanOnePointSphere e.ambientDimension).symm.continuous)⟩

theorem sphereMap_infty :
    d.sphereMap (sphereInfinity e.ambientDimension) = sphereInfinity (e.ambientDimension - n) := by
  change euclideanOnePointSphere (e.ambientDimension - n)
    (d.map ((euclideanOnePointSphere e.ambientDimension).symm
      (euclideanOnePointSphere e.ambientDimension OnePoint.infty))) = _
  rw [Homeomorph.symm_apply_apply, d.map_infty]
  rfl

theorem sphereMap_zero_iff (y : Sphere e.ambientDimension) :
    d.sphereMap y = sphereZero (e.ambientDimension - n) ↔
      ∃ x, e.compactifiedEmbedding x = y := by
  let s := euclideanOnePointSphere e.ambientDimension
  let t := euclideanOnePointSphere (e.ambientDimension - n)
  change t (d.map (s.symm y)) = t (↑(0 : e.NormalModel)) ↔ _
  rw [t.injective.eq_iff, d.zero_fiber]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change s (↑(e.toFun x)) = y
    rw [hx, s.apply_symm_apply]
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have h := congrArg s.symm hx
    change s.symm (s (↑(e.toFun x))) = s.symm y at h
    simpa only [s.symm_apply_apply] using h

theorem sphereMap_finite {x : EuclideanSpace ℝ (Fin e.ambientDimension)}
    (hx : x ∈ d.neighborhood) :
    d.sphereMap (euclideanOnePointSphere e.ambientDimension (x : OnePoint _)) =
      euclideanOnePointSphere (e.ambientDimension - n) (↑(d.coordinates x) : OnePoint _) := by
  change euclideanOnePointSphere (e.ambientDimension - n)
    (d.map ((euclideanOnePointSphere e.ambientDimension).symm
      (euclideanOnePointSphere e.ambientDimension (x : OnePoint _)))) = _
  rw [Homeomorph.symm_apply_apply, d.local_formula x hx]

noncomputable def sphereNeighborhood : Set (Sphere e.ambientDimension) :=
  (sphereProjection e.ambientDimension).symm '' d.neighborhood

theorem isOpen_sphereNeighborhood : IsOpen d.sphereNeighborhood :=
  ((sphereProjection e.ambientDimension).symm.isOpenEmbedding
    (sphereProjection_target e.ambientDimension)).isOpenMap _ d.open_neighborhood

theorem sphereNeighborhood_subset_source :
    d.sphereNeighborhood ⊆ (sphereProjection e.ambientDimension).source := by
  rintro y ⟨x, _, rfl⟩
  exact (sphereProjection e.ambientDimension).map_target (by rw [sphereProjection_target]; trivial)

theorem sphereProjection_mapsTo_neighborhood :
    MapsTo (sphereProjection e.ambientDimension) d.sphereNeighborhood d.neighborhood := by
  rintro y ⟨x, hx, rfl⟩
  rwa [(sphereProjection e.ambientDimension).right_inv
    (by rw [sphereProjection_target]; trivial)]

theorem sphereMap_eq_local : EqOn d.sphereMap
    (fun y ↦ euclideanOnePointSphere (e.ambientDimension - n)
      (↑(d.coordinates (sphereProjection e.ambientDimension y)) : OnePoint _))
    d.sphereNeighborhood := by
  rintro y ⟨x, hx, rfl⟩
  change d.sphereMap ((sphereProjection e.ambientDimension).symm x) =
    euclideanOnePointSphere (e.ambientDimension - n)
      (↑(d.coordinates (sphereProjection e.ambientDimension
        ((sphereProjection e.ambientDimension).symm x))) : OnePoint _)
  rw [(sphereProjection e.ambientDimension).right_inv
    (by rw [sphereProjection_target]; trivial)]
  rw [← euclideanOnePointSphere_coe]
  exact d.sphereMap_finite hx

theorem contMDiffOn_sphereMap :
    ContMDiffOn (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - n)) ∞
      d.sphereMap d.sphereNeighborhood := by
  have hp := (sphereProjectionDiffeomorph e.ambientDimension).contMDiffOn_toFun
  change ContMDiffOn (𝓡 e.ambientDimension) (𝓡 e.ambientDimension) ∞
    (sphereProjection e.ambientDimension) (sphereProjection e.ambientDimension).source at hp
  have hc := d.smooth_coordinates.contMDiffOn.comp
    (hp.mono d.sphereNeighborhood_subset_source) d.sphereProjection_mapsTo_neighborhood
  exact ((contMDiff_euclideanOnePointSphere_coe (e.ambientDimension - n)).comp_contMDiffOn hc).congr
    d.sphereMap_eq_local

theorem zero_fiber_subset_sphereNeighborhood :
    d.sphereMap ⁻¹' {sphereZero (e.ambientDimension - n)} ⊆ d.sphereNeighborhood := by
  intro y hy
  obtain ⟨x, hx⟩ := (d.sphereMap_zero_iff y).mp hy
  refine ⟨e.toFun x, d.range_subset ⟨x, rfl⟩, ?_⟩
  rw [← euclideanOnePointSphere_coe]
  exact hx

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
