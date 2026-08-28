import Wikipedia.HopfProblem.ToricBlowdownExceptionalBoundary
import Wikipedia.HopfProblem.AffineBlowupExceptional
import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# The three exceptional spheres of the projective blow-down

The exceptional spheres are actual holomorphic closed embeddings into
the compact toric component.  Their images are exactly the three fibres
over the coordinate points of the standard projective plane, and exactly
the three alternating boundary curves of the toric hexagon.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricComponent

open ToricCharts ToricFan ToricSpace Triangle

/-- The exceptional sphere in the `k`th open incidence blow-up. -/
def exceptionalSphere (k : Fin 3) : RiemannSphere → rayDivisor 0 :=
  blowupMap k ∘ AffineBlowup.exceptionalInclusion

def exceptionalFibre (k : Fin 3) : Set (rayDivisor 0) :=
  blowdown ⁻¹' {ProjectivePlane.coordinatePoint k}

theorem exceptionalSphere_holomorphic (k : Fin 3) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ (CoordinateSpace 2))
      ω (exceptionalSphere k) :=
  (blowupMap_holomorphic k).comp AffineBlowup.exceptionalInclusion_holomorphic

theorem exceptionalSphere_continuous (k : Fin 3) : Continuous (exceptionalSphere k) :=
  (exceptionalSphere_holomorphic k).continuous

theorem exceptionalSphere_injective (k : Fin 3) : Function.Injective (exceptionalSphere k) :=
  (blowupMap_injective k).comp AffineBlowup.exceptionalInclusion_isClosedEmbedding.injective

/-- Compactness of the genuine Riemann sphere and Hausdorffness of the
toric component make this an actual closed topological embedding. -/
theorem exceptionalSphere_isClosedEmbedding (k : Fin 3) :
    IsClosedEmbedding (exceptionalSphere k) :=
  (exceptionalSphere_continuous k).isClosedEmbedding (exceptionalSphere_injective k)

@[simp] theorem blowdown_exceptionalSphere (k : Fin 3) (z : RiemannSphere) :
    blowdown (exceptionalSphere k z) = ProjectivePlane.coordinatePoint k := by
  change blowdown (blowupMap k (AffineBlowup.exceptionalInclusion z)) = _
  rw [blowdown_blowupMap, AffineBlowup.projection_exceptionalInclusion]
  rfl

theorem range_exceptionalSphere (k : Fin 3) : range (exceptionalSphere k) = exceptionalFibre k := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact blowdown_exceptionalSphere k z
  · intro hx
    have he : blowdown x = ProjectivePlane.coordinatePoint k := hx
    have ht : blowdown x ∈ ProjectivePlane.affineTarget k := by
      rw [he]
      exact ProjectivePlane.affineMap_mem_target k 0
    have hrange : x ∈ range (blowupMap k) := by
      rw [← blowdown_preimage_affineTarget]
      exact ht
    obtain ⟨y, rfl⟩ := hrange
    have hp : AffineBlowup.projection y = 0 := by
      apply ProjectivePlane.affineMap_injective k
      simpa only [blowdown_blowupMap, ProjectivePlane.coordinatePoint] using he
    have hy : y ∈ range AffineBlowup.exceptionalInclusion := by
      rw [AffineBlowup.range_exceptionalInclusion]
      exact hp
    obtain ⟨z, rfl⟩ := hy
    exact ⟨z, rfl⟩

theorem exceptionalFibre_isClosed (k : Fin 3) : IsClosed (exceptionalFibre k) :=
  isClosed_singleton.preimage blowdown_continuous

theorem exceptionalFibre_isCompact (k : Fin 3) : IsCompact (exceptionalFibre k) :=
  blowdown_isProperMap.isCompact_preimage isCompact_singleton

theorem exceptionalFibres_disjoint (i j : Fin 3) (hij : i ≠ j) :
    Disjoint (exceptionalFibre i) (exceptionalFibre j) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact hij (ProjectivePlane.coordinatePoint_injective (hi.symm.trans hj))

theorem exceptionalSphere_ranges_disjoint (i j : Fin 3) (hij : i ≠ j) :
    Disjoint (range (exceptionalSphere i)) (range (exceptionalSphere j)) := by
  rw [range_exceptionalSphere, range_exceptionalSphere]
  exact exceptionalFibres_disjoint i j hij

/-- The actual exceptional fibre, with its induced topology, is a sphere. -/
def exceptionalSphereHomeomorph (k : Fin 3) : RiemannSphere ≃ₜ exceptionalFibre k :=
  (exceptionalSphere_isClosedEmbedding k).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_exceptionalSphere k))

@[simp] theorem exceptionalSphereHomeomorph_coe (k : Fin 3) (z : RiemannSphere) :
    (exceptionalSphereHomeomorph k z : rayDivisor 0) = exceptionalSphere k z := rfl

theorem exceptionalFibre_eq_componentBoundary (k : Fin 3) :
    exceptionalFibre k = CuspQuotient.componentBoundary (exceptionalRay k) :=
  blowdown_fibre_eq_componentBoundary k

theorem range_exceptionalSphere_eq_componentBoundary (k : Fin 3) :
    range (exceptionalSphere k) = CuspQuotient.componentBoundary (exceptionalRay k) := by
  rw [range_exceptionalSphere, exceptionalFibre_eq_componentBoundary]

/-- The sphere parametrization in either affine chart of the incidence
blow-up, prior to its inclusion into the toric component. -/
theorem exceptionalSphere_affineMap (k : Fin 3) (b : Bool) (z : ℂ) :
    exceptionalSphere k (RiemannSphere.standardCharts.affineMap b z) =
      blowupMap k (AffineBlowup.affineMap b (AffineBlowup.exceptionalCoordinates b z)) := by
  change blowupMap k
    (AffineBlowup.exceptionalInclusion (RiemannSphere.standardCharts.affineMap b z)) = _
  rw [AffineBlowup.exceptionalInclusion_affineMap]

/-- A genuine complex chart around the exceptional sphere. -/
def exceptionalSphereChart (k : Fin 3) (b : Bool) :
    OpenPartialHomeomorph (rayDivisor 0) (CoordinateSpace 2) :=
  (blowupParametrization k).symm.trans (AffineBlowup.parametrization b).symm

theorem exceptionalSphereChart_source (k : Fin 3) (b : Bool) :
    (exceptionalSphereChart k b).source = range (blowupMap k) ∩
      (blowupParametrization k).symm ⁻¹' AffineBlowup.affineTarget b := by
  simp only [exceptionalSphereChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, blowupParametrization_target,
    AffineBlowup.parametrization_target]

theorem exceptionalSphereChart_mem_maximalAtlas (k : Fin 3) (b : Bool) :
    exceptionalSphereChart k b ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (rayDivisor 0) := by
  apply (exceptionalSphereChart k b).mem_maximalAtlas_of_contMDiffOn
  · have he : (AffineBlowup.parametrization b).symm ∈ IsManifold.maximalAtlas
        (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω AffineBlowup.Space :=
      IsManifold.subset_maximalAtlas (mem_range_self b)
    exact (contMDiffOn_of_mem_maximalAtlas he).comp
      ((blowupParametrization_symm_holomorphic k).mono
        (by rw [exceptionalSphereChart_source]; exact inter_subset_left))
      (fun x hx => (by rw [exceptionalSphereChart_source] at hx; exact hx.2))
  · exact ((blowupMap_holomorphic k).comp (AffineBlowup.affineMap_holomorphic b)).contMDiffOn

theorem exceptionalSphere_affine_mem_chart (k : Fin 3) (b : Bool) (z : ℂ) :
    exceptionalSphere k (RiemannSphere.standardCharts.affineMap b z) ∈
      (exceptionalSphereChart k b).source := by
  rw [exceptionalSphere_affineMap, exceptionalSphereChart_source]
  constructor
  · exact mem_range_self _
  · have hi := (blowupParametrization k).left_inv
      (mem_univ (AffineBlowup.affineMap b (AffineBlowup.exceptionalCoordinates b z)))
    simp only [blowupParametrization_apply] at hi
    change (blowupParametrization k).symm
      (blowupMap k (AffineBlowup.affineMap b (AffineBlowup.exceptionalCoordinates b z))) ∈
        AffineBlowup.affineTarget b
    rw [hi]
    exact AffineBlowup.affineMap_mem_target b _

theorem exceptionalSphereChart_affineMap (k : Fin 3) (b : Bool) (z : ℂ) :
    exceptionalSphereChart k b
      (exceptionalSphere k (RiemannSphere.standardCharts.affineMap b z)) =
        AffineBlowup.exceptionalCoordinates b z := by
  rw [exceptionalSphere_affineMap]
  change (AffineBlowup.parametrization b).symm
      ((blowupParametrization k).symm
        (blowupMap k (AffineBlowup.affineMap b (AffineBlowup.exceptionalCoordinates b z)))) = _
  have hi := (blowupParametrization k).left_inv
    (mem_univ (AffineBlowup.affineMap b (AffineBlowup.exceptionalCoordinates b z)))
  simp only [blowupParametrization_apply] at hi
  rw [hi, AffineBlowup.parametrization_symm_affineMap]

/-- In the two sphere charts the map has the standard codimension-one
normal form, with one complex normal coordinate. -/
theorem exceptionalSphereAffine_isImmersionOfComplement (k : Fin 3) (b : Bool) :
    Manifold.IsImmersionOfComplement ℂ (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω
      (exceptionalSphere k ∘ RiemannSphere.standardCharts.affineMap b) := by
  intro z
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    ((exceptionalSphere_continuous k).comp
      (RiemannSphere.standardCharts.affineMap_isOpenEmbedding b).continuous).continuousAt
    (AffineBlowup.exceptionalCoordinateJoin b) (OpenPartialHomeomorph.refl ℂ)
    (exceptionalSphereChart k b) (mem_univ z) (exceptionalSphere_affine_mem_chart k b z)
    ?_ (exceptionalSphereChart_mem_maximalAtlas k b) ?_
  · simpa only [chartAt_self_eq] using IsManifold.chart_mem_maximalAtlas
      (I := modelWithCornersSelf ℂ ℂ) (n := ω) z
  · intro w _
    change exceptionalSphereChart k b
        (exceptionalSphere k (RiemannSphere.standardCharts.affineMap b w)) =
      AffineBlowup.exceptionalCoordinateJoin b (w, 0)
    rw [exceptionalSphereChart_affineMap, AffineBlowup.exceptionalCoordinateJoin_apply_zero]

theorem exceptionalSphere_isImmersionOfComplement (k : Fin 3) :
    Manifold.IsImmersionOfComplement ℂ (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (exceptionalSphere k) :=
  RiemannSphere.standardCharts.immersion_of_comp_affineMaps _
    (exceptionalSphere_continuous k) (exceptionalSphereAffine_isImmersionOfComplement k)

theorem exceptionalSphere_isImmersion (k : Fin 3) :
    Manifold.IsImmersion (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (exceptionalSphere k) :=
  (exceptionalSphere_isImmersionOfComplement k).isImmersion

/-- The exceptional curves are holomorphically embedded Riemann spheres. -/
theorem exceptionalSphere_isSmoothEmbedding (k : Fin 3) :
    Manifold.IsSmoothEmbedding (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (exceptionalSphere k) :=
  ⟨exceptionalSphere_isImmersion k, (exceptionalSphere_isClosedEmbedding k).isEmbedding⟩

end Wikipedia.HopfProblem.ToricComponent
