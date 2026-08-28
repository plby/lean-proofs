import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProduct
import Wikipedia.HopfProblem.EllipticHigherHomologySurfaceGroups

/-!
# The actual cap section in the original mapping-torus coordinates

The constructed cap section sends a representative `[s,y]` of the actual
central-surface mapping torus to `[-s,(s/m,y)]` in the original affine
boundary.  Thus its base circle is reversed.  The fibre maps at different
real times are explicitly homotopic, and at time zero their real lift is
the unchanged coordinate inclusion `k ↦ (0,k)`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct

open Elliptic Elliptic.HigherHomology SpecialPeriods SpecialPeriods.EllipticFilling
open PeriodTorusHigherHomology SingularMayerVietoris MappingTorusHomology

/-- The actual fibre in the cylinder formula for the cap section. -/
def capSectionFibre (j : Kind) (s : ℝ) : C(ProductTorus 3, RealTorus₄) where
  toFun y := (splitFlatTorusHomeomorph j).symm
    (((s / j.order : ℝ) : MappingTorus.Circle), y)
  continuous_toFun := (splitFlatTorusHomeomorph j).symm.continuous.comp
    (continuous_const.prodMk continuous_id)

@[simp] theorem capSectionFibre_apply (j : Kind) (s : ℝ) (y : ProductTorus 3) :
    capSectionFibre j s y = (splitFlatTorusHomeomorph j).symm
      (((s / j.order : ℝ) : MappingTorus.Circle), y) := rfl

/-- All fixed-time fibre maps are connected by the literal affine-time homotopy. -/
def capSectionFibreHomotopy (j : Kind) (s t : ℝ) :
    (capSectionFibre j s).Homotopy (capSectionFibre j t) where
  toFun p := (splitFlatTorusHomeomorph j).symm
    (((((1 - (p.1 : ℝ)) * s + (p.1 : ℝ) * t) / j.order : ℝ) : MappingTorus.Circle), p.2)
  continuous_toFun := (splitFlatTorusHomeomorph j).symm.continuous.comp
    (((AddCircle.continuous_mk' (1 : ℝ)).comp (by fun_prop)).prodMk continuous_snd)
  map_zero_left y := by simp [capSectionFibre]
  map_one_left y := by simp [capSectionFibre]

/-- This equality is induced by the actual homotopy, in every degree. -/
theorem capSectionFibre_homology (j : Kind) (s t : ℝ) (n : ℕ) :
    singularHomologyMap (capSectionFibre j s) n =
      singularHomologyMap (capSectionFibre j t) n :=
  homotopy_homologyMap (capSectionFibreHomotopy j s t) n

/-- At zero the real lift is the same positive coordinate three-torus for both caps. -/
theorem capSectionFibre_zero_coordinateProjection (j : Kind) (k : FibreCoordinates) :
    capSectionFibre j 0 (coordinateProjection 3 k) =
      standardLattice.mkQ (Fin.cons 0 k) := by
  rw [capSectionFibre_apply, zero_div]
  rw [splitFlatTorusHomeomorph_symm_coordinateProjection]
  simp only [splitRealCoordinates_symm_apply, zero_smul, zero_add]

/-- The zero-time coordinate inclusion is literally independent of the elliptic order. -/
theorem capSectionFibre_zero_eq (j j' : Kind) :
    capSectionFibre j 0 = capSectionFibre j' 0 := by
  ext y
  obtain ⟨k, rfl⟩ := coordinateProjection_surjective 3 y
  rw [capSectionFibre_zero_coordinateProjection, capSectionFibre_zero_coordinateProjection]

/-- The cap section, with the genuine mapping-torus model of its original surface as domain. -/
def capSectionFromModel (j : Kind) :
    C(mappingTorusModel j, ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j) :=
  (capSection j).comp
    ((surfaceMappingTorusHomeomorph j (specialLocalData j).centralPeriod).symm : C(_, _))

/-- The exact real-cylinder formula fixes the reversed time convention and all fibre terms. -/
theorem capSectionFromModel_mk (j : Kind) (s : ℝ) (y : ProductTorus 3) :
    capSectionFromModel j (MappingTorus.mk (fibreTorusHomeomorph j).symm (s, y)) =
      MappingTorus.mk (flatTorusAffine j j.twist) (-s, capSectionFibre j s y) := by
  apply (boundaryProductHomeomorph j).injective
  change boundaryProductHomeomorph j
      ((boundaryProductHomeomorph j).symm
        ((surfaceMappingTorusHomeomorph j (specialLocalData j).centralPeriod).symm
          (MappingTorus.mk (fibreTorusHomeomorph j).symm (s, y)), 0)) = _
  rw [Homeomorph.apply_symm_apply, boundaryProductHomeomorph_mk,
    ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral_mk,
    surfaceMappingTorusHomeomorph_symm_mk]
  apply Prod.ext
  · apply congrArg (surfaceProjection j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j))
    rw [← splitPeriodTorusHomeomorph_symm_splitFlat j]
    simp only [capSectionFibre_apply, Homeomorph.apply_symm_apply]
  · simp only [capSectionFibre_apply, Homeomorph.apply_symm_apply]
    change (0 : MappingTorus.Circle) =
      ((s / j.order : ℝ) : MappingTorus.Circle) + ((-s / j.order : ℝ) : MappingTorus.Circle)
    rw [← AddCircle.coe_add, ← add_div, add_neg_cancel, zero_div, AddCircle.coe_zero]

/-- The inverse affine generator has the actual split-coordinate expression on each
section fibre.  Its remaining linear factor is the original inverse three-torus monodromy. -/
theorem affine_symm_capSectionFibre (j : Kind) (s : ℝ) (y : ProductTorus 3) :
    (flatTorusAffine j j.twist).symm (capSectionFibre j s y) =
      capSectionFibre j (s - 1) ((fibreTorusHomeomorph j).symm y) := by
  apply (flatTorusAffine j j.twist).injective
  rw [Homeomorph.apply_symm_apply]
  simp only [capSectionFibre_apply, flatTorusAffine_splitFlatTorusHomeomorph_symm,
    Homeomorph.apply_symm_apply]
  apply congrArg (splitFlatTorusHomeomorph j).symm
  apply Prod.ext
  · change ((s / j.order : ℝ) : MappingTorus.Circle) =
      (((s - 1) / j.order : ℝ) : MappingTorus.Circle) +
        ((1 / j.order : ℝ) : MappingTorus.Circle)
    rw [← AddCircle.coe_add]
    congr 1
    ring
  · rfl

/-- The actual image of the source Wang boundary is fixed by its actual monodromy. -/
theorem surfaceWangBoundary_fixed (j : Kind) (n : ℕ)
    (a : SingularHomology (mappingTorusModel j) (n + 1)) :
    singularHomologyMap ((fibreTorusHomeomorph j).symm : C(_, _)) n
      (wangBoundary (fibreTorusHomeomorph j).symm n a) =
        wangBoundary (fibreTorusHomeomorph j).symm n a := by
  have h : wangBoundary (fibreTorusHomeomorph j).symm n a ∈
      LinearMap.range (wangBoundary (fibreTorusHomeomorph j).symm n) := ⟨a, rfl⟩
  rw [wangBoundary_range] at h
  change wangBoundary (fibreTorusHomeomorph j).symm n a -
    singularHomologyMap ((fibreTorusHomeomorph j).symm : C(_, _)) n
      (wangBoundary (fibreTorusHomeomorph j).symm n a) = 0 at h
  exact (sub_eq_zero.mp h).symm

/-- The actual quarter-column fibre maps have the same induced value on every source
Wang class, with their inverse-generator coordinate changes retained. -/
theorem affine_symm_capSectionFibre_wang (j : Kind) (s : ℝ) (n : ℕ)
    (a : SingularHomology (mappingTorusModel j) (n + 1)) :
    singularHomologyMap
      (((flatTorusAffine j j.twist).symm : C(RealTorus₄, RealTorus₄)).comp
        (capSectionFibre j s)) n (wangBoundary (fibreTorusHomeomorph j).symm n a) =
      singularHomologyMap (capSectionFibre j 0) n
        (wangBoundary (fibreTorusHomeomorph j).symm n a) := by
  have hmap : ((flatTorusAffine j j.twist).symm : C(RealTorus₄, RealTorus₄)).comp
      (capSectionFibre j s) = (capSectionFibre j (s - 1)).comp
        ((fibreTorusHomeomorph j).symm : C(ProductTorus 3, ProductTorus 3)) := by
    ext y
    exact affine_symm_capSectionFibre j s y
  rw [hmap, singularHomologyMap_comp, LinearMap.comp_apply,
    surfaceWangBoundary_fixed, capSectionFibre_homology j (s - 1) 0]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct
