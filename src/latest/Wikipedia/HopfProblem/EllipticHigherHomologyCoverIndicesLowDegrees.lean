import Wikipedia.HopfProblem.EllipticHigherHomologyCoverIndicesFilling
import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusLowDegrees

/-!
# Actual covering indices in degrees zero and one

The actual primitive fibre classes show that the period cover is onto
in degree zero and contains the primitive first axis in degree one.
Naturality of point classes makes the actual zeroth-homology norm
multiplication by the elliptic order.  The proved covering-boundary
formula then gives the complete first-homology image and its cyclic
cokernel, on both the central surface and the full filling.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology

/-- The actual positive degree-zero marking transported from the mapping torus. -/
def surfaceH0Equiv (j : Kind) (p : FixedPeriod j) :
    SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 0 ≃ₗ[ℤ] ℤ :=
  (surfaceMappingTorusHomologyEquiv j p 0).trans (mappingTorusH0Equiv j)

/-- The actual first-homology marking retaining its fibre and boundary axes. -/
def surfaceH1Equiv (j : Kind) (p : FixedPeriod j) :
    SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 1 ≃ₗ[ℤ]
      (Fin 2 → ℤ) :=
  (surfaceMappingTorusHomologyEquiv j p 1).trans (mappingTorusH1Equiv j)

theorem surfaceH0Equiv_fibre (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (ProductTorus 3) 0) :
    surfaceH0Equiv j p (singularHomologyMap (fibreIntoSurface j p) 0 a) =
      torusH0Coordinates a := by
  change mappingTorusH0Equiv j
    (homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) 0
      (singularHomologyMap (fibreIntoSurface j p) 0 a)) = _
  rw [surfaceMappingTorusHomology_fibre, mappingTorusH0Equiv_fibre]

theorem surfaceH1Equiv_fibre (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (ProductTorus 3) 1) :
    surfaceH1Equiv j p (singularHomologyMap (fibreIntoSurface j p) 1 a) =
      ![fibreCoinvariantCoordinate j (torusH1Equiv a), 0] := by
  change mappingTorusH1Equiv j
    (homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) 1
      (singularHomologyMap (fibreIntoSurface j p) 1 a)) = _
  rw [surfaceMappingTorusHomology_fibre, mappingTorusH1Equiv_fibre]

theorem surfaceH0Equiv_periodCover_fibre (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (ProductTorus 3) 0) :
    surfaceH0Equiv j p
      (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 0
        (singularHomologyMap (fibreIntoPeriodTorus j p) 0 a)) =
      torusH0Coordinates a := by
  change surfaceH0Equiv j p
    (((singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 0).comp
      (singularHomologyMap (fibreIntoPeriodTorus j p) 0)) a) = _
  rw [← singularHomologyMap_comp]
  exact surfaceH0Equiv_fibre j p a

theorem surfaceH1Equiv_periodCover_fibre (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (ProductTorus 3) 1) :
    surfaceH1Equiv j p
      (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 1
        (singularHomologyMap (fibreIntoPeriodTorus j p) 1 a)) =
      ![fibreCoinvariantCoordinate j (torusH1Equiv a), 0] := by
  change surfaceH1Equiv j p
    (((singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 1).comp
      (singularHomologyMap (fibreIntoPeriodTorus j p) 1)) a) = _
  rw [← singularHomologyMap_comp]
  exact surfaceH1Equiv_fibre j p a

/-- Every actual zero-class is already the image of a primitive fibre zero-class. -/
theorem surfacePeriodCover_h0_surjective (j : Kind) (p : FixedPeriod j) :
    Function.Surjective (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 0) := by
  intro a
  refine ⟨singularHomologyMap (fibreIntoPeriodTorus j p) 0
    (torusH0Coordinates.symm (surfaceH0Equiv j p a)), ?_⟩
  apply (surfaceH0Equiv j p).injective
  rw [surfaceH0Equiv_periodCover_fibre, LinearEquiv.apply_symm_apply]

theorem surfacePeriodCover_h0_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 0)).toAddSubgroup.index = 1 := by
  rw [LinearMap.range_eq_top.mpr (surfacePeriodCover_h0_surjective j p)]
  simp

/-- The actual forward monodromy preserves augmentation on the connected fibre. -/
theorem fibreHomologyMonodromy_zero (j : Kind) :
    monodromyHomologyMap (fibreTorusHomeomorph j) 0 = 1 := by
  ext a
  apply torusH0Coordinates.injective
  exact connectedHomologyZeroEquiv_natural
    (fibreTorusHomeomorph j : C(ProductTorus 3, ProductTorus 3)) a

/-- The degree-zero norm counts the actual finite number of sheets. -/
theorem fibreHomologyNorm_zero (j : Kind)
    (a : SingularHomology (ProductTorus 3) 0) :
    torusH0Coordinates (fibreHomologyNorm j 0 a) =
      (j.order : ℤ) * torusH0Coordinates a := by
  simp [fibreHomologyNorm, fibreHomologyMonodromy_zero]

def fibreHomologyNormZeroCoordinate (j : Kind) :
    SingularHomology (ProductTorus 3) 0 →ₗ[ℤ] ℤ :=
  torusH0Coordinates.toLinearMap.comp (fibreHomologyNorm j 0)

theorem fibreHomologyNormZeroCoordinate_apply (j : Kind)
    (a : SingularHomology (ProductTorus 3) 0) :
    fibreHomologyNormZeroCoordinate j a = (j.order : ℤ) * torusH0Coordinates a :=
  fibreHomologyNorm_zero j a

theorem fibreHomologyNormZeroCoordinate_range (j : Kind) :
    LinearMap.range (fibreHomologyNormZeroCoordinate j) =
      Submodule.span ℤ {(j.order : ℤ)} := by
  have h : fibreHomologyNormZeroCoordinate j =
      (j.order : ℤ) • torusH0Coordinates.toLinearMap := by
    ext a
    exact fibreHomologyNormZeroCoordinate_apply j a
  rw [h]
  exact int_scaled_coordinate_range _ torusH0Coordinates.surjective _

/-- The actual period cover expressed in the proved first-homology marking. -/
def surfacePeriodCoverH1Coordinates (j : Kind) (p : FixedPeriod j) :
    SingularHomology p.val.Torus 1 →ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceH1Equiv j p).toLinearMap.comp
    (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 1)

/-- The fibre coinvariant coordinate is primitive in the actual covering image. -/
theorem surfacePeriodCoverH1Coordinates_firstAxis (j : Kind) (p : FixedPeriod j) (t : ℤ) :
    ![t, 0] ∈ LinearMap.range (surfacePeriodCoverH1Coordinates j p) := by
  obtain ⟨v, hv⟩ := fibreCoinvariantCoordinate_surjective j t
  refine ⟨singularHomologyMap (fibreIntoPeriodTorus j p) 1
    (torusH1Equiv.symm v), ?_⟩
  change surfaceH1Equiv j p
    (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 1
      (singularHomologyMap (fibreIntoPeriodTorus j p) 1 _)) = _
  rw [surfaceH1Equiv_periodCover_fibre, LinearEquiv.apply_symm_apply, hv]

/-- The remaining coordinate is the actual zeroth norm of the circle boundary. -/
theorem surfacePeriodCoverH1Coordinates_secondMap (j : Kind) (p : FixedPeriod j) :
    CoverAlgebra.secondMap (surfacePeriodCoverH1Coordinates j p) =
      (fibreHomologyNormZeroCoordinate j).comp (surfacePeriodCoverCircleBoundary j p 0) := by
  ext a
  change mappingTorusH1Equiv j
    (surfaceMappingTorusHomologyEquiv j p 1
      (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 1 a)) 1 = _
  rw [mappingTorusH1Equiv_boundary, surfacePeriodCover_wangBoundary]
  rfl

theorem surfacePeriodCoverH1Coordinates_secondMap_range (j : Kind) (p : FixedPeriod j) :
    LinearMap.range (CoverAlgebra.secondMap (surfacePeriodCoverH1Coordinates j p)) =
      Submodule.span ℤ {(j.order : ℤ)} := by
  rw [surfacePeriodCoverH1Coordinates_secondMap,
    cover_range_comp_of_surjective _ _ (surfacePeriodCoverCircleBoundary_surjective j p 0),
    fibreHomologyNormZeroCoordinate_range]

theorem surfacePeriodCoverH1Coordinates_range (j : Kind) (p : FixedPeriod j) :
    LinearMap.range (surfacePeriodCoverH1Coordinates j p) =
      CoverAlgebra.divisibleSecond j.order :=
  CoverAlgebra.range_eq_divisibleSecond _ (surfacePeriodCoverH1Coordinates_firstAxis j p) _
    (surfacePeriodCoverH1Coordinates_secondMap_range j p)

theorem surfacePeriodCoverH1Coordinates_range_iff (j : Kind) (p : FixedPeriod j)
    (v : Fin 2 → ℤ) :
    v ∈ LinearMap.range (surfacePeriodCoverH1Coordinates j p) ↔ (j.order : ℤ) ∣ v 1 := by
  rw [surfacePeriodCoverH1Coordinates_range, CoverAlgebra.mem_divisibleSecond_iff]

def surfacePeriodCoverH1CoordinatesCokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    ((Fin 2 → ℤ) ⧸ LinearMap.range (surfacePeriodCoverH1Coordinates j p)) ≃ₗ[ℤ]
      ZMod j.order :=
  CoverAlgebra.cokernelEquivZMod _ (surfacePeriodCoverH1Coordinates_firstAxis j p) _
    (surfacePeriodCoverH1Coordinates_secondMap_range j p)

@[simp] theorem surfacePeriodCoverH1CoordinatesCokernelEquivZMod_mk
    (j : Kind) (p : FixedPeriod j) (v : Fin 2 → ℤ) :
    surfacePeriodCoverH1CoordinatesCokernelEquivZMod j p (Submodule.Quotient.mk v) =
      (v 1 : ZMod j.order) := rfl

theorem surfacePeriodCoverH1Coordinates_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (surfacePeriodCoverH1Coordinates j p)).toAddSubgroup.index = j.order :=
  CoverAlgebra.range_index _ (surfacePeriodCoverH1Coordinates_firstAxis j p) _
    (surfacePeriodCoverH1Coordinates_secondMap_range j p)

/-- The native actual first-homology covering cokernel is the sheet-count residue group. -/
def surfacePeriodCoverH1CokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 1 ⧸
      LinearMap.range (singularHomologyMap
        (periodCover j p j.twist (mainTwist_admissible j)) 1)) ≃ₗ[ℤ] ZMod j.order :=
  (coverCokernelCoordinatesEquiv
    (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 1)
    (surfaceH1Equiv j p)).trans (surfacePeriodCoverH1CoordinatesCokernelEquivZMod j p)

@[simp] theorem surfacePeriodCoverH1CokernelEquivZMod_mk (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 1) :
    surfacePeriodCoverH1CokernelEquivZMod j p (Submodule.Quotient.mk a) =
      (surfaceH1Equiv j p a 1 : ZMod j.order) := rfl

theorem surfacePeriodCover_h1_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 1)).toAddSubgroup.index = j.order := by
  rw [cover_range_index_coordinates _ (surfaceH1Equiv j p)]
  exact surfacePeriodCoverH1Coordinates_range_index j p

theorem surfacePeriodCover_h1_range_finiteIndex (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 1)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [surfacePeriodCover_h1_range_index]
  exact j.order_pos.ne'

variable {j : Kind} (D : Equivariant.Data j)

theorem periodTorusIntoFilling_h0_surjective :
    Function.Surjective (singularHomologyMap
      (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) 0) := by
  intro a
  obtain ⟨b, hb⟩ := surfacePeriodCover_h0_surjective j D.centralPeriod
    ((centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) 0).symm a)
  refine ⟨b, ?_⟩
  rw [← centralSurfaceHomologyEquiv_periodCover, hb, LinearEquiv.apply_symm_apply]

theorem periodTorusIntoFilling_h0_range_index :
    (LinearMap.range (singularHomologyMap
      (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) 0)).toAddSubgroup.index = 1 := by
  rw [periodTorusIntoFilling_homology_range_index, surfacePeriodCover_h0_range_index]

/-- The actual first-homology marking of the full filling retains the surface axes. -/
def fillingH1Equiv :
    SingularHomology (D.Space j.twist (mainTwist_admissible j)) 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) 1).symm.trans
    (surfaceH1Equiv j D.centralPeriod)

def fillingPeriodCoverH1CokernelEquivZMod :
    (SingularHomology (D.Space j.twist (mainTwist_admissible j)) 1 ⧸
      LinearMap.range (singularHomologyMap
        (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) 1)) ≃ₗ[ℤ] ZMod j.order :=
  (periodTorusIntoFillingCokernelSurfaceEquiv D 1).trans
    (surfacePeriodCoverH1CokernelEquivZMod j D.centralPeriod)

@[simp] theorem fillingPeriodCoverH1CokernelEquivZMod_mk
    (a : SingularHomology (D.Space j.twist (mainTwist_admissible j)) 1) :
    fillingPeriodCoverH1CokernelEquivZMod D (Submodule.Quotient.mk a) =
      (fillingH1Equiv D a 1 : ZMod j.order) := rfl

theorem periodTorusIntoFilling_h1_range_index :
    (LinearMap.range (singularHomologyMap
      (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) 1)).toAddSubgroup.index =
      j.order := by
  rw [periodTorusIntoFilling_homology_range_index, surfacePeriodCover_h1_range_index]

theorem periodTorusIntoFilling_h1_range_finiteIndex :
    (LinearMap.range (singularHomologyMap
      (periodTorusIntoFilling D j.twist
        (mainTwist_admissible j)) 1)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodTorusIntoFilling_h1_range_index]
  exact j.order_pos.ne'

end Wikipedia.HopfProblem.Elliptic.HigherHomology
