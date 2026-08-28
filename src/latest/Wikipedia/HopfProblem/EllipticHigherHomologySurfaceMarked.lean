import Wikipedia.HopfProblem.EllipticHigherHomologySurfaceGroups
import Wikipedia.HopfProblem.EllipticHigherHomologySurfaceMaps

/-!
# Marked actual fibre and period-cover homology maps

The time-zero three-torus is included in the original period torus in
the literal primitive fibre directions.  Its actual homology images
give the first integral axes of the central-surface markings.  Thus the
image of the genuine period cover contains those primitive axes.  This
does not yet identify the other covering coordinate or its index.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual fibre two-class maps to its ordered `01` coordinate on the first axis. -/
theorem surfaceH2Equiv_fibre (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (ProductTorus 3) 2) :
    surfaceH2Equiv j p (singularHomologyMap (fibreIntoSurface j p) 2 a) =
      ![torusH2Coordinates a 0, 0] := by
  change mappingTorusH2Equiv j
    (homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) 2
      (singularHomologyMap (fibreIntoSurface j p) 2 a)) = _
  rw [surfaceMappingTorusHomology_fibre, mappingTorusH2Equiv_fibre]

/-- The actual positive fibre orientation maps to the first third-homology axis. -/
theorem surfaceH3Equiv_fibre (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (ProductTorus 3) 3) :
    surfaceH3Equiv j p (singularHomologyMap (fibreIntoSurface j p) 3 a) =
      ![torusH3Coordinates a, 0] := by
  change mappingTorusH3Equiv j
    (homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) 3
      (singularHomologyMap (fibreIntoSurface j p) 3 a)) = _
  rw [surfaceMappingTorusHomology_fibre, mappingTorusH3Equiv_fibre]

/-- The period cover acts on the actual primitive fibre classes by the displayed degree-two axis. -/
theorem surfaceH2Equiv_periodCover_fibre (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (ProductTorus 3) 2) :
    surfaceH2Equiv j p
      (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 2
        (singularHomologyMap (fibreIntoPeriodTorus j p) 2 a)) =
      ![torusH2Coordinates a 0, 0] := by
  change surfaceH2Equiv j p
    (((singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 2).comp
      (singularHomologyMap (fibreIntoPeriodTorus j p) 2)) a) = _
  rw [← singularHomologyMap_comp]
  exact surfaceH2Equiv_fibre j p a

/-- The same literal period-cover factorization preserves the positive fibre orientation. -/
theorem surfaceH3Equiv_periodCover_fibre (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (ProductTorus 3) 3) :
    surfaceH3Equiv j p
      (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 3
        (singularHomologyMap (fibreIntoPeriodTorus j p) 3 a)) =
      ![torusH3Coordinates a, 0] := by
  change surfaceH3Equiv j p
    (((singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 3).comp
      (singularHomologyMap (fibreIntoPeriodTorus j p) 3)) a) = _
  rw [← singularHomologyMap_comp]
  exact surfaceH3Equiv_fibre j p a

/-- The degree-two actual period-cover map, expressed in the proved surface coordinates. -/
def surfacePeriodCoverH2Coordinates (j : Kind) (p : FixedPeriod j) :
    SingularHomology p.val.Torus 2 →ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceH2Equiv j p).toLinearMap.comp
    (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 2)

/-- The degree-three actual period-cover map in the proved surface coordinates. -/
def surfacePeriodCoverH3Coordinates (j : Kind) (p : FixedPeriod j) :
    SingularHomology p.val.Torus 3 →ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceH3Equiv j p).toLinearMap.comp
    (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 3)

/-- The top-degree actual period-cover map in the proved orientation coordinate. -/
def surfacePeriodCoverH4Coordinates (j : Kind) (p : FixedPeriod j) :
    SingularHomology p.val.Torus 4 →ₗ[ℤ] ℤ :=
  (surfaceH4Equiv j p).toLinearMap.comp
    (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 4)

/-- The actual covering image contains every integer multiple of the primitive first two-axis. -/
theorem surfacePeriodCoverH2Coordinates_firstAxis (j : Kind) (p : FixedPeriod j) (t : ℤ) :
    ![t, 0] ∈ LinearMap.range (surfacePeriodCoverH2Coordinates j p) := by
  refine ⟨singularHomologyMap (fibreIntoPeriodTorus j p) 2
    (torusH2Coordinates.symm ![t, 0, 0]), ?_⟩
  change surfaceH2Equiv j p
    (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 2
      (singularHomologyMap (fibreIntoPeriodTorus j p) 2 _)) = _
  rw [surfaceH2Equiv_periodCover_fibre, LinearEquiv.apply_symm_apply]
  rfl

/-- The actual covering image contains every integer multiple of the primitive first three-axis. -/
theorem surfacePeriodCoverH3Coordinates_firstAxis (j : Kind) (p : FixedPeriod j) (t : ℤ) :
    ![t, 0] ∈ LinearMap.range (surfacePeriodCoverH3Coordinates j p) := by
  refine ⟨singularHomologyMap (fibreIntoPeriodTorus j p) 3
    (torusH3Coordinates.symm t), ?_⟩
  change surfaceH3Equiv j p
    (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 3
      (singularHomologyMap (fibreIntoPeriodTorus j p) 3 _)) = _
  rw [surfaceH3Equiv_periodCover_fibre, LinearEquiv.apply_symm_apply]

/-- The kernel of the actual fibre map in degree two is exactly the vanishing `01` coordinate. -/
theorem fibreIntoSurface_h2_eq_zero_iff (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (ProductTorus 3) 2) :
    singularHomologyMap (fibreIntoSurface j p) 2 a = 0 ↔ torusH2Coordinates a 0 = 0 := by
  constructor
  · intro h
    have he := congrArg (fun v => surfaceH2Equiv j p v 0) h
    simpa only [surfaceH2Equiv_fibre, Matrix.cons_val_zero, map_zero, Pi.zero_apply] using he
  · intro h
    apply (surfaceH2Equiv j p).injective
    rw [surfaceH2Equiv_fibre, h, map_zero]
    ext i
    fin_cases i <;> rfl

/-- The actual fibre orientation injects into third homology of the surface. -/
theorem fibreIntoSurface_h3_injective (j : Kind) (p : FixedPeriod j) :
    Function.Injective (singularHomologyMap (fibreIntoSurface j p) 3) := by
  intro a b hab
  apply torusH3Coordinates.injective
  have he := congrArg (fun v => surfaceH3Equiv j p v 0) hab
  simpa only [surfaceH3Equiv_fibre, Matrix.cons_val_zero] using he

end Wikipedia.HopfProblem.Elliptic.HigherHomology
