import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMarking

/-!
# Actual integral higher monodromy of the period changes

The genuine period-change biholomorphisms act on actual singular homology
by the exterior powers of their already proved integral first-homology
matrices. The coordinate statements use the source's increasing-pair
and increasing-triple order, and the final statements identify the whole
induced linear maps with the literal integral minor matrices.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris PeriodTorusHigherHomologyExterior

theorem periodTorusH2ExteriorEquiv_step₁ (p : PeriodDomain)
    (a : SingularHomology p.Torus 2) :
    periodTorusH2ExteriorEquiv p.step₁ (singularHomologyMap p.step₁ContinuousMap 2 a) =
      exteriorMap 2 A₁ (periodTorusH2ExteriorEquiv p a) :=
  periodTorusH2ExteriorEquiv_natural p p.step₁ p.step₁ContinuousMap
    (step₁ContinuousMap_add p) A₁.mulVecLin (periodTorusH1_marking_step₁ p) a

theorem periodTorusH2ExteriorEquiv_step₂ (p : PeriodDomain)
    (a : SingularHomology p.Torus 2) :
    periodTorusH2ExteriorEquiv p.step₂ (singularHomologyMap p.step₂ContinuousMap 2 a) =
      exteriorMap 2 A₂ (periodTorusH2ExteriorEquiv p a) :=
  periodTorusH2ExteriorEquiv_natural p p.step₂ p.step₂ContinuousMap
    (step₂ContinuousMap_add p) A₂.mulVecLin (periodTorusH1_marking_step₂ p) a

theorem periodTorusH2ExteriorEquiv_step₀ (p : PeriodDomain)
    (a : SingularHomology p.Torus 2) :
    periodTorusH2ExteriorEquiv p.step₀ (singularHomologyMap p.step₀ContinuousMap 2 a) =
      exteriorMap 2 M₀ (periodTorusH2ExteriorEquiv p a) :=
  periodTorusH2ExteriorEquiv_natural p p.step₀ p.step₀ContinuousMap
    (step₀ContinuousMap_add p) M₀.mulVecLin (periodTorusH1_marking_step₀ p) a

theorem periodTorusH3ExteriorEquiv_step₁ (p : PeriodDomain)
    (a : SingularHomology p.Torus 3) :
    periodTorusH3ExteriorEquiv p.step₁ (singularHomologyMap p.step₁ContinuousMap 3 a) =
      exteriorMap 3 A₁ (periodTorusH3ExteriorEquiv p a) :=
  periodTorusH3ExteriorEquiv_natural p p.step₁ p.step₁ContinuousMap
    (step₁ContinuousMap_add p) A₁.mulVecLin (periodTorusH1_marking_step₁ p) a

theorem periodTorusH3ExteriorEquiv_step₂ (p : PeriodDomain)
    (a : SingularHomology p.Torus 3) :
    periodTorusH3ExteriorEquiv p.step₂ (singularHomologyMap p.step₂ContinuousMap 3 a) =
      exteriorMap 3 A₂ (periodTorusH3ExteriorEquiv p a) :=
  periodTorusH3ExteriorEquiv_natural p p.step₂ p.step₂ContinuousMap
    (step₂ContinuousMap_add p) A₂.mulVecLin (periodTorusH1_marking_step₂ p) a

theorem periodTorusH3ExteriorEquiv_step₀ (p : PeriodDomain)
    (a : SingularHomology p.Torus 3) :
    periodTorusH3ExteriorEquiv p.step₀ (singularHomologyMap p.step₀ContinuousMap 3 a) =
      exteriorMap 3 M₀ (periodTorusH3ExteriorEquiv p a) :=
  periodTorusH3ExteriorEquiv_natural p p.step₀ p.step₀ContinuousMap
    (step₀ContinuousMap_add p) M₀.mulVecLin (periodTorusH1_marking_step₀ p) a

/-- The first actual biholomorphism acts on the six second-homology coordinates by ∧²A₁. -/
theorem periodTorusH2Coordinates_step₁ (p : PeriodDomain) (a : SingularHomology p.Torus 2) :
    periodTorusH2Coordinates p.step₁ (singularHomologyMap p.step₁ContinuousMap 2 a) =
      squareA₁ *ᵥ periodTorusH2Coordinates p a := by
  change squareCoordinates (periodTorusH2ExteriorEquiv p.step₁
    (singularHomologyMap p.step₁ContinuousMap 2 a)) =
      squareA₁ *ᵥ squareCoordinates (periodTorusH2ExteriorEquiv p a)
  rw [periodTorusH2ExteriorEquiv_step₁, squareCoordinates_A₁]

/-- The second actual biholomorphism acts on second homology by ∧²A₂. -/
theorem periodTorusH2Coordinates_step₂ (p : PeriodDomain) (a : SingularHomology p.Torus 2) :
    periodTorusH2Coordinates p.step₂ (singularHomologyMap p.step₂ContinuousMap 2 a) =
      squareA₂ *ᵥ periodTorusH2Coordinates p a := by
  change squareCoordinates (periodTorusH2ExteriorEquiv p.step₂
    (singularHomologyMap p.step₂ContinuousMap 2 a)) =
      squareA₂ *ᵥ squareCoordinates (periodTorusH2ExteriorEquiv p a)
  rw [periodTorusH2ExteriorEquiv_step₂, squareCoordinates_A₂]

/-- The actual cusp change acts on second homology by ∧²M₀. -/
theorem periodTorusH2Coordinates_step₀ (p : PeriodDomain) (a : SingularHomology p.Torus 2) :
    periodTorusH2Coordinates p.step₀ (singularHomologyMap p.step₀ContinuousMap 2 a) =
      squareM₀ *ᵥ periodTorusH2Coordinates p a := by
  change squareCoordinates (periodTorusH2ExteriorEquiv p.step₀
    (singularHomologyMap p.step₀ContinuousMap 2 a)) =
      squareM₀ *ᵥ squareCoordinates (periodTorusH2ExteriorEquiv p a)
  rw [periodTorusH2ExteriorEquiv_step₀, squareCoordinates_M₀]

/-- The first actual biholomorphism acts on the four third-homology coordinates by ∧³A₁. -/
theorem periodTorusH3Coordinates_step₁ (p : PeriodDomain) (a : SingularHomology p.Torus 3) :
    periodTorusH3Coordinates p.step₁ (singularHomologyMap p.step₁ContinuousMap 3 a) =
      cubeA₁ *ᵥ periodTorusH3Coordinates p a := by
  change cubeCoordinates (periodTorusH3ExteriorEquiv p.step₁
    (singularHomologyMap p.step₁ContinuousMap 3 a)) =
      cubeA₁ *ᵥ cubeCoordinates (periodTorusH3ExteriorEquiv p a)
  rw [periodTorusH3ExteriorEquiv_step₁, cubeCoordinates_A₁]

/-- The second actual biholomorphism acts on third homology by ∧³A₂. -/
theorem periodTorusH3Coordinates_step₂ (p : PeriodDomain) (a : SingularHomology p.Torus 3) :
    periodTorusH3Coordinates p.step₂ (singularHomologyMap p.step₂ContinuousMap 3 a) =
      cubeA₂ *ᵥ periodTorusH3Coordinates p a := by
  change cubeCoordinates (periodTorusH3ExteriorEquiv p.step₂
    (singularHomologyMap p.step₂ContinuousMap 3 a)) =
      cubeA₂ *ᵥ cubeCoordinates (periodTorusH3ExteriorEquiv p a)
  rw [periodTorusH3ExteriorEquiv_step₂, cubeCoordinates_A₂]

/-- The actual cusp change acts on third homology by ∧³M₀. -/
theorem periodTorusH3Coordinates_step₀ (p : PeriodDomain) (a : SingularHomology p.Torus 3) :
    periodTorusH3Coordinates p.step₀ (singularHomologyMap p.step₀ContinuousMap 3 a) =
      cubeM₀ *ᵥ periodTorusH3Coordinates p a := by
  change cubeCoordinates (periodTorusH3ExteriorEquiv p.step₀
    (singularHomologyMap p.step₀ContinuousMap 3 a)) =
      cubeM₀ *ᵥ cubeCoordinates (periodTorusH3ExteriorEquiv p a)
  rw [periodTorusH3ExteriorEquiv_step₀, cubeCoordinates_M₀]

/-- Equality of the entire actual second-homology map with the first six-minor matrix. -/
theorem periodTorusH2_step₁_conjugate (p : PeriodDomain) :
    (periodTorusH2Coordinates p.step₁).toLinearMap.comp
      ((singularHomologyMap p.step₁ContinuousMap 2).comp
        (periodTorusH2Coordinates p).symm.toLinearMap) = squareA₁.mulVecLin := by
  apply LinearMap.ext
  intro v
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
    LinearEquiv.apply_symm_apply] using
      periodTorusH2Coordinates_step₁ p ((periodTorusH2Coordinates p).symm v)

theorem periodTorusH2_step₂_conjugate (p : PeriodDomain) :
    (periodTorusH2Coordinates p.step₂).toLinearMap.comp
      ((singularHomologyMap p.step₂ContinuousMap 2).comp
        (periodTorusH2Coordinates p).symm.toLinearMap) = squareA₂.mulVecLin := by
  apply LinearMap.ext
  intro v
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
    LinearEquiv.apply_symm_apply] using
      periodTorusH2Coordinates_step₂ p ((periodTorusH2Coordinates p).symm v)

theorem periodTorusH2_step₀_conjugate (p : PeriodDomain) :
    (periodTorusH2Coordinates p.step₀).toLinearMap.comp
      ((singularHomologyMap p.step₀ContinuousMap 2).comp
        (periodTorusH2Coordinates p).symm.toLinearMap) = squareM₀.mulVecLin := by
  apply LinearMap.ext
  intro v
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
    LinearEquiv.apply_symm_apply] using
      periodTorusH2Coordinates_step₀ p ((periodTorusH2Coordinates p).symm v)

/-- Equality of the entire actual third-homology map with the first four-minor matrix. -/
theorem periodTorusH3_step₁_conjugate (p : PeriodDomain) :
    (periodTorusH3Coordinates p.step₁).toLinearMap.comp
      ((singularHomologyMap p.step₁ContinuousMap 3).comp
        (periodTorusH3Coordinates p).symm.toLinearMap) = cubeA₁.mulVecLin := by
  apply LinearMap.ext
  intro v
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
    LinearEquiv.apply_symm_apply] using
      periodTorusH3Coordinates_step₁ p ((periodTorusH3Coordinates p).symm v)

theorem periodTorusH3_step₂_conjugate (p : PeriodDomain) :
    (periodTorusH3Coordinates p.step₂).toLinearMap.comp
      ((singularHomologyMap p.step₂ContinuousMap 3).comp
        (periodTorusH3Coordinates p).symm.toLinearMap) = cubeA₂.mulVecLin := by
  apply LinearMap.ext
  intro v
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
    LinearEquiv.apply_symm_apply] using
      periodTorusH3Coordinates_step₂ p ((periodTorusH3Coordinates p).symm v)

theorem periodTorusH3_step₀_conjugate (p : PeriodDomain) :
    (periodTorusH3Coordinates p.step₀).toLinearMap.comp
      ((singularHomologyMap p.step₀ContinuousMap 3).comp
        (periodTorusH3Coordinates p).symm.toLinearMap) = cubeM₀.mulVecLin := by
  apply LinearMap.ext
  intro v
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
    LinearEquiv.apply_symm_apply] using
      periodTorusH3Coordinates_step₀ p ((periodTorusH3Coordinates p).symm v)

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
