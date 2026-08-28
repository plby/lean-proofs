import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyCoordinates
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMarkingProductTorus
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorLatticeMatrices

/-!
# The actual source shear on second and third singular homology

The actual source-coordinate homeomorphism, in the original period order
`(β₀, β₁, α₀, α₁)`, transports the proved four-circle exterior markings.
Functoriality and the proved continuous-map conjugacy then identify the
descended source shear with the exterior square and cube of `M₀`.

The six- and four-coordinate markings use the existing ordered-minor
bases. No homology marking, rank comparison, or shear action is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyExterior LocalSystemMatrices
open scoped Matrix

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ)

/-- The actual source-coordinate homeomorphism induces an integral
homology equivalence in every degree. -/
def sourceCoordinateTorusHomologyEquiv (n : ℕ) :
    SingularHomology (SourceModel C₀) n ≃ₗ[ℤ] SingularHomology (ProductTorus 4) n :=
  homeomorphHomologyEquiv (sourceCoordinateTorusHomeomorph C₀) n

@[simp] theorem sourceCoordinateTorusHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (SourceModel C₀) n) :
    sourceCoordinateTorusHomologyEquiv C₀ n a =
      singularHomologyMap
        (sourceCoordinateTorusHomeomorph C₀ : C(SourceModel C₀, ProductTorus 4)) n a := rfl

/-- The proved source shear conjugacy gives the actual homology square,
without introducing an independent monodromy representation. -/
theorem sourceCoordinateTorusHomologyEquiv_shear (n : ℕ)
    (a : SingularHomology (SourceModel C₀) n) :
    sourceCoordinateTorusHomologyEquiv C₀ n (singularHomologyMap (sourceShear C₀) n a) =
      singularHomologyMap (torusMatrixMap M₀) n
        (sourceCoordinateTorusHomologyEquiv C₀ n a) := by
  have he := congrArg
    (fun g : C(SourceModel C₀, ProductTorus 4) => singularHomologyMap g n)
    (sourceCoordinateTorusHomeomorph_shear_comp C₀)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at he
  exact LinearMap.congr_fun he a

/-- The actual second singular homology of the source in the original
ordered integral exterior-square marking. -/
def sourceH2ExteriorEquiv :
    SingularHomology (SourceModel C₀) 2 ≃ₗ[ℤ] latticeExterior 2 :=
  (sourceCoordinateTorusHomologyEquiv C₀ 2).trans coordinateTorusH2ExteriorEquiv

/-- The actual third singular homology of the source in the original
ordered integral exterior-cube marking. -/
def sourceH3ExteriorEquiv :
    SingularHomology (SourceModel C₀) 3 ≃ₗ[ℤ] latticeExterior 3 :=
  (sourceCoordinateTorusHomologyEquiv C₀ 3).trans coordinateTorusH3ExteriorEquiv

@[simp] theorem sourceH2ExteriorEquiv_apply (a : SingularHomology (SourceModel C₀) 2) :
    sourceH2ExteriorEquiv C₀ a =
      coordinateTorusH2ExteriorEquiv (sourceCoordinateTorusHomologyEquiv C₀ 2 a) := rfl

@[simp] theorem sourceH3ExteriorEquiv_apply (a : SingularHomology (SourceModel C₀) 3) :
    sourceH3ExteriorEquiv C₀ a =
      coordinateTorusH3ExteriorEquiv (sourceCoordinateTorusHomologyEquiv C₀ 3 a) := rfl

/-- In degree two the genuine descended source shear acts by `∧² M₀`. -/
theorem sourceH2ExteriorEquiv_shear (a : SingularHomology (SourceModel C₀) 2) :
    sourceH2ExteriorEquiv C₀ (singularHomologyMap (sourceShear C₀) 2 a) =
      exteriorPower.map 2 M₀.mulVecLin (sourceH2ExteriorEquiv C₀ a) := by
  change coordinateTorusH2ExteriorEquiv
    (sourceCoordinateTorusHomologyEquiv C₀ 2 (singularHomologyMap (sourceShear C₀) 2 a)) = _
  rw [sourceCoordinateTorusHomologyEquiv_shear, coordinateTorusH2ExteriorEquiv_matrix]
  rfl

/-- In degree three the genuine descended source shear acts by `∧³ M₀`. -/
theorem sourceH3ExteriorEquiv_shear (a : SingularHomology (SourceModel C₀) 3) :
    sourceH3ExteriorEquiv C₀ (singularHomologyMap (sourceShear C₀) 3 a) =
      exteriorPower.map 3 M₀.mulVecLin (sourceH3ExteriorEquiv C₀ a) := by
  change coordinateTorusH3ExteriorEquiv
    (sourceCoordinateTorusHomologyEquiv C₀ 3 (singularHomologyMap (sourceShear C₀) 3 a)) = _
  rw [sourceCoordinateTorusHomologyEquiv_shear, coordinateTorusH3ExteriorEquiv_matrix]
  rfl

/-- The exterior-square marking intertwines the two actual linear maps. -/
theorem sourceH2ExteriorEquiv_shear_comp :
    (sourceH2ExteriorEquiv C₀).toLinearMap.comp (singularHomologyMap (sourceShear C₀) 2) =
      (exteriorPower.map 2 M₀.mulVecLin).comp (sourceH2ExteriorEquiv C₀).toLinearMap := by
  apply LinearMap.ext
  exact sourceH2ExteriorEquiv_shear C₀

/-- The exterior-cube marking intertwines the two actual linear maps. -/
theorem sourceH3ExteriorEquiv_shear_comp :
    (sourceH3ExteriorEquiv C₀).toLinearMap.comp (singularHomologyMap (sourceShear C₀) 3) =
      (exteriorPower.map 3 M₀.mulVecLin).comp (sourceH3ExteriorEquiv C₀).toLinearMap := by
  apply LinearMap.ext
  exact sourceH3ExteriorEquiv_shear C₀

/-- Conjugating the actual second-homology shear gives its exterior square. -/
theorem sourceH2ExteriorEquiv_shear_conjugate :
    ((sourceH2ExteriorEquiv C₀).toLinearMap.comp
        (singularHomologyMap (sourceShear C₀) 2)).comp
        (sourceH2ExteriorEquiv C₀).symm.toLinearMap = exteriorPower.map 2 M₀.mulVecLin := by
  apply LinearMap.ext
  intro a
  change sourceH2ExteriorEquiv C₀
    (singularHomologyMap (sourceShear C₀) 2 ((sourceH2ExteriorEquiv C₀).symm a)) = _
  rw [sourceH2ExteriorEquiv_shear, LinearEquiv.apply_symm_apply]

/-- Conjugating the actual third-homology shear gives its exterior cube. -/
theorem sourceH3ExteriorEquiv_shear_conjugate :
    ((sourceH3ExteriorEquiv C₀).toLinearMap.comp
        (singularHomologyMap (sourceShear C₀) 3)).comp
        (sourceH3ExteriorEquiv C₀).symm.toLinearMap = exteriorPower.map 3 M₀.mulVecLin := by
  apply LinearMap.ext
  intro a
  change sourceH3ExteriorEquiv C₀
    (singularHomologyMap (sourceShear C₀) 3 ((sourceH3ExteriorEquiv C₀).symm a)) = _
  rw [sourceH3ExteriorEquiv_shear, LinearEquiv.apply_symm_apply]

/-- Actual source second homology in the six ordered-minor coordinates. -/
def sourceH2Coordinates : SingularHomology (SourceModel C₀) 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  (sourceH2ExteriorEquiv C₀).trans squareCoordinates

/-- Actual source third homology in the four ordered-minor coordinates. -/
def sourceH3Coordinates : SingularHomology (SourceModel C₀) 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (sourceH3ExteriorEquiv C₀).trans cubeCoordinates

@[simp] theorem sourceH2Coordinates_apply (a : SingularHomology (SourceModel C₀) 2) :
    sourceH2Coordinates C₀ a =
      coordinateTorusH2Coordinates (sourceCoordinateTorusHomologyEquiv C₀ 2 a) := rfl

@[simp] theorem sourceH3Coordinates_apply (a : SingularHomology (SourceModel C₀) 3) :
    sourceH3Coordinates C₀ a =
      coordinateTorusH3Coordinates (sourceCoordinateTorusHomologyEquiv C₀ 3 a) := rfl

/-- The actual second-homology shear has the literal ordered square-minor matrix. -/
theorem sourceH2Coordinates_shear (a : SingularHomology (SourceModel C₀) 2) :
    sourceH2Coordinates C₀ (singularHomologyMap (sourceShear C₀) 2 a) =
      squareM₀ *ᵥ sourceH2Coordinates C₀ a := by
  change coordinateTorusH2Coordinates
    (sourceCoordinateTorusHomologyEquiv C₀ 2 (singularHomologyMap (sourceShear C₀) 2 a)) = _
  rw [sourceCoordinateTorusHomologyEquiv_shear, coordinateTorusH2Coordinates_matrix]
  rfl

/-- The actual third-homology shear has the literal ordered cube-minor matrix. -/
theorem sourceH3Coordinates_shear (a : SingularHomology (SourceModel C₀) 3) :
    sourceH3Coordinates C₀ (singularHomologyMap (sourceShear C₀) 3 a) =
      cubeM₀ *ᵥ sourceH3Coordinates C₀ a := by
  change coordinateTorusH3Coordinates
    (sourceCoordinateTorusHomologyEquiv C₀ 3 (singularHomologyMap (sourceShear C₀) 3 a)) = _
  rw [sourceCoordinateTorusHomologyEquiv_shear, coordinateTorusH3Coordinates_matrix]
  rfl

/-- Exact six-coordinate conjugacy of the genuine second-homology map. -/
theorem sourceH2Coordinates_shear_conjugate :
    ((sourceH2Coordinates C₀).toLinearMap.comp
        (singularHomologyMap (sourceShear C₀) 2)).comp
        (sourceH2Coordinates C₀).symm.toLinearMap = squareM₀.mulVecLin := by
  apply LinearMap.ext
  intro a
  change sourceH2Coordinates C₀
    (singularHomologyMap (sourceShear C₀) 2 ((sourceH2Coordinates C₀).symm a)) = _
  rw [sourceH2Coordinates_shear, LinearEquiv.apply_symm_apply]
  rfl

/-- Exact four-coordinate conjugacy of the genuine third-homology map. -/
theorem sourceH3Coordinates_shear_conjugate :
    ((sourceH3Coordinates C₀).toLinearMap.comp
        (singularHomologyMap (sourceShear C₀) 3)).comp
        (sourceH3Coordinates C₀).symm.toLinearMap = cubeM₀.mulVecLin := by
  apply LinearMap.ext
  intro a
  change sourceH3Coordinates C₀
    (singularHomologyMap (sourceShear C₀) 3 ((sourceH3Coordinates C₀).symm a)) = _
  rw [sourceH3Coordinates_shear, LinearEquiv.apply_symm_apply]
  rfl

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
