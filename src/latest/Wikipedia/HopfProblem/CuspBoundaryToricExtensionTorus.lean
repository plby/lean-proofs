import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusCuspCoordinates
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMatrixMaps

/-!
# The literal fixed phase subtorus of the cusp monodromy

The two last original period coordinates give the actual inclusion
`(w,δ) ↦ (0,0,w,δ)` in the real four-torus.  The real-representative
formula and fixedness under the original cusp homeomorphism are proved
before passing to its mapping torus.  No homology marking is assigned
by these definitions.
-/

noncomputable section

open scoped Matrix ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryToricExtension

open PeriodTorusHigherHomology SpecialPeriods.CuspFamily

/-- The literal inclusion in the original four additive-circle coordinates. -/
def fibreCoordinates : C(ProductTorus 2, ProductTorus 4) where
  toFun y := ![0, 0, y 0, y 1]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact continuous_const
    · exact continuous_apply 0
    · exact continuous_apply 1

@[simp] theorem fibreCoordinates_apply (y : ProductTorus 2) :
    fibreCoordinates y = ![0, 0, y 0, y 1] := rfl

/-- Its integral matrix in the fixed original coordinate order. -/
def fibreInclusionMatrix : Matrix (Fin 4) (Fin 2) ℤ :=
  !![0, 0; 0, 0; 1, 0; 0, 1]

theorem fibreCoordinates_eq_matrixMap :
    fibreCoordinates = torusMatrixMap fibreInclusionMatrix := by
  apply ContinuousMap.ext
  intro y
  funext i
  fin_cases i <;>
    simp [fibreCoordinates, fibreInclusionMatrix, torusMatrixMap_apply, Fin.sum_univ_two]

/-- The literal inclusion matrix is fixed by the actual integral monodromy. -/
theorem fibreInclusionMatrix_monodromy : M₀ * fibreInclusionMatrix = fibreInclusionMatrix := by
  decide

/-- The continuous inclusion in the original real quotient torus. -/
def fibreMap : C(ProductTorus 2, RealTorus₄) :=
  (flatTorusCircleHomeomorph.symm : C(ProductTorus 4, RealTorus₄)).comp fibreCoordinates

@[simp] theorem fibreMap_apply (y : ProductTorus 2) :
    fibreMap y = flatTorusCircleHomeomorph.symm ![0, 0, y 0, y 1] := rfl

/-- Taking the original circle coordinates recovers exactly the fixed two-torus. -/
@[simp] theorem fibreMap_coordinates (y : ProductTorus 2) :
    flatTorusCircleHomeomorph (fibreMap y) = fibreCoordinates y :=
  flatTorusCircleHomeomorph.apply_symm_apply _

/-- Real period representatives retain two leading zeros literally. -/
@[simp] theorem fibreMap_coordinateProjection (x : Fin 2 → ℝ) :
    fibreMap (coordinateProjection 2 x) = standardLattice.mkQ ![0, 0, x 0, x 1] := by
  apply flatTorusCircleHomeomorph.injective
  rw [fibreMap_coordinates, flatTorusCircleHomeomorph_mkQ]
  funext i
  fin_cases i <;> simp [fibreCoordinates, coordinateProjection]

theorem fibreMap_injective : Function.Injective fibreMap := by
  intro y z hyz
  have h := congrArg flatTorusCircleHomeomorph hyz
  rw [fibreMap_coordinates, fibreMap_coordinates] at h
  funext i
  fin_cases i
  · exact congrFun h 2
  · exact congrFun h 3

/-- The real cusp shear fixes every vector with two leading zeros. -/
theorem cuspRealEquiv_fixed_last_two (x : Fin 2 → ℝ) :
    cuspRealEquiv 1 ![0, 0, x 0, x 1] = ![0, 0, x 0, x 1] := by
  funext i
  fin_cases i <;> simp [cuspRealEquiv]

/-- The actual native cusp monodromy fixes the entire literal phase subtorus. -/
@[simp] theorem monodromy_fibreMap (y : ProductTorus 2) :
    ThreefoldOverlapMappingTorus.Cusp.monodromy (fibreMap y) = fibreMap y := by
  obtain ⟨x, rfl⟩ := coordinateProjection_surjective 2 y
  rw [fibreMap_coordinateProjection]
  change cuspTorusHomeomorph 1 (standardLattice.mkQ ![0, 0, x 0, x 1]) = _
  rw [cuspTorusHomeomorph_mkQ, cuspRealEquiv_fixed_last_two]

/-- The equivariance statement with the literal identity source homeomorphism. -/
theorem fibreMap_monodromy (y : ProductTorus 2) :
    fibreMap ((Homeomorph.refl (ProductTorus 2)) y) =
      ThreefoldOverlapMappingTorus.Cusp.monodromy (fibreMap y) :=
  (monodromy_fibreMap y).symm

end Wikipedia.HopfProblem.CuspBoundaryToricExtension
