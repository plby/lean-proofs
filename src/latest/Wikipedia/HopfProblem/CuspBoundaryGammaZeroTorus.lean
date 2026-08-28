import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroTorusTopology
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusCuspCoordinates
import Wikipedia.HopfProblem.EllipticHigherHomologyCoordinatesTorus

/-!
# The actual zero-first-coordinate subtorus of the native cusp boundary

The literal inclusion is obtained from the actual gamma-zero fibre, not
from a replacement torus. On real representatives the native cusp map
restricts to the three-dimensional shear displayed below. This proves the
intertwining needed for an actual map of the original mapping-torus
quotients, with no assumed homology or monodromy comparison.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspBoundaryGammaZero

open PeriodTorusHigherHomology Elliptic.HigherHomology SpecialPeriods.CuspFamily

/-- The lower-right block of the source's actual cusp monodromy. -/
def restrictedMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0; 1, 1, 0; 0, 0, 1]

/-- Its literal inverse shear. -/
def restrictedInverseMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0; -1, 1, 0; 0, 0, 1]

theorem restrictedMatrix_native_block (i j : Fin 3) :
    restrictedMatrix i j = M₀ i.succ j.succ := by
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem restrictedMatrix_det : restrictedMatrix.det = 1 := by decide

theorem restrictedInverseMatrix_mul : restrictedInverseMatrix * restrictedMatrix = 1 := by
  decide

theorem restrictedMatrix_mul_inverse : restrictedMatrix * restrictedInverseMatrix = 1 := by
  decide

/-- The actual integral shear on the three circle coordinates `(u,w,δ)`. -/
def restrictedMonodromy : ProductTorus 3 ≃ₜ ProductTorus 3 :=
  matrixTorusHomeomorph restrictedMatrix restrictedInverseMatrix
    restrictedInverseMatrix_mul restrictedMatrix_mul_inverse

@[simp] theorem restrictedMonodromy_apply (y : ProductTorus 3) :
    restrictedMonodromy y = torusMatrixMap restrictedMatrix y := rfl

/-- The real matrix formula fixes the source-coordinate order. -/
theorem restrictedMatrix_real_apply (x : Fin 3 → ℝ) :
    restrictedMatrix.map (Int.castRingHom ℝ) *ᵥ x = ![x 0, x 0 + x 1, x 2] := by
  ext i
  fin_cases i <;>
    simp [restrictedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The restricted map is literally the quotient of that real shear. -/
theorem restrictedMonodromy_coordinateProjection (x : Fin 3 → ℝ) :
    restrictedMonodromy (coordinateProjection 3 x) =
      coordinateProjection 3 ![x 0, x 0 + x 1, x 2] := by
  rw [restrictedMonodromy_apply, torusMatrixMap_coordinateProjection, restrictedMatrix_real_apply]

/-- The genuine gamma-zero inclusion with the three remaining circle coordinates. -/
def fibreMap : C(ProductTorus 3, RealTorus₄) :=
  TrianglePeriodFamily.GammaZero.fibreInclusion.comp
    (TrianglePeriodFamily.GammaZero.fibreHomeomorph.symm :
      C(ProductTorus 3, TrianglePeriodFamily.GammaZero.Fibre))

@[simp] theorem fibreMap_apply (y : ProductTorus 3) :
    fibreMap y = flatTorusCircleHomeomorph.symm (Fin.cons 0 y) := rfl

/-- On the original real period representatives the first coordinate is exactly zero. -/
@[simp] theorem fibreMap_coordinateProjection (x : Fin 3 → ℝ) :
    fibreMap (coordinateProjection 3 x) = standardLattice.mkQ (Fin.cons 0 x) :=
  TrianglePeriodFamily.GammaZero.fibreHomeomorph_symm_coordinateProjection x

theorem fibreMap_injective : Function.Injective fibreMap :=
  TrianglePeriodFamily.GammaZero.fibreInclusion_injective.comp
    TrianglePeriodFamily.GammaZero.fibreHomeomorph.symm.injective

/-- Its image lies in the literal zero fibre of the first circle character. -/
@[simp] theorem fibreMap_gamma (y : ProductTorus 3) :
    TrianglePeriodFamily.GammaZero.fibreGamma (fibreMap y) = 0 :=
  (TrianglePeriodFamily.GammaZero.fibreHomeomorph.symm y).property

/-- The original real cusp transformation restricts to this exact three-dimensional shear. -/
theorem cuspRealEquiv_cons_zero (x : Fin 3 → ℝ) :
    cuspRealEquiv 1 (Fin.cons 0 x) = Fin.cons 0 ![x 0, x 0 + x 1, x 2] := by
  ext i
  fin_cases i <;> simp [cuspRealEquiv, add_comm] <;> rfl

/-- The actual zero-head inclusion intertwines the original cusp homeomorphism. -/
theorem fibreMap_monodromy (y : ProductTorus 3) :
    fibreMap (restrictedMonodromy y) =
      ThreefoldOverlapMappingTorus.Cusp.monodromy (fibreMap y) := by
  obtain ⟨x, rfl⟩ := coordinateProjection_surjective 3 y
  rw [restrictedMonodromy_coordinateProjection, fibreMap_coordinateProjection,
    fibreMap_coordinateProjection]
  change standardLattice.mkQ (Fin.cons 0 ![x 0, x 0 + x 1, x 2]) =
    cuspTorusHomeomorph 1 (standardLattice.mkQ (Fin.cons 0 x))
  rw [cuspTorusHomeomorph_mkQ, cuspRealEquiv_cons_zero]

end Wikipedia.HopfProblem.CuspBoundaryGammaZero
