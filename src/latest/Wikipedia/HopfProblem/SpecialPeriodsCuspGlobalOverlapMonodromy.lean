import Wikipedia.HopfProblem.TrianglePeriodFamilyAction
import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyMonodromy

/-!
# Agreement of global and local cusp monodromy

Every integer power of the actual triangle cusp generator induces the
same integral matrix, real equivalence, and quotient-torus homeomorphism
as the clockwise local cusp action. The matrix is the dual monodromy
`M₀^k`; the source coordinate convention is `s ↦ s - k`.

In the varying complex period coordinates the corresponding right block
is the identity, so the complex vector coordinate is unchanged. This
distinction from the nontrivial real-torus monodromy is explicit below.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

open CuspFamily

/-- The actual dual triangle representation agrees with the clockwise
local cusp matrix at every integer power, including negative powers. -/
theorem triangleDualRepresentation_cusp_zpow_matrix (k : ℤ) :
    (triangleDualRepresentation (triangleCuspGenerator ^ k) : LatticeMatrix) =
      cuspIntegralMatrix k := by
  let C : Multiplicative ℤ →* LatticeMatrix :=
    { toFun := fun n => cuspIntegralMatrix n.toAdd
      map_one' := cuspIntegralMatrix_zero
      map_mul' := fun m n => cuspIntegralMatrix_add m.toAdd n.toAdd }
  let R : Multiplicative ℤ →* LatticeMatrix :=
    { toFun := fun n =>
        (triangleDualRepresentation (triangleCuspGenerator ^ n.toAdd) : LatticeMatrix)
      map_one' := by simp
      map_mul' := by
        intro m n
        change (triangleDualRepresentation (triangleCuspGenerator ^ (m.toAdd + n.toAdd)) :
          LatticeMatrix) = _
        rw [zpow_add, map_mul, Matrix.SpecialLinearGroup.coe_mul] }
  have he : R = C := by
    apply MonoidHom.ext_mint
    change (triangleDualRepresentation (triangleCuspGenerator ^ (1 : ℤ)) : LatticeMatrix) =
      cuspIntegralMatrix 1
    rw [zpow_one, cuspIntegralMatrix_one, triangleDualRepresentation_cusp_matrix]
  exact DFunLike.congr_fun he (Multiplicative.ofAdd k)

/-- The source coordinate matrix uses the opposite integer, as required
by its inverse-dual convention. -/
theorem triangleCoordinateMatrix_cusp_zpow (k : ℤ) :
    triangleCoordinateMatrix (triangleCuspGenerator ^ k) = cuspIntegralMatrix (-k) := by
  calc
    _ = triangleCoordinateMatrix ((triangleCuspGenerator ^ (-k))⁻¹) := by
      rw [zpow_neg, inv_inv]
    _ = (triangleDualRepresentation (triangleCuspGenerator ^ (-k)) : LatticeMatrix) :=
      triangleCoordinateMatrix_inv _
    _ = cuspIntegralMatrix (-k) := triangleDualRepresentation_cusp_zpow_matrix (-k)

/-- The original lattice representation is the inverse transpose of
the dual cusp monodromy used on real torus coordinates. -/
theorem triangleLatticeRepresentation_cusp_zpow_matrix (k : ℤ) :
    (triangleLatticeRepresentation (triangleCuspGenerator ^ k) : LatticeMatrix) =
      (cuspIntegralMatrix (-k)).transpose := by
  have h := congrArg Matrix.transpose (triangleCoordinateMatrix_cusp_zpow k)
  simpa only [triangleCoordinateMatrix, Matrix.transpose_transpose] using h

/-- The actual global and local real-linear cusp maps coincide. -/
theorem triangleRealEquiv_cusp_zpow (k : ℤ) :
    triangleRealEquiv (triangleCuspGenerator ^ k) = cuspRealEquiv k := by
  apply LinearEquiv.ext
  intro x
  rw [triangleRealEquiv_apply, triangleDualRepresentation_cusp_zpow_matrix,
    cuspRealEquiv_apply]

/-- Their descended linear maps coincide on the actual lattice quotient. -/
theorem triangleTorusLinearEquiv_cusp_zpow (k : ℤ) :
    triangleTorusLinearEquiv (triangleCuspGenerator ^ k) = cuspTorusLinearEquiv k := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  change standardLattice.mkQ (triangleRealEquiv (triangleCuspGenerator ^ k) v) =
    standardLattice.mkQ (cuspRealEquiv k v)
  rw [triangleRealEquiv_cusp_zpow]

/-- Exact equality of the global and local monodromy homeomorphisms,
not merely equality of their actions on a homology basis. -/
theorem triangleTorusHomeomorph_cusp_zpow (k : ℤ) :
    triangleTorusHomeomorph (triangleCuspGenerator ^ k) = cuspTorusHomeomorph k := by
  apply Homeomorph.ext
  intro x
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  rw [triangleTorusHomeomorph_mkQ, cuspTorusHomeomorph_mkQ, triangleRealEquiv_cusp_zpow]

/-- The last two normalized period columns are unchanged by the actual
clockwise integral cusp matrix. -/
theorem periodMatrix_cuspIntegralMatrix_right (p : PeriodPoint) (k : ℤ) :
    TrianglePeriodFamily.matrixRight
      (p.matrix * (cuspIntegralMatrix k).map (Int.castRingHom ℂ)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TrianglePeriodFamily.matrixRight, PeriodPoint.matrix, cuspIntegralMatrix,
      Matrix.mul_apply, Fin.sum_univ_four]

end Wikipedia.HopfProblem.SpecialPeriods

namespace Wikipedia.HopfProblem.TrianglePeriodFamily

open SpecialPeriods SpecialPeriods.CuspFamily

theorem dualComplexMatrix_cusp_zpow (k : ℤ) :
    dualComplexMatrix (triangleCuspGenerator ^ k) =
      (cuspIntegralMatrix k).map (Int.castRingHom ℂ) := by
  rw [dualComplexMatrix, triangleDualRepresentation_cusp_zpow_matrix]

theorem coordinateComplexMatrix_cusp_zpow (k : ℤ) :
    coordinateComplexMatrix (triangleCuspGenerator ^ k) =
      (cuspIntegralMatrix (-k)).map (Int.castRingHom ℂ) := by
  rw [coordinateComplexMatrix_eq, triangleCoordinateMatrix_cusp_zpow]

namespace Data

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)

/-- The actual complex cusp cocycle is the identity, independently of
the particular admissible covariant period data. -/
theorem rightBlock_cusp_zpow (k : ℤ) (b : B) :
    D.rightBlock (triangleCuspGenerator ^ k) b = 1 := by
  change matrixRight ((D.periods.point ((triangleCuspGenerator ^ k) • b)).val.matrix *
    dualComplexMatrix (triangleCuspGenerator ^ k)) = 1
  rw [dualComplexMatrix_cusp_zpow]
  exact periodMatrix_cuspIntegralMatrix_right _ k

/-- Real cusp monodromy is exactly absorbed by the varying periods. -/
theorem periodEquiv_cusp_zpow (k : ℤ) (b : B) (x : RealPlane₄) :
    D.periods.periodEquiv ((triangleCuspGenerator ^ k) • b) (cuspRealEquiv k x) =
      D.periods.periodEquiv b x := by
  have h := D.periodEquiv_monodromy (triangleCuspGenerator ^ k) b x
  rw [triangleRealEquiv_cusp_zpow, D.rightBlock_cusp_zpow, Matrix.one_mulVec] at h
  exact h

/-- The global cusp lift changes only the base coordinate, exactly as
the local clockwise cusp lift does in complex-vector coordinates. -/
theorem complexLift_cusp_zpow (k : ℤ) (x : B × ComplexPlane₂) :
    D.complexLift (triangleCuspGenerator ^ k) x =
      ((triangleCuspGenerator ^ k) • x.1, x.2) := by
  simp only [complexLift, D.rightBlock_cusp_zpow, Matrix.one_mulVec]

/-- On the actual topological total family the same cusp iterate uses
the local cusp torus homeomorphism, with integer `k`, not `-k`. -/
theorem totalAction_cusp_zpow (k : ℤ) (x : D.TotalSpace) :
    letI := D.totalAction
    (triangleCuspGenerator ^ k) • x =
      ((triangleCuspGenerator ^ k) • x.1, cuspTorusHomeomorph k x.2) := by
  let := D.totalAction
  change ((triangleCuspGenerator ^ k) • x.1,
    triangleTorusHomeomorph (triangleCuspGenerator ^ k) x.2) = _
  rw [triangleTorusHomeomorph_cusp_zpow]

end Data

end Wikipedia.HopfProblem.TrianglePeriodFamily
