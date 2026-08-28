import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorBasis
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorDual
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorLatticeMatrices

/-!
# Actual exterior-power actions and the source's ordered-minor matrices

The coordinate maps below intertwine Mathlib's actual `exteriorPower.map` with
the ordered-minor matrices already used in `LocalSystemMatrices`. The statement
holds for every integral rank-four matrix, hence for both the lattice actions
`A₁,A₂,M₀` and the source's dual transport actions `T₁,T₂,T₀`.

Ordinary dual pullback has the transpose matrix. The source's forward transport
on the dual lattice is instead inverse transpose; the checked two-sided inverse
relations in `PeriodTorusHigherHomologyExteriorLatticeMatrices` record this
distinction. No exterior power is asserted here to be a singular-homology group.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomologyExterior

open LocalSystemMatrices
open scoped Matrix

/-- The actual exterior-power map of an integral lattice matrix. -/
def exteriorMap (n : ℕ) (T : LatticeMatrix) :
    latticeExterior n →ₗ[ℤ] latticeExterior n :=
  exteriorPower.map n T.mulVecLin

@[simp] theorem exteriorMap_one (n : ℕ) :
    exteriorMap n 1 = LinearMap.id := by
  simp only [exteriorMap, Matrix.mulVecLin_one, exteriorPower.map_id]

theorem exteriorMap_mul (n : ℕ) (A B : LatticeMatrix) :
    exteriorMap n (A * B) = (exteriorMap n A).comp (exteriorMap n B) := by
  simp only [exteriorMap, Matrix.mulVecLin_mul, exteriorPower.map_comp]

/-- The genuine multiplicative action on the exterior power. -/
def exteriorRepresentation (n : ℕ) : LatticeMatrix →* Module.End ℤ (latticeExterior n) where
  toFun := exteriorMap n
  map_one' := exteriorMap_one n
  map_mul' := exteriorMap_mul n

/-- Every entry is the literal ordered two-by-two minor of the original matrix. -/
theorem squareMap_coefficient (T : LatticeMatrix) (i j : Fin 6) :
    squareBasis.repr (exteriorMap 2 T (squareBasis j)) i = exteriorSquare T i j := by
  rw [squareBasis, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  change (standardExteriorBasis 4 2).repr
      (exteriorPower.map 2 T.mulVecLin (standardExteriorBasis 4 2 (pairSubset j)))
      (pairSubset i) = _
  rw [standardExterior_map_coefficient, pairSubset_ordered, pairSubset_ordered]
  rfl

/-- Every entry is the literal ordered three-by-three minor of the original matrix. -/
theorem cubeMap_coefficient (T : LatticeMatrix) (i j : Fin 4) :
    cubeBasis.repr (exteriorMap 3 T (cubeBasis j)) i = exteriorCube T i j := by
  rw [cubeBasis, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  change (standardExteriorBasis 4 3).repr
      (exteriorPower.map 3 T.mulVecLin (standardExteriorBasis 4 3 (tripleSubset j)))
      (tripleSubset i) = _
  rw [standardExterior_map_coefficient, tripleSubset_ordered, tripleSubset_ordered]
  rfl

theorem squareMap_toMatrix (T : LatticeMatrix) :
    LinearMap.toMatrix squareBasis squareBasis (exteriorMap 2 T) = exteriorSquare T := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact squareMap_coefficient T i j

theorem cubeMap_toMatrix (T : LatticeMatrix) :
    LinearMap.toMatrix cubeBasis cubeBasis (exteriorMap 3 T) = exteriorCube T := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact cubeMap_coefficient T i j

/-- The actual degree-two exterior map is represented by the existing minor matrix. -/
theorem squareCoordinates_map (T : LatticeMatrix) (x : latticeExterior 2) :
    squareCoordinates (exteriorMap 2 T x) = exteriorSquare T *ᵥ squareCoordinates x := by
  have h := LinearMap.toMatrix_mulVec_repr squareBasis squareBasis (exteriorMap 2 T) x
  rw [squareMap_toMatrix] at h
  simpa only [squareCoordinates, Module.Basis.equivFun_apply] using h.symm

/-- The actual degree-three exterior map is represented by the existing minor matrix. -/
theorem cubeCoordinates_map (T : LatticeMatrix) (x : latticeExterior 3) :
    cubeCoordinates (exteriorMap 3 T x) = exteriorCube T *ᵥ cubeCoordinates x := by
  have h := LinearMap.toMatrix_mulVec_repr cubeBasis cubeBasis (exteriorMap 3 T) x
  rw [cubeMap_toMatrix] at h
  simpa only [cubeCoordinates, Module.Basis.equivFun_apply] using h.symm

theorem squareCoordinates_intertwines (T : LatticeMatrix) :
    squareCoordinates.toLinearMap.comp (exteriorMap 2 T) =
      (exteriorSquare T).mulVecLin.comp squareCoordinates.toLinearMap := by
  apply LinearMap.ext
  exact squareCoordinates_map T

theorem cubeCoordinates_intertwines (T : LatticeMatrix) :
    cubeCoordinates.toLinearMap.comp (exteriorMap 3 T) =
      (exteriorCube T).mulVecLin.comp cubeCoordinates.toLinearMap := by
  apply LinearMap.ext
  exact cubeCoordinates_map T

theorem squareCoordinates_conjugate (T : LatticeMatrix) :
    (squareCoordinates.toLinearMap.comp (exteriorMap 2 T)).comp
        squareCoordinates.symm.toLinearMap = (exteriorSquare T).mulVecLin := by
  apply LinearMap.ext
  intro x
  change squareCoordinates (exteriorMap 2 T (squareCoordinates.symm x)) = _
  rw [squareCoordinates_map, LinearEquiv.apply_symm_apply]
  rfl

theorem cubeCoordinates_conjugate (T : LatticeMatrix) :
    (cubeCoordinates.toLinearMap.comp (exteriorMap 3 T)).comp
        cubeCoordinates.symm.toLinearMap = (exteriorCube T).mulVecLin := by
  apply LinearMap.ext
  intro x
  change cubeCoordinates (exteriorMap 3 T (cubeCoordinates.symm x)) = _
  rw [cubeCoordinates_map, LinearEquiv.apply_symm_apply]
  rfl

theorem exteriorSquare_one : exteriorSquare (1 : LatticeMatrix) = 1 := by
  rw [← squareMap_toMatrix, exteriorMap_one, LinearMap.toMatrix_id]

theorem exteriorCube_one : exteriorCube (1 : LatticeMatrix) = 1 := by
  rw [← cubeMap_toMatrix, exteriorMap_one, LinearMap.toMatrix_id]

theorem exteriorSquare_mul (A B : LatticeMatrix) :
    exteriorSquare (A * B) = exteriorSquare A * exteriorSquare B := by
  rw [← squareMap_toMatrix, exteriorMap_mul,
    LinearMap.toMatrix_comp squareBasis squareBasis squareBasis,
    squareMap_toMatrix, squareMap_toMatrix]

theorem exteriorCube_mul (A B : LatticeMatrix) :
    exteriorCube (A * B) = exteriorCube A * exteriorCube B := by
  rw [← cubeMap_toMatrix, exteriorMap_mul,
    LinearMap.toMatrix_comp cubeBasis cubeBasis cubeBasis,
    cubeMap_toMatrix, cubeMap_toMatrix]

theorem exteriorSquare_transpose (T : LatticeMatrix) :
    exteriorSquare T.transpose = (exteriorSquare T).transpose := by
  ext i j
  change (T.submatrix (pairIndices j) (pairIndices i)).transpose.det =
    (T.submatrix (pairIndices j) (pairIndices i)).det
  exact Matrix.det_transpose _

theorem exteriorCube_transpose (T : LatticeMatrix) :
    exteriorCube T.transpose = (exteriorCube T).transpose := by
  ext i j
  change (T.submatrix (tripleIndices j) (tripleIndices i)).transpose.det =
    (T.submatrix (tripleIndices j) (tripleIndices i)).det
  exact Matrix.det_transpose _

/-! ## Actual dual maps and the transpose convention -/

def squareDualCoordinates : Module.Dual ℤ (latticeExterior 2) ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  squareBasis.dualBasis.equivFun

def cubeDualCoordinates : Module.Dual ℤ (latticeExterior 3) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  cubeBasis.dualBasis.equivFun

theorem squareDualMap_toMatrix (T : LatticeMatrix) :
    LinearMap.toMatrix squareBasis.dualBasis squareBasis.dualBasis (exteriorMap 2 T).dualMap =
      (exteriorSquare T).transpose := by
  rw [LinearMap.dualMap_def, LinearMap.toMatrix_transpose, squareMap_toMatrix]

theorem cubeDualMap_toMatrix (T : LatticeMatrix) :
    LinearMap.toMatrix cubeBasis.dualBasis cubeBasis.dualBasis (exteriorMap 3 T).dualMap =
      (exteriorCube T).transpose := by
  rw [LinearMap.dualMap_def, LinearMap.toMatrix_transpose, cubeMap_toMatrix]

theorem squareDualCoordinates_map (T : LatticeMatrix)
    (ξ : Module.Dual ℤ (latticeExterior 2)) :
    squareDualCoordinates ((exteriorMap 2 T).dualMap ξ) =
      (exteriorSquare T).transpose *ᵥ squareDualCoordinates ξ := by
  have h := LinearMap.toMatrix_mulVec_repr squareBasis.dualBasis squareBasis.dualBasis
    (exteriorMap 2 T).dualMap ξ
  rw [squareDualMap_toMatrix] at h
  simpa only [squareDualCoordinates, Module.Basis.equivFun_apply] using h.symm

theorem cubeDualCoordinates_map (T : LatticeMatrix)
    (ξ : Module.Dual ℤ (latticeExterior 3)) :
    cubeDualCoordinates ((exteriorMap 3 T).dualMap ξ) =
      (exteriorCube T).transpose *ᵥ cubeDualCoordinates ξ := by
  have h := LinearMap.toMatrix_mulVec_repr cubeBasis.dualBasis cubeBasis.dualBasis
    (exteriorMap 3 T).dualMap ξ
  rw [cubeDualMap_toMatrix] at h
  simpa only [cubeDualCoordinates, Module.Basis.equivFun_apply] using h.symm

/-! ## The three actual lattice monodromy actions -/

theorem squareCoordinates_A₁ (x : latticeExterior 2) :
    squareCoordinates (exteriorMap 2 A₁ x) = squareA₁ *ᵥ squareCoordinates x :=
  squareCoordinates_map A₁ x

theorem squareCoordinates_A₂ (x : latticeExterior 2) :
    squareCoordinates (exteriorMap 2 A₂ x) = squareA₂ *ᵥ squareCoordinates x :=
  squareCoordinates_map A₂ x

theorem squareCoordinates_M₀ (x : latticeExterior 2) :
    squareCoordinates (exteriorMap 2 M₀ x) = squareM₀ *ᵥ squareCoordinates x :=
  squareCoordinates_map M₀ x

theorem cubeCoordinates_A₁ (x : latticeExterior 3) :
    cubeCoordinates (exteriorMap 3 A₁ x) = cubeA₁ *ᵥ cubeCoordinates x :=
  cubeCoordinates_map A₁ x

theorem cubeCoordinates_A₂ (x : latticeExterior 3) :
    cubeCoordinates (exteriorMap 3 A₂ x) = cubeA₂ *ᵥ cubeCoordinates x :=
  cubeCoordinates_map A₂ x

theorem cubeCoordinates_M₀ (x : latticeExterior 3) :
    cubeCoordinates (exteriorMap 3 M₀ x) = cubeM₀ *ᵥ cubeCoordinates x :=
  cubeCoordinates_map M₀ x

/-! The same coordinate theorem directly recovers all the existing `T` minor matrices. -/

theorem squareCoordinates_T₁ (x : latticeExterior 2) :
    squareCoordinates (exteriorMap 2 T₁ x) = squareT₁ *ᵥ squareCoordinates x :=
  squareCoordinates_map T₁ x

theorem squareCoordinates_T₂ (x : latticeExterior 2) :
    squareCoordinates (exteriorMap 2 T₂ x) = squareT₂ *ᵥ squareCoordinates x :=
  squareCoordinates_map T₂ x

theorem squareCoordinates_T₀ (x : latticeExterior 2) :
    squareCoordinates (exteriorMap 2 T₀ x) = squareT₀ *ᵥ squareCoordinates x :=
  squareCoordinates_map T₀ x

theorem cubeCoordinates_T₁ (x : latticeExterior 3) :
    cubeCoordinates (exteriorMap 3 T₁ x) = cubeT₁ *ᵥ cubeCoordinates x :=
  cubeCoordinates_map T₁ x

theorem cubeCoordinates_T₂ (x : latticeExterior 3) :
    cubeCoordinates (exteriorMap 3 T₂ x) = cubeT₂ *ᵥ cubeCoordinates x :=
  cubeCoordinates_map T₂ x

theorem cubeCoordinates_T₀ (x : latticeExterior 3) :
    cubeCoordinates (exteriorMap 3 T₀ x) = cubeT₀ *ᵥ cubeCoordinates x :=
  cubeCoordinates_map T₀ x

end Wikipedia.HopfProblem.PeriodTorusHigherHomologyExterior
