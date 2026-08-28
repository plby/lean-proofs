import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Coefficients of the actual exterior-power map

In the basis indexed by increasing subsets of the standard basis, coefficients
of `exteriorPower.map` are the corresponding matrix minors. This is a statement
about the actual exterior-power module and its canonical basis, not a definition
of the action by a matrix and not an assertion about singular homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomologyExterior

/-- The actual exterior-power basis indexed by subsets in increasing order. -/
def standardExteriorBasis (m n : ℕ) :
    Module.Basis (Set.powersetCard (Fin m) n) ℤ (⋀[ℤ]^n (Fin m → ℤ)) :=
  (Pi.basisFun ℤ (Fin m)).exteriorPower n

/-- The row-`s`, column-`t` coefficient of the actual exterior-power map is the
minor whose rows and columns are the increasing enumerations of `s` and `t`. -/
theorem standardExterior_map_coefficient (m n : ℕ) (A : Matrix (Fin m) (Fin m) ℤ)
    (s t : Set.powersetCard (Fin m) n) :
    (standardExteriorBasis m n).repr
        (exteriorPower.map n A.mulVecLin (standardExteriorBasis m n t)) s =
      (A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
        (Set.powersetCard.ofFinEmbEquiv.symm t)).det := by
  unfold standardExteriorBasis
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti,
    exteriorPower.ιMultiDual_apply_ιMulti]
  have hmatrix :
      (Matrix.of fun i j =>
        (Pi.basisFun ℤ (Fin m)).coord (Set.powersetCard.ofFinEmbEquiv.symm s j)
          ((A.mulVecLin ∘
            ((Pi.basisFun ℤ (Fin m)) ∘ Set.powersetCard.ofFinEmbEquiv.symm t)) i)) =
        (A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
          (Set.powersetCard.ofFinEmbEquiv.symm t)).transpose := by
    ext i j
    simp only [Matrix.of_apply, Module.Basis.coord_apply, Pi.basisFun_repr,
      Function.comp_apply, Pi.basisFun_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply, Matrix.submatrix_apply]
  rw [hmatrix, Matrix.det_transpose]

end Wikipedia.HopfProblem.PeriodTorusHigherHomologyExterior
