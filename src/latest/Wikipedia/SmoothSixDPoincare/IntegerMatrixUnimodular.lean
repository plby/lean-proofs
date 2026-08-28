import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Group.Int.Units

/-!
# A bijective integer matrix is square, and a surjective square one is unimodular

The size equality is finite-rank invariance of the actual induced linear
equivalence. The determinant conclusion uses the actual matrix inverse
provided by surjectivity, not an assigned determinant or rank invariant.
-/

noncomputable section

namespace Wikipedia.SmoothSixDPoincare.HomologyTransport

theorem matrix_sizes_eq_of_bijective {R : Type*} [CommRing R] [Nontrivial R]
    [StrongRankCondition R] {r c : ℕ} (A : Matrix (Fin r) (Fin c) R)
    (hA : Function.Bijective A.mulVec) : c = r := by
  let e := LinearEquiv.ofBijective A.mulVecLin hA
  simpa using e.finrank_eq

theorem integer_matrix_det_natAbs_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : Function.Surjective A.mulVec) : A.det.natAbs = 1 :=
  Int.isUnit_iff_natAbs_eq.mp
    ((Matrix.isUnit_iff_isUnit_det A).mp (Matrix.mulVec_surjective_iff_isUnit.mp hA))

end Wikipedia.SmoothSixDPoincare.HomologyTransport
