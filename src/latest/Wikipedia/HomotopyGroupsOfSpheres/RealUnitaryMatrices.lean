import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryCongruence
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Star.Unitary

/-! # Real orthogonal matrices inside the complex unitary group -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.RealUnitaryMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

def complexification : Matrix N N ℝ →ₐ[ℝ] Matrix N N ℂ := (Algebra.ofId ℝ ℂ).mapMatrix

theorem complexification_injective :
    Function.Injective (complexification : Matrix N N ℝ → Matrix N N ℂ) := by
  intro A B h
  apply Matrix.ext
  intro r s
  exact Complex.ofReal_injective (congrArg (fun C ↦ C r s) h)

theorem complexification_transpose (A : Matrix N N ℝ) :
    complexification A.transpose = (complexification A).transpose := rfl

omit [Fintype N] [DecidableEq N] in
theorem star_eq_transpose (A : Matrix N N ℝ) : star A = A.transpose := by
  apply Matrix.ext
  intro r s
  exact star_trivial (A s r)

theorem complexification_star (A : Matrix N N ℝ) :
    complexification (star A) = star (complexification A) := by
  apply Matrix.ext
  intro r s
  change ((star (A s r) : ℝ) : ℂ) = star ((A s r : ℝ) : ℂ)
  simp

theorem continuous_complexification :
    Continuous (complexification : Matrix N N ℝ → Matrix N N ℂ) := by
  apply continuous_matrix
  intro r s
  exact Complex.continuous_ofReal.comp ((continuous_apply s).comp (continuous_apply r))

def toComplex (U : unitary (Matrix N N ℝ)) : unitary (Matrix N N ℂ) :=
  ⟨complexification U.val, by
    constructor
    · rw [← complexification_star, ← map_mul, Unitary.star_mul_self_of_mem U.property, map_one]
    · rw [← complexification_star, ← map_mul, Unitary.mul_star_self_of_mem U.property, map_one]⟩

theorem continuous_toComplex :
    Continuous (toComplex : unitary (Matrix N N ℝ) → unitary (Matrix N N ℂ)) :=
  (continuous_complexification.comp continuous_subtype_val).subtype_mk _

theorem toComplex_mul_transpose (U : unitary (Matrix N N ℝ)) :
    (toComplex U).val * (toComplex U).val.transpose = 1 := by
  change complexification U.val * (complexification U.val).transpose = 1
  rw [← complexification_transpose, ← star_eq_transpose, ← map_mul,
    Unitary.mul_star_self_of_mem U.property, map_one]

theorem toComplex_det_square (U : unitary (Matrix N N ℝ)) : (toComplex U).val.det ^ 2 = 1 := by
  have h := congrArg Matrix.det (toComplex_mul_transpose U)
  simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, pow_two] using h

open scoped Matrix.Norms.Elementwise in
theorem isCompact_real_unitary : IsCompact (unitary (Matrix N N ℝ) : Set (Matrix N N ℝ)) := by
  have hclosed : IsClosed (unitary (Matrix N N ℝ) : Set (Matrix N N ℝ)) := by
    have hm : Continuous (fun U : Matrix N N ℝ ↦ star U * U) :=
      continuous_star.matrix_mul continuous_id
    have hm' : Continuous (fun U : Matrix N N ℝ ↦ U * star U) :=
      continuous_id.matrix_mul continuous_star
    exact (isClosed_eq hm continuous_const).inter (isClosed_eq hm' continuous_const)
  apply (isCompact_closedBall (0 : Matrix N N ℝ) 1).of_isClosed_subset hclosed
  intro U hU
  simpa only [Metric.mem_closedBall, dist_zero_right] using entrywise_sup_norm_bound_of_unitary hU

instance realUnitary_compactSpace : CompactSpace (unitary (Matrix N N ℝ)) :=
  isCompact_iff_compactSpace.mp isCompact_real_unitary

end Wikipedia.HomotopyGroupsOfSpheres.RealUnitaryMatrices
