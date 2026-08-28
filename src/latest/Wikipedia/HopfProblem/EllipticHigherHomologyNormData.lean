import Wikipedia.HopfProblem.EllipticHigherHomologyAlgebra
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.RingTheory.Ideal.Operations

/-!
# The finite norm matrices of the actual elliptic fibre actions

The sums of all powers of the order-three and order-four matrices have
rank one over the integers.  Their nonzero primitive factors have index
one and two respectively.  These are algebraic norm operators only.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

/-- The integral image index of the norms in exterior degrees one and two. -/
def fibreNormIndex : Kind → ℕ
  | .three => 1
  | .four => 2

@[simp] theorem fibreNormIndex_three : fibreNormIndex .three = 1 := rfl
@[simp] theorem fibreNormIndex_four : fibreNormIndex .four = 2 := rfl

theorem fibreNormIndex_pos (j : Kind) : 0 < fibreNormIndex j := by
  cases j <;> decide

theorem fibreNormIndex_int_ne_zero (j : Kind) : (fibreNormIndex j : ℤ) ≠ 0 := by
  exact_mod_cast (fibreNormIndex_pos j).ne'

/-- The finite degree-one norm of the actual restricted monodromy. -/
def fibreNormMatrix (j : Kind) : FibreMatrix :=
  ∑ k ∈ Finset.range j.order, (fibreMatrix j) ^ k

/-- The finite degree-two norm of the actual exterior-square monodromy. -/
def fibreSquareNormMatrix (j : Kind) : FibreMatrix :=
  ∑ k ∈ Finset.range j.order, (fibreSquareMatrix j) ^ k

@[simp] theorem fibreNormMatrix_three :
    fibreNormMatrix .three = !![0, 0, 0; 0, 0, 0; 2, 1, 3] := by
  decide

@[simp] theorem fibreNormMatrix_four :
    fibreNormMatrix .four = !![0, 0, 0; 0, 0, 0; 2, 2, 4] := by
  decide

@[simp] theorem fibreSquareNormMatrix_three :
    fibreSquareNormMatrix .three = !![3, 0, 0; -1, 0, 0; 2, 0, 0] := by
  decide

@[simp] theorem fibreSquareNormMatrix_four :
    fibreSquareNormMatrix .four = !![4, 0, 0; -2, 0, 0; 2, 0, 0] := by
  decide

theorem fibreDifference_mul_normMatrix (j : Kind) :
    (fibreMatrix j - 1) * fibreNormMatrix j = 0 := by
  cases j <;> decide

theorem fibreNormMatrix_mul_difference (j : Kind) :
    fibreNormMatrix j * (fibreMatrix j - 1) = 0 := by
  cases j <;> decide

theorem fibreSquareDifference_mul_normMatrix (j : Kind) :
    (fibreSquareMatrix j - 1) * fibreSquareNormMatrix j = 0 := by
  cases j <;> decide

theorem fibreSquareNormMatrix_mul_difference (j : Kind) :
    fibreSquareNormMatrix j * (fibreSquareMatrix j - 1) = 0 := by
  cases j <;> decide

/-- The exact additive index of an integer principal submodule. -/
theorem int_span_singleton_index (a : ℤ) :
    (Submodule.span ℤ {a}).toAddSubgroup.index = a.natAbs := by
  rw [Submodule.span_singleton_toAddSubgroup_eq_zmultiples, Int.index_zmultiples]

/-- Scaling a surjective integer coordinate gives exactly the principal
submodule, without an additional divisibility condition. -/
theorem int_scaled_coordinate_range {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : M →ₗ[ℤ] ℤ) (hf : Function.Surjective f) (a : ℤ) :
    LinearMap.range (a • f) = Submodule.span ℤ {a} := by
  ext z
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨f x, by simp [mul_comm]⟩
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := hf k
    refine ⟨x, ?_⟩
    simpa [hx, mul_comm] using hk

end Wikipedia.HopfProblem.Elliptic.HigherHomology
