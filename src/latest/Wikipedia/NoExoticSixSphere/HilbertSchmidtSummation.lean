import Wikipedia.NoExoticSixSphere.HilbertSchmidt
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite summation by parts for the Hilbert--Schmidt pairing

The endpoint terms vanish when the vertex field is zero at both endpoints.
-/

namespace NoExoticSixSphere.HilbertSchmidt

open GLOrthonormalization

variable {n m : ℕ}

theorem innerForm_zero_right (A : Vector n →L[ℝ] Vector n) : innerForm A 0 = 0 := by
  simp [innerForm]

theorem innerForm_sub_left (A B C : Vector n →L[ℝ] Vector n) :
    innerForm (A - B) C = innerForm A C - innerForm B C := by
  simp [innerForm, inner_sub_left, Finset.sum_sub_distrib]

theorem sum_pairing_difference
    (V : Fin (m + 1) → Vector n →L[ℝ] Vector n)
    (W : Fin (m + 2) → Vector n →L[ℝ] Vector n)
    (hzero : W 0 = 0) (hlast : W (Fin.last (m + 1)) = 0) :
    (∑ i : Fin (m + 1), (innerForm (V i) (W i.succ) - innerForm (V i) (W i.castSucc))) =
      ∑ j : Fin m, innerForm (V j.castSucc - V j.succ) (W j.castSucc.succ) := by
  rw [Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc (fun i ↦ innerForm (V i) (W i.succ)),
    Fin.sum_univ_succ (fun i ↦ innerForm (V i) (W i.castSucc))]
  simp only [Fin.succ_castSucc, Fin.succ_last, Fin.castSucc_zero,
    hlast, hzero, innerForm_zero_right, add_zero, zero_add,
    innerForm_sub_left, Finset.sum_sub_distrib]

end NoExoticSixSphere.HilbertSchmidt
