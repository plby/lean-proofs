import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.Abel

/-!
# Alternating-face algebra for cubical dimension reduction

Closing the first-coordinate paths changes one remaining upper facet.  Its
cyclic coordinate shift has sign `(-1)^n`; the outer face sign cancels this
second copy of the same sign.  These elementary identities isolate that
calculation from the topology.
-/

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

variable {A : Type*} [AddCommGroup A]

theorem alternatingSign_smul_involution (n : ℕ) (a : A) :
    (-1 : ℤ) ^ n • ((-1 : ℤ) ^ n • a) = a := by
  rw [smul_smul, ← mul_pow]
  simp

theorem alternatingSum_head (n : ℕ) (a : Fin (n + 2) → A) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • a i) =
      a 0 - ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • a i.succ := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ',
    neg_mul, one_mul, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- One cyclically corrected final facet supplies the missing first-coordinate faces. -/
theorem alternatingSum_dimension_reduction (n : ℕ)
    (a : Fin (n + 2) → A) (b : Fin (n + 1) → A)
    (hmid : ∀ i : Fin n, b i.castSucc = a i.castSucc.succ)
    (hlast : b (Fin.last n) = a (Fin.last (n + 1)) - (-1 : ℤ) ^ n • a 0) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • a i) =
      -(∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • b i) := by
  have htail : (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • b i) =
      (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • a i.succ) - a 0 := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [hmid, hlast, Fin.val_castSucc, Fin.val_last, Fin.succ_last,
      smul_sub, alternatingSign_smul_involution]
    abel
  rw [alternatingSum_head, htail]
  abel

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
