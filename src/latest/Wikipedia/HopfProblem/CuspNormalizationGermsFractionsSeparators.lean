import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Separating elements and non-zero-divisors in a product of branch domains

Suppose a subring of a product contains, for each coordinate, an element
that is nonzero there and zero at every other coordinate. An element of
the subring is then a non-zero-divisor precisely when all its coordinates
are nonzero. No finiteness of the index type is needed for this criterion.

For a finite product, weighted sums of the separating elements isolate
the prescribed diagonal coefficients and provide non-zero-divisors when
those coefficients are nonzero.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.CuspNormalization.GermsFractions

variable {I : Type*} {B : I → Type*} [∀ i, CommRing (B i)]

/-- Elements of the actual subring separating the different coordinates. -/
structure SeparatingFamily (A : Subring (∀ i, B i)) where
  element : I → A
  diagonal_ne_zero : ∀ i, (element i : ∀ j, B j) i ≠ 0
  off_diagonal : ∀ i j, j ≠ i → (element i : ∀ k, B k) j = 0

namespace SeparatingFamily

variable {A : Subring (∀ i, B i)} (s : SeparatingFamily A)

theorem element_ne_zero (i : I) : s.element i ≠ 0 := by
  intro hi
  apply s.diagonal_ne_zero i
  exact congrArg (fun x : A => (x : ∀ j, B j) i) hi

include s in
/-- Separators detect every zero coordinate of a non-zero-divisor; the
converse follows by cancellation in each branch domain. -/
theorem mem_nonZeroDivisors_iff [∀ i, IsDomain (B i)] (x : A) :
    x ∈ nonZeroDivisors A ↔ ∀ i, (x : ∀ j, B j) i ≠ 0 := by
  constructor
  · intro hx i hxi
    have hprod : x * s.element i = 0 := by
      apply Subtype.ext
      funext j
      change (x : ∀ k, B k) j * (s.element i : ∀ k, B k) j = 0
      by_cases hji : j = i
      · subst j
        rw [hxi, zero_mul]
      · rw [s.off_diagonal i j hji, mul_zero]
    exact s.element_ne_zero i ((mem_nonZeroDivisors_iff_left.mp hx) _ hprod)
  · intro hx
    apply mem_nonZeroDivisors_iff_left.mpr
    intro y hy
    apply Subtype.ext
    funext i
    have hi := congrArg (fun z : A => (z : ∀ j, B j) i) hy
    change (x : ∀ j, B j) i * (y : ∀ j, B j) i = 0 at hi
    change (y : ∀ j, B j) i = 0
    exact (mul_eq_zero.mp hi).resolve_left (hx i)

variable [Fintype I]

/-- A finite weighted sum formed inside the original subring. -/
def weightedSum (c : I → A) : A := ∑ i, s.element i * c i

@[simp] theorem weightedSum_apply (c : I → A) (i : I) :
    (s.weightedSum c : ∀ j, B j) i =
      (s.element i : ∀ j, B j) i * (c i : ∀ j, B j) i := by
  classical
  let e : A →+* B i := (Pi.evalRingHom B i).comp A.subtype
  change e (∑ j, s.element j * c j) = e (s.element i) * e (c i)
  rw [map_sum]
  calc
    ∑ j, e (s.element j * c j) = e (s.element i * c i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        change (s.element j : ∀ k, B k) i * (c j : ∀ k, B k) i = 0
        rw [s.off_diagonal j i hji.symm, zero_mul]
      · simp
    _ = e (s.element i) * e (c i) := map_mul e _ _

theorem weightedSum_mem_nonZeroDivisors [∀ i, IsDomain (B i)]
    (c : I → A) (hc : ∀ i, (c i : ∀ j, B j) i ≠ 0) :
    s.weightedSum c ∈ nonZeroDivisors A := by
  apply (s.mem_nonZeroDivisors_iff _).mpr
  intro i
  rw [s.weightedSum_apply]
  exact mul_ne_zero (s.diagonal_ne_zero i) (hc i)

end SeparatingFamily

end Wikipedia.HopfProblem.CuspNormalization.GermsFractions
