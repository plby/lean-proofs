import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessEulerAlgebraSum
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessAlgebraRank

/-!
# Finite rational Euler additivity from a genuine long exact sequence

Rank-nullity at the three positions of a long exact sequence expresses the
dimensions in terms of the actual images of its maps.  Alternating these
identities cancels all internal boundary terms.  The last boundary term
vanishes when its actual target module is zero.

No coordinate description of a boundary map or dimension of an unknown
homology group is an input.
-/

noncomputable section

open Function Module
open scoped BigOperators

namespace Wikipedia.HopfProblem.ThreefoldHomologyFinitenessEulerAlgebra

open ThreefoldHomologyFinitenessAlgebra

/-- The integral alternating sum of rational dimensions through degree `N`. -/
def rationalEulerThrough (V : ℕ → Type*) [∀ n, AddCommGroup (V n)]
    [∀ n, Module ℚ (V n)] (N : ℕ) : ℤ :=
  alternatingSumThrough (fun n => (finrank ℚ (V n) : ℤ)) N

@[simp] theorem rationalEulerThrough_eq (V : ℕ → Type*)
    [∀ n, AddCommGroup (V n)] [∀ n, Module ℚ (V n)] (N : ℕ) :
    rationalEulerThrough V N =
      ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (finrank ℚ (V n) : ℤ) := rfl

section ExactSequence

variable {A B H : ℕ → Type*}
variable [∀ n, AddCommGroup (A n)] [∀ n, Module ℚ (A n)]
variable [∀ n, AddCommGroup (B n)] [∀ n, Module ℚ (B n)]
variable [∀ n, AddCommGroup (H n)] [∀ n, Module ℚ (H n)]
variable [finiteA : ∀ n, Module.Finite ℚ (A n)]
variable [finiteB : ∀ n, Module.Finite ℚ (B n)]
variable [finiteH : ∀ n, Module.Finite ℚ (H n)]

variable (f : ∀ n, A n →ₗ[ℚ] B n) (g : ∀ n, B n →ₗ[ℚ] H n)
variable (d : ∀ n, H (n + 1) →ₗ[ℚ] A n)
variable (hfg : ∀ n, Exact (f n) (g n))
variable (hgd : ∀ n, Exact (g (n + 1)) (d n))
variable (hdf : ∀ n, Exact (d n) (f n))
variable (hgzero : Surjective (g 0))

include f g d hfg hgd hdf hgzero finiteA finiteB finiteH

/-- Euler additivity for the actual exact sequence, with the final image
dimension retained rather than silently discarded. -/
theorem rational_euler_through_with_boundary (N : ℕ) :
    rationalEulerThrough H N = rationalEulerThrough B N - rationalEulerThrough A N +
      (-1 : ℤ) ^ N * (finrank ℚ (LinearMap.range (d N)) : ℤ) := by
  refine alternatingSumThrough_eq_sub_add_last
    (fun n => (finrank ℚ (A n) : ℤ))
    (fun n => (finrank ℚ (B n) : ℤ))
    (fun n => (finrank ℚ (H n) : ℤ))
    (fun n => (finrank ℚ (LinearMap.range (d n)) : ℤ)) ?_ ?_ N
  · have hA := rational_finrank_eq_add_ranges_of_exact (d 0) (f 0) (hdf 0)
    have hB := rational_finrank_eq_add_ranges_of_exact (f 0) (g 0) (hfg 0)
    have hG : finrank ℚ (LinearMap.range (g 0)) = finrank ℚ (H 0) := by
      rw [LinearMap.range_eq_top.mpr hgzero, finrank_top]
    omega
  · intro n
    have hA := rational_finrank_eq_add_ranges_of_exact
      (d (n + 1)) (f (n + 1)) (hdf (n + 1))
    have hB := rational_finrank_eq_add_ranges_of_exact
      (f (n + 1)) (g (n + 1)) (hfg (n + 1))
    have hH := rational_finrank_eq_add_ranges_of_exact
      (g (n + 1)) (d n) (hgd n)
    omega

/-- A zero top overlap module kills the last actual boundary term, giving
the finite Euler identity without computing any boundary matrix. -/
theorem rational_euler_through_of_exact (N : ℕ) (hTop : Subsingleton (A N)) :
    rationalEulerThrough H N = rationalEulerThrough B N - rationalEulerThrough A N := by
  rw [rational_euler_through_with_boundary f g d hfg hgd hdf hgzero N]
  have : Subsingleton (A N) := hTop
  have hlast : finrank ℚ (LinearMap.range (d N)) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [hlast, Nat.cast_zero, mul_zero, add_zero]

/-- The same genuine long-exact-sequence Euler identity as literal finite sums. -/
theorem rational_finrank_euler_of_exact_sequence (N : ℕ) (hTop : Subsingleton (A N)) :
    (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (finrank ℚ (H n) : ℤ)) =
      (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (finrank ℚ (B n) : ℤ)) -
        (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (finrank ℚ (A n) : ℤ)) :=
  rational_euler_through_of_exact f g d hfg hgd hdf hgzero N hTop

end ExactSequence

end Wikipedia.HopfProblem.ThreefoldHomologyFinitenessEulerAlgebra
