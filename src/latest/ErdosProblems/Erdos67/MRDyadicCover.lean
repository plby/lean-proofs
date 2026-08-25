import ErdosProblems.Erdos67.MRLemma14

/-!
# Two-dyadic cover of the short-interval coefficient support

For starting points in `(X,2X]` and lengths `H ≤ X`, every sampled
coefficient lies in `(X,3X]`.  The two restrictions `(X,2X]` and
`(2X,4X]` therefore recover the short sum exactly.  This removes a support
bookkeeping gap when applying the dyadic Lemma-14 polynomial.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67

noncomputable section

/-- The two adjacent dyadic restrictions recover a coefficient at every
integer in `(X,3X]`. -/
theorem dyadicRestrictedCoefficient_add_next_eq
    (a : ℕ → ℂ) {X m : ℕ} (hlo : X < m) (hhi : m ≤ 3 * X) :
    dyadicRestrictedCoefficient (Finset.Ioc X (2 * X)) a X m +
        dyadicRestrictedCoefficient
          (Finset.Ioc (2 * X) (4 * X)) a (2 * X) m =
      a m := by
  have h4 : m ≤ 4 * X := by omega
  unfold dyadicRestrictedCoefficient dyadicRestrictedSupport
  by_cases hm : m ≤ 2 * X
  · have hfirst : m ∈ Finset.Ioc X (2 * X) :=
      Finset.mem_Ioc.mpr ⟨hlo, hm⟩
    have hsecond : m ∉ Finset.Ioc (2 * X) (4 * X) := by
      simp only [Finset.mem_Ioc, not_and_or]
      exact Or.inl (not_lt_of_ge hm)
    simp [hfirst, hsecond]
  · have hfirst : m ∉ Finset.Ioc X (2 * X) := by
      simp only [Finset.mem_Ioc, not_and_or]
      exact Or.inr hm
    have hsecond : m ∈ Finset.Ioc (2 * X) (4 * X) :=
      Finset.mem_Ioc.mpr ⟨lt_of_not_ge hm, h4⟩
    have hscale : 2 * (2 * X) = 4 * X := by omega
    simp [hfirst, hsecond, hscale]

/-- Exact short-sum decomposition into the two adjacent dyadic pieces. -/
theorem sum_Icc_eq_two_dyadicRestricted
    (a : ℕ → ℂ) {X H n : ℕ}
    (hHX : H ≤ X) (hn : n ∈ Finset.Ioc X (2 * X)) :
    (∑ j ∈ Finset.Icc 1 H, a (n + j)) =
      (∑ j ∈ Finset.Icc 1 H,
        dyadicRestrictedCoefficient (Finset.Ioc X (2 * X)) a X (n + j)) +
      ∑ j ∈ Finset.Icc 1 H,
        dyadicRestrictedCoefficient
          (Finset.Ioc (2 * X) (4 * X)) a (2 * X) (n + j) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dyadicRestrictedCoefficient_add_next_eq]
  · have hnlo := (Finset.mem_Ioc.mp hn).1
    omega
  · have hnhi := (Finset.mem_Ioc.mp hn).2
    have hjhi := (Finset.mem_Icc.mp hj).2
    omega

/-- The unrestricted short-interval square mean is at most twice the sum
of the square means of the two adjacent dyadic restrictions. -/
theorem uncenteredShortIntervalMeanSquare_le_two_dyadic
    (a : ℕ → ℂ) {X H : ℕ} (hHX : H ≤ X) :
    uncenteredShortIntervalMeanSquare a X H ≤
      2 * uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient (Finset.Ioc X (2 * X)) a X) X H +
      2 * uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient
          (Finset.Ioc (2 * X) (4 * X)) a (2 * X)) X H := by
  unfold uncenteredShortIntervalMeanSquare
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  let z : ℂ := ∑ j ∈ Finset.Icc 1 H,
    dyadicRestrictedCoefficient (Finset.Ioc X (2 * X)) a X (n + j)
  let w : ℂ := ∑ j ∈ Finset.Icc 1 H,
    dyadicRestrictedCoefficient
      (Finset.Ioc (2 * X) (4 * X)) a (2 * X) (n + j)
  rw [sum_Icc_eq_two_dyadicRestricted a hHX hn]
  change Complex.normSq (z + w) ≤
    2 * Complex.normSq z + 2 * Complex.normSq w
  simp only [Complex.normSq_eq_norm_sq]
  have htri := norm_add_le z w
  nlinarith [norm_nonneg (z + w), norm_nonneg z, norm_nonneg w,
    sq_nonneg (‖z‖ - ‖w‖)]

end

end Erdos67
