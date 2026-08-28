import Wikipedia.HopfProblem.AnalyticGermsFactorialNewton

/-!
# Finite multisets of actual zeros with multiplicity

This is the explicit bookkeeping connecting the weighted argument principle
to Newton's polynomial reconstruction.  Multiplicities are retained, not
replaced by an enumeration of distinct roots.
-/

noncomputable section

open Finset Polynomial

namespace Wikipedia.HopfProblem.AnalyticGermsFactorial

/-- Repeat each point in a finite zero set according to its multiplicity. -/
def rootMultiset (t : Finset ℂ) (n : ℂ → ℕ) : Multiset ℂ :=
  t.val.bind (fun a => Multiset.replicate (n a) a)

theorem rootMultiset_card (t : Finset ℂ) (n : ℂ → ℕ) :
    (rootMultiset t n).card = ∑ a ∈ t, n a := by
  simp only [rootMultiset, Multiset.card_bind, Multiset.card_replicate,
    Finset.sum_eq_multiset_sum, Function.comp_apply]

theorem rootMultiset_powerSum (t : Finset ℂ) (n : ℂ → ℕ) (k : ℕ) :
    ((rootMultiset t n).map (fun a => a ^ k)).sum =
      ∑ a ∈ t, (n a : ℂ) * a ^ k := by
  simp only [rootMultiset, Multiset.map_bind, Multiset.map_replicate,
    Multiset.sum_bind, Multiset.sum_replicate, nsmul_eq_mul,
    Finset.sum_eq_multiset_sum]

theorem rootMultiset_prod_X_sub_C (t : Finset ℂ) (n : ℂ → ℕ) :
    ((rootMultiset t n).map (fun a => (X - C a : ℂ[X]))).prod =
      ∏ a ∈ t, (X - C a) ^ n a := by
  simp only [rootMultiset, Multiset.map_bind, Multiset.map_replicate,
    Multiset.prod_bind, Multiset.prod_replicate, Finset.prod_eq_multiset_prod]

theorem rootMultiset_mem {t : Finset ℂ} {n : ℂ → ℕ} {a : ℂ} :
    a ∈ rootMultiset t n ↔ a ∈ t ∧ 0 < n a := by
  classical
  simp [rootMultiset, Multiset.mem_bind, Multiset.mem_replicate, and_comm,
    and_left_comm]

theorem rootMultiset_polynomial (t : Finset ℂ) (n : ℂ → ℕ) :
    Newton.polynomial (fun k => ∑ a ∈ t, (n a : ℂ) * a ^ k)
        (∑ a ∈ t, n a) = ∏ a ∈ t, (X - C a) ^ n a := by
  rw [← rootMultiset_card, ← rootMultiset_prod_X_sub_C]
  have h := Newton.polynomial_eq_multiset_prod (rootMultiset t n)
  simpa only [rootMultiset_powerSum] using h

end Wikipedia.HopfProblem.AnalyticGermsFactorial
