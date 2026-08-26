import ErdosProblems.Erdos1188.SparseParametricLower

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary quadratic lower bound for the sparse profile exponent
-/

namespace Erdos1188

open scoped BigOperators

/-- Adding one late coordinate adds its complete nonzero-residue count to the
sparse exponent. -/
theorem sparsePrimeExponent_succ {m : ℕ} (hm : sparseSeed ≤ m) :
    sparsePrimeExponent (m + 1) = sparsePrimeExponent m + (nthPrime m - 1) := by
  unfold sparsePrimeExponent
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp [hm]

/-- A binomial (triangular-number) lower bound for the exponent. -/
theorem choose_two_le_sparsePrimeExponent {m : ℕ} (hm : sparseSeed ≤ m) :
    (m - sparseSeed).choose 2 ≤ sparsePrimeExponent m := by
  induction m, hm using Nat.le_induction with
  | base =>
      have hempty :
          (Finset.univ.filter fun i : Fin sparseSeed => sparseSeed ≤ i.val) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i _ hi
        omega
      simp [sparsePrimeExponent, hempty]
  | succ m hm ih =>
      rw [sparsePrimeExponent_succ hm]
      have hp := index_add_two_le_nthPrime m
      have ht : m - sparseSeed ≤ nthPrime m - 1 := by omega
      have hsub : m + 1 - sparseSeed = (m - sparseSeed) + 1 := by omega
      rw [hsub, Nat.choose_succ_succ, Nat.choose_one_right]
      calc
        m - sparseSeed + (m - sparseSeed).choose 2 ≤
            (nthPrime m - 1) + sparsePrimeExponent m := Nat.add_le_add ht ih
        _ = sparsePrimeExponent m + (nthPrime m - 1) := Nat.add_comm _ _

/-- The exponent is at least a triangular number, hence quadratic in the
number of late coordinates. -/
theorem triangular_le_sparsePrimeExponent {m : ℕ} (hm : sparseSeed ≤ m) :
    (m - sparseSeed) * (m - sparseSeed - 1) / 2 ≤ sparsePrimeExponent m := by
  rw [← Nat.choose_two_right]
  exact choose_two_le_sparsePrimeExponent hm

/-- Strengthened finite parametric lower bound with a simple explicit
quadratic exponent. -/
theorem explicit_sparse_quadratic_parametric_lower (m : ℕ)
    (hm : sparseSeed ≤ m) :
    2 ^ ((m - sparseSeed) * (m - sparseSeed - 1) / 2) ≤
      coveringCount (sparsePrimeCutoff m) := by
  exact (Nat.pow_le_pow_right (by decide) (triangular_le_sparsePrimeExponent hm)).trans
    (explicit_sparse_parametric_lower m hm)

end Erdos1188
