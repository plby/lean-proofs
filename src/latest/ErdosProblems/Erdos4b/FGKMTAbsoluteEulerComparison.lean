/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAbsoluteDenominators
import ErdosProblems.Erdos4b.FGKMTMovedPrimeMass

/-!
# Dimension-independent normalization of the absolute-kernel mean

Comparing the multivariate Euler factors directly gives a fixed factor
`exp 4`. Bounding each one-dimensional normalization separately would
instead create an unusable exponential loss in the sieve dimension.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators Topology

def roughSquareEulerCost (k M p : ℕ) : ℝ :=
  if p ∣ M then 0 else 4 * (k : ℝ) ^ 2 / (p : ℝ) ^ 2

theorem roughSquareEulerCost_nonneg (k M p : ℕ) : 0 ≤ roughSquareEulerCost k M p := by
  unfold roughSquareEulerCost
  split_ifs <;> positivity

theorem sum_roughSquareEulerCost_le {k M : ℕ} (hk : 0 < k)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ p ∈ S, roughSquareEulerCost k M p) ≤ 4 := by
  let Q := S.filter (fun p => ¬p ∣ M)
  have hrough (q : Q) : k ^ 2 < (q : ℕ) := by
    have hq := Finset.mem_filter.mp q.property
    by_contra hnot
    exact hq.2 (hsmall q (hS q hq.1) (by omega))
  have hsum := sum_labels_inv_sq_le (p := fun q : Q => (q : ℕ)) Subtype.val_injective hk hrough
  rw [Finset.sum_coe_sort Q (fun n : ℕ => 1 / (n : ℝ) ^ 2)] at hsum
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    _ = 4 * (k : ℝ) ^ 2 * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
      simp only [Q, roughSquareEulerCost, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hpM : p ∣ M <;> simp [hpM, div_eq_mul_inv]
    _ ≤ 4 * (k : ℝ) ^ 2 * (1 / (k : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 := by field_simp

theorem primeHarmonicDensity_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ 1 - 1 / (p : ℝ) := by
  apply sub_nonneg.mpr
  apply (div_le_iff₀ (show (0 : ℝ) < p by exact_mod_cast hp.pos)).mpr
  simpa only [one_mul] using (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_le)

theorem absoluteEulerFactor_le {k M j a p : ℕ} (hk : 2 ≤ k)
    (ha : 1 ≤ a) (ha2 : a ≤ 2) (hj : j ≤ k) (hp : p.Prime)
    (hrough : ¬p ∣ M → 2 * k ^ 2 < p) :
    (if p ∣ M then 1 else 1 + (j : ℝ) / absoluteSieveDenominator a k p) *
        (1 - 1 / (p : ℝ)) ^ j ≤
      (1 + roughSquareEulerCost k M p) *
        ((if p ∣ M then 1 else 1 + (j : ℝ) / ((p : ℝ) - k)) * (1 - 1 / (p : ℝ)) ^ j) := by
  by_cases hpM : p ∣ M
  · simp [hpM, roughSquareEulerCost]
  · have hr : 2 * (k : ℝ) ^ 2 < p := by exact_mod_cast hrough hpM
    have hpk : 0 < (p : ℝ) - k := by
      have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    have hbase : 0 < 1 + (j : ℝ) / ((p : ℝ) - k) :=
      add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (Nat.cast_nonneg j) hpk.le)
    have hratio := (div_le_iff₀ hbase).mp
      (absoluteDenominator_local_ratio_le (k := (k : ℝ)) (p := (p : ℝ))
        (a := (a : ℝ)) (j := (j : ℝ)) (by exact_mod_cast hk) hr
        (by exact_mod_cast ha) (by exact_mod_cast ha2) (Nat.cast_nonneg j) (by exact_mod_cast hj))
    have hdensity : 0 ≤ (1 - 1 / (p : ℝ)) ^ j := pow_nonneg (primeHarmonicDensity_nonneg hp) j
    simp only [if_neg hpM, roughSquareEulerCost] at ⊢
    simpa only [absoluteSieveDenominator, mul_assoc] using
      mul_le_mul_of_nonneg_right hratio hdensity

theorem absoluteEulerProduct_le {k M j a : ℕ} (hk : 2 ≤ k)
    (ha : 1 ≤ a) (ha2 : a ≤ 2) (hj : j ≤ k)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) (N : ℕ) :
    (∏ p ∈ N.primesBelow,
      (if p ∣ M then 1 else 1 + (j : ℝ) / absoluteSieveDenominator a k p) *
        (1 - 1 / (p : ℝ)) ^ j) ≤
      Real.exp 4 * ∏ p ∈ N.primesBelow,
        (if p ∣ M then 1 else 1 + (j : ℝ) / ((p : ℝ) - k)) * (1 - 1 / (p : ℝ)) ^ j := by
  have hrough (p : ℕ) (hp : p.Prime) (hpM : ¬p ∣ M) : 2 * k ^ 2 < p := by
    by_contra hnot
    exact hpM (hsmall p hp (by omega))
  have hfactor (p : ℕ) (hp : p.Prime) :
      0 ≤ (if p ∣ M then 1 else 1 + (j : ℝ) / ((p : ℝ) - k)) *
        (1 - 1 / (p : ℝ)) ^ j := by
    apply mul_nonneg
    · split_ifs with hpM
      · exact zero_le_one
      · have hr : 2 * (k : ℝ) ^ 2 < p := by exact_mod_cast hrough p hp hpM
        have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
        exact add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg j) (by nlinarith))
    · exact pow_nonneg (primeHarmonicDensity_nonneg hp) j
  have hcost : (∏ p ∈ N.primesBelow, (1 + roughSquareEulerCost k M p)) ≤ Real.exp 4 :=
    (Real.prod_one_add_le_exp_sum _ (roughSquareEulerCost_nonneg k M)).trans
      (Real.exp_le_exp.mpr (sum_roughSquareEulerCost_le (by omega : 0 < k) hsmall _
        (fun p hp => Nat.prime_of_mem_primesBelow hp)))
  calc
    _ ≤ ∏ p ∈ N.primesBelow, (1 + roughSquareEulerCost k M p) *
        ((if p ∣ M then 1 else 1 + (j : ℝ) / ((p : ℝ) - k)) * (1 - 1 / (p : ℝ)) ^ j) := by
      apply Finset.prod_le_prod
      · intro p hp
        apply mul_nonneg
        · split_ifs
          · exact zero_le_one
          · exact add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg j)
              (div_nonneg (sq_nonneg _) (by
                have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
                have haR : (a : ℝ) ≤ 2 := by exact_mod_cast ha2
                linarith)))
        · exact pow_nonneg (primeHarmonicDensity_nonneg (Nat.prime_of_mem_primesBelow hp)) j
      · intro p hp
        exact absoluteEulerFactor_le hk ha ha2 hj (Nat.prime_of_mem_primesBelow hp)
          (hrough p (Nat.prime_of_mem_primesBelow hp))
    _ = (∏ p ∈ N.primesBelow, (1 + roughSquareEulerCost k M p)) *
        ∏ p ∈ N.primesBelow,
          (if p ∣ M then 1 else 1 + (j : ℝ) / ((p : ℝ) - k)) * (1 - 1 / (p : ℝ)) ^ j :=
      Finset.prod_mul_distrib
    _ ≤ _ := mul_le_mul_of_nonneg_right hcost
      (Finset.prod_nonneg fun p hp => hfactor p (Nat.prime_of_mem_primesBelow hp))

theorem absolute_multivariateSieveConstant_le {k M j a : ℕ} (hk : 2 ≤ k) (hM : 0 < M)
    (ha : 1 ≤ a) (ha2 : a ≤ 2) (hj : j + a ≤ k + 1)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) :
    multivariateSieveConstant M (absoluteSieveDenominator a k) j ≤
      Real.exp 4 * multivariateSieveConstant M (fun p => (p : ℝ) - k) j := by
  have hchain := absoluteSieveDenominator_chain hk ha ha2 hj hsmall
  have hpos (p : ℕ) (hp : p.Prime) (hpM : ¬p ∣ M) : 0 < absoluteSieveDenominator a k p := by
    have hr : 2 * k ^ 2 < p := by
      by_contra hnot
      exact hpM (hsmall p hp (by omega))
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hb := absoluteDenominator_real_bounds (k := (k : ℝ)) (p := (p : ℝ)) (a := (a : ℝ))
      (by exact_mod_cast hk)
      (by exact_mod_cast hr) (by exact_mod_cast ha) (by exact_mod_cast ha2)
      (le_refl (0 : ℝ)) (by exact_mod_cast (show 0 + a ≤ k by omega))
    change (p : ℝ) / 2 ≤ absoluteSieveDenominator a k p + 0 ∧ _ at hb
    linarith [hb.1]
  have hlim := multivariateSieveConstant_eulerProduct (absoluteSieveDenominator a k) hpos
    (fun s hs => (harmonicCorrection_roughSieveWeight_moments (by omega : 0 < k) hM
      (fun p hp hpk => hsmall p hp (by omega)) _
      (fun p hp hpM => (hchain s hs p hp hpM).1)
      (fun p hp hpM => (hchain s hs p hp hpM).2.1)).1)
  exact le_of_tendsto_of_tendsto hlim
    ((actual_multivariateSieveConstant_eulerProduct hk hM (by omega) hsmall).const_mul (Real.exp 4))
    (Filter.Eventually.of_forall (absoluteEulerProduct_le hk ha ha2 (by omega) hsmall))

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.absoluteEulerProduct_le
#print axioms Erdos4b.FGKMT.absolute_multivariateSieveConstant_le
