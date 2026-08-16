/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.RomanoffBlockTail
import ErdosProblems.Erdos851.RomanoffPartialSum

/-!
# Convergence of Romanoff's series

This file combines the finite Euler-product estimate with the geometric
order-block argument.  The result is the summability, with a quantitative
order tail, of

`1 / (phi(q) * ord_q(2))`

over odd squarefree moduli.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos851

open RomanoffBlockTail

noncomputable local instance instDecidableIsRomanoffModulusConvergence (q : ℕ) :
    Decidable (IsRomanoffModulus q) := Classical.propDecidable _

private theorem prefixMass_romanoffCoeff_nonneg (S : Finset ℕ) (X : ℕ) :
    0 ≤ prefixMass romanoffCoeff twoOrder S X := by
  unfold prefixMass
  exact Finset.sum_nonneg fun q _ ↦ romanoffCoeff_nonneg q

/-- A finite prefix of the Romanoff coefficients is dominated by the full
order-product Euler product. -/
theorem prefixMass_romanoffCoeff_le_product (S : Finset ℕ) (X : ℕ) :
    prefixMass romanoffCoeff twoOrder S X ≤
      ∏ p ∈ (romanoffOrderProduct X).primeFactors,
        (p : ℝ) / ((p : ℝ) - 1) := by
  classical
  let U := S.filter fun q ↦ twoOrder q ≤ X
  let T := U.filter IsRomanoffModulus
  have hsumUT :
      ∑ q ∈ U, romanoffCoeff q = ∑ q ∈ T, romanoffCoeff q := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hqU hqT
    apply romanoffCoeff_eq_zero_of_not_modulus
    intro hq
    exact hqT (Finset.mem_filter.mpr ⟨hqU, hq⟩)
  have hTsub : T ⊆ romanoffModuliUpToOrder X := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqU := Finset.mem_filter.mp hq'.1
    exact mem_romanoffModuliUpToOrder_iff.mpr ⟨hq'.2, hqU.2⟩
  calc
    prefixMass romanoffCoeff twoOrder S X =
        ∑ q ∈ U, romanoffCoeff q := by rfl
    _ = ∑ q ∈ T, romanoffCoeff q := hsumUT
    _ ≤ ∑ q ∈ romanoffModuliUpToOrder X, romanoffCoeff q := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hTsub
        (fun q _ _ ↦ romanoffCoeff_nonneg q)
    _ ≤ ∏ p ∈ (romanoffOrderProduct X).primeFactors,
          (p : ℝ) / ((p : ℝ) - 1) :=
      sum_romanoffCoeff_moduli_le_product X

/-- The cumulative Romanoff coefficient has the fifth-moment bound needed
for geometric order blocks. -/
theorem prefixMass_romanoffCoeff_fifth_le (S : Finset ℕ) (X : ℕ) :
    (prefixMass romanoffCoeff twoOrder S X) ^ 5 ≤
      8 * (X : ℝ) ^ 4 := by
  by_cases hX : X = 0
  · subst X
    have hzero : prefixMass romanoffCoeff twoOrder S 0 = 0 := by
      unfold prefixMass
      apply Finset.sum_eq_zero
      intro q hq
      have hord := (Finset.mem_filter.mp hq).2
      by_cases hmod : IsRomanoffModulus q
      · have hpos := twoOrder_pos hmod.2
        omega
      · exact romanoffCoeff_eq_zero_of_not_modulus hmod
    simp [hzero]
  have hXpos : 0 < X := Nat.pos_of_ne_zero hX
  let P := (romanoffOrderProduct X).primeFactors
  have hprefix := prefixMass_romanoffCoeff_le_product S X
  have hprefixNonneg := prefixMass_romanoffCoeff_nonneg S X
  by_cases hP : P.Nonempty
  · have hpow :
        (prefixMass romanoffCoeff twoOrder S X) ^ 5 ≤
          (∏ p ∈ P, (p : ℝ) / ((p : ℝ) - 1)) ^ 5 :=
      pow_le_pow_left₀ hprefixNonneg hprefix 5
    calc
      (prefixMass romanoffCoeff twoOrder S X) ^ 5 ≤
          (∏ p ∈ P, (p : ℝ) / ((p : ℝ) - 1)) ^ 5 := hpow
      _ ≤ 8 * (((X ^ 2 : ℕ) : ℝ) ^ 2) := by
        exact romanoffOrderProduct_eulerProduct_fifth_le_sq X hP
      _ = 8 * (X : ℝ) ^ 4 := by
        norm_num [Nat.cast_pow]
        ring
  · have hPempty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    have hprefixOne : prefixMass romanoffCoeff twoOrder S X ≤ 1 := by
      simpa [P, hPempty] using hprefix
    have hpow : (prefixMass romanoffCoeff twoOrder S X) ^ 5 ≤ (1 : ℝ) ^ 5 :=
      pow_le_pow_left₀ hprefixNonneg hprefixOne 5
    have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hXpos
    have hXpow : (1 : ℝ) ≤ (X : ℝ) ^ 4 := one_le_pow₀ hXR
    calc
      (prefixMass romanoffCoeff twoOrder S X) ^ 5 ≤ 1 := by simpa using hpow
      _ ≤ 8 * (X : ℝ) ^ 4 := by nlinarith

private theorem twoOrder_pos_of_romanoffCoeff_ne_zero (q : ℕ)
    (hq : romanoffCoeff q ≠ 0) : 0 < twoOrder q := by
  apply twoOrder_pos
  by_contra hodd
  have hmod : ¬ IsRomanoffModulus q := fun hm ↦ hodd hm.2
  exact hq (romanoffCoeff_eq_zero_of_not_modulus hmod)

/-- Romanoff's reciprocal-totient multiplicative-order series converges. -/
theorem summable_romanoffTerm : Summable romanoffTerm := by
  change Summable (fun q ↦ romanoffCoeff q / (twoOrder q : ℝ))
  exact summable_weighted_of_fifthMoment romanoffCoeff_nonneg
    twoOrder_pos_of_romanoffCoeff_ne_zero prefixMass_romanoffCoeff_fifth_le

/-- Quantitative order tail for Romanoff's series. -/
theorem romanoff_orderTail_tsum_le (J : ℕ) :
    (∑' q : ℕ, if 32 ^ J ≤ twoOrder q then romanoffTerm q else 0) ≤
      64 * (1 / 2 : ℝ) ^ J := by
  apply Real.tsum_le_of_sum_le
  · exact fun q ↦ by
      split_ifs
      · exact romanoffTerm_nonneg q
      · exact le_rfl
  · intro S
    let T := S.filter fun q ↦ 32 ^ J ≤ twoOrder q
    calc
      ∑ q ∈ S, (if 32 ^ J ≤ twoOrder q then romanoffTerm q else 0) =
          ∑ q ∈ T, romanoffCoeff q / (twoOrder q : ℝ) := by
        change (∑ q ∈ S,
          if 32 ^ J ≤ twoOrder q then
            romanoffCoeff q / (twoOrder q : ℝ) else 0) =
          ∑ q ∈ S.filter (fun q ↦ 32 ^ J ≤ twoOrder q),
            romanoffCoeff q / (twoOrder q : ℝ)
        rw [Finset.sum_filter]
      _ ≤ 64 * (1 / 2 : ℝ) ^ J := by
        apply sum_weighted_le_tail romanoffCoeff_nonneg
          twoOrder_pos_of_romanoffCoeff_ne_zero
          prefixMass_romanoffCoeff_fifth_le T J
        intro q hq _
        exact (Finset.mem_filter.mp hq).2

/-- The quantitative order tails tend to zero. -/
theorem romanoff_orderTail_tendsto_zero :
    Tendsto
      (fun J : ℕ ↦
        ∑' q : ℕ, if 32 ^ J ≤ twoOrder q then romanoffTerm q else 0)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro J
    exact tsum_nonneg fun q ↦ by
      split_ifs
      · exact romanoffTerm_nonneg q
      · exact le_rfl
  · exact romanoff_orderTail_tsum_le
  · simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 64

end Erdos851
