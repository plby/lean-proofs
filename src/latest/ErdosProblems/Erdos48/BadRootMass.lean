/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PrimeChains

/-!
# Reciprocal mass of prefix-sparse bad roots

FLP's few-bad-moduli lemma is uniform in the upper endpoint.  This file
turns that prefix cardinal estimate into the reciprocal and weighted masses
consumed by the prime-chain closure theorem.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- The elements of `E` in the `j`-th binary logarithmic shell. -/
noncomputable def badRootLogShell (E : Finset ℕ) (j : ℕ) : Finset ℕ := by
  classical
  exact E.filter fun q ↦ Nat.log 2 q = j

theorem pairwiseDisjoint_badRootLogShell (E : Finset ℕ) (J : ℕ) :
    ((Finset.Icc 1 J : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (badRootLogShell E) := by
  classical
  intro i hi j hj hij
  change Disjoint (badRootLogShell E i) (badRootLogShell E j)
  rw [Finset.disjoint_left]
  intro q hqi hqj
  rw [badRootLogShell, Finset.mem_filter] at hqi hqj
  exact hij (hqi.2.symm.trans hqj.2)

/-- Binary logarithmic shells partition a set whose elements lie in
`[2,u]`. -/
theorem biUnion_badRootLogShell {E : Finset ℕ} {u : ℕ}
    (hE : ∀ q ∈ E, 2 ≤ q ∧ q ≤ u) :
    (Finset.Icc 1 (Nat.log 2 u)).biUnion (badRootLogShell E) = E := by
  classical
  ext q
  constructor
  · intro hq
    rw [Finset.mem_biUnion] at hq
    obtain ⟨j, hj, hqj⟩ := hq
    exact (Finset.mem_filter.mp hqj).1
  · intro hq
    have hqData := hE q hq
    have hlogPos : 1 ≤ Nat.log 2 q := Nat.log_pos (by omega) hqData.1
    have hlogLe : Nat.log 2 q ≤ Nat.log 2 u :=
      Nat.log_mono_right hqData.2
    rw [Finset.mem_biUnion]
    refine ⟨Nat.log 2 q, Finset.mem_Icc.mpr ⟨hlogPos, hlogLe⟩, ?_⟩
    rw [badRootLogShell, Finset.mem_filter]
    exact ⟨hq, rfl⟩

/-- Every reciprocal in logarithmic shell `j` is at most `2⁻ʲ`. -/
theorem sum_badRootLogShell_inv_le_card_div_pow
    (E : Finset ℕ) (j : ℕ) (hj : 1 ≤ j) :
    (∑ q ∈ badRootLogShell E j, (q : ℝ)⁻¹) ≤
      ((badRootLogShell E j).card : ℝ) / (2 : ℝ) ^ j := by
  classical
  calc
    (∑ q ∈ badRootLogShell E j, (q : ℝ)⁻¹) ≤
        ∑ _q ∈ badRootLogShell E j, ((2 : ℝ) ^ j)⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      have hqData := Finset.mem_filter.mp
        (show q ∈ E.filter (fun n ↦ Nat.log 2 n = j) by
          simpa only [badRootLogShell] using hq)
      have hqNe : q ≠ 0 := by
        intro hzero
        subst q
        simp at hqData
        omega
      have hpowNat : 2 ^ j ≤ q := by
        rw [← hqData.2]
        exact Nat.pow_log_le_self 2 hqNe
      exact inv_anti₀ (by positivity) (by exact_mod_cast hpowNat)
    _ = ((badRootLogShell E j).card : ℝ) / (2 : ℝ) ^ j := by
      simp [div_eq_mul_inv]

/-- A logarithmic shell is contained in the corresponding prefix. -/
theorem badRootLogShell_subset_prefix (E : Finset ℕ) (j : ℕ) :
    badRootLogShell E j ⊆ E.filter fun q ↦ q ≤ 2 ^ (j + 1) := by
  intro q hq
  have hqData := Finset.mem_filter.mp
    (show q ∈ E.filter (fun n ↦ Nat.log 2 n = j) by
      simpa only [badRootLogShell] using hq)
  rw [Finset.mem_filter]
  refine ⟨hqData.1, ?_⟩
  have hlt : q < 2 ^ (Nat.log 2 q + 1) :=
    Nat.lt_pow_succ_log_self (by omega) q
  rw [hqData.2] at hlt
  exact hlt.le

/-- A uniform prefix density bound gives a constant reciprocal bound on
each binary shell. -/
theorem sum_badRootLogShell_inv_le_two_mul
    {E : Finset ℕ} {rho : ℝ}
    (hprefix : ∀ y : ℕ,
      (((E.filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤ rho * y)
    (j : ℕ) (hj : 1 ≤ j) :
    (∑ q ∈ badRootLogShell E j, (q : ℝ)⁻¹) ≤ 2 * rho := by
  have hcardNat := Finset.card_le_card (badRootLogShell_subset_prefix E j)
  have hcard : ((badRootLogShell E j).card : ℝ) ≤
      rho * (2 ^ (j + 1) : ℕ) := by
    have hcast : ((badRootLogShell E j).card : ℝ) ≤
        (((E.filter fun q ↦ q ≤ 2 ^ (j + 1)).card : ℕ) : ℝ) := by
      exact_mod_cast hcardNat
    exact hcast.trans (hprefix (2 ^ (j + 1)))
  calc
    (∑ q ∈ badRootLogShell E j, (q : ℝ)⁻¹) ≤
        ((badRootLogShell E j).card : ℝ) / (2 : ℝ) ^ j :=
      sum_badRootLogShell_inv_le_card_div_pow E j hj
    _ ≤ (rho * (2 ^ (j + 1) : ℕ)) / (2 : ℝ) ^ j := by
      exact div_le_div_of_nonneg_right hcard (by positivity)
    _ = 2 * rho := by
      rw [show ((2 ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) by norm_cast,
        pow_succ]
      field_simp

/-- Prefix sparsity bounds the total reciprocal root mass by the number of
nonempty binary scales. -/
theorem sum_badRoots_inv_le_log_mul
    {E : Finset ℕ} {u : ℕ} {rho : ℝ}
    (hE : ∀ q ∈ E, 2 ≤ q ∧ q ≤ u)
    (hprefix : ∀ y : ℕ,
      (((E.filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤ rho * y) :
    (∑ q ∈ E, (q : ℝ)⁻¹) ≤
      (Nat.log 2 u : ℝ) * (2 * rho) := by
  classical
  rw [← biUnion_badRootLogShell hE,
    Finset.sum_biUnion (pairwiseDisjoint_badRootLogShell E (Nat.log 2 u))]
  calc
    (∑ j ∈ Finset.Icc 1 (Nat.log 2 u),
        ∑ q ∈ badRootLogShell E j, (q : ℝ)⁻¹) ≤
        ∑ _j ∈ Finset.Icc 1 (Nat.log 2 u), 2 * rho := by
      exact Finset.sum_le_sum fun j hj ↦
        sum_badRootLogShell_inv_le_two_mul hprefix j (Finset.mem_Icc.mp hj).1
    _ ≤ (Nat.log 2 u : ℝ) * (2 * rho) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · have hcardIcc : (Finset.Icc 1 (Nat.log 2 u)).card ≤ Nat.log 2 u := by
          simp
        exact_mod_cast hcardIcc
      · have hrho : 0 ≤ rho := by
          have hone := hprefix 1
          have hcardNonneg : (0 : ℝ) ≤
              (((E.filter fun q ↦ q ≤ 1).card : ℕ) : ℝ) := by positivity
          norm_num at hone
          linarith
        positivity

/-- The same prefix estimate bounds the FKL root weight
`q⁻¹⁻ᵋ` by the reciprocal mass. -/
theorem sum_badRoots_rpow_le_log_mul
    {E : Finset ℕ} {u : ℕ} {rho epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hE : ∀ q ∈ E, 2 ≤ q ∧ q ≤ u)
    (hprefix : ∀ y : ℕ,
      (((E.filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤ rho * y) :
    (∑ q ∈ E, (q : ℝ) ^ (-(1 + epsilon))) ≤
      (Nat.log 2 u : ℝ) * (2 * rho) := by
  calc
    (∑ q ∈ E, (q : ℝ) ^ (-(1 + epsilon))) ≤
        ∑ q ∈ E, (q : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast (hE q hq).1.trans' (by omega)
      calc
        (q : ℝ) ^ (-(1 + epsilon)) ≤ (q : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hqOne (by linarith)
        _ = (q : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ _ := sum_badRoots_inv_le_log_mul hE hprefix

/-- End-to-end closure-mass form used by the good-scale assembly. -/
theorem exists_primeChainClosureTargets_harmonic_bound_of_prefix_sparse
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ Q : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (E : Finset ℕ) (u : ℕ) (rho : ℝ),
        (∀ q ∈ E, q.Prime ∧ Q < q ∧ q ≤ u) →
        (∀ y : ℕ,
          (((E.filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤ rho * y) →
        (∑ t ∈ primeChainClosureTargets u E, (t : ℝ)⁻¹) ≤
          C * (u : ℝ) ^ epsilon *
            ((Nat.log 2 u : ℝ) * (2 * rho)) := by
  obtain ⟨Q, C, hC, hclosure⟩ :=
    exists_primeChainClosureTargets_harmonic_bound hepsilon
  refine ⟨Q, C, hC, ?_⟩
  intro E u rho hE hprefix
  exact (hclosure E u hE).trans <|
    mul_le_mul_of_nonneg_left
      (sum_badRoots_rpow_le_log_mul hepsilon.le
        (fun q hq ↦ ⟨(hE q hq).1.two_le, (hE q hq).2.2⟩) hprefix)
      (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))

end

end Erdos48
