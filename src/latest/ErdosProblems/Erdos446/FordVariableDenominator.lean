/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FordLargestPrimeSummation

/-!
# Erdős Problem 446: removal of Ford's varying logarithmic denominator

This is the finite form of Ford--Koukoulopoulos Lemma 3.3.  The ordinary
supports have a logarithmic denominator of order `log y`.  On the exceptional
supports we insert `log(product)^3 / log(y)^3`; summation by the largest prime
is exactly `exists_pos_largestPrimeWeightedClusterMoment_le`.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable section

/-- The argument `y^(2/3)/a + P⁺(a)` in Ford's variable logarithm, written
for the squarefree integer represented by a prime support. -/
def fordVariableLogArgument (y : ℕ) (S : Finset ℕ) : ℝ :=
  (y : ℝ) ^ (2 / 3 : ℝ) / ((S.prod id : ℕ) : ℝ) +
    (primeSupportMax S : ℝ)

/-- The exceptional family `P₁`: its product is larger than `y^(1/2)`,
while its largest prime is at most `y^(1/4)`, in logarithmic form. -/
def fordExceptionalSupport (y : ℕ) (S : Finset ℕ) : Prop :=
  Real.log (y : ℝ) / 2 < Real.log ((S.prod id : ℕ) : ℝ) ∧
    Real.log (primeSupportMax S : ℝ) ≤ Real.log (y : ℝ) / 4

/-- The finite squarefree cluster sum with Ford's varying denominator and an
arbitrary smoothness cutoff. -/
def fordVariableDenominatorSum (y P : ℕ) : ℝ :=
  ∑ S ∈ (primesUpTo P).powerset,
    primeSubsetClusterTerm S /
      Real.log (fordVariableLogArgument y S) ^ 2

/-- The exact dyadic specialization occurring after Ford's Lemma 3.2. -/
def fordDyadicVariableDenominatorSum (y : ℕ) : ℝ :=
  fordVariableDenominatorSum y (2 * y)

theorem fordVariableLogArgument_pos {y P : ℕ} {S : Finset ℕ}
    (hy : 0 < y) (hSP : S ⊆ primesUpTo P) :
    0 < fordVariableLogArgument y S := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hprod : 0 < S.prod id := primeSubset_product_pos hSP
  have hprodR : (0 : ℝ) < S.prod id := by exact_mod_cast hprod
  unfold fordVariableLogArgument
  have hpow : 0 < (y : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos hyR _
  positivity

private theorem log_fordScale_div_product
    {y P : ℕ} {S : Finset ℕ} (hy : 0 < y)
    (hSP : S ⊆ primesUpTo P) :
    Real.log ((y : ℝ) ^ (2 / 3 : ℝ) /
        ((S.prod id : ℕ) : ℝ)) =
      (2 / 3 : ℝ) * Real.log (y : ℝ) -
        Real.log ((S.prod id : ℕ) : ℝ) := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hprod : 0 < S.prod id := primeSubset_product_pos hSP
  have hprodR : (0 : ℝ) < S.prod id := by exact_mod_cast hprod
  rw [Real.log_div (Real.rpow_pos_of_pos hyR _).ne' hprodR.ne',
    Real.log_rpow hyR]

private theorem log_firstTerm_le_log_argument
    {y P : ℕ} {S : Finset ℕ} (hy : 0 < y)
    (hSP : S ⊆ primesUpTo P) :
    Real.log ((y : ℝ) ^ (2 / 3 : ℝ) /
        ((S.prod id : ℕ) : ℝ)) ≤
      Real.log (fordVariableLogArgument y S) := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hprod : 0 < S.prod id := primeSubset_product_pos hSP
  have hprodR : (0 : ℝ) < S.prod id := by exact_mod_cast hprod
  have hfirst : 0 < (y : ℝ) ^ (2 / 3 : ℝ) /
      ((S.prod id : ℕ) : ℝ) := by positivity
  have harg : 0 < fordVariableLogArgument y S :=
    fordVariableLogArgument_pos hy hSP
  apply Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hfirst)
      (by simpa only [Set.mem_Ioi] using harg)
  unfold fordVariableLogArgument
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

private theorem log_max_le_log_argument
    {y P : ℕ} {S : Finset ℕ} (hy : 0 < y)
    (hSP : S ⊆ primesUpTo P) (hS : S.Nonempty) :
    Real.log (primeSupportMax S : ℝ) ≤
      Real.log (fordVariableLogArgument y S) := by
  have hp : (primeSupportMax S).Prime :=
    prime_of_mem_primesUpTo (hSP (primeSupportMax_mem hS))
  have hmax : (0 : ℝ) < primeSupportMax S := by exact_mod_cast hp.pos
  have harg : 0 < fordVariableLogArgument y S :=
    fordVariableLogArgument_pos hy hSP
  apply Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hmax)
      (by simpa only [Set.mem_Ioi] using harg)
  unfold fordVariableLogArgument
  exact le_add_of_nonneg_left (by positivity)

private theorem nonempty_of_fordExceptionalSupport
    {y : ℕ} {S : Finset ℕ} (hy : 2 ≤ y)
    (hS : fordExceptionalSupport y S) : S.Nonempty := by
  by_contra hne
  have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  unfold fordExceptionalSupport at hS
  rw [hEmpty] at hS
  simp only [Finset.prod_empty, Nat.cast_one, Real.log_one] at hS
  linarith [hS.1]

/-- Outside `P₁`, either the quotient term or the largest-prime term forces
at least one sixth of `log y` in the logarithm. -/
theorem log_y_div_six_le_log_fordVariableLogArgument_of_not_exceptional
    {y P : ℕ} {S : Finset ℕ} (hy : 2 ≤ y)
    (hSP : S ⊆ primesUpTo P)
    (hnot : ¬ fordExceptionalSupport y S) :
    Real.log (y : ℝ) / 6 ≤
      Real.log (fordVariableLogArgument y S) := by
  have hypos : 0 < y := by omega
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  by_cases hprod : Real.log ((S.prod id : ℕ) : ℝ) ≤
      Real.log (y : ℝ) / 2
  · have hfirst := log_firstTerm_le_log_argument hypos hSP
    rw [log_fordScale_div_product hypos hSP] at hfirst
    linarith
  · have hmax : Real.log (y : ℝ) / 4 <
        Real.log (primeSupportMax S : ℝ) := by
      by_contra hmaxnot
      apply hnot
      exact ⟨lt_of_not_ge hprod, le_of_not_gt hmaxnot⟩
    have hSne : S.Nonempty := by
      by_contra hne
      have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      apply hprod
      rw [hEmpty]
      simp only [Finset.prod_empty, Nat.cast_one, Real.log_one]
      positivity
    have hmaxArg := log_max_le_log_argument hypos hSP hSne
    linarith

theorem log_max_le_log_fordVariableLogArgument_of_exceptional
    {y P : ℕ} {S : Finset ℕ} (hy : 2 ≤ y)
    (hSP : S ⊆ primesUpTo P)
    (hS : fordExceptionalSupport y S) :
    Real.log (primeSupportMax S : ℝ) ≤
      Real.log (fordVariableLogArgument y S) :=
  log_max_le_log_argument (by omega) hSP
    (nonempty_of_fordExceptionalSupport hy hS)

/-- The summand appearing after insertion of the cubic product logarithm. -/
def fordLargestPrimeWeightedTerm (S : Finset ℕ) : ℝ :=
  primeSubsetClusterTerm S * Real.log ((S.prod id : ℕ) : ℝ) ^ 3 /
    Real.log (primeSupportMax S : ℝ) ^ 2

theorem fordLargestPrimeWeightedTerm_nonneg
    {P : ℕ} {S : Finset ℕ} (hSP : S ⊆ primesUpTo P) :
    0 ≤ fordLargestPrimeWeightedTerm S := by
  have hprod : 0 < S.prod id := primeSubset_product_pos hSP
  have hlogprod : 0 ≤ Real.log ((S.prod id : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hprod)
  unfold fordLargestPrimeWeightedTerm
  exact div_nonneg
    (mul_nonneg (primeSubsetClusterTerm_nonneg S)
      (pow_nonneg hlogprod _))
    (sq_nonneg _)

private theorem ordinary_fordVariableDenominatorTerm_le
    {y P : ℕ} {S : Finset ℕ} (hy : 2 ≤ y)
    (hSP : S ⊆ primesUpTo P)
    (hnot : ¬ fordExceptionalSupport y S) :
    primeSubsetClusterTerm S /
        Real.log (fordVariableLogArgument y S) ^ 2 ≤
      (36 / Real.log (y : ℝ) ^ 2) * primeSubsetClusterTerm S := by
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlower :=
    log_y_div_six_le_log_fordVariableLogArgument_of_not_exceptional
      hy hSP hnot
  have hsix : 0 < Real.log (y : ℝ) / 6 := by positivity
  have hsq : (Real.log (y : ℝ) / 6) ^ 2 ≤
      Real.log (fordVariableLogArgument y S) ^ 2 :=
    (sq_le_sq₀ hsix.le (hsix.le.trans hlower)).2 hlower
  calc
    primeSubsetClusterTerm S /
        Real.log (fordVariableLogArgument y S) ^ 2 ≤
      primeSubsetClusterTerm S / (Real.log (y : ℝ) / 6) ^ 2 :=
        div_le_div_of_nonneg_left (primeSubsetClusterTerm_nonneg S)
          (sq_pos_of_pos hsix) hsq
    _ = (36 / Real.log (y : ℝ) ^ 2) *
        primeSubsetClusterTerm S := by
      field_simp [hlogy.ne']
      ring

private theorem exceptional_fordVariableDenominatorTerm_le
    {y P : ℕ} {S : Finset ℕ} (hy : 2 ≤ y)
    (hSP : S ⊆ primesUpTo P)
    (hS : fordExceptionalSupport y S) :
    primeSubsetClusterTerm S /
        Real.log (fordVariableLogArgument y S) ^ 2 ≤
      (8 / Real.log (y : ℝ) ^ 3) *
        fordLargestPrimeWeightedTerm S := by
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hSne : S.Nonempty := nonempty_of_fordExceptionalSupport hy hS
  have hp : (primeSupportMax S).Prime :=
    prime_of_mem_primesUpTo (hSP (primeSupportMax_mem hSne))
  have hlogmax : 0 < Real.log (primeSupportMax S : ℝ) := hp.log_pos
  have hmaxArg :=
    log_max_le_log_fordVariableLogArgument_of_exceptional hy hSP hS
  have hsq : Real.log (primeSupportMax S : ℝ) ^ 2 ≤
      Real.log (fordVariableLogArgument y S) ^ 2 :=
    (sq_le_sq₀ hlogmax.le (hlogmax.le.trans hmaxArg)).2 hmaxArg
  have hprod : 0 < S.prod id := primeSubset_product_pos hSP
  have hlogprod : 0 ≤ Real.log ((S.prod id : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hprod)
  have hcubic : Real.log (y : ℝ) ^ 3 ≤
      8 * Real.log ((S.prod id : ℕ) : ℝ) ^ 3 := by
    have hpow := pow_le_pow_left₀ (by positivity :
        0 ≤ Real.log (y : ℝ) / 2) hS.1.le 3
    nlinarith
  have hscale : 1 ≤
      8 * Real.log ((S.prod id : ℕ) : ℝ) ^ 3 /
        Real.log (y : ℝ) ^ 3 := by
    exact (le_div_iff₀ (pow_pos hlogy 3)).2 (by simpa using hcubic)
  have hweightedBase : 0 ≤
      primeSubsetClusterTerm S /
        Real.log (primeSupportMax S : ℝ) ^ 2 :=
    div_nonneg (primeSubsetClusterTerm_nonneg S) (sq_nonneg _)
  calc
    primeSubsetClusterTerm S /
        Real.log (fordVariableLogArgument y S) ^ 2 ≤
      primeSubsetClusterTerm S /
        Real.log (primeSupportMax S : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (primeSubsetClusterTerm_nonneg S)
        (sq_pos_of_pos hlogmax) hsq
    _ ≤ (8 * Real.log ((S.prod id : ℕ) : ℝ) ^ 3 /
          Real.log (y : ℝ) ^ 3) *
        (primeSubsetClusterTerm S /
          Real.log (primeSupportMax S : ℝ) ^ 2) := by
      exact le_mul_of_one_le_left hweightedBase hscale
    _ = (8 / Real.log (y : ℝ) ^ 3) *
        fordLargestPrimeWeightedTerm S := by
      unfold fordLargestPrimeWeightedTerm
      ring

/-- Pointwise `P₁` split: the ordinary term pays `36/log(y)^2`, while the
exceptional term is charged to the largest-prime cubic moment. -/
theorem fordVariableDenominatorTerm_le_split
    {y P : ℕ} {S : Finset ℕ} (hy : 2 ≤ y)
    (hSP : S ⊆ primesUpTo P) :
    primeSubsetClusterTerm S /
        Real.log (fordVariableLogArgument y S) ^ 2 ≤
      (36 / Real.log (y : ℝ) ^ 2) * primeSubsetClusterTerm S +
        (8 / Real.log (y : ℝ) ^ 3) *
          fordLargestPrimeWeightedTerm S := by
  by_cases hS : fordExceptionalSupport y S
  · exact (exceptional_fordVariableDenominatorTerm_le hy hSP hS).trans
      (le_add_of_nonneg_left
        (mul_nonneg (by positivity) (primeSubsetClusterTerm_nonneg S)))
  · exact (ordinary_fordVariableDenominatorTerm_le hy hSP hS).trans
      (le_add_of_nonneg_right
        (mul_nonneg (by positivity)
          (fordLargestPrimeWeightedTerm_nonneg hSP)))

theorem sum_primeSubsetClusterTerm_eq_squarefreeClusterMass (P : ℕ) :
    (∑ S ∈ (primesUpTo P).powerset, primeSubsetClusterTerm S) =
      squarefreeClusterMass P := by
  rw [squarefreeClusterMass_eq_powersetMoment_zero]
  simp only [powersetAdditiveMoment, pow_zero, mul_one]

theorem sum_fordLargestPrimeWeightedTerm_eq (P : ℕ) :
    (∑ S ∈ (primesUpTo P).powerset,
      fordLargestPrimeWeightedTerm S) =
        largestPrimeWeightedClusterMoment P := by
  unfold largestPrimeWeightedClusterMoment nonemptySmoothSupports
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hSne : S.Nonempty
  · simp only [hSne, ↓reduceIte]
    rfl
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
    subst S
    simp [fordLargestPrimeWeightedTerm, primeSubsetClusterTerm,
      primeSupportMax]

/-- Finite denominator removal before partial summation: the complete
varying-denominator sum is bounded by the ordinary cluster mass plus the
largest-prime cubic moment. -/
theorem fordVariableDenominatorSum_le_mass_add_largestPrimeMoment
    {y P : ℕ} (hy : 2 ≤ y) :
    fordVariableDenominatorSum y P ≤
      (36 / Real.log (y : ℝ) ^ 2) * squarefreeClusterMass P +
        (8 / Real.log (y : ℝ) ^ 3) *
          largestPrimeWeightedClusterMoment P := by
  unfold fordVariableDenominatorSum
  calc
    (∑ S ∈ (primesUpTo P).powerset,
      primeSubsetClusterTerm S /
        Real.log (fordVariableLogArgument y S) ^ 2) ≤
      ∑ S ∈ (primesUpTo P).powerset,
        ((36 / Real.log (y : ℝ) ^ 2) * primeSubsetClusterTerm S +
          (8 / Real.log (y : ℝ) ^ 3) *
            fordLargestPrimeWeightedTerm S) := by
      exact Finset.sum_le_sum fun S hS ↦
        fordVariableDenominatorTerm_le_split hy
          (Finset.mem_powerset.mp hS)
    _ = (36 / Real.log (y : ℝ) ^ 2) * squarefreeClusterMass P +
        (8 / Real.log (y : ℝ) ^ 3) *
          largestPrimeWeightedClusterMoment P := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        sum_primeSubsetClusterTerm_eq_squarefreeClusterMass,
        sum_fordLargestPrimeWeightedTerm_eq]

private theorem log_two_mul_le_two_log {y : ℕ} (hy : 2 ≤ y) :
    Real.log ((2 * y : ℕ) : ℝ) ≤ 2 * Real.log (y : ℝ) := by
  have hypos : 0 < y := by omega
  have hlog2le : Real.log (2 : ℝ) ≤ Real.log (y : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; norm_num)
      (by simp only [Set.mem_Ioi]; exact_mod_cast hypos)
      (by exact_mod_cast hy)
  calc
    Real.log ((2 * y : ℕ) : ℝ) =
        Real.log (2 : ℝ) + Real.log (y : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (by norm_num)
        (ne_of_gt (by exact_mod_cast hypos : (0 : ℝ) < y))]
      norm_num
    _ = Real.log (y : ℝ) + Real.log (2 : ℝ) := add_comm _ _
    _ ≤ Real.log (y : ℝ) + Real.log (y : ℝ) :=
      add_le_add_right hlog2le _
    _ = 2 * Real.log (y : ℝ) := by ring

/-- Ford--Koukoulopoulos Lemma 3.3 in the exact finite dyadic form needed
after Lemma 3.2.  No analytic estimate remains as a hypothesis: the constant
comes from the proved prime Mertens theorem, cubic expansion, largest-prime
deletion, and finite partial summation above. -/
theorem exists_pos_fordDyadicVariableDenominatorSum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
      fordDyadicVariableDenominatorSum y ≤
        C * squarefreeClusterMass (2 * y) /
          Real.log (y : ℝ) ^ 2 := by
  obtain ⟨D, hD, hMoment⟩ :=
    exists_pos_largestPrimeWeightedClusterMoment_le
  let C : ℝ := 36 + 16 * D
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun y hy ↦ ?_⟩
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hcutoff : 2 ≤ 2 * y := by omega
  have hMass : 0 ≤ squarefreeClusterMass (2 * y) := by
    rw [squarefreeClusterMass_eq_powersetMoment_zero]
    exact Finset.sum_nonneg fun S hS ↦ by
      simpa [powersetAdditiveMoment] using primeSubsetClusterTerm_nonneg S
  have hMomentBound :
      largestPrimeWeightedClusterMoment (2 * y) ≤
        D * Real.log ((2 * y : ℕ) : ℝ) *
          squarefreeClusterMass (2 * y) :=
    hMoment (2 * y) hcutoff
  have hlogCutoff : Real.log ((2 * y : ℕ) : ℝ) ≤
      2 * Real.log (y : ℝ) := log_two_mul_le_two_log hy
  unfold fordDyadicVariableDenominatorSum
  calc
    fordVariableDenominatorSum y (2 * y) ≤
        (36 / Real.log (y : ℝ) ^ 2) *
            squarefreeClusterMass (2 * y) +
          (8 / Real.log (y : ℝ) ^ 3) *
            largestPrimeWeightedClusterMoment (2 * y) :=
      fordVariableDenominatorSum_le_mass_add_largestPrimeMoment hy
    _ ≤ (36 / Real.log (y : ℝ) ^ 2) *
            squarefreeClusterMass (2 * y) +
          (8 / Real.log (y : ℝ) ^ 3) *
            (D * Real.log ((2 * y : ℕ) : ℝ) *
              squarefreeClusterMass (2 * y)) := by
      gcongr
    _ ≤ (36 / Real.log (y : ℝ) ^ 2) *
            squarefreeClusterMass (2 * y) +
          (8 / Real.log (y : ℝ) ^ 3) *
            (D * (2 * Real.log (y : ℝ)) *
              squarefreeClusterMass (2 * y)) := by
      gcongr
    _ = C * squarefreeClusterMass (2 * y) /
          Real.log (y : ℝ) ^ 2 := by
      dsimp [C]
      field_simp [hlogy.ne']
      ring

end

end Erdos446
