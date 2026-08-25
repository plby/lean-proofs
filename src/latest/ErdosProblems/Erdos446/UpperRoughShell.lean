/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperPowerfulReduction
import ErdosProblems.Erdos387.RoughIntervalBrunUpper

/-!
# Erdős Problem 446: the finite rough-residual shell

This file formalizes the upper-sieve part of Ford's Lemma 3.2.  Once a small
factor `a` and the distinguished prime `p` have been fixed, all prime factors
of the residual factor `b` exceed the sieve threshold `p`.  The product
condition

`X₀ < a*p*b ≤ X₁`

puts `b` in the exact quotient interval

`(X₀/(a*p), X₁/(a*p)]`.

The theorem `card_roughProductShell_le_brun` applies the already formalized
finite Brun upper sieve to this interval.  The final theorem sums the result
over an arbitrary finite family of `(a,p)` shells, including the CRT endpoint
loss.  These are finite cardinal inequalities, not asymptotic interfaces.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable section

/-- Residual factors in one fixed `(a,p)` shell. -/
def roughProductShell (X₀ X₁ a p : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc 0 X₁).filter fun b ↦
    Erdos387.IsZRough p b ∧ X₀ < a * p * b ∧ a * p * b ≤ X₁

theorem mem_roughProductShell {X₀ X₁ a p b : ℕ} :
    b ∈ roughProductShell X₀ X₁ a p ↔
      0 < b ∧ b ≤ X₁ ∧ Erdos387.IsZRough p b ∧
        X₀ < a * p * b ∧ a * p * b ≤ X₁ := by
  classical
  simp [roughProductShell, and_assoc]

/-- The product inequalities put the residual in the exact quotient
interval. -/
theorem roughProductShell_subset_roughPositiveIoc
    {X₀ X₁ a p : ℕ} (ha : 0 < a) (hp : 0 < p) :
    roughProductShell X₀ X₁ a p ⊆
      Erdos387.RoughHarmonic.roughPositiveIoc p
        (X₀ / (a * p)) (X₁ / (a * p)) := by
  classical
  intro b hb
  rw [mem_roughProductShell] at hb
  rw [Erdos387.RoughHarmonic.mem_roughPositiveIoc]
  have hap : 0 < a * p := Nat.mul_pos ha hp
  refine ⟨?_, ?_, hb.2.2.1⟩
  · apply (Nat.div_lt_iff_lt_mul hap).2
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hb.2.2.2.1
  · apply (Nat.le_div_iff_mul_le hap).2
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hb.2.2.2.2

/-- Multiplying the residual back by the fixed shell coefficient. -/
def roughProductShellValues (X₀ X₁ a p : ℕ) : Finset ℕ :=
  (roughProductShell X₀ X₁ a p).image fun b ↦ a * p * b

theorem card_roughProductShellValues_le (X₀ X₁ a p : ℕ) :
    (roughProductShellValues X₀ X₁ a p).card ≤
      (roughProductShell X₀ X₁ a p).card := by
  exact Finset.card_image_le

/-- The exact finite Brun upper bound for one largest-prime/rough-residual
shell. -/
theorem card_roughProductShell_le_brun
    {X₀ X₁ a p L : ℕ}
    (hX : X₀ ≤ X₁) (ha : 0 < a) (hp : 2 ≤ p) (hL : Even L)
    (htail :
      2 * Erdos387.brunSubsetTail
          (Erdos387.sievePrimeProduct 1 p).primeFactors
          (fun q ↦ Erdos387.binomialSieveNu 1 q) L ≤
        Erdos387.finiteEulerProduct
          (Erdos387.sievePrimeProduct 1 p).primeFactors
          (fun q ↦ Erdos387.binomialSieveNu 1 q)) :
    ((roughProductShell X₀ X₁ a p).card : ℝ) ≤
      (((X₁ / (a * p) - X₀ / (a * p) : ℕ) : ℝ) *
          (3 / (2 * Real.log (p : ℝ))) +
        2 * (p ^ L + 1 : ℕ)) := by
  have hp0 : 0 < p := by omega
  have hap : 0 < a * p := Nat.mul_pos ha hp0
  have hquot : X₀ / (a * p) ≤ X₁ / (a * p) :=
    Nat.div_le_div_right hX
  calc
    ((roughProductShell X₀ X₁ a p).card : ℝ) ≤
        ((Erdos387.RoughHarmonic.roughPositiveIoc p
          (X₀ / (a * p)) (X₁ / (a * p))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (roughProductShell_subset_roughPositiveIoc ha
          hp0)
    _ ≤ (((X₁ / (a * p) - X₀ / (a * p) : ℕ) : ℝ) *
          (3 / (2 * Real.log (p : ℝ))) +
        2 * (p ^ L + 1 : ℕ)) :=
      Erdos387.RoughBrun.card_roughPositiveIoc_le_brunDensity_add_endpoint'
        hquot hp hL htail

/-- The union of a finite family of reconstructed rough shells. -/
def roughProductShellUnion
    (X₀ X₁ : ℕ) (AP : Finset (ℕ × ℕ)) : Finset ℕ :=
  AP.biUnion fun ap ↦ roughProductShellValues X₀ X₁ ap.1 ap.2

/-- Ford's finite shell sum after the one-dimensional upper sieve.  The
first sum is the main `1/log p` term and the second is the explicit truncated
Brun endpoint loss. -/
theorem card_roughProductShellUnion_le_brun
    {X₀ X₁ L : ℕ} {AP : Finset (ℕ × ℕ)}
    (hX : X₀ ≤ X₁)
    (ha : ∀ ap ∈ AP, 0 < ap.1)
    (hp : ∀ ap ∈ AP, 2 ≤ ap.2)
    (hL : Even L)
    (htail : ∀ ap ∈ AP,
      2 * Erdos387.brunSubsetTail
          (Erdos387.sievePrimeProduct 1 ap.2).primeFactors
          (fun q ↦ Erdos387.binomialSieveNu 1 q) L ≤
        Erdos387.finiteEulerProduct
          (Erdos387.sievePrimeProduct 1 ap.2).primeFactors
          (fun q ↦ Erdos387.binomialSieveNu 1 q)) :
    ((roughProductShellUnion X₀ X₁ AP).card : ℝ) ≤
      ∑ ap ∈ AP,
        (((X₁ / (ap.1 * ap.2) - X₀ / (ap.1 * ap.2) : ℕ) : ℝ) *
            (3 / (2 * Real.log (ap.2 : ℝ))) +
          2 * (ap.2 ^ L + 1 : ℕ)) := by
  calc
    ((roughProductShellUnion X₀ X₁ AP).card : ℝ) ≤
        ∑ ap ∈ AP,
          ((roughProductShellValues X₀ X₁ ap.1 ap.2).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ ap ∈ AP,
        ((roughProductShell X₀ X₁ ap.1 ap.2).card : ℝ) := by
      apply Finset.sum_le_sum
      intro ap hap
      exact_mod_cast card_roughProductShellValues_le X₀ X₁ ap.1 ap.2
    _ ≤ ∑ ap ∈ AP,
        (((X₁ / (ap.1 * ap.2) - X₀ / (ap.1 * ap.2) : ℕ) : ℝ) *
            (3 / (2 * Real.log (ap.2 : ℝ))) +
          2 * (ap.2 ^ L + 1 : ℕ)) := by
      apply Finset.sum_le_sum
      intro ap hap
      exact card_roughProductShell_le_brun hX (ha ap hap) (hp ap hap) hL
        (htail ap hap)

end

end Erdos446
