/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceUniformConstantIndependent
import ErdosProblems.Erdos240.BakerSourceOversizedConstantUniform

/-!
# The complete fixed-family source-constant ledger

All constants in this file are chosen after the finite old prime family and
before the varying prime and coefficient cutoff.  The main theorem combines
the structural and jet requirements with the exact local-circle, integral
Liouville, and rational Liouville absorption constants used by the concrete
source proof.

The theorem takes one arbitrary additional bound `A`.  Thus a later
closed-form majorant can add a newly isolated fixed-family coefficient merely
by instantiating `A`; the uniformity argument itself never has to be repeated.
-/

noncomputable section

namespace Erdos240.BakerSourceUniformConstantCompletion

open Erdos240
open BakerLemma3Concrete
open BakerSourceAssemblyIndependent
open BakerSourceOversizedConstantNumerics
open BakerSourceOversizedConstantUniform
open BakerSourceUniformConstantIndependent

/-! ## A generic finite-ledger bound -/

/-- Every finite list of real requirements has a strictly positive common
upper bound.  The absolute-value sum is used instead of a maximum so the
statement also covers an empty ledger without a separate case. -/
theorem exists_pos_upperBound_finset (s : Finset ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ s, x ≤ C := by
  classical
  let C : ℝ := ∑ x ∈ s, |x| + 1
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C]
    positivity
  · intro x hx
    dsimp only [C]
    have hxsum : |x| ≤ ∑ y ∈ s, |y| := by
      exact Finset.single_le_sum
        (fun y hy ↦ abs_nonneg y) hx
    exact (le_abs_self x).trans (hxsum.trans (le_add_of_nonneg_right zero_le_one))

/-! ## The concrete source ledger -/

/-- The literal fixed-family coefficient used by the integral Liouville
denominator estimate.  It is repeated here so the uniformity layer does not
import the analytic lower-bound development. -/
def sourceIntegralDenominatorConstant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℝ :=
  8 * P.k * P.OmegaOld

/-- The literal fixed-family coefficient used by the rational Liouville
product estimate.  As with the contour constant, keeping its formula in the
ledger prevents a dependency cycle with the analytic consumer. -/
def sourceRationalLiouvilleConstant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℝ :=
  5 + P.k ^ (P.mu / 2) * (P.k + 32)

/-- The five fixed-family lower bounds consumed by the current source
construction.  The factor four on the contour constant leaves the strict
slack needed when the local-circle and outer remainders are combined. -/
def fixedSourceRequirements {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : Finset ℝ :=
  {4 * P.C,
    jetAbsorptionConstant P,
    4 * sourceLemmaFourContourConstant P,
    16 * P.k * sourceIntegralDenominatorConstant P,
    4 * sourceRationalLiouvilleConstant P * P.k}

/-- The complete collection of inequalities supplied by one normalized
constant at a concrete source specialization. -/
def HasFixedSourceConstantBounds {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (C₀ : ℝ) : Prop :=
  4 * P.C ≤ C₀ ∧
    jetAbsorptionConstant P ≤ C₀ ∧
    4 * sourceLemmaFourContourConstant P ≤ C₀ ∧
    16 * P.k * sourceIntegralDenominatorConstant P ≤ C₀ ∧
    4 * sourceRationalLiouvilleConstant P * P.k ≤ C₀ ∧
    8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld)

/-- Membership in the explicit finite ledger is equivalent to the five
non-exponent inequalities of `HasFixedSourceConstantBounds`. -/
theorem fixedSourceRequirements_le_iff {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (C₀ : ℝ) :
    (∀ A ∈ fixedSourceRequirements P, A ≤ C₀) ↔
      4 * P.C ≤ C₀ ∧
        jetAbsorptionConstant P ≤ C₀ ∧
        4 * sourceLemmaFourContourConstant P ≤ C₀ ∧
        16 * P.k * sourceIntegralDenominatorConstant P ≤ C₀ ∧
        4 * sourceRationalLiouvilleConstant P * P.k ≤ C₀ := by
  simp only [fixedSourceRequirements, Finset.mem_insert,
    Finset.mem_singleton]
  aesop

/-! ## Independence of the varying prime and cutoff -/

/-- Every entry of the concrete fixed-family ledger is definitionally
unchanged when only the varying prime and cutoff change. -/
theorem fixedSourceRequirements_sourceParameters_eq {oldRank : ℕ}
    (old : Fin oldRank → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime₁ : ℕ) (newPrimePrime₁ : newPrime₁.Prime)
    (newFresh₁ : ∀ i, old i ≠ newPrime₁)
    (N₁ : ℕ) (Nlarge₁ : Real.exp 2 ≤ (N₁ : ℝ))
    (newPrime₂ : ℕ) (newPrimePrime₂ : newPrime₂.Prime)
    (newFresh₂ : ∀ i, old i ≠ newPrime₂)
    (N₂ : ℕ) (Nlarge₂ : Real.exp 2 ≤ (N₂ : ℝ)) :
    fixedSourceRequirements
        (sourceParameters old oldPrime oldInjective newPrime₁ newPrimePrime₁
          newFresh₁ N₁ Nlarge₁) =
      fixedSourceRequirements
        (sourceParameters old oldPrime oldInjective newPrime₂ newPrimePrime₂
          newFresh₂ N₂ Nlarge₂) := by
  rfl

/-- A single positive normalized constant dominates every currently explicit
source requirement, together with an arbitrary additional fixed-family
number `A`.  The conclusion is uniform in the varying prime and in `N`. -/
theorem exists_uniform_completeSourceConstant_ge {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    (old : Fin oldRank → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old) (A : ℝ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ A ≤ C₀ ∧
      ∀ (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
        (newFresh : ∀ i, old i ≠ newPrime)
        (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)),
        let P := sourceParameters old oldPrime oldInjective newPrime
          newPrimePrime newFresh N Nlarge
        HasFixedSourceConstantBounds P C₀ := by
  classical
  let oldMax : ℕ := Finset.univ.sup old
  obtain ⟨referencePrime, hreferencePrime, referencePrime_prime⟩ :=
    Nat.exists_infinite_primes (oldMax + 1)
  have referencePrime_fresh : ∀ i, old i ≠ referencePrime := by
    intro i
    have holdMax : old i ≤ oldMax :=
      Finset.le_sup (f := old) (Finset.mem_univ i)
    exact ne_of_lt (show old i < referencePrime by omega)
  let referenceBound : ℕ := ⌈Real.exp 2⌉₊
  have referenceBound_large : Real.exp 2 ≤ (referenceBound : ℝ) :=
    Nat.le_ceil (Real.exp 2)
  let Pref := sourceParameters old oldPrime oldInjective referencePrime
    referencePrime_prime referencePrime_fresh referenceBound
      referenceBound_large
  let extraLedger := insert A (fixedSourceRequirements Pref)
  obtain ⟨B, hBpos, hB⟩ := exists_pos_upperBound_finset extraLedger
  obtain ⟨C₀, hC₀pos, hBC₀, huniform⟩ :=
    exists_uniform_oversizedConstant_ge old oldPrime oldInjective B
  refine ⟨C₀, hC₀pos, ?_, ?_⟩
  · exact (hB A (by simp only [extraLedger, Finset.mem_insert, true_or])).trans hBC₀
  · intro newPrime newPrimePrime newFresh N Nlarge
    dsimp only
    let P := sourceParameters old oldPrime oldInjective newPrime
      newPrimePrime newFresh N Nlarge
    have hrequirements : fixedSourceRequirements P =
        fixedSourceRequirements Pref := by
      exact fixedSourceRequirements_sourceParameters_eq old oldPrime
        oldInjective newPrime newPrimePrime newFresh N Nlarge referencePrime
          referencePrime_prime referencePrime_fresh referenceBound
            referenceBound_large
    have hledger : ∀ X ∈ fixedSourceRequirements P, X ≤ C₀ := by
      intro X hX
      apply (hB X ?_).trans hBC₀
      simp only [extraLedger, Finset.mem_insert]
      exact Or.inr (by simpa only [hrequirements] using hX)
    have hfive := (fixedSourceRequirements_le_iff P C₀).mp hledger
    have hbase := huniform newPrime newPrimePrime newFresh N Nlarge
    exact ⟨hfive.1, hfive.2.1, hfive.2.2.1, hfive.2.2.2.1,
      hfive.2.2.2.2, hbase.2.2⟩

end Erdos240.BakerSourceUniformConstantCompletion

#print axioms Erdos240.BakerSourceUniformConstantCompletion.exists_pos_upperBound_finset
#print axioms Erdos240.BakerSourceUniformConstantCompletion.fixedSourceRequirements_sourceParameters_eq
#print axioms Erdos240.BakerSourceUniformConstantCompletion.exists_uniform_completeSourceConstant_ge
