/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAssemblyIndependent
import ErdosProblems.Erdos240.BakerSourceOversizedConstantNumerics

/-!
# A fixed-family oversized source constant

The normalized logarithmic-form constant is chosen after the finite old
prime family, but before the varying prime and coefficient cutoff.  This
module records that the two lower bounds needed by the sharp source
estimates---four times the base source constant and the equation-(7) jet
absorption constant---have exactly that allowed dependence.
-/

noncomputable section

namespace Erdos240.BakerSourceUniformConstantIndependent

open Erdos240
open Erdos240.BakerSourceAssemblyIndependent
open Erdos240.BakerSourceOversizedConstantNumerics

/-- The fixed-family coefficient appearing in the local-circle contour
budget.  It is kept here by its literal formula so that choosing the uniform
constant does not import the analytic budget module. -/
def sourceLemmaFourContourConstant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℝ :=
  960 * P.k ^ 2

/-- The jet-absorption constant is independent of the varying prime and
coefficient cutoff.  Its only non-rank input is the fixed old logarithm
family. -/
theorem sourceParameters_jetAbsorptionConstant_eq {oldRank : ℕ}
    (old : Fin oldRank → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime₁ : ℕ) (newPrimePrime₁ : newPrime₁.Prime)
    (newFresh₁ : ∀ i, old i ≠ newPrime₁)
    (N₁ : ℕ) (Nlarge₁ : Real.exp 2 ≤ (N₁ : ℝ))
    (newPrime₂ : ℕ) (newPrimePrime₂ : newPrime₂.Prime)
    (newFresh₂ : ∀ i, old i ≠ newPrime₂)
    (N₂ : ℕ) (Nlarge₂ : Real.exp 2 ≤ (N₂ : ℝ)) :
    jetAbsorptionConstant
        (sourceParameters old oldPrime oldInjective newPrime₁ newPrimePrime₁
          newFresh₁ N₁ Nlarge₁) =
      jetAbsorptionConstant
        (sourceParameters old oldPrime oldInjective newPrime₂ newPrimePrime₂
          newFresh₂ N₂ Nlarge₂) := by
  rfl

/-- The local-circle loss constant is likewise rank-only. -/
theorem sourceParameters_lemmaFourContourAbsorptionConstant_eq
    {oldRank : ℕ}
    (old : Fin oldRank → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime₁ : ℕ) (newPrimePrime₁ : newPrime₁.Prime)
    (newFresh₁ : ∀ i, old i ≠ newPrime₁)
    (N₁ : ℕ) (Nlarge₁ : Real.exp 2 ≤ (N₁ : ℝ))
    (newPrime₂ : ℕ) (newPrimePrime₂ : newPrime₂.Prime)
    (newFresh₂ : ∀ i, old i ≠ newPrime₂)
    (N₂ : ℕ) (Nlarge₂ : Real.exp 2 ≤ (N₂ : ℝ)) :
    sourceLemmaFourContourConstant
        (sourceParameters old oldPrime oldInjective newPrime₁ newPrimePrime₁
          newFresh₁ N₁ Nlarge₁) =
      sourceLemmaFourContourConstant
        (sourceParameters old oldPrime oldInjective newPrime₂ newPrimePrime₂
          newFresh₂ N₂ Nlarge₂) := by
  rfl

/-- Positivity of the concrete absorption constant. -/
theorem jetAbsorptionConstant_pos {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    0 < jetAbsorptionConstant P := by
  have hsum : 0 ≤ ∑ r, ‖Erdos240.BakerSourceState.oldLog P r‖ := by
    exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hold : 0 < oldJetFactor P := by
    unfold oldJetFactor
    nlinarith
  unfold jetAbsorptionConstant
  exact mul_pos (mul_pos (by norm_num) (by nlinarith [P.k_pos])) hold

/-- A single normalized constant, chosen from the fixed old prime family,
dominates the fourfold base source constant, every actual jet-absorption
constant, and the local-circle contour-loss constant. -/
theorem exists_uniform_oversizedSourceConstant {oldRank : ℕ}
    (old : Fin oldRank → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
        (newFresh : ∀ i, old i ≠ newPrime)
        (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)),
        let P := sourceParameters old oldPrime oldInjective newPrime
          newPrimePrime newFresh N Nlarge
        4 * P.C ≤ C₀ ∧ jetAbsorptionConstant P ≤ C₀ ∧
          sourceLemmaFourContourConstant P ≤ C₀ := by
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
  let C₀ : ℝ := 4 * Pref.C + jetAbsorptionConstant Pref +
    sourceLemmaFourContourConstant Pref
  have hC₀ : 0 < C₀ := by
    dsimp only [C₀]
    have hcontour : 0 < sourceLemmaFourContourConstant Pref := by
      unfold sourceLemmaFourContourConstant
      exact mul_pos (by norm_num) (pow_pos Pref.k_pos 2)
    exact add_pos
      (add_pos (mul_pos (by norm_num) Pref.C_pos)
        (jetAbsorptionConstant_pos Pref)) hcontour
  refine ⟨C₀, hC₀, ?_⟩
  intro newPrime newPrimePrime newFresh N Nlarge
  dsimp only
  have hbase :
      (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
          newFresh N Nlarge).C = Pref.C :=
    sourceParameters_C_eq old oldPrime oldInjective newPrime newPrimePrime
      newFresh N Nlarge old oldPrime oldInjective referencePrime
        referencePrime_prime referencePrime_fresh referenceBound
          referenceBound_large
  have hjet :
      jetAbsorptionConstant
          (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
            newFresh N Nlarge) = jetAbsorptionConstant Pref :=
    sourceParameters_jetAbsorptionConstant_eq old oldPrime oldInjective
      newPrime newPrimePrime newFresh N Nlarge referencePrime
        referencePrime_prime referencePrime_fresh referenceBound
          referenceBound_large
  have hcontour :
      sourceLemmaFourContourConstant
          (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
            newFresh N Nlarge) = sourceLemmaFourContourConstant Pref :=
    sourceParameters_lemmaFourContourAbsorptionConstant_eq old oldPrime
      oldInjective newPrime newPrimePrime newFresh N Nlarge referencePrime
        referencePrime_prime referencePrime_fresh referenceBound
          referenceBound_large
  constructor
  · rw [hbase]
    dsimp only [C₀]
    have hcontour0 : 0 ≤ sourceLemmaFourContourConstant Pref := by
      unfold sourceLemmaFourContourConstant
      positivity
    nlinarith [jetAbsorptionConstant_pos Pref]
  · constructor
    · rw [hjet]
      dsimp only [C₀]
      have hcontour0 : 0 ≤ sourceLemmaFourContourConstant Pref := by
        unfold sourceLemmaFourContourConstant
        positivity
      nlinarith [Pref.C_pos]
    · rw [hcontour]
      dsimp only [C₀]
      nlinarith [Pref.C_pos, jetAbsorptionConstant_pos Pref]

end Erdos240.BakerSourceUniformConstantIndependent

#print axioms Erdos240.BakerSourceUniformConstantIndependent.sourceParameters_jetAbsorptionConstant_eq
#print axioms Erdos240.BakerSourceUniformConstantIndependent.sourceParameters_lemmaFourContourAbsorptionConstant_eq
#print axioms Erdos240.BakerSourceUniformConstantIndependent.jetAbsorptionConstant_pos
#print axioms Erdos240.BakerSourceUniformConstantIndependent.exists_uniform_oversizedSourceConstant
