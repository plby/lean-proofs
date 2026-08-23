/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAssemblyIndependent
import ErdosProblems.Erdos240.BakerSourceReindexCoreIndependent

/-!
# Reindexing the rational-prime source data

The project-facing normalized smallness hypothesis is stated on an arbitrary
finite index type, whereas the concrete auxiliary-function construction uses
the canonical `Fin (Fintype.card ι)` enumeration.  This file proves the exact
transport facts needed at that boundary: the logarithmic form, the old height
product, and the distinguished new height are unchanged by a finite
equivalence.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceReindexIndependent

open RationalPrimeBaker
open BakerSourceAssemblyIndependent
open BakerSourceReindexCoreIndependent

universe u v

/-- The product of normalized old heights is invariant under reindexing. -/
theorem fixedHeightProduct_sourceParameters_comp_equiv
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι)
    (old : ι → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
    (newFresh : ∀ i, old i ≠ newPrime)
    (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)) :
    (sourceParameters (old ∘ e) (fun j ↦ oldPrime (e j))
        (oldInjective.comp e.injective) newPrime newPrimePrime
        (fun j ↦ newFresh (e j)) N Nlarge).fixedHeightProduct =
      (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
        newFresh N Nlarge).fixedHeightProduct := by
  unfold VDPLParameters.fixedHeightProduct VDPLParameters.oldHeight
  change (∏ j : κ, max (Real.exp (Real.exp 1)) ((old (e j) : ℝ) + 1)) =
    ∏ i : ι, max (Real.exp (Real.exp 1)) ((old i : ℝ) + 1)
  exact normalizedOldHeight_prod_comp_equiv e old

/-- The logarithmic old-height product `OmegaOld` is invariant under the same
reindexing. -/
theorem OmegaOld_sourceParameters_comp_equiv
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι)
    (old : ι → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
    (newFresh : ∀ i, old i ≠ newPrime)
    (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)) :
    (sourceParameters (old ∘ e) (fun j ↦ oldPrime (e j))
        (oldInjective.comp e.injective) newPrime newPrimePrime
        (fun j ↦ newFresh (e j)) N Nlarge).OmegaOld =
      (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
        newFresh N Nlarge).OmegaOld := by
  unfold VDPLParameters.OmegaOld VDPLParameters.oldHeight
  change
    (∏ j : κ, Real.log
      (max (Real.exp (Real.exp 1)) ((old (e j) : ℝ) + 1))) =
    ∏ i : ι, Real.log
      (max (Real.exp (Real.exp 1)) ((old i : ℝ) + 1))
  exact log_normalizedOldHeight_prod_comp_equiv e old

/-- Since the varying height itself is unchanged, so is the combined
distinguished height used by the normalized source exponent. -/
theorem newHeight_sourceParameters_comp_equiv
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι)
    (old : ι → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
    (newFresh : ∀ i, old i ≠ newPrime)
    (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)) :
    (sourceParameters (old ∘ e) (fun j ↦ oldPrime (e j))
        (oldInjective.comp e.injective) newPrime newPrimePrime
        (fun j ↦ newFresh (e j)) N Nlarge).newHeight =
      (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
        newFresh N Nlarge).newHeight := by
  unfold VDPLParameters.newHeight
  rw [fixedHeightProduct_sourceParameters_comp_equiv e old oldPrime
    oldInjective newPrime newPrimePrime newFresh N Nlarge]
  rfl

/-- The complete exponent appearing in normalized source smallness is
literally unchanged by a coordinate equivalence. -/
theorem normalizedSourceExponentFactor_sourceParameters_comp_equiv
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι)
    (old : ι → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
    (newFresh : ∀ i, old i ≠ newPrime)
    (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)) :
    let Pfin := sourceParameters (old ∘ e) (fun j ↦ oldPrime (e j))
      (oldInjective.comp e.injective) newPrime newPrimePrime
      (fun j ↦ newFresh (e j)) N Nlarge
    let P := sourceParameters old oldPrime oldInjective newPrime newPrimePrime
      newFresh N Nlarge
    Pfin.OmegaOld * Real.log Pfin.OmegaOld * Real.log Pfin.newHeight =
      P.OmegaOld * Real.log P.OmegaOld * Real.log P.newHeight := by
  dsimp only
  rw [OmegaOld_sourceParameters_comp_equiv e old oldPrime oldInjective
      newPrime newPrimePrime newFresh N Nlarge,
    newHeight_sourceParameters_comp_equiv e old oldPrime oldInjective
      newPrime newPrimePrime newFresh N Nlarge]

/-- Exact transport of the normalized strict-smallness proposition from an
arbitrary finite old index type to an equivalent concrete index type. -/
theorem normalizedSmallness_sourceParameters_comp_equiv
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι)
    (old : ι → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
    (newFresh : ∀ i, old i ≠ newPrime)
    (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ))
    (C₀ : ℝ) (c : ι → ℤ) (d : ℤ) :
    let Pfin := sourceParameters (old ∘ e) (fun j ↦ oldPrime (e j))
      (oldInjective.comp e.injective) newPrime newPrimePrime
      (fun j ↦ newFresh (e j)) N Nlarge
    let P := sourceParameters old oldPrime oldInjective newPrime newPrimePrime
      newFresh N Nlarge
    |indexedRationalLogForm (old ∘ e) newPrime (c ∘ e) d| <
        Real.exp (-(C₀ * Pfin.OmegaOld * Real.log Pfin.OmegaOld *
          Real.log Pfin.newHeight * Real.log (N : ℝ))) ↔
      |indexedRationalLogForm old newPrime c d| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (N : ℝ))) := by
  dsimp only
  rw [BakerSourceReindexCoreIndependent.indexedRationalLogForm_comp_equiv,
    OmegaOld_sourceParameters_comp_equiv e old oldPrime oldInjective
      newPrime newPrimePrime newFresh N Nlarge,
    newHeight_sourceParameters_comp_equiv e old oldPrime oldInjective
      newPrime newPrimePrime newFresh N Nlarge]

end Erdos240.BakerSourceReindexIndependent

#print axioms Erdos240.BakerSourceReindexIndependent.OmegaOld_sourceParameters_comp_equiv
#print axioms Erdos240.BakerSourceReindexIndependent.newHeight_sourceParameters_comp_equiv
#print axioms Erdos240.BakerSourceReindexIndependent.normalizedSourceExponentFactor_sourceParameters_comp_equiv
#print axioms Erdos240.BakerSourceReindexIndependent.normalizedSmallness_sourceParameters_comp_equiv
