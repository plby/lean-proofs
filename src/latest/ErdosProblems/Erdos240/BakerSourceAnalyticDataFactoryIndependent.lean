/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceConcreteConstructionIndependent
import ErdosProblems.Erdos240.BakerSourceReindexIndependent

/-!
# Stable factory for the concrete source analytic data

The final source assembly consumes `ConcreteAnalyticSourceData`.  This file
provides a small, main-independent integration boundary for the four
concrete analytic endpoints.  In particular, the pointwise integral-grid
vanishing conclusion is converted internally to the exact Lemma-4 inner
iteration callback.
-/

noncomputable section

namespace Erdos240.BakerSourceAnalyticDataFactoryIndependent

open BakerInduction
open BakerLemma4InnerInduction
open BakerSourceAssemblyIndependent
open BakerSourceConcreteConstructionIndependent
open BakerSourceNumericalAssemblyIndependent
open BakerSourceRationalAlternativeIndependent
open BakerSourceReindexCoreIndependent
open BakerSourceReindexIndependent
open BakerSourceState
open RationalPrimeBaker

universe u

variable {oldRank : ℕ} [Nonempty (Fin oldRank)]
  {P : VDPLParameters (Fin oldRank)}
  {b : Fin oldRank → ℤ} {bLast : ℤ}

/-- Package four already-instantiated analytic source endpoints.  This is a
named constructor rather than a local structure literal so the final source
assembly is insensitive to harmless reordering of the data fields. -/
def ofFields
    (hbLast : bLast ≠ 0)
    (hintegral : ∀ J (state : LevelState P J), P.LevelOK J →
      IntegralStepInputs P state b bLast)
    (hrationalLower : ∀ J (state : LevelState P J), P.LevelOK J →
      AlgebraicRationalLowerInputs P state b bLast)
    (hupper : ∀ J (state : LevelState P J) (hJ : P.LevelOK J),
      IntegralExtrapolatedAtLevel P (g state b bLast) J →
        RationalInterpolationUpperAtLevel P (f state b bLast)
          (BakerSourceRationalAlternativeIndependent.lower
            P state b bLast) J)
    (hcomplete : ∀ J (state : LevelState P (J + 1)),
      P.LevelOK (J + 1) →
        CoprimeCompletionAtLevel P (g state b bLast) J) :
    ConcreteAnalyticSourceData P b bLast where
  last_ne_zero := hbLast
  integral := hintegral
  rationalLower := hrationalLower
  upper := hupper
  completeCoprime := hcomplete

/-- Build the integral input from the concrete pointwise Lemma-4 conclusion,
while accepting the other three analytic endpoints in their final forms. -/
def ofPointwiseIntegral
    (hbLast : bLast ≠ 0)
    (hpoint : ∀ J (state : LevelState P J), P.LevelOK J →
      ∀ t, t < terminalStage P →
        InnerInvariant P (g state b bLast) J t →
          ∀ l, 1 ≤ l → l ≤ P.lemmaFourRadius J (t + 1) →
            ∀ m, VDPLMultiIndex.weight m ≤
                P.lemmaFourBudget J (t + 1) →
              g state b bLast (l : ℂ) m = 0)
    (hrationalLower : ∀ J (state : LevelState P J), P.LevelOK J →
      AlgebraicRationalLowerInputs P state b bLast)
    (hupper : ∀ J (state : LevelState P J) (hJ : P.LevelOK J),
      IntegralExtrapolatedAtLevel P (g state b bLast) J →
        RationalInterpolationUpperAtLevel P (f state b bLast)
          (BakerSourceRationalAlternativeIndependent.lower
            P state b bLast) J)
    (hcomplete : ∀ J (state : LevelState P (J + 1)),
      P.LevelOK (J + 1) →
        CoprimeCompletionAtLevel P (g state b bLast) J) :
    ConcreteAnalyticSourceData P b bLast :=
  ofFields hbLast
    (fun J state hJ ↦ integralStepInputsOfPointwise state b bLast
      (hpoint J state hJ))
    hrationalLower hupper hcomplete

/-- Directly expose the continuation produced by the pointwise factory. -/
def continuationOfPointwiseIntegral
    (hbLast : bLast ≠ 0)
    (hpoint : ∀ J (state : LevelState P J), P.LevelOK J →
      ∀ t, t < terminalStage P →
        InnerInvariant P (g state b bLast) J t →
          ∀ l, 1 ≤ l → l ≤ P.lemmaFourRadius J (t + 1) →
            ∀ m, VDPLMultiIndex.weight m ≤
                P.lemmaFourBudget J (t + 1) →
              g state b bLast (l : ℂ) m = 0)
    (hrationalLower : ∀ J (state : LevelState P J), P.LevelOK J →
      AlgebraicRationalLowerInputs P state b bLast)
    (hupper : ∀ J (state : LevelState P J) (hJ : P.LevelOK J),
      IntegralExtrapolatedAtLevel P (g state b bLast) J →
        RationalInterpolationUpperAtLevel P (f state b bLast)
          (BakerSourceRationalAlternativeIndependent.lower
            P state b bLast) J)
    (hcomplete : ∀ J (state : LevelState P (J + 1)),
      P.LevelOK (J + 1) →
        CoprimeCompletionAtLevel P (g state b bLast) J) :
    ConcreteSourceContinuation P b bLast :=
  (ofPointwiseIntegral hbLast hpoint hrationalLower hupper hcomplete).continuation

/-! ## Reindexing-independent component assembly -/

/-- The concrete analytic construction stated only for its canonical `Fin`
old-prime coordinates.  The constant is selected once for the fixed old
family and is uniform in the varying prime, coefficients, and cutoff. -/
def HasNormalizedFinAnalyticSourceData : Prop :=
  ∀ (oldRank : ℕ) [Nonempty (Fin oldRank)] (old : Fin oldRank → ℕ),
    (oldPrime : ∀ i, (old i).Prime) →
    (oldInjective : Function.Injective old) →
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ ⦃p : ℕ⦄ (c : Fin oldRank → ℤ) (d : ℤ) (N : ℕ)
        (hp : p.Prime) (hpFresh : ∀ i, old i ≠ p)
        (hN : Real.exp 2 ≤ (N : ℝ))
        (_hc : ∀ i, (c i).natAbs ≤ N) (_hd : d.natAbs ≤ N)
        (_hdne : d ≠ 0)
        (_hform : indexedRationalLogForm old p c d ≠ 0),
        let P := sourceParameters old oldPrime oldInjective p hp hpFresh N hN
        |indexedRationalLogForm old p c d| <
            Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
              Real.log P.newHeight * Real.log (N : ℝ))) →
          Nonempty (ConcreteAnalyticSourceData P c d)

/-- A canonical-`Fin` analytic construction supplies the universe-polymorphic
component interface.  This theorem performs the only required coordinate
transport: coefficient bounds, form nonvanishing, and normalized strict
smallness are all preserved by `Fintype.equivFin`. -/
theorem normalizedConcreteSourceComponents_of_finAnalyticData
    (hsource : HasNormalizedFinAnalyticSourceData) :
    HasNormalizedConcreteSourceComponents.{u} := by
  classical
  intro ι _ _ old oldPrime oldInjective
  let : Nonempty (Fin (Fintype.card ι)) := finCardNonempty ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let oldFin : Fin (Fintype.card ι) → ℕ := old ∘ e
  let oldPrimeFin : ∀ j, (oldFin j).Prime := fun j ↦ oldPrime (e j)
  let oldInjectiveFin : Function.Injective oldFin :=
    oldInjective.comp e.injective
  obtain ⟨C₀, hC₀, hdata⟩ :=
    hsource (Fintype.card ι) oldFin oldPrimeFin oldInjectiveFin
  refine ⟨C₀, hC₀, ?_⟩
  intro p c d N hp hpFresh hN hc hd hdne hform
  dsimp only
  intro hsmall
  let freshFin : ∀ j, oldFin j ≠ p := fun j ↦ hpFresh (e j)
  let bfin : Fin (Fintype.card ι) → ℤ := c ∘ e
  have hcfin : ∀ j, (bfin j).natAbs ≤ N := fun j ↦ hc (e j)
  have hformfin : indexedRationalLogForm oldFin p bfin d ≠ 0 := by
    rw [show oldFin = old ∘ e from rfl, show bfin = c ∘ e from rfl,
      indexedRationalLogForm_comp_equiv e old p c d]
    exact hform
  have hsmallfin :
      let Pfin := sourceParameters oldFin oldPrimeFin oldInjectiveFin p hp
        freshFin N hN
      |indexedRationalLogForm oldFin p bfin d| <
        Real.exp (-(C₀ * Pfin.OmegaOld * Real.log Pfin.OmegaOld *
          Real.log Pfin.newHeight * Real.log (N : ℝ))) := by
    dsimp only
    have htransport :=
      (normalizedSmallness_sourceParameters_comp_equiv e old oldPrime
        oldInjective p hp hpFresh N hN C₀ c d).2 hsmall
    simpa only [oldFin, oldPrimeFin, oldInjectiveFin, freshFin, bfin] using
      htransport
  obtain ⟨data⟩ := hdata bfin d N hp freshFin hN hcfin hd hdne hformfin
    hsmallfin
  exact ⟨data.continuation⟩

/-- Complete main-independent bridge from canonical finite analytic data to
the uniform rational-prime logarithmic-form lower bound used by Erdős 240. -/
theorem uniformBounds_of_finAnalyticData
    (hsource : HasNormalizedFinAnalyticSourceData) :
    HasUniformRationalPrimeLogBounds.{u} :=
  uniformBounds_of_normalizedConcreteSourceChains
    (normalizedConcreteSourceChains_of_components
      (normalizedConcreteSourceComponents_of_finAnalyticData hsource))

end Erdos240.BakerSourceAnalyticDataFactoryIndependent

#print axioms Erdos240.BakerSourceAnalyticDataFactoryIndependent.ofFields
#print axioms Erdos240.BakerSourceAnalyticDataFactoryIndependent.ofPointwiseIntegral
#print axioms Erdos240.BakerSourceAnalyticDataFactoryIndependent.continuationOfPointwiseIntegral
#print axioms Erdos240.BakerSourceAnalyticDataFactoryIndependent.normalizedConcreteSourceComponents_of_finAnalyticData
#print axioms Erdos240.BakerSourceAnalyticDataFactoryIndependent.uniformBounds_of_finAnalyticData
