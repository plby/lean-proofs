/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZShellZeroReplacementNumerics
import ErdosProblems.Erdos1165.HLOZShellZeroReplacementWindows
import ErdosProblems.Erdos1165.TilingTypedShellZeroReplacement

/-!
# Global typed shell-zero replacement adapter

This module joins the two independent parts of the source-correct initial
shell argument:

* exact finite `I₁`-to-`I₀` product identities on every source atom; and
* globally disjoint replacement events, indexed by their complete prefix at
  the newly created favourite rank.

The quantitative input below is an
`HLOZShellZeroReplacementProduct.ReplacementAtomProductCertificate`.
Thus the input records literal product masses and their common external
factor; it is not an assumption of the desired path-event inequality.
The disjoint global summation is supplied by the checked creation-prefix
construction.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZTypedShellZeroGlobalAdapter

open HLOZShellZeroReplacementProduct HLOZShellZeroReplacementNumerics
open HLOZShellZeroReplacementWindows TilingTypedShellZeroReplacement
open HLOZPathEvents HLOZProposition48Candidates

noncomputable section

/-- A fixed nonnegative local-ratio constant produces the exact global
replacement coefficient, with no loss proportional to the number of
retained traces.  Pairwise disjointness of the replacement events follows
from their injective complete creation-prefix codes. -/
theorem measure_source_le_fixedReplacementCost_of_creationPrefixAtomProducts
    {Index : Type*} [Countable Index]
    (mu : Measure WalkPath) [IsProbabilityMeasure mu]
    (source : Set WalkPath)
    (sourceAtom replacement : Index → Set WalkPath)
    (code : Index → CreationPrefixCode)
    (C : ℝ) (level rank shellScale : ℕ)
    (hcode : Function.Injective code)
    (hsource : source ⊆ ⋃ z, sourceAtom z)
    (hmeasurable : ∀ z, MeasurableSet (replacement z))
    (hsubset : ∀ z,
      replacement z ⊆ creationPrefixAtom level rank (code z))
    (atom : ∀ z, ReplacementAtomProductCertificate
      mu (sourceAtom z) (replacement z)
        (replacementBase C ^ (initialBudget48 shellScale + 1))) :
    mu source ≤ fixedReplacementCost C shellScale := by
  let cert :=
    globalDisjointReplacementCertificateOfCreationPrefixAtomProducts
      mu source sourceAtom replacement code
        (replacementBase C ^ (initialBudget48 shellScale + 1))
        level rank hcode hsource hmeasurable hsubset atom
  have h := measure_le_of_globalDisjointReplacementCertificate
    mu source
      (ENNReal.ofReal
        (replacementBase C ^ (initialBudget48 shellScale + 1))) cert
  simpa only [fixedReplacementCost] using h

/-- Canonical simple-random-walk specialization of the global typed
replacement estimate. -/
theorem simpleRandomWalk_source_le_fixedReplacementCost_of_creationPrefixAtomProducts
    {Index : Type*} [Countable Index]
    (source : Set WalkPath)
    (sourceAtom replacement : Index → Set WalkPath)
    (code : Index → CreationPrefixCode)
    (C : ℝ) (level rank shellScale : ℕ)
    (hcode : Function.Injective code)
    (hsource : source ⊆ ⋃ z, sourceAtom z)
    (hmeasurable : ∀ z, MeasurableSet (replacement z))
    (hsubset : ∀ z,
      replacement z ⊆ creationPrefixAtom level rank (code z))
    (atom : ∀ z, ReplacementAtomProductCertificate
      simpleRandomWalk (sourceAtom z) (replacement z)
        (replacementBase C ^ (initialBudget48 shellScale + 1))) :
    simpleRandomWalk source ≤ fixedReplacementCost C shellScale := by
  exact measure_source_le_fixedReplacementCost_of_creationPrefixAtomProducts
    simpleRandomWalk source sourceAtom replacement code C level rank
      shellScale hcode hsource hmeasurable hsubset atom

lemma shellZeroLocalRatioConstant_nonneg :
    0 ≤ shellZeroLocalRatioConstant := by
  unfold shellZeroLocalRatioConstant
  positivity

/-- The literal-window constant proved in
`HLOZShellZeroReplacementWindows` still gives a strictly subunit,
summable replacement coefficient.  No unjustified `C ≤ 4/3` estimate is
used. -/
theorem tsum_literalShellZeroReplacementCost_ne_top :
    ∑' shellScale,
        fixedReplacementCost shellZeroLocalRatioConstant shellScale ≠ ∞ :=
  tsum_fixedReplacementCost_ne_top shellZeroLocalRatioConstant_nonneg

/-- Bundled source-correct shell-zero screen.  The hidden index is a
countable family of stopped retained traces.  Its quantitative field is the
finite stopped-coordinate comparison inside
`StoppedFiberReplacementAtomFamily`, not the desired event estimate. -/
structure LiteralShellZeroStoppedFiberScreen
    (source : Set WalkPath) (shellScale : ℕ) where
  Index : Type*
  indexCountable : Countable Index
  family : StoppedFiberReplacementAtomFamily Index
    (replacementBase shellZeroLocalRatioConstant ^
      (initialBudget48 shellScale + 1))
  source_subset : source ⊆ ⋃ z, family.sourceAtom z
  jump : ThresholdJumpReplacementFamily family.replacementAtom

/-- Fully specialized source-event bound at the checked literal local-ratio
constant.  Its hypotheses are only exact atom product identities and the
pathwise creation-prefix coverage data. -/
theorem simpleRandomWalk_source_le_literalShellZeroReplacementCost
    {Index : Type*} [Countable Index]
    (source : Set WalkPath)
    (sourceAtom replacement : Index → Set WalkPath)
    (code : Index → CreationPrefixCode)
    (level rank shellScale : ℕ)
    (hcode : Function.Injective code)
    (hsource : source ⊆ ⋃ z, sourceAtom z)
    (hmeasurable : ∀ z, MeasurableSet (replacement z))
    (hsubset : ∀ z,
      replacement z ⊆ creationPrefixAtom level rank (code z))
    (atom : ∀ z, ReplacementAtomProductCertificate
      simpleRandomWalk (sourceAtom z) (replacement z)
        (replacementBase shellZeroLocalRatioConstant ^
          (initialBudget48 shellScale + 1))) :
    simpleRandomWalk source ≤
      fixedReplacementCost shellZeroLocalRatioConstant shellScale := by
  exact
    simpleRandomWalk_source_le_fixedReplacementCost_of_creationPrefixAtomProducts
      source sourceAtom replacement code shellZeroLocalRatioConstant
      level rank shellScale hcode hsource
      hmeasurable hsubset atom

/-- Compact stopped-fibre form.  Here exact cylinder-mass factorization,
replacement measurability, and the atomwise probability comparison have
already been derived by `StoppedFiberReplacementAtomFamily`; only literal
source coverage and the pathwise threshold-jump certificate remain. -/
theorem simpleRandomWalk_source_le_literalShellZeroReplacementCost_of_stoppedFibers
    {Index : Type*} [Countable Index]
    (shellScale : ℕ)
    (data : StoppedFiberReplacementAtomFamily Index
      (replacementBase shellZeroLocalRatioConstant ^
        (initialBudget48 shellScale + 1)))
    (source : Set WalkPath)
    (hsource : source ⊆ ⋃ z, data.sourceAtom z)
    (jump : ThresholdJumpReplacementFamily data.replacementAtom) :
    simpleRandomWalk source ≤
      fixedReplacementCost shellZeroLocalRatioConstant shellScale := by
  have h := measure_le_of_globalDisjointReplacementCertificate
    simpleRandomWalk source
      (ENNReal.ofReal
        (replacementBase shellZeroLocalRatioConstant ^
          (initialBudget48 shellScale + 1)))
      (globalStoppedFiberReplacementCertificateOfSubset
        (replacementBase shellZeroLocalRatioConstant ^
          (initialBudget48 shellScale + 1)) data source hsource jump)
  simpa only [fixedReplacementCost] using h

/-- The bundled literal screen gives the exact fixed-ratio global bound. -/
theorem LiteralShellZeroStoppedFiberScreen.measure_le
    {source : Set WalkPath} {shellScale : ℕ}
    (screen : LiteralShellZeroStoppedFiberScreen source shellScale) :
    simpleRandomWalk source ≤
      fixedReplacementCost shellZeroLocalRatioConstant shellScale := by
  let _ : Countable screen.Index := screen.indexCountable
  exact
    simpleRandomWalk_source_le_literalShellZeroReplacementCost_of_stoppedFibers
      shellScale screen.family source screen.source_subset screen.jump

/-- The compact stopped-fibre certificates also give summability directly.
This is the intended interface for adding the source-correct shell-zero
event to the upper exceptional family. -/
theorem tsum_simpleRandomWalk_source_ne_top_of_stoppedFibers
    {Index : Type*} [Countable Index]
    (source : ℕ → Set WalkPath)
    (data : ∀ shellScale, StoppedFiberReplacementAtomFamily Index
      (replacementBase shellZeroLocalRatioConstant ^
        (initialBudget48 shellScale + 1)))
    (hsource : ∀ shellScale,
      source shellScale ⊆ ⋃ z, (data shellScale).sourceAtom z)
    (jump : ∀ shellScale,
      ThresholdJumpReplacementFamily (data shellScale).replacementAtom) :
    ∑' shellScale, simpleRandomWalk (source shellScale) ≠ ∞ := by
  apply ne_top_of_le_ne_top tsum_literalShellZeroReplacementCost_ne_top
  apply ENNReal.tsum_le_tsum
  intro shellScale
  exact
    simpleRandomWalk_source_le_literalShellZeroReplacementCost_of_stoppedFibers
      shellScale (data shellScale) (source shellScale)
      (hsource shellScale) (jump shellScale)

/-- A family of literal shell-zero source events is summable once every
scale has the exact typed creation-prefix product certificate.  This is the
direct Borel--Cantelli-facing conclusion: neither an atomwise transition
bound nor a uniform conditional trace estimate is assumed. -/
theorem tsum_simpleRandomWalk_source_ne_top_of_creationPrefixAtomProducts
    {Index : Type*} [Countable Index]
    (source : ℕ → Set WalkPath)
    (sourceAtom replacement : ℕ → Index → Set WalkPath)
    (code : ℕ → Index → CreationPrefixCode)
    (level rank : ℕ → ℕ)
    (hcode : ∀ shellScale, Function.Injective (code shellScale))
    (hsource : ∀ shellScale,
      source shellScale ⊆ ⋃ z, sourceAtom shellScale z)
    (hmeasurable : ∀ shellScale z,
      MeasurableSet (replacement shellScale z))
    (hsubset : ∀ shellScale z,
      replacement shellScale z ⊆
        creationPrefixAtom (level shellScale) (rank shellScale)
          (code shellScale z))
    (atom : ∀ shellScale z, ReplacementAtomProductCertificate
      simpleRandomWalk (sourceAtom shellScale z)
        (replacement shellScale z)
        (replacementBase shellZeroLocalRatioConstant ^
          (initialBudget48 shellScale + 1))) :
    ∑' shellScale, simpleRandomWalk (source shellScale) ≠ ∞ := by
  apply ne_top_of_le_ne_top tsum_literalShellZeroReplacementCost_ne_top
  apply ENNReal.tsum_le_tsum
  intro shellScale
  exact simpleRandomWalk_source_le_literalShellZeroReplacementCost
    (source shellScale) (sourceAtom shellScale)
      (replacement shellScale) (code shellScale)
      (level shellScale) (rank shellScale) shellScale
      (hcode shellScale) (hsource shellScale)
      (hmeasurable shellScale) (hsubset shellScale) (atom shellScale)

end

end Erdos1165.HLOZTypedShellZeroGlobalAdapter
