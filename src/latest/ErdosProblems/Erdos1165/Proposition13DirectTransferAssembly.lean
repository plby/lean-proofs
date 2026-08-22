/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.Proposition13LiteralAssembly
import ErdosProblems.Erdos1165.LowerConclusion

/-!
# Direct chronological-profile assembly for Proposition 1.3

The source-correct Appendix A.6 construction integrates the intermediate
spatial endpoints of a chronological radial-boundary word.  Its natural
walk-facing output is therefore `AnnularOnePointProfileTransfer`, rather than
the older fixed-endpoint `FullSkeletonProfileFamily` interface.

This file combines that direct transfer with the literal asymmetric pair data
and the unconditional terminal comparison.  It is deliberately a thin
adapter: all probability estimates remain in the modules that construct its
two input fields.
-/

open Filter MeasureTheory Set

namespace Erdos1165.Proposition13DirectTransferAssembly

noncomputable section

open AppendixA11A12ScaleCertificate AppendixFirstMoment
open AppendixTerminalMarkedAssembly GaussianGeometricOnePoint
open LowerConclusion
open Proposition13Assembly Proposition13LiteralAssembly Proposition13Scales

/-- The two genuinely walk-facing inputs at one selected scale.  The terminal
marked comparison is already unconditional and hence is not stored here. -/
structure DirectAnnularScaleData (delta : ℝ) (n : ℕ) : Type 1 where
  onePoint : AnnularOnePointProfileTransfer delta n
  pair : LiteralPairData delta n

/-- The direct chronological one-point transfer, unconditional terminal
comparison, and literal asymmetric pair comparison give the complete annular
certificate at every sufficiently large selected scale. -/
theorem eventually_annularComparisons_of_directData
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      DirectAnnularScaleData delta n → AnnularComparisons delta n := by
  filter_upwards
      [eventually_annularComparisons_onePointProfile_of_transfer hdelta,
       eventually_annularComparisons_terminalThick hdelta,
       eventually_pairMoment_of_literalPairData hdelta]
      with n honePoint hterminal hpair
  intro data
  exact {
    onePointProfile := honePoint data.onePoint
    terminalThick := hterminal
    pairMoment := hpair data.pair }

/-- Eventual existence of the source-correct chronological one-point and
asymmetric pair inputs. -/
def HasDirectAnnularScaleData : Prop :=
  ∀ delta : ℝ, 0 < delta → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    Nonempty (DirectAnnularScaleData delta n)

/-- Independent eventual constructions of the chronological one-point
transfer and the asymmetric pair data assemble into the direct scale
package.  This keeps the two walk decompositions separate until the final
Proposition 1.3 adapter. -/
theorem hasDirectAnnularScaleData_of_eventually_nonempty
    (honePoint : ∀ delta : ℝ, 0 < delta → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (AnnularOnePointProfileTransfer delta n))
    (hpair : ∀ delta : ℝ, 0 < delta → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (LiteralPairData delta n)) :
    HasDirectAnnularScaleData := by
  intro delta hdelta
  obtain ⟨N₁, hN₁⟩ := honePoint delta hdelta
  obtain ⟨N₂, hN₂⟩ := hpair delta hdelta
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  exact ⟨{
    onePoint := Classical.choice (hN₁ n hn₁)
    pair := Classical.choice (hN₂ n hn₂) }⟩

/-- Filter-form adapter for the two eventual literal constructions.  This is
the form produced by the chronological one-point and asymmetric pair source
modules, so the final lower assembly does not need to unpack `atTop` by hand. -/
theorem hasDirectAnnularScaleData_of_eventually
    (honePoint : ∀ delta : ℝ, 0 < delta →
      ∀ᶠ n : ℕ in atTop,
        Nonempty (AnnularOnePointProfileTransfer delta n))
    (hpair : ∀ delta : ℝ, 0 < delta →
      ∀ᶠ n : ℕ in atTop, Nonempty (LiteralPairData delta n)) :
    HasDirectAnnularScaleData := by
  apply hasDirectAnnularScaleData_of_eventually_nonempty
  · intro delta hdelta
    exact eventually_atTop.mp (honePoint delta hdelta)
  · intro delta hdelta
    exact eventually_atTop.mp (hpair delta hdelta)

theorem hasAnnularComparisons_of_directData
    (hdirect : HasDirectAnnularScaleData) : HasAnnularComparisons := by
  intro delta hdelta
  obtain ⟨N₁, hN₁⟩ := hdirect delta hdelta
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (eventually_annularComparisons_of_directData hdelta)
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  exact ⟨hN₂ n hn₂ (Classical.choice (hN₁ n hn₁))⟩

/-- Proposition 1.3 from the source-correct chronological profile transfer
and asymmetric pair construction. -/
theorem hasPlanarMaximumLowerDeviation_of_directData
    (hdirect : HasDirectAnnularScaleData) :
    HasPlanarMaximumLowerDeviation simpleRandomWalk :=
  hasPlanarMaximumLowerDeviation_of_annularComparisons
    (hasAnnularComparisons_of_directData hdirect)

/-- The direct chronological one-point and asymmetric pair constructions
already imply the complete almost-sure lower half of the HLOZ conclusion. -/
theorem ae_frequently_favoriteCount_ge_three_of_directData
    (hdirect : HasDirectAnnularScaleData) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∃ᶠ n in atTop, 3 ≤ favoriteCount s n :=
  ae_frequently_favoriteCount_ge_three_of_lowerDeviation
    (hasPlanarMaximumLowerDeviation_of_directData hdirect)

/-- The eventual literal one-point and pair constructors imply the complete
almost-sure lower half directly. -/
theorem ae_frequently_favoriteCount_ge_three_of_eventually_nonempty
    (honePoint : ∀ delta : ℝ, 0 < delta →
      ∀ᶠ n : ℕ in atTop,
        Nonempty (AnnularOnePointProfileTransfer delta n))
    (hpair : ∀ delta : ℝ, 0 < delta →
      ∀ᶠ n : ℕ in atTop, Nonempty (LiteralPairData delta n)) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∃ᶠ n in atTop, 3 ≤ favoriteCount s n :=
  ae_frequently_favoriteCount_ge_three_of_directData
    (hasDirectAnnularScaleData_of_eventually honePoint hpair)

end

end Erdos1165.Proposition13DirectTransferAssembly
