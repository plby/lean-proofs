/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.TerminalExcursionDisintegration
import ErdosProblems.Erdos1165.TerminalKernelRadial
import ErdosProblems.Erdos1165.BoundaryStoppedHarnack
import ErdosProblems.Erdos1165.MarkedTerminalDisintegration
import ErdosProblems.Erdos1165.Proposition13Scales

/-!
# The terminal-thickness field of the Proposition 1.3 scale certificate

This file specializes the checked Bernoulli--geometric terminal calculation
to the literal stopped events used by
`Proposition13Scales.AnnularComparisons.terminalThick`.

The primary stochastic interface exposes the complete complementary
outer-to-inner skeleton, including every next outer endpoint.  It compares
the joint visit-count/endpoint kernel pointwise and then sums against an
arbitrary nonnegative skeleton weight.  In particular, no successful event
is assumed measurable at the first terminal entrance, and no exact product
law on a coarse fixed-horizon fibre is assumed.  The terminal vector uses
`requiredTerminalCount`; pathwise global-exit geometry is responsible for
showing that its final coordinate is not sentinel-truncated.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Erdos1165.AppendixTerminalThick

open Proposition13Assembly Proposition13Scales

noncomputable section

/-! ## Literal boundary-stopped terminal comparison -/

/-- The sharp boundary Harnack theorem at the exact two terminal radii
`r_{n,n}=n^9` and `r_{n,n+1}=n^6`.  The conclusion uses the literal
half-open terminal segment: it stops at the next visit to
`terminalOuterBoundary`, rather than on the first step outside a closed
disc. -/
theorem conditionStar_terminalBoundaryStoppedHitKernel
    {Entrance : Type*} [Fintype Entrance]
    (n : ℕ) (hn : 2 ≤ n) {lower : ℝ} (center q : Point)
    (entrance : Entrance → Point)
    (hq : q ∈ TerminalExcursionPathwise.terminalOuterBoundary n center)
    (hentrance : ∀ u,
      entrance u ∈ TerminalExcursionPathwise.terminalInnerBoundary n center)
    (hlower : 0 < lower)
    (href : ∀ u, lower ≤
      PotentialConvergence.planarPotentialKernel (q - center) -
        PotentialConvergence.planarPotentialKernel (entrance u - center) -
          BoundaryStoppedHarnack.literalBoundaryError (n ^ 9)) :
    AppendixDecoupling.ConditionStar
      (BoundaryStoppedHarnack.literalBoundaryHitError
        (n ^ 9) (n ^ 6 - 1) lower)
      (fun u ↦ TerminalExcursionDisintegration.boundaryStoppedHitKernel
        (TerminalExcursionPathwise.terminalOuterBoundary n center)
        center (entrance u)) := by
  have hpow6 : 2 ^ 6 ≤ n ^ 6 := Nat.pow_le_pow_left hn 6
  have hpow9 : 2 ^ 9 ≤ n ^ 9 := Nat.pow_le_pow_left hn 9
  have hR : 5 ≤ n ^ 9 := by omega
  have hseparated : n ^ 6 - 1 + 2 ≤ n ^ 9 := by
    have hpow3 : 2 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
    calc
      n ^ 6 - 1 + 2 = n ^ 6 + 1 := by omega
      _ ≤ n ^ 6 + n ^ 6 := by omega
      _ = n ^ 6 * 2 := by ring
      _ ≤ n ^ 6 * n ^ 3 := Nat.mul_le_mul_left _ (by omega)
      _ = n ^ 9 := by ring
  have hrho : 4 ≤ n ^ 6 - 1 := by omega
  have houter : TerminalExcursionPathwise.terminalOuterBoundary n center =
      ThickPoint.discBoundary center ((n ^ 9 : ℕ) : ℝ) := by
    simp [TerminalExcursionPathwise.terminalOuterBoundary,
      ThickPoint.scaleRadius, ThickPoint.regularRadius]
  have hinner : TerminalExcursionPathwise.terminalInnerBoundary n center =
      ThickPoint.discBoundary center (((n ^ 6 - 1 : ℕ) : ℝ) + 1) := by
    rw [TerminalExcursionPathwise.terminalInnerBoundary,
      ThickPoint.scaleRadius_succ_self]
    congr 2
    norm_cast
    omega
  have hstar :=
    BoundaryStoppedHarnack.conditionStar_centeredTerminalBoundaryStoppedHitKernel
      (n ^ 9) (n ^ 6 - 1) center q entrance hR hseparated
      (by simpa only [← houter] using hq)
      (by intro u; simpa only [← hinner] using hentrance u)
      hrho hlower href
  have hkernel :
      BoundaryStoppedHarnack.centeredBoundaryStoppedHitKernel
          (n ^ 9) center entrance =
        (fun u ↦ TerminalExcursionDisintegration.boundaryStoppedHitKernel
          (TerminalExcursionPathwise.terminalOuterBoundary n center)
          center (entrance u)) := by
    funext u
    rw [houter]
    rfl
  rw [hkernel] at hstar
  exact hstar

/-- The literal terminal Harnack estimate, combined with the exact
Bernoulli--positive-geometric one-excursion law, supplies a standalone vector
kernel comparison.  No independence of a future entrance vector is claimed
here.  The future-dependent Appendix-A.7 event is handled below by the joint
marked endpoint kernel and complementary-skeleton decomposition. -/
theorem terminalKernelComparison_terminalBoundaryStopped
    {Entrance : Type*} [Fintype Entrance]
    {scale : ℕ} (hscale : 2 ≤ scale)
    {profileDelta thickDelta qHit p epsilon lower : ℝ}
    (center qBoundary : Point) (entrance : Entrance → Point)
    (hqBoundary : qBoundary ∈
      TerminalExcursionPathwise.terminalOuterBoundary scale center)
    (hentrance : ∀ u, entrance u ∈
      TerminalExcursionPathwise.terminalInnerBoundary scale center)
    (hlower : 0 < lower)
    (hrefPotential : ∀ u, lower ≤
      PotentialConvergence.planarPotentialKernel (qBoundary - center) -
        PotentialConvergence.planarPotentialKernel (entrance u - center) -
          BoundaryStoppedHarnack.literalBoundaryError (scale ^ 9))
    (hhit0 : ∀ u, 0 ≤
      TerminalExcursionDisintegration.boundaryStoppedHitKernel
        (TerminalExcursionPathwise.terminalOuterBoundary scale center)
        center (entrance u))
    (hhitHalf : ∀ u,
      TerminalExcursionDisintegration.boundaryStoppedHitKernel
        (TerminalExcursionPathwise.terminalOuterBoundary scale center)
        center (entrance u) ≤ 1 / 2)
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hepsilon : epsilon = BoundaryStoppedHarnack.literalBoundaryHitError
      (scale ^ 9) (scale ^ 6 - 1) lower)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (reference : Fin (AppendixLocalTime.requiredTerminalCount
      scale profileDelta) → Entrance)
    (hrefHit : ∀ j,
      TerminalExcursionDisintegration.boundaryStoppedHitKernel
        (TerminalExcursionPathwise.terminalOuterBoundary scale center)
        center (entrance (reference j)) = qHit)
    (hq0 : 0 ≤ qHit) (hq1 : qHit ≤ 1)
    (hsmall : (1 + epsilon) ^
      AppendixLocalTime.requiredTerminalCount scale profileDelta ≤ 2) :
    AppendixLocalTimeTransfer.TerminalKernelComparison
      (2 * (AppendixLocalTime.requiredTerminalCount scale profileDelta : ℝ) *
        epsilon)
      (AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
        scale profileDelta qHit p hq0 hq1 hp0 hp1 thickDelta)
      (TerminalKernelRadial.terminalVisitKernel
        (fun _ : Fin (AppendixLocalTime.requiredTerminalCount
            scale profileDelta) ↦ fun u ↦
          TerminalExcursionDisintegration.boundaryStoppedHitKernel
          (TerminalExcursionPathwise.terminalOuterBoundary scale center)
          center (entrance u))
        (fun _ : Fin (AppendixLocalTime.requiredTerminalCount
            scale profileDelta) ↦ p)
        (fun _ u ↦ hhit0 u)
        (fun _ u ↦ (hhitHalf u).trans (by norm_num))
        (fun _ ↦ hp0) (fun _ ↦ hp1)
        {v : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ |
          ThickPoint.thickThreshold scale thickDelta ≤
          AppendixLocalTime.totalVisits v}) := by
  subst epsilon
  apply
    TerminalKernelRadial.terminalKernelComparison_referenceSuccess_of_visitHit_conditionStar
      (fun _ : Fin (AppendixLocalTime.requiredTerminalCount
          scale profileDelta) ↦ fun u ↦
        TerminalExcursionDisintegration.boundaryStoppedHitKernel
        (TerminalExcursionPathwise.terminalOuterBoundary scale center)
        center (entrance u))
      (fun _ u ↦ hhit0 u) (fun _ u ↦ hhitHalf u)
      hp0 hp1 hepsilon0 hepsilon1
      (fun _ ↦ conditionStar_terminalBoundaryStoppedHitKernel scale hscale
        center qBoundary entrance hqBoundary hentrance hlower hrefPotential)
      reference hrefHit hq0 hq1 hsmall

/-! ## Full complementary-skeleton terminal reduction -/

/-- Strongest coefficient-level form of the full-skeleton reduction.  The
caller may establish the retained reference coefficient by any sharper
concentration or Poisson-kernel estimate; no prescribed split of the error
budget is built into this statement. -/
theorem event_terminal_lower_of_markedStoppedData_of_coefficient
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (successful thick : Set Omega)
    (scale : ℕ) (profileDelta thickDelta q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (coefficient : ℝ)
    (hcoefficient : coefficient ≤
      (1 - eta) ^ (AppendixLocalTime.requiredTerminalCount scale profileDelta) *
        AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
          scale profileDelta q p hq0 hq1 hp0 hp1 thickDelta)
    (skeletonWeight : Data →
      (Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) →
        Entrance) →
      (Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) →
        Exit) → ℝ≥0∞)
    (skeletonKernel :
      Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) →
        Entrance → Exit → ℝ≥0∞)
    (markedKernel :
      Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) →
        Entrance → ℕ → Exit → ℝ≥0∞)
    (hlower : MarkedTerminalDisintegration.MarkedKernelLower
      (fun _ ↦ ENNReal.ofReal (1 - eta))
      (fun _ k ↦ ENNReal.ofReal (AppendixLocalTime.visitMass q p k))
      skeletonKernel markedKernel)
    (hdecompose :
      MarkedTerminalDisintegration.MarkedStoppedDataLowerDecomposition
        mu successful thick skeletonWeight skeletonKernel markedKernel
        {v | ThickPoint.thickThreshold scale thickDelta ≤
          AppendixLocalTime.totalVisits v}) :
    coefficient * mu.real successful ≤ mu.real thick := by
  have hmarked :=
    MarkedTerminalDisintegration.hlozTerminal_event_real_lower_of_markedStoppedData
      mu successful thick scale profileDelta thickDelta q p
      hq0 hq1 hp0 hp1 eta heta0 heta1 skeletonWeight skeletonKernel
      markedKernel hlower hdecompose
  exact (mul_le_mul_of_nonneg_right hcoefficient measureReal_nonneg).trans hmarked

/-- Appendix A.7 from the honest joint visit-count/outer-endpoint kernel.

The arbitrary nonnegative `skeletonWeight` retains the entire complementary
outer-to-inner skeleton, including the global-exit horizon, every multiscale
profile constraint, and all future outer endpoints.  Thus this theorem does
not condition the future-dependent successful event at the first terminal
entrance.  The only probabilistic input is the pointwise marked-kernel lower
bound, coordinate by coordinate. -/
theorem event_terminal_lower_of_markedStoppedData
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (successful thick : Set Omega)
    {scale : ℕ} (hscale : 1 ≤ scale)
    (profileDelta thickDelta q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < AppendixLocalTime.requiredHLOZTerminalMargin
      scale profileDelta thickDelta q p)
    (hratio : AppendixLocalTime.requiredTerminalVisitVariance
        scale profileDelta q p /
      (AppendixLocalTime.requiredHLOZTerminalMargin
        scale profileDelta thickDelta q p) ^ 2 ≤ (scale : ℝ)⁻¹)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hlossInv :
      (AppendixLocalTime.requiredTerminalCount scale profileDelta : ℝ) * eta ≤
        (scale : ℝ)⁻¹)
    (skeletonWeight : Data →
      (Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) →
        Entrance) →
      (Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) →
        Exit) → ℝ≥0∞)
    (skeletonKernel :
      Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) →
        Entrance → Exit → ℝ≥0∞)
    (markedKernel :
      Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) →
        Entrance → ℕ → Exit → ℝ≥0∞)
    (hlower : MarkedTerminalDisintegration.MarkedKernelLower
      (fun _ ↦ ENNReal.ofReal (1 - eta))
      (fun _ k ↦ ENNReal.ofReal (AppendixLocalTime.visitMass q p k))
      skeletonKernel markedKernel)
    (hdecompose :
      MarkedTerminalDisintegration.MarkedStoppedDataLowerDecomposition
        mu successful thick skeletonWeight skeletonKernel markedKernel
        {v | ThickPoint.thickThreshold scale thickDelta ≤
          AppendixLocalTime.totalVisits v}) :
    (1 - 2 * (scale : ℝ)⁻¹) * mu.real successful ≤ mu.real thick := by
  let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
  have href : 1 - (scale : ℝ)⁻¹ ≤
      AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
        scale profileDelta q p hq0 hq1 hp0 hp1 thickDelta :=
    AppendixLocalTime.required_hlozThreshold_probability_ge_one_sub_inv
      scale profileDelta thickDelta q p hq0 hq1 hp0 hp1 hmargin hratio
  have hinv0 : 0 ≤ (scale : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg scale)
  have hscaleReal : (1 : ℝ) ≤ scale := by exact_mod_cast hscale
  have hinv1 : (scale : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hscaleReal
  have hpowBernoulli :
      1 - (m : ℝ) * eta ≤ (1 - eta) ^ m :=
    AppendixDecoupling.one_sub_nat_mul_le_pow_one_sub heta1 m
  have hpow : 1 - (scale : ℝ)⁻¹ ≤ (1 - eta) ^ m :=
    (sub_le_sub_left hlossInv 1).trans hpowBernoulli
  have hbase0 : 0 ≤ 1 - (scale : ℝ)⁻¹ := sub_nonneg.mpr hinv1
  have hpow0 : 0 ≤ (1 - eta) ^ m :=
    pow_nonneg (sub_nonneg.mpr heta1) m
  have hfactor : 1 - 2 * (scale : ℝ)⁻¹ ≤
      (1 - eta) ^ m *
        AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
          scale profileDelta q p hq0 hq1 hp0 hp1 thickDelta := by
    calc
      1 - 2 * (scale : ℝ)⁻¹ ≤
          (1 - (scale : ℝ)⁻¹) * (1 - (scale : ℝ)⁻¹) := by
            nlinarith [sq_nonneg ((scale : ℝ)⁻¹)]
      _ ≤ (1 - eta) ^ m *
          AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
            scale profileDelta q p hq0 hq1 hp0 hp1 thickDelta :=
        mul_le_mul hpow href hbase0 hpow0
  have hmarked :=
    MarkedTerminalDisintegration.hlozTerminal_event_real_lower_of_markedStoppedData
      mu successful thick scale profileDelta thickDelta q p
      hq0 hq1 hp0 hp1 eta heta0 heta1 skeletonWeight skeletonKernel
      markedKernel hlower hdecompose
  exact (mul_le_mul_of_nonneg_right hfactor measureReal_nonneg).trans hmarked

/-- The numerically natural half-loss form of Appendix A.7.  It is enough
that the accumulated marked Poisson-kernel loss is at most `1/4`; requiring
it to be of order `scale⁻¹` would be unnecessarily strong.  The independent
terminal concentration loss is at most `scale⁻¹ ≤ 1/4`, so the two retained
factors are each at least `3/4` and their product is at least `1/2`. -/
theorem event_terminal_half_lower_of_markedStoppedData
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (successful thick : Set Omega)
    {scale : ℕ} (hscale : 4 ≤ scale)
    (profileDelta thickDelta q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < AppendixLocalTime.requiredHLOZTerminalMargin
      scale profileDelta thickDelta q p)
    (hratio : AppendixLocalTime.requiredTerminalVisitVariance
        scale profileDelta q p /
      (AppendixLocalTime.requiredHLOZTerminalMargin
        scale profileDelta thickDelta q p) ^ 2 ≤ (scale : ℝ)⁻¹)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hlossQuarter :
      (AppendixLocalTime.requiredTerminalCount scale profileDelta : ℝ) * eta ≤
        1 / 4)
    (skeletonWeight : Data →
      (Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) →
        Entrance) →
      (Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) →
        Exit) → ℝ≥0∞)
    (skeletonKernel :
      Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) →
        Entrance → Exit → ℝ≥0∞)
    (markedKernel :
      Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) →
        Entrance → ℕ → Exit → ℝ≥0∞)
    (hlower : MarkedTerminalDisintegration.MarkedKernelLower
      (fun _ ↦ ENNReal.ofReal (1 - eta))
      (fun _ k ↦ ENNReal.ofReal (AppendixLocalTime.visitMass q p k))
      skeletonKernel markedKernel)
    (hdecompose :
      MarkedTerminalDisintegration.MarkedStoppedDataLowerDecomposition
        mu successful thick skeletonWeight skeletonKernel markedKernel
        {v | ThickPoint.thickThreshold scale thickDelta ≤
          AppendixLocalTime.totalVisits v}) :
    (1 / 2 : ℝ) * mu.real successful ≤ mu.real thick := by
  let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
  have hrefRaw : 1 - (scale : ℝ)⁻¹ ≤
      AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
        scale profileDelta q p hq0 hq1 hp0 hp1 thickDelta :=
    AppendixLocalTime.required_hlozThreshold_probability_ge_one_sub_inv
      scale profileDelta thickDelta q p hq0 hq1 hp0 hp1 hmargin hratio
  have hscaleReal : (4 : ℝ) ≤ scale := by exact_mod_cast hscale
  have hscalePos : (0 : ℝ) < scale := by positivity
  have hinvQuarter : (scale : ℝ)⁻¹ ≤ 1 / 4 := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hscaleReal
  have href : (3 / 4 : ℝ) ≤
      AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
        scale profileDelta q p hq0 hq1 hp0 hp1 thickDelta := by
    calc
      (3 / 4 : ℝ) = 1 - 1 / 4 := by norm_num
      _ ≤ 1 - (scale : ℝ)⁻¹ := sub_le_sub_left hinvQuarter 1
      _ ≤ _ := hrefRaw
  have hpowBernoulli :
      1 - (m : ℝ) * eta ≤ (1 - eta) ^ m :=
    AppendixDecoupling.one_sub_nat_mul_le_pow_one_sub heta1 m
  have hpow : (3 / 4 : ℝ) ≤ (1 - eta) ^ m := by
    calc
      (3 / 4 : ℝ) = 1 - 1 / 4 := by norm_num
      _ ≤ 1 - (m : ℝ) * eta := sub_le_sub_left hlossQuarter 1
      _ ≤ _ := hpowBernoulli
  have hpow0 : 0 ≤ (1 - eta) ^ m :=
    pow_nonneg (sub_nonneg.mpr heta1) m
  have hfactor : (1 / 2 : ℝ) ≤
      (1 - eta) ^ m *
        AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
          scale profileDelta q p hq0 hq1 hp0 hp1 thickDelta := by
    calc
      (1 / 2 : ℝ) ≤ (3 / 4) * (3 / 4) := by norm_num
      _ ≤ (1 - eta) ^ m *
          AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
            scale profileDelta q p hq0 hq1 hp0 hp1 thickDelta :=
        mul_le_mul hpow href (by norm_num) hpow0
  have hmarked :=
    MarkedTerminalDisintegration.hlozTerminal_event_real_lower_of_markedStoppedData
      mu successful thick scale profileDelta thickDelta q p
      hq0 hq1 hp0 hp1 eta heta0 heta1 skeletonWeight skeletonKernel
      markedKernel hlower hdecompose
  exact (mul_le_mul_of_nonneg_right hfactor measureReal_nonneg).trans hmarked

/-- **Exact marked stopped-data adapter for
`AnnularComparisons.terminalThick`.**

For every block and candidate point, `skeletonWeight` may retain the entire
complementary outer-to-inner skeleton and all future profile information.
The only coordinatewise input is the joint lower comparison between the
visit mark *and the next outer endpoint*.  Consequently this adapter does
not require the successful event to be measurable at any terminal entrance.
-/
theorem annularComparisons_terminalThick_of_markedStoppedData
    {delta : ℝ} {n : ℕ}
    (hscale : 4 ≤ scaleIndex delta n)
    (Data Entrance Exit : Fin (chosenBlockCount delta n) → Point → Type*)
    (q p eta : Fin (chosenBlockCount delta n) → Point → ℝ)
    (hq0 : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      0 ≤ q i x)
    (hq1 : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      q i x ≤ 1)
    (hp0 : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      0 < p i x)
    (hp1 : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      p i x ≤ 1)
    (hmargin : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      0 < AppendixLocalTime.requiredHLOZTerminalMargin
        (scaleIndex delta n) chosenProfileDelta (chosenThickDelta delta)
          (q i x) (p i x))
    (hratio : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      AppendixLocalTime.requiredTerminalVisitVariance
          (scaleIndex delta n) chosenProfileDelta (q i x) (p i x) /
        (AppendixLocalTime.requiredHLOZTerminalMargin
          (scaleIndex delta n) chosenProfileDelta (chosenThickDelta delta)
            (q i x) (p i x)) ^ 2 ≤ (scaleIndex delta n : ℝ)⁻¹)
    (heta0 : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      0 ≤ eta i x)
    (heta1 : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      eta i x ≤ 1)
    (hlossQuarter : ∀ i (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      (AppendixLocalTime.requiredTerminalCount
          (scaleIndex delta n) chosenProfileDelta : ℝ) * eta i x ≤
        1 / 4)
    (skeletonWeight : ∀ i x, Data i x →
      (Fin (AppendixLocalTime.requiredTerminalCount
          (scaleIndex delta n) chosenProfileDelta) → Entrance i x) →
      (Fin (AppendixLocalTime.requiredTerminalCount
          (scaleIndex delta n) chosenProfileDelta) → Exit i x) → ℝ≥0∞)
    (skeletonKernel : ∀ i x,
      Fin (AppendixLocalTime.requiredTerminalCount
          (scaleIndex delta n) chosenProfileDelta) →
        Entrance i x → Exit i x → ℝ≥0∞)
    (markedKernel : ∀ i x,
      Fin (AppendixLocalTime.requiredTerminalCount
          (scaleIndex delta n) chosenProfileDelta) →
        Entrance i x → ℕ → Exit i x → ℝ≥0∞)
    (hlower : ∀ i (x : Point)
        (_hx : x ∈ ThickPoint.candidateBox (scaleIndex delta n)),
      MarkedTerminalDisintegration.MarkedKernelLower
        (fun _ ↦ ENNReal.ofReal (1 - eta i x))
        (fun _ k ↦ ENNReal.ofReal
          (AppendixLocalTime.visitMass (q i x) (p i x) k))
        (skeletonKernel i x) (markedKernel i x))
    (hdecompose : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      MarkedTerminalDisintegration.MarkedStoppedDataLowerDecomposition
        fairSteps
        (stoppedSuccessfulPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta x)
        (stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) x)
        (skeletonWeight i x) (skeletonKernel i x) (markedKernel i x)
        {visits | ThickPoint.thickThreshold
            (scaleIndex delta n) (chosenThickDelta delta) ≤
          AppendixLocalTime.totalVisits visits}) :
    ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      (1 - terminalEpsilon) * fairSteps.real
          (stoppedSuccessfulPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta x) ≤
        fairSteps.real
          (stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) x) := by
  intro i x hx
  have hlowerEvent := event_terminal_half_lower_of_markedStoppedData
    fairSteps
    (stoppedSuccessfulPointEvent
      ((i : ℕ) * chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta x)
    (stoppedThickPointEvent
      ((i : ℕ) * chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta
      (chosenThickDelta delta) x)
    hscale
    chosenProfileDelta (chosenThickDelta delta) (q i x) (p i x)
    (hq0 i x hx) (hq1 i x hx) (hp0 i x hx) (hp1 i x hx)
    (hmargin i x hx) (hratio i x hx)
    (eta i x) (heta0 i x hx) (heta1 i x hx) (hlossQuarter i x hx)
    (skeletonWeight i x) (skeletonKernel i x) (markedKernel i x)
    (hlower i x hx) (hdecompose i x hx)
  have hterminal : (1 : ℝ) - terminalEpsilon = 1 / 2 := by
    norm_num [terminalEpsilon]
  rw [hterminal]
  exact hlowerEvent

/-! ## Full stopped-data terminal reduction -/

/-- Event-level Appendix-A.7 lower bound from the valid sequential kernel
interface.  `Data` contains the complete stopped past and boundary data;
`actualKernel` is its conditional terminal-success probability. -/
theorem event_terminal_lower_of_sequentialKernelComparison
    {Omega Data Entrance : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Data] [Fintype Entrance]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (successful thick : Set Omega)
    {scale : ℕ} (profileDelta thickDelta : ℝ)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < AppendixLocalTime.requiredHLOZTerminalMargin
      scale profileDelta thickDelta q p)
    (hratio : AppendixLocalTime.requiredTerminalVisitVariance
        scale profileDelta q p /
      (AppendixLocalTime.requiredHLOZTerminalMargin
        scale profileDelta thickDelta q p) ^ 2 ≤ (scale : ℝ)⁻¹)
    (dataLaw : Measure Data) [IsProbabilityMeasure dataLaw]
    (entranceData : Data →
      Fin (AppendixLocalTime.requiredTerminalCount
        scale profileDelta) → Entrance)
    (modelKernel :
      (Fin (AppendixLocalTime.requiredTerminalCount
        scale profileDelta) → Entrance) → ℝ)
    (actualKernel : Data → ℝ) (hactual : Integrable actualKernel dataLaw)
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilonInv : epsilon ≤ (scale : ℝ)⁻¹)
    (hcompare : AppendixLocalTimeTransfer.TerminalKernelComparison epsilon
      (AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
        scale profileDelta q p hq0 hq1 hp0 hp1 thickDelta) modelKernel)
    (hsequential :
      TerminalExcursionDisintegration.SequentialConditionalKernelLower
        entranceData modelKernel actualKernel)
    (hdisintegrate :
      TerminalExcursionDisintegration.StoppedDataDisintegrationLower
        mu successful thick dataLaw actualKernel) :
    (1 - 2 * (scale : ℝ)⁻¹) * mu.real successful ≤ mu.real thick := by
  exact
    TerminalExcursionDisintegration.event_terminal_lower_of_sequentialKernelComparison
      mu successful thick profileDelta thickDelta q p hq0 hq1 hp0 hp1
      hmargin hratio dataLaw entranceData modelKernel actualKernel hactual
      epsilon hepsilon0 hepsilonInv hcompare hsequential hdisintegrate

/-- **Exact `AnnularComparisons.terminalThick` adapter.**

For every block and candidate point, the caller supplies a probability law
on the complete stopped data, a model terminal kernel, a pointwise sequential
lower comparison with the actual conditional kernel, and a one-sided stopped
event disintegration.  The checked complete-segment concentration gives the
factor `1-2/scale`; at scale at least four this dominates the certificate's
reserved factor `1-terminalEpsilon = 1/2`. -/
theorem annularComparisons_terminalThick_of_sequentialKernelComparison
    {delta : ℝ} {n : ℕ}
    (hscale : 4 ≤ scaleIndex delta n)
    (Data Entrance : Fin (chosenBlockCount delta n) → Point → Type*)
    [∀ i x, MeasurableSpace (Data i x)]
    [∀ i x, Fintype (Entrance i x)]
    (q p : Fin (chosenBlockCount delta n) → Point → ℝ)
    (hq0 : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      0 ≤ q i x)
    (hq1 : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      q i x ≤ 1)
    (hp0 : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      0 < p i x)
    (hp1 : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      p i x ≤ 1)
    (hmargin : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      0 < AppendixLocalTime.requiredHLOZTerminalMargin
        (scaleIndex delta n) chosenProfileDelta (chosenThickDelta delta)
          (q i x) (p i x))
    (hratio : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      AppendixLocalTime.requiredTerminalVisitVariance
          (scaleIndex delta n) chosenProfileDelta (q i x) (p i x) /
        (AppendixLocalTime.requiredHLOZTerminalMargin
          (scaleIndex delta n) chosenProfileDelta (chosenThickDelta delta)
            (q i x) (p i x)) ^ 2 ≤ (scaleIndex delta n : ℝ)⁻¹)
    (dataLaw : ∀ i x, Measure (Data i x))
    [∀ i x, IsProbabilityMeasure (dataLaw i x)]
    (entranceData : ∀ i x, Data i x →
      Fin (AppendixLocalTime.requiredTerminalCount
        (scaleIndex delta n) chosenProfileDelta) → Entrance i x)
    (modelKernel : ∀ i x,
      (Fin (AppendixLocalTime.requiredTerminalCount
        (scaleIndex delta n) chosenProfileDelta) → Entrance i x) → ℝ)
    (actualKernel : ∀ i x, Data i x → ℝ)
    (hactual : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      Integrable (actualKernel i x) (dataLaw i x))
    (epsilon : Fin (chosenBlockCount delta n) → Point → ℝ)
    (hepsilon0 : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      0 ≤ epsilon i x)
    (hepsilonInv : ∀ i (x : Point), x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      epsilon i x ≤ (scaleIndex delta n : ℝ)⁻¹)
    (hcompare : ∀ i (x : Point)
        (hx : x ∈ ThickPoint.candidateBox (scaleIndex delta n)),
      AppendixLocalTimeTransfer.TerminalKernelComparison (epsilon i x)
        (AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
          (scaleIndex delta n) chosenProfileDelta (q i x) (p i x)
          (hq0 i x hx) (hq1 i x hx) (hp0 i x hx) (hp1 i x hx)
          (chosenThickDelta delta)) (modelKernel i x))
    (hsequential : ∀ i (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      TerminalExcursionDisintegration.SequentialConditionalKernelLower
        (entranceData i x) (modelKernel i x) (actualKernel i x))
    (hdisintegrate : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      TerminalExcursionDisintegration.StoppedDataDisintegrationLower fairSteps
        (stoppedSuccessfulPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta x)
        (stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) x)
        (dataLaw i x) (actualKernel i x)) :
    ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      (1 - terminalEpsilon) * fairSteps.real
          (stoppedSuccessfulPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta x) ≤
        fairSteps.real
          (stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) x) := by
  intro i x hx
  have hlower := event_terminal_lower_of_sequentialKernelComparison
    fairSteps
    (stoppedSuccessfulPointEvent
      ((i : ℕ) * chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta x)
    (stoppedThickPointEvent
      ((i : ℕ) * chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta
      (chosenThickDelta delta) x)
    chosenProfileDelta (chosenThickDelta delta)
    (q i x) (p i x) (hq0 i x hx) (hq1 i x hx) (hp0 i x hx) (hp1 i x hx)
    (hmargin i x hx) (hratio i x hx) (dataLaw i x)
    (entranceData i x) (modelKernel i x) (actualKernel i x) (hactual i x hx)
    (epsilon i x) (hepsilon0 i x hx) (hepsilonInv i x hx)
    (hcompare i x hx) (hsequential i x hx) (hdisintegrate i x hx)
  have hscaleReal : (4 : ℝ) ≤ scaleIndex delta n := by exact_mod_cast hscale
  have hscalePos : (0 : ℝ) < scaleIndex delta n := by positivity
  have hinv : 2 * (scaleIndex delta n : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hscalePos).2
    nlinarith
  have hfactor : 1 - terminalEpsilon ≤
      1 - 2 * (scaleIndex delta n : ℝ)⁻¹ := by
    norm_num [terminalEpsilon]
    linarith
  exact (mul_le_mul_of_nonneg_right hfactor
      (measureReal_nonneg (μ := fairSteps))).trans hlower

end

end Erdos1165.AppendixTerminalThick
