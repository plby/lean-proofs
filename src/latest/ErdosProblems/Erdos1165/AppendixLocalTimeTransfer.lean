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

import ErdosProblems.Erdos1165.AppendixLocalTime
import ErdosProblems.Erdos1165.AppendixDecoupling

/-!
# Transferring the HLOZ terminal local-time estimate through annular decoupling

`AppendixLocalTime` proves the exact Bernoulli--geometric concentration under
the iid reference law.  `AppendixDecoupling` proves that a uniform Harnack
comparison survives mixing over the entrance data exposed by the outer path.
This file composes those results at HLOZ's exact terminal count and thick-point
threshold.  The comparison interface is the generic
`TerminalKernelComparison`; the planar-walk boundary Harnack theorem and its
sequential stopped-history realization are supplied in later modules.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.AppendixLocalTimeTransfer

noncomputable section

/-! ## Exact terminal scales -/

/-- Outer radius of the terminal annulus in Appendix A. -/
def terminalOuterRadius (n : ℕ) : ℝ := ThickPoint.scaleRadius n n

/-- Inner radius of the terminal annulus in Appendix A. -/
def terminalInnerRadius (n : ℕ) : ℝ := ThickPoint.scaleRadius n (n + 1)

@[simp] lemma terminalOuterRadius_eq (n : ℕ) :
    terminalOuterRadius n = (n : ℝ) ^ 9 := by
  simp [terminalOuterRadius, ThickPoint.regularRadius_self]

@[simp] lemma terminalInnerRadius_eq (n : ℕ) :
    terminalInnerRadius n = (n : ℝ) ^ 6 := by
  simp [terminalInnerRadius]

/-- Error factor in HLOZ Lemma A.2: `lambda' m n^{-3} log n`. -/
def hlozDecouplingError (lambda : ℝ) (n m : ℕ) : ℝ :=
  lambda * (m : ℝ) * ((n : ℝ)⁻¹) ^ 3 * Real.log n

/-! ## The terminal kernel comparison -/

/-- A conditional success kernel, indexed by all terminal-annulus entrance
data, is within `1 ± epsilon` of a fixed fresh-walk reference probability. -/
def TerminalKernelComparison {Entrance : Type*} [Fintype Entrance] {m : ℕ}
    (ε reference : ℝ) (kernel : (Fin m → Entrance) → ℝ) : Prop :=
  ∀ u, kernel u ∈ Set.Icc ((1 - ε) * reference) ((1 + ε) * reference)

lemma terminalKernelComparison_of_conditionStar
    {Entrance : Type*} [Fintype Entrance] {m : ℕ}
    {ε : ℝ} {kernel : (Fin m → Entrance) → ℝ}
    (hstar : AppendixDecoupling.ConditionStar ε kernel)
    (referenceEntrance : Fin m → Entrance) :
    TerminalKernelComparison ε (kernel referenceEntrance) kernel := by
  intro u
  exact hstar referenceEntrance u

/-! ## Mixing the comparison over the outer path -/

theorem mix_mem_Icc_of_terminalKernelComparison
    {Entrance : Type*} [Fintype Entrance] {m : ℕ}
    (entranceLaw : AppendixDecoupling.EntranceDistribution (Fin m → Entrance))
    {ε reference : ℝ} {kernel : (Fin m → Entrance) → ℝ}
    (hcompare : TerminalKernelComparison ε reference kernel) :
    entranceLaw.mix kernel ∈
      Set.Icc ((1 - ε) * reference) ((1 + ε) * reference) := by
  exact entranceLaw.mix_mem_Icc kernel _ _ hcompare

/-- The exact iid reference probability for HLOZ's thick threshold. -/
def referenceTerminalSuccessProbability
    (n : ℕ) (δ : ℝ) (q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (δ' : ℝ) : ℝ :=
  (AppendixLocalTime.iidVisitMeasure (AppendixLocalTime.requiredTerminalCount n δ)
      q p hq0 hq1 hp0 hp1).real
    {v | ThickPoint.thickThreshold n δ' ≤ AppendixLocalTime.totalVisits v}

/-- Profile-independent terminal transfer.  The deterministic number of
terminal excursions was selected from the successful-window lower endpoint,
so the iid calculation and the mixing argument themselves require no fixed
profile.  A pathwise use separately proves that this initial block exists. -/
theorem required_terminal_transfer_ge_one_sub_two_inv_of_comparison
    {Entrance : Type*} [Fintype Entrance]
    {n : ℕ} (δ δ' : ℝ)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < AppendixLocalTime.requiredHLOZTerminalMargin n δ δ' q p)
    (hratio : AppendixLocalTime.requiredTerminalVisitVariance n δ q p /
      (AppendixLocalTime.requiredHLOZTerminalMargin n δ δ' q p) ^ 2 ≤
        (n : ℝ)⁻¹)
    (entranceLaw : AppendixDecoupling.EntranceDistribution
      (Fin (AppendixLocalTime.requiredTerminalCount n δ) → Entrance))
    (kernel : (Fin (AppendixLocalTime.requiredTerminalCount n δ) → Entrance) → ℝ)
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilonInv : epsilon ≤ (n : ℝ)⁻¹)
    (hcompare : TerminalKernelComparison epsilon
      (referenceTerminalSuccessProbability n δ q p hq0 hq1 hp0 hp1 δ') kernel) :
    1 - 2 * (n : ℝ)⁻¹ ≤ entranceLaw.mix kernel := by
  have href := AppendixLocalTime.required_hlozThreshold_probability_ge_one_sub_inv
    n δ δ' q p hq0 hq1 hp0 hp1 hmargin hratio
  have hinv0 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  have hepsilon1 : epsilon ≤ 1 := by
    by_cases hn : n = 0
    · subst n
      norm_num at hepsilonInv
      linarith
    · exact hepsilonInv.trans
        (inv_le_one_of_one_le₀ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)))
  have hmix := (mix_mem_Icc_of_terminalKernelComparison entranceLaw hcompare).1
  have hproduct : (1 - epsilon) * (1 - (n : ℝ)⁻¹) ≤
      entranceLaw.mix kernel :=
    (mul_le_mul_of_nonneg_left href (sub_nonneg.mpr hepsilon1)).trans hmix
  have hcross : 0 ≤ epsilon * (n : ℝ)⁻¹ := mul_nonneg hepsilon0 hinv0
  calc
    1 - 2 * (n : ℝ)⁻¹ ≤ 1 - (n : ℝ)⁻¹ - epsilon := by linarith
    _ ≤ (1 - epsilon) * (1 - (n : ℝ)⁻¹) := by nlinarith
    _ ≤ entranceLaw.mix kernel := hproduct

/-- **Exact terminal transfer reduction.**  After successfulness fixes the
terminal excursion count, iid concentration gives the reference lower bound;
the kernel comparison transfers it through the arbitrary entrance
distribution generated by the outer path. -/
theorem successfulProfile_terminal_transfer
    {Entrance : Type*} [Fintype Entrance]
    {n : ℕ} {δ δ' : ℝ} {N : Fin (n + 2) → ℕ}
    (hN : ThickPoint.SuccessfulProfile n δ N)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < AppendixLocalTime.requiredHLOZTerminalMargin n δ δ' q p)
    (lambda : ℝ)
    (entranceLaw : AppendixDecoupling.EntranceDistribution
      (Fin (AppendixLocalTime.requiredTerminalCount n δ) → Entrance))
    (kernel : (Fin (AppendixLocalTime.requiredTerminalCount n δ) → Entrance) → ℝ)
    (hHarnack : TerminalKernelComparison
      (hlozDecouplingError lambda n
        (AppendixLocalTime.requiredTerminalCount n δ))
      (referenceTerminalSuccessProbability n δ q p hq0 hq1 hp0 hp1 δ') kernel)
    (herror : hlozDecouplingError lambda n
      (AppendixLocalTime.requiredTerminalCount n δ) ≤ 1) :
    (1 - hlozDecouplingError lambda n
        (AppendixLocalTime.requiredTerminalCount n δ)) *
        (1 - AppendixLocalTime.requiredTerminalVisitVariance n δ q p /
          (AppendixLocalTime.requiredHLOZTerminalMargin n δ δ' q p) ^ 2) ≤
      entranceLaw.mix kernel := by
  have href := (AppendixLocalTime.successfulProfile_required_hlozThreshold_concentrate
    hN q p hq0 hq1 hp0 hp1 hmargin).2
  have hmix := (mix_mem_Icc_of_terminalKernelComparison entranceLaw hHarnack).1
  exact (mul_le_mul_of_nonneg_left href (sub_nonneg.mpr herror)).trans hmix

/-- The form used to obtain HLOZ (A.7): if the explicit variance ratio is at
most `1/n`, the conditional success probability is at least
`(1-error)(1-1/n)`. -/
theorem successfulProfile_terminal_transfer_one_sub_inv
    {Entrance : Type*} [Fintype Entrance]
    {n : ℕ} {δ δ' : ℝ} {N : Fin (n + 2) → ℕ}
    (hN : ThickPoint.SuccessfulProfile n δ N)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < AppendixLocalTime.requiredHLOZTerminalMargin n δ δ' q p)
    (hratio : AppendixLocalTime.requiredTerminalVisitVariance n δ q p /
      (AppendixLocalTime.requiredHLOZTerminalMargin n δ δ' q p) ^ 2 ≤
        (n : ℝ)⁻¹)
    (lambda : ℝ)
    (entranceLaw : AppendixDecoupling.EntranceDistribution
      (Fin (AppendixLocalTime.requiredTerminalCount n δ) → Entrance))
    (kernel : (Fin (AppendixLocalTime.requiredTerminalCount n δ) → Entrance) → ℝ)
    (hHarnack : TerminalKernelComparison
      (hlozDecouplingError lambda n
        (AppendixLocalTime.requiredTerminalCount n δ))
      (referenceTerminalSuccessProbability n δ q p hq0 hq1 hp0 hp1 δ') kernel)
    (herror : hlozDecouplingError lambda n
      (AppendixLocalTime.requiredTerminalCount n δ) ≤ 1) :
    (1 - hlozDecouplingError lambda n
      (AppendixLocalTime.requiredTerminalCount n δ)) *
        (1 - (n : ℝ)⁻¹) ≤
      entranceLaw.mix kernel := by
  have href :=
    AppendixLocalTime.successfulProfile_required_hlozThreshold_probability_ge_one_sub_inv
    hN q p hq0 hq1 hp0 hp1 hmargin hratio
  have hmix := (mix_mem_Icc_of_terminalKernelComparison entranceLaw hHarnack).1
  exact (mul_le_mul_of_nonneg_left href (sub_nonneg.mpr herror)).trans hmix

/-- Additive form of the preceding product estimate.  It records explicitly
that the two failure probabilities add; the omitted product of the two errors
is nonnegative. -/
theorem successfulProfile_terminal_transfer_additive
    {Entrance : Type*} [Fintype Entrance]
    {n : ℕ} {δ δ' : ℝ} {N : Fin (n + 2) → ℕ}
    (hN : ThickPoint.SuccessfulProfile n δ N)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < AppendixLocalTime.requiredHLOZTerminalMargin n δ δ' q p)
    (hratio : AppendixLocalTime.requiredTerminalVisitVariance n δ q p /
      (AppendixLocalTime.requiredHLOZTerminalMargin n δ δ' q p) ^ 2 ≤
        (n : ℝ)⁻¹)
    (lambda : ℝ)
    (entranceLaw : AppendixDecoupling.EntranceDistribution
      (Fin (AppendixLocalTime.requiredTerminalCount n δ) → Entrance))
    (kernel : (Fin (AppendixLocalTime.requiredTerminalCount n δ) → Entrance) → ℝ)
    (hHarnack : TerminalKernelComparison
      (hlozDecouplingError lambda n
        (AppendixLocalTime.requiredTerminalCount n δ))
      (referenceTerminalSuccessProbability n δ q p hq0 hq1 hp0 hp1 δ') kernel)
    (herror0 : 0 ≤ hlozDecouplingError lambda n
      (AppendixLocalTime.requiredTerminalCount n δ))
    (herror1 : hlozDecouplingError lambda n
      (AppendixLocalTime.requiredTerminalCount n δ) ≤ 1) :
    1 - (n : ℝ)⁻¹ - hlozDecouplingError lambda n
        (AppendixLocalTime.requiredTerminalCount n δ) ≤
      entranceLaw.mix kernel := by
  have hproduct := successfulProfile_terminal_transfer_one_sub_inv
    hN q p hq0 hq1 hp0 hp1 hmargin hratio lambda entranceLaw kernel hHarnack herror1
  have hinv : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  have hcross : 0 ≤ hlozDecouplingError lambda n
      (AppendixLocalTime.requiredTerminalCount n δ) * (n : ℝ)⁻¹ :=
    mul_nonneg herror0 hinv
  calc
    1 - (n : ℝ)⁻¹ - hlozDecouplingError lambda n
          (AppendixLocalTime.requiredTerminalCount n δ)
        ≤ (1 - hlozDecouplingError lambda n
            (AppendixLocalTime.requiredTerminalCount n δ)) * (1 - (n : ℝ)⁻¹) := by
          nlinarith
    _ ≤ entranceLaw.mix kernel := hproduct

/-- In particular, if the Harnack error is itself at most `1/n`, the mixed
terminal success probability is at least `1-2/n`, the concrete `1-O(1/n)`
form of HLOZ (A.7). -/
theorem successfulProfile_terminal_transfer_ge_one_sub_two_inv
    {Entrance : Type*} [Fintype Entrance]
    {n : ℕ} {δ δ' : ℝ} {N : Fin (n + 2) → ℕ}
    (hN : ThickPoint.SuccessfulProfile n δ N)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < AppendixLocalTime.requiredHLOZTerminalMargin n δ δ' q p)
    (hratio : AppendixLocalTime.requiredTerminalVisitVariance n δ q p /
      (AppendixLocalTime.requiredHLOZTerminalMargin n δ δ' q p) ^ 2 ≤
        (n : ℝ)⁻¹)
    (lambda : ℝ)
    (entranceLaw : AppendixDecoupling.EntranceDistribution
      (Fin (AppendixLocalTime.requiredTerminalCount n δ) → Entrance))
    (kernel : (Fin (AppendixLocalTime.requiredTerminalCount n δ) → Entrance) → ℝ)
    (hHarnack : TerminalKernelComparison
      (hlozDecouplingError lambda n
        (AppendixLocalTime.requiredTerminalCount n δ))
      (referenceTerminalSuccessProbability n δ q p hq0 hq1 hp0 hp1 δ') kernel)
    (herror0 : 0 ≤ hlozDecouplingError lambda n
      (AppendixLocalTime.requiredTerminalCount n δ))
    (herrorInv : hlozDecouplingError lambda n
      (AppendixLocalTime.requiredTerminalCount n δ) ≤ (n : ℝ)⁻¹)
    (herror1 : hlozDecouplingError lambda n
      (AppendixLocalTime.requiredTerminalCount n δ) ≤ 1) :
    1 - 2 * (n : ℝ)⁻¹ ≤ entranceLaw.mix kernel := by
  have hadd := successfulProfile_terminal_transfer_additive
    hN q p hq0 hq1 hp0 hp1 hmargin hratio lambda entranceLaw kernel hHarnack
      herror0 herror1
  linarith

/-- Large-`n` form with only the natural sign assumption on the Harnack
constant.  For `n ≥ 1`, nonnegativity of the displayed error follows from
its exact formula, and an `error ≤ 1/n` estimate automatically implies the
auxiliary `error ≤ 1` condition. -/
theorem successfulProfile_terminal_transfer_ge_one_sub_two_inv_of_nonneg
    {Entrance : Type*} [Fintype Entrance]
    {n : ℕ} {δ δ' : ℝ} {N : Fin (n + 2) → ℕ}
    (hn : 1 ≤ n)
    (hN : ThickPoint.SuccessfulProfile n δ N)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < AppendixLocalTime.requiredHLOZTerminalMargin n δ δ' q p)
    (hratio : AppendixLocalTime.requiredTerminalVisitVariance n δ q p /
      (AppendixLocalTime.requiredHLOZTerminalMargin n δ δ' q p) ^ 2 ≤
        (n : ℝ)⁻¹)
    (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (entranceLaw : AppendixDecoupling.EntranceDistribution
      (Fin (AppendixLocalTime.requiredTerminalCount n δ) → Entrance))
    (kernel : (Fin (AppendixLocalTime.requiredTerminalCount n δ) → Entrance) → ℝ)
    (hHarnack : TerminalKernelComparison
      (hlozDecouplingError lambda n
        (AppendixLocalTime.requiredTerminalCount n δ))
      (referenceTerminalSuccessProbability n δ q p hq0 hq1 hp0 hp1 δ') kernel)
    (herrorInv : hlozDecouplingError lambda n
      (AppendixLocalTime.requiredTerminalCount n δ) ≤ (n : ℝ)⁻¹) :
    1 - 2 * (n : ℝ)⁻¹ ≤ entranceLaw.mix kernel := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have herror0 : 0 ≤ hlozDecouplingError lambda n
      (AppendixLocalTime.requiredTerminalCount n δ) := by
    unfold hlozDecouplingError
    positivity
  have herror1 : hlozDecouplingError lambda n
      (AppendixLocalTime.requiredTerminalCount n δ) ≤ 1 :=
    herrorInv.trans (inv_le_one_of_one_le₀ hnreal)
  exact successfulProfile_terminal_transfer_ge_one_sub_two_inv
    hN q p hq0 hq1 hp0 hp1 hmargin hratio lambda entranceLaw kernel hHarnack
      herror0 herrorInv herror1

/-! ## Pathwise realization -/

/-- Concrete visit counts carried by disjoint terminal excursions of a path.
Constructing this structure from the actual annular stopping times is a
deterministic bookkeeping obligation, separate from Harnack. -/
structure TerminalVisitRealization
    (s : ThickPoint.WalkPath) (horizon m : ℕ) (x : ThickPoint.Point) where
  visits : Fin m → ℕ
  contained : ∑ i, visits i ≤ ThickPoint.localTimeThrough s horizon x

/-- A realized successful terminal event implies HLOZ's pathwise
`ThickSuccessfulPoint` predicate. -/
theorem thickSuccessfulPoint_of_terminalRealization
    {s : ThickPoint.WalkPath} {n horizon : ℕ} {δ δ' : ℝ} {x : ThickPoint.Point}
    (hx : ThickPoint.SuccessfulPoint s n horizon δ x)
    (R : TerminalVisitRealization s horizon
      (AppendixLocalTime.requiredTerminalCount n δ) x)
    (hthick : ThickPoint.thickThreshold n δ' ≤
      AppendixLocalTime.totalVisits R.visits) :
    AppendixLocalTime.requiredTerminalCount n δ ≤
        AppendixLocalTime.terminalCount (ThickPoint.excursionProfile s n horizon x) ∧
      ThickPoint.ThickSuccessfulPoint s n horizon δ δ' x := by
  exact ⟨AppendixLocalTime.requiredTerminalCount_le_terminalCount hx.2,
    AppendixLocalTime.thickSuccessfulPoint_of_excursionVisits
      hx R.visits R.contained hthick⟩

end

end Erdos1165.AppendixLocalTimeTransfer
