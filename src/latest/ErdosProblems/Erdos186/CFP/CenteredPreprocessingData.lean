/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredIdentification
import ErdosProblems.Erdos186.CFP.PreprocessingBilu

/-!
# Centered preprocessing with retained approximation data

The original Lemma 2.38-facing conclusion deliberately exposes only its
stable core.  The later random/greedy construction also needs the actual
ambient approximation selected before subgroup pruning: it supplies the
common coordinate rank, the quantitative relative-index bound, and the
large proper dilation used for no-carry evaluation.  This file retains that
data without changing the source-facing CFP propositions.
-/

namespace Erdos186.CFP.Preprocessing

noncomputable section

/-- The centered Lemma 2.38 output together with the approximation family
from which its relevant coordinate systems were constructed. -/
structure CenteredPreprocessingData (A : Finset ℤ)
    (stableBudget maxRank n C0 scaleNum scaleDen : ℕ) where
  weakCore : Finset ℤ
  core : Finset ℤ
  relevant : Finset ℕ
  boxesProper : Stability.RelevantBoxesProper weakCore relevant
  hAt : {d // d ∈ relevant} → ℕ
  weakCore_subset_source : weakCore ⊆ A
  zero_mem_weakCore : 0 ∈ weakCore
  weakCore_stable :
    Stability.WeaklyStableMinimalFor weakCore (2 * stableBudget) maxRank n
  approximation : ∀ d : {d // d ∈ relevant},
    Nonempty (HDimension.HApproximation weakCore (hAt d) d.1
      scaleNum scaleDen)
  rank_le : ∀ d : {d // d ∈ relevant}, d.1 ≤ maxRank
  horizon_le : ∀ d : {d // d ∈ relevant}, hAt d ≤ n
  horizon_large : ∀ d : {d // d ∈ relevant},
    4 * (6 * scaleDen) ^ maxRank * (4 * scaleDen) ^ maxRank ≤ hAt d
  accessible : ∀ {B : Finset ℤ}, B ⊆ weakCore →
    weakCore.card ≤ B.card +
      (stableBudget / C0) *
        (maxRank * Nat.log 2
          (4 * (6 * scaleDen) ^ maxRank *
            (4 * scaleDen) ^ maxRank) + 1) →
    0 ∈ B → ∀ d : {d // d ∈ relevant},
      ∃ e : ℕ, 0 < e ∧ e ≤ maxRank ∧
        ∃ V : HDimension.HApproximation B (hAt d) e
            scaleNum scaleDen,
          (2 * scaleDen) ^ e * (hAt d + 1) ^ (e - 1) <
            (scaleNum * hAt d) ^ e
  spanLoss :
    (stableBudget / C0) *
      (maxRank * Nat.log 2
        (4 * (6 * scaleDen) ^ maxRank *
          (4 * scaleDen) ^ maxRank)) ≤ stableBudget
  core_subset_weakCore : core ⊆ weakCore
  zero_mem_core : 0 ∈ core
  source_card_le : A.card ≤ core.card +
    (2 * stableBudget) * boxPotential A maxRank + stableBudget
  stable : Stability.StronglyStableFor core
    (Stability.minimalBoxFamily weakCore) stableBudget maxRank (n ^ 2)
    relevant (Stability.centeredMinimalIdentificationFamily boxesProper) C0

/-- The centered preprocessing proof with its ambient H-approximation
certificate retained.  This is the data-preserving form of
`preprocessing_lemma238_centered`. -/
theorem exists_centeredPreprocessingData
    {A : Finset ℤ}
    {stableBudget maxRank n C0 scaleNum scaleDen : ℕ}
    (hzero : 0 ∈ A) (hC0 : 0 < C0)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (happrox : PreprocessingBilu.PreprocessingHApproximationArgument A
      stableBudget maxRank n C0 scaleNum scaleDen) :
    Nonempty (CenteredPreprocessingData A stableBudget maxRank n C0
      scaleNum scaleDen) := by
  classical
  obtain ⟨W, hWA, hzeroW, hweakW, hlossW⟩ :=
    exists_weaklyStable_core hzero
  obtain ⟨relevant, hproper, hAt, hambient, hrank_le, hh_le,
      hlarge, haccessible, hspanLoss⟩ := happrox hWA hzeroW hweakW
  let hambient' : ∀ d : {d // d ∈ relevant},
      HDimension.HApproximation W (hAt d) d.1 scaleNum scaleDen :=
    fun d ↦ Classical.choice (hambient d)
  let K := 4 * (6 * scaleDen) ^ maxRank * (4 * scaleDen) ^ maxRank
  let height := maxRank * Nat.log 2 K
  let robustBudget := stableBudget / C0
  have hrobust_le : robustBudget ≤ stableBudget :=
    Nat.div_le_self _ _
  have hcap : robustBudget * (height + 1) ≤ 2 * stableBudget := by
    have hspanLoss' : robustBudget * height ≤ stableBudget := by
      simpa only [robustBudget, height, K] using hspanLoss
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have haccessible' : ∀ {B : Finset ℤ}, B ⊆ W →
      W.card ≤ B.card + robustBudget * (height + 1) → 0 ∈ B →
      ∀ d : {d // d ∈ relevant},
        ∃ e : ℕ, 0 < e ∧ e ≤ maxRank ∧
          ∃ V : HDimension.HApproximation B (hAt d) e scaleNum scaleDen,
            (2 * scaleDen) ^ e * (hAt d + 1) ^ (e - 1) <
              (scaleNum * hAt d) ^ e := by
    intro B hBW hcard hzeroB d
    apply haccessible hBW (B := B) ?_ hzeroB d
    simpa only [robustBudget, height, K] using hcard
  obtain ⟨B, hBW, hzeroB, hlossB, hspanB⟩ :=
    span_pruning_lemma232_of_centeredHApproximations
      hzeroW hweakW (fun z hz ↦ hA z (hWA hz)) hproper hAt
      hambient' hrank_le hh_le hlarge haccessible' hcap
  have hweakB : Stability.WeaklyStableFor B
      (Stability.minimalBoxFamily W) stableBudget maxRank (n ^ 2) := by
    apply Stability.WeaklyStableFor.delete hweakW hBW hzeroB hlossB
    have hspanLoss' : robustBudget * height ≤ stableBudget := by
      simpa only [robustBudget, height, K] using hspanLoss
    exact (Nat.add_le_add_right hspanLoss' stableBudget).trans_eq (by omega)
  have hsourceCard : A.card ≤ B.card +
      (2 * stableBudget) * boxPotential A maxRank + stableBudget := by
    have hspanLoss' : robustBudget * height ≤ stableBudget := by
      simpa only [robustBudget, height, K] using hspanLoss
    have hlossB' : W.card ≤ B.card + stableBudget :=
      hlossB.trans (Nat.add_le_add_left hspanLoss' B.card)
    omega
  have hstrong : Stability.StronglyStableFor B
      (Stability.minimalBoxFamily W) stableBudget maxRank (n ^ 2)
      relevant (Stability.centeredMinimalIdentificationFamily hproper) C0 := by
    refine ⟨hweakB, hC0, ?_⟩
    intro d hd B' hB'B hcard hzeroB'
    exact hspanB hd hB'B (by simpa only [robustBudget] using hcard) hzeroB'
  exact ⟨{
    weakCore := W
    core := B
    relevant := relevant
    boxesProper := hproper
    hAt := hAt
    weakCore_subset_source := hWA
    zero_mem_weakCore := hzeroW
    weakCore_stable := hweakW
    approximation := hambient
    rank_le := hrank_le
    horizon_le := hh_le
    horizon_large := hlarge
    accessible := haccessible
    spanLoss := hspanLoss
    core_subset_weakCore := hBW
    zero_mem_core := hzeroB
    source_card_le := hsourceCard
    stable := hstrong }⟩

end

end Erdos186.CFP.Preprocessing

#print axioms Erdos186.CFP.Preprocessing.exists_centeredPreprocessingData
