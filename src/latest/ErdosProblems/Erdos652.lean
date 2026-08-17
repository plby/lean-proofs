/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos652.ElekesConstruction

/-!
# Erdős Problem 652

For a finite planar point set `S`, `pinnedDistanceCount p S` is the number
of distinct distances from `p` to the other points of `S`.
`AdmissiblePinnedConstant k a` says literally that, for every sufficiently
large cardinality `n`, an `n`-point set exists with at least `k` points whose
pinned-distance count is less than `a * sqrt n`.  Having at least `k` such
points is equivalent to the `k`th value in the nondecreasing ordering being
below that threshold, without making an arbitrary choice to break ties.

We define `erdos652Alpha k` as the infimum of all admissible constants.
Elekes's circle-grid construction proves that this set is nonempty, while
Mathialagan's pinned bipartite distance theorem proves that its infimum tends
to infinity.  The detailed mathematical reconstruction is in `tex/652.tex`.
-/

open Classical Filter
open scoped Real Topology
noncomputable section

namespace Erdos652

/-- A normalized constant works for the `k`th ordered pinned-distance count
for every sufficiently large number of points. -/
def AdmissiblePinnedConstant (k : ℕ) (a : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ S : Finset Point, S.card = n ∧
      k ≤ (lowPinnedDistancePoints S a).card

/-- The set of normalized constants which work eventually for the `k`th
ordered pinned-distance count. -/
def admissiblePinnedConstants (k : ℕ) : Set ℝ :=
  {a | AdmissiblePinnedConstant k a}

/-- The constant `αₖ` from Erdős Problem 652, interpreted as an infimum (the
strict inequality in the problem need not yield an attained minimum). -/
def erdos652Alpha (k : ℕ) : ℝ :=
  sInf (admissiblePinnedConstants k)

lemma lowPinnedDistancePoints_mono {S : Finset Point} {a b : ℝ} (hab : a ≤ b) :
    lowPinnedDistancePoints S a ⊆ lowPinnedDistancePoints S b := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpS, hpLow⟩
  apply Finset.mem_filter.mpr
  refine ⟨hpS, hpLow.trans_le ?_⟩
  exact mul_le_mul_of_nonneg_right hab (Real.sqrt_nonneg _)

/-- Elekes's construction makes the defining set for `αₖ` nonempty. -/
lemma admissiblePinnedConstants_nonempty {k : ℕ} (hk : 1 ≤ k) :
    (admissiblePinnedConstants k).Nonempty := by
  refine ⟨(8 * k + 1 : ℕ), ?_⟩
  change AdmissiblePinnedConstant k ((8 * k + 1 : ℕ) : ℝ)
  simpa [AdmissiblePinnedConstant] using elekes_eventual_low_points k hk

lemma admissiblePinnedConstant_pos {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha : AdmissiblePinnedConstant k a) : 0 < a := by
  rcases ha with ⟨N, hN⟩
  let n := max N 1
  obtain ⟨S, hScard, hmany⟩ := hN n (le_max_left _ _)
  have hnonempty : (lowPinnedDistancePoints S a).Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < k) hmany)
  obtain ⟨p, hp⟩ := hnonempty
  have hpLow := (Finset.mem_filter.mp hp).2
  have hn1 : 1 ≤ n := le_max_right _ _
  have hsqrtPos : 0 < Real.sqrt S.card := by
    rw [hScard]
    exact Real.sqrt_pos.2 (by exact_mod_cast hn1)
  by_contra hapos
  have ha0 : a ≤ 0 := le_of_not_gt hapos
  have hprod : a * Real.sqrt S.card ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg ha0 hsqrtPos.le
  have hcount0 : (0 : ℝ) ≤ pinnedDistanceCount p S := by positivity
  linarith

lemma admissiblePinnedConstants_bddBelow {k : ℕ} (hk : 1 ≤ k) :
    BddBelow (admissiblePinnedConstants k) := by
  refine ⟨0, ?_⟩
  intro a ha
  exact (admissiblePinnedConstant_pos hk ha).le

lemma erdos652Alpha_le_admissible {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha : AdmissiblePinnedConstant k a) : erdos652Alpha k ≤ a := by
  exact csInf_le (admissiblePinnedConstants_bddBelow hk) ha

/-- For every fixed normalized bound `C`, all sufficiently high ordered
statistics have `αₖ ≥ C`. -/
theorem eventually_constant_le_erdos652Alpha (C : ℝ) (hC : 0 < C) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → C ≤ erdos652Alpha k := by
  obtain ⟨K, hK8, hFew⟩ := eventually_few_lowPinnedDistancePoints C hC
  refine ⟨K, ?_⟩
  intro k hKk
  have hk8 : 8 ≤ k := hK8.trans hKk
  have hk1 : 1 ≤ k := by omega
  apply le_csInf (admissiblePinnedConstants_nonempty hk1)
  intro a ha
  change AdmissiblePinnedConstant k a at ha
  by_contra hCa
  have haC : a < C := lt_of_not_ge hCa
  rcases ha with ⟨N, hN⟩
  let n := max N (k ^ 3 + k)
  have hNn : N ≤ n := le_max_left _ _
  have hkn : k ^ 3 + k ≤ n := le_max_right _ _
  obtain ⟨S, hScard, hmanyA⟩ := hN n hNn
  have hsub : lowPinnedDistancePoints S a ⊆ lowPinnedDistancePoints S C :=
    lowPinnedDistancePoints_mono haC.le
  have hmanyC : k ≤ (lowPinnedDistancePoints S C).card :=
    hmanyA.trans (Finset.card_le_card hsub)
  have hfew := hFew k hKk n hkn S hScard
  omega

/-- **Resolution of Erdős Problem 652.**  The optimal normalized constants
for the `k`th ordered pinned-distance count tend to `+∞`. -/
theorem erdos_652 :
    Tendsto erdos652Alpha atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro B
  let C : ℝ := max B 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨K, hK⟩ := eventually_constant_le_erdos652Alpha C hC
  filter_upwards [eventually_ge_atTop K] with k hk
  exact (le_max_left B 1).trans (hK k hk)

end Erdos652

#print axioms Erdos652.erdos_652
