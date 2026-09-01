/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.BlueMass

/-!
# Hue balance on a dyadic window

The prefix balance theorem also yields a lower bound for one residue class:
all other residue classes satisfy the upper bound, and together the classes
partition the prefix.  Subtracting this lower bound from the upper bound at a
later prefix controls one hue on an arbitrary rank interval.  We use a coarse
endpoint loss of `h^2`; it is asymptotically harmless and greatly simplifies
the formal finite argument.
-/

namespace Erdos55

open scoped BigOperators

theorem sum_residueIndices_all (w : ℕ → ℝ) (m : ℕ) {h : ℕ} (hh : 0 < h) :
    (∑ s ∈ Finset.range h, ∑ k ∈ residueIndices m h s, w k) =
      ∑ k ∈ Finset.range m, w k := by
  classical
  simp_rw [residueIndices, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single (k % h)]
  · simp
  · intro s hs hne
    simp only [ite_eq_right_iff]
    exact fun heq ↦ (hne heq.symm).elim
  · exact fun hnot ↦ (hnot (Finset.mem_range.mpr (Nat.mod_lt k hh))).elim

/-- Lower counterpart to the decreasing-weight prefix balance. -/
theorem sum_residueIndices_lower_of_antitone
    (w : ℕ → ℝ) {m h s : ℕ} (hh : 0 < h) (hs : s < h)
    (hw : Antitone w) (hw0 : ∀ k, 0 ≤ w k) :
    (∑ k ∈ Finset.range m, w k) -
        (h : ℝ) * (h - 1 : ℕ) * w 0 ≤
      (h : ℝ) * ∑ k ∈ residueIndices m h s, w k := by
  classical
  let P : ℕ → ℝ := fun t ↦ ∑ k ∈ residueIndices m h t, w k
  let T : ℝ := ∑ k ∈ Finset.range m, w k
  let O := (Finset.range h).erase s
  have hsrange : s ∈ Finset.range h := Finset.mem_range.mpr hs
  have hpart : T = P s + ∑ t ∈ O, P t := by
    have hall := sum_residueIndices_all w m hh
    rw [← Finset.sum_erase_add _ _ hsrange] at hall
    simpa [P, T, O, add_comm] using hall.symm
  have hupper (t : ℕ) :
      (h : ℝ) * P t ≤ T + (h : ℝ) * w 0 := by
    simpa [P, T] using natCast_mul_sum_residueIndices_le_of_antitone
      (s := t) w hh hw hw0
  have hsumUpper :
      (h : ℝ) * (∑ t ∈ O, P t) ≤
        ((O.card : ℝ) * (T + (h : ℝ) * w 0)) := by
    rw [Finset.mul_sum]
    calc
      (∑ t ∈ O, (h : ℝ) * P t) ≤
          ∑ _t ∈ O, (T + (h : ℝ) * w 0) :=
        Finset.sum_le_sum fun t _ ↦ hupper t
      _ = (O.card : ℝ) * (T + (h : ℝ) * w 0) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : O.card = h - 1 := by simp [O, hsrange]
  have hT : 0 ≤ T := Finset.sum_nonneg fun k _ ↦ hw0 k
  have hwzero : 0 ≤ w 0 := hw0 0
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hcast : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcard] at hsumUpper
  rw [hcast] at hsumUpper ⊢
  rw [hpart] at hsumUpper
  nlinarith

/-- One hue inside the CFP blue window. -/
noncomputable def blueHueWindow (A : Set ℕ) (h s j : ℕ) : Finset ℕ :=
  rankHuePrefix A h s (j * 2 ^ j) \ rankHuePrefix A h s (2 ^ j)

private theorem rankHuePrefix_mono {A : Set ℕ} (hA : A.Infinite)
    {h s M N : ℕ} (hMN : M ≤ N) :
    rankHuePrefix A h s M ⊆ rankHuePrefix A h s N := by
  intro a ha
  rw [mem_rankHuePrefix_iff hA] at ha ⊢
  exact ⟨ha.1, ha.2.1.trans hMN, ha.2.2⟩

theorem blueHueWindow_subset_blueWindow {A : Set ℕ} (hA : A.Infinite)
    {h s j : ℕ} :
    blueHueWindow A h s j ⊆ blueWindow A j := by
  intro a ha
  have ha' := Finset.mem_sdiff.mp ha
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [mem_rankPrefix_iff hA]
    have hau := (mem_rankHuePrefix_iff hA).mp ha'.1
    exact ⟨hau.1, hau.2.1⟩
  · intro halow
    apply ha'.2
    have hau := (mem_rankHuePrefix_iff hA).mp ha'.1
    have hal := (mem_rankPrefix_iff hA).mp halow
    exact (mem_rankHuePrefix_iff hA).mpr ⟨hau.1, hal.2, hau.2.2⟩

/-- Exponential mass in one hue of a blue window is at most the average
window mass plus the coarse endpoint error `h`. -/
theorem blueHueWindow_exp_balance {A : Set ℕ} (hA : A.Infinite)
    {h s j : ℕ} (hh : 0 < h) (hs : s < h) (hj : 1 ≤ j) :
    (h : ℝ) * (∑ a ∈ blueHueWindow A h s j,
        Real.exp (-(a : ℝ) / (2 ^ (j + 4) : ℕ))) ≤
      blueMass A j + (h : ℝ) ^ 2 := by
  classical
  let U := j * 2 ^ j
  let L := 2 ^ j
  let q : ℕ := 2 ^ (j + 4)
  have hq : 0 < q := by dsimp only [q]; positivity
  let PU : ℝ := ∑ a ∈ rankHuePrefix A h s U,
    Real.exp (-(a : ℝ) / q)
  let PL : ℝ := ∑ a ∈ rankHuePrefix A h s L,
    Real.exp (-(a : ℝ) / q)
  let TU : ℝ := ∑ a ∈ rankPrefix A U,
    Real.exp (-(a : ℝ) / q)
  let TL : ℝ := ∑ a ∈ rankPrefix A L,
    Real.exp (-(a : ℝ) / q)
  have hLU : L ≤ U := by
    dsimp only [L, U]
    exact Nat.le_mul_of_pos_left (2 ^ j) hj
  have hupper : (h : ℝ) * PU ≤ TU + h := by
    simpa [PU, TU, U] using huePrefix_exp_balance hA hh hq
  let w : ℕ → ℝ := fun k ↦ Real.exp (-(enumeration A k : ℝ) / q)
  have hw : Antitone w := by
    intro x y hxy
    apply Real.exp_le_exp.mpr
    have henum := enumeration_monotone hA hxy
    apply div_le_div_of_nonneg_right
    · exact neg_le_neg (by exact_mod_cast henum)
    · positivity
  have hlower0 := sum_residueIndices_lower_of_antitone
    w (m := prefixLength A L) hh hs hw (fun _ ↦ (Real.exp_pos _).le)
  have hwzero : w 0 ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hlower : TL - (h : ℝ) * (h - 1 : ℕ) ≤ (h : ℝ) * PL := by
    dsimp only [TL, PL]
    rw [sum_exp_rankPrefix hA, sum_exp_rankHuePrefix hA]
    calc
      (∑ k ∈ Finset.range (prefixLength A L),
          Real.exp (-(enumeration A k : ℝ) / q)) -
            (h : ℝ) * (h - 1 : ℕ) ≤
        (∑ k ∈ Finset.range (prefixLength A L),
          Real.exp (-(enumeration A k : ℝ) / q)) -
            (h : ℝ) * (h - 1 : ℕ) * w 0 := by
          have hcoef : 0 ≤ (h : ℝ) * (h - 1 : ℕ) := by positivity
          nlinarith
      _ ≤ (h : ℝ) *
          ∑ k ∈ residueIndices (prefixLength A L) h s,
            Real.exp (-(enumeration A k : ℝ) / q) := hlower0
  have hHueDiff :
      (∑ a ∈ blueHueWindow A h s j, Real.exp (-(a : ℝ) / q)) = PU - PL := by
    have hsum := Finset.sum_sdiff (rankHuePrefix_mono hA (h := h) (s := s) hLU)
      (f := fun a : ℕ ↦ Real.exp (-(a : ℝ) / q))
    dsimp only [blueHueWindow, PU, PL, U, L]
    dsimp only [U, L] at hsum
    linarith
  have hTotalDiff : blueMass A j = TU - TL := by
    have hsum := Finset.sum_sdiff (rankPrefix_mono hA hLU)
      (f := fun a : ℕ ↦ Real.exp (-(a : ℝ) / q))
    dsimp only [blueMass, blueWindow, TU, TL, U, L, q]
    dsimp only [U, L, q] at hsum
    norm_num [Nat.cast_pow] at hsum ⊢
    linarith
  change (h : ℝ) * (∑ a ∈ blueHueWindow A h s j,
      Real.exp (-(a : ℝ) / q)) ≤ blueMass A j + (h : ℝ) ^ 2
  rw [hHueDiff, hTotalDiff]
  have hhcast : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hhcast] at hlower
  nlinarith

end Erdos55
