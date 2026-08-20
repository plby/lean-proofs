/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.BlockFamily

/-!
# Erdős Problem 446: lower bounds for elementary reciprocal sums

Ford's block construction selects distinct primes.  This module records the
finite weighted without-replacement estimate which makes that restriction
quantitative.  If the total weight is `W`, every individual weight is at most
`m`, and `r*m ≤ W/2`, then the `r`th elementary sum is at least
`(W/2)^r / r!`.
-/

namespace Erdos446

open Finset
open scoped BigOperators

noncomputable def subsetWeight {α : Type*} [DecidableEq α]
    (w : α → ℝ) (S : Finset α) : ℝ :=
  ∏ x ∈ S, w x

noncomputable def elementaryMass {α : Type*} [DecidableEq α]
    (P : Finset α) (w : α → ℝ) (r : ℕ) : ℝ :=
  ∑ S ∈ P.powersetCard r, subsetWeight w S

def extensionPairs {α : Type*} [DecidableEq α]
    (P : Finset α) (r : ℕ) : Finset (α × Finset α) :=
  (P ×ˢ P.powersetCard r).filter fun pS ↦ pS.1 ∉ pS.2

def deletionPairs {α : Type*} [DecidableEq α]
    (P : Finset α) (r : ℕ) : Finset (Finset α × α) :=
  (P.powersetCard (r + 1) ×ˢ P).filter fun Tp ↦ Tp.2 ∈ Tp.1

theorem mem_extensionPairs {α : Type*} [DecidableEq α]
    {P : Finset α} {r : ℕ} {p : α} {S : Finset α} :
    (p, S) ∈ extensionPairs P r ↔
      p ∈ P ∧ S ⊆ P ∧ S.card = r ∧ p ∉ S := by
  simp [extensionPairs, Finset.mem_powersetCard, and_assoc]

theorem mem_deletionPairs {α : Type*} [DecidableEq α]
    {P : Finset α} {r : ℕ} {T : Finset α} {p : α} :
    (T, p) ∈ deletionPairs P r ↔
      T ⊆ P ∧ T.card = r + 1 ∧ p ∈ P ∧ p ∈ T := by
  simp [deletionPairs, Finset.mem_powersetCard, and_assoc]

theorem subsetWeight_insert {α : Type*} [DecidableEq α]
    (w : α → ℝ) {p : α} {S : Finset α} (hp : p ∉ S) :
    subsetWeight w (insert p S) = w p * subsetWeight w S := by
  simp [subsetWeight, hp]

theorem extension_deletion_weight_bijection
    {α : Type*} [DecidableEq α] (P : Finset α) (w : α → ℝ) (r : ℕ) :
    (∑ pS ∈ extensionPairs P r,
        w pS.1 * subsetWeight w pS.2) =
      ∑ Tp ∈ deletionPairs P r, subsetWeight w Tp.1 := by
  classical
  refine Finset.sum_bij'
      (fun pS _ ↦ (insert pS.1 pS.2, pS.1))
      (fun Tp _ ↦ (Tp.2, Tp.1.erase Tp.2)) ?_ ?_ ?_ ?_ ?_
  · intro pS hpS
    rcases mem_extensionPairs.mp hpS with ⟨hpP, hSP, hScard, hpSnot⟩
    apply mem_deletionPairs.mpr
    refine ⟨?_, ?_, hpP, Finset.mem_insert_self _ _⟩
    · exact Finset.insert_subset hpP hSP
    · rw [Finset.card_insert_of_notMem hpSnot, hScard]
  · intro Tp hTp
    rcases mem_deletionPairs.mp hTp with ⟨hTP, hTcard, hpP, hpT⟩
    apply mem_extensionPairs.mpr
    refine ⟨hpP, (Finset.erase_subset _ _).trans hTP, ?_,
      Finset.notMem_erase _ _⟩
    rw [Finset.card_erase_of_mem hpT, hTcard]
    omega
  · intro pS hpS
    have hpSnot := (mem_extensionPairs.mp hpS).2.2.2
    apply Prod.ext
    · simp [hpSnot]
    · simpa using Finset.erase_insert hpSnot
  · intro Tp hTp
    have hpT := (mem_deletionPairs.mp hTp).2.2.2
    apply Prod.ext
    · exact Finset.insert_erase hpT
    · rfl
  · intro pS hpS
    exact (subsetWeight_insert w
      (mem_extensionPairs.mp hpS).2.2.2).symm

theorem extensionPairs_weight_sum
    {α : Type*} [DecidableEq α] (P : Finset α) (w : α → ℝ) (r : ℕ) :
    (∑ pS ∈ extensionPairs P r,
        w pS.1 * subsetWeight w pS.2) =
      ∑ S ∈ P.powersetCard r,
        subsetWeight w S * (∑ p ∈ P \ S, w p) := by
  classical
  rw [extensionPairs, Finset.sum_filter, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mul_sum]
  calc
    (∑ p ∈ P, if p ∉ S then w p * subsetWeight w S else 0) =
        ∑ p ∈ P.filter (fun p ↦ p ∉ S),
          w p * subsetWeight w S := by
      rw [Finset.sum_filter]
    _ = ∑ p ∈ P \ S, subsetWeight w S * w p := by
      apply Finset.sum_congr
      · ext p
        simp
      · intro p hp
        ring

theorem deletionPairs_weight_sum
    {α : Type*} [DecidableEq α] (P : Finset α) (w : α → ℝ) (r : ℕ) :
    (∑ Tp ∈ deletionPairs P r, subsetWeight w Tp.1) =
      (r + 1 : ℝ) * elementaryMass P w (r + 1) := by
  classical
  rw [deletionPairs, Finset.sum_filter, Finset.sum_product,
    elementaryMass]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have hTP := (Finset.mem_powersetCard.mp hT).1
  have hTcard := (Finset.mem_powersetCard.mp hT).2
  calc
    (∑ p ∈ P, if p ∈ T then subsetWeight w T else 0) =
        ∑ p ∈ T, if p ∈ T then subsetWeight w T else 0 := by
      symm
      apply Finset.sum_subset hTP
      intro p hpP hpT
      simp [hpT]
    _ = ∑ p ∈ T, subsetWeight w T := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [hp]
    _ = (r + 1 : ℝ) * subsetWeight w T := by
      simp [hTcard, nsmul_eq_mul]

theorem elementaryMass_double_count
    {α : Type*} [DecidableEq α] (P : Finset α) (w : α → ℝ) (r : ℕ) :
    (r + 1 : ℝ) * elementaryMass P w (r + 1) =
      ∑ S ∈ P.powersetCard r,
        subsetWeight w S * (∑ p ∈ P \ S, w p) := by
  rw [← deletionPairs_weight_sum P w r,
    ← extension_deletion_weight_bijection P w r,
    extensionPairs_weight_sum]

theorem subsetWeight_nonneg {α : Type*} [DecidableEq α]
    {w : α → ℝ} (hw : ∀ x, 0 ≤ w x) (S : Finset α) :
    0 ≤ subsetWeight w S := by
  exact Finset.prod_nonneg fun x hx ↦ hw x

theorem elementaryMass_nonneg {α : Type*} [DecidableEq α]
    {w : α → ℝ} (hw : ∀ x, 0 ≤ w x) (P : Finset α) (r : ℕ) :
    0 ≤ elementaryMass P w r := by
  exact Finset.sum_nonneg fun S hS ↦ subsetWeight_nonneg hw S

theorem elementaryMass_nonneg_of_mem {α : Type*} [DecidableEq α]
    {w : α → ℝ} {P : Finset α} (hw : ∀ x ∈ P, 0 ≤ w x) (r : ℕ) :
    0 ≤ elementaryMass P w r := by
  apply Finset.sum_nonneg
  intro S hS
  apply Finset.prod_nonneg
  intro x hx
  exact hw x ((Finset.mem_powersetCard.mp hS).1 hx)

theorem subset_sum_le_card_mul
    {α : Type*} [DecidableEq α] {P S : Finset α}
    {w : α → ℝ} {m : ℝ} (hSP : S ⊆ P)
    (hw : ∀ x ∈ P, 0 ≤ w x ∧ w x ≤ m) :
    (∑ x ∈ S, w x) ≤ (S.card : ℝ) * m := by
  calc
    (∑ x ∈ S, w x) ≤ ∑ _x ∈ S, m := by
      apply Finset.sum_le_sum
      intro x hx
      exact (hw x (hSP hx)).2
    _ = (S.card : ℝ) * m := by
      simp [nsmul_eq_mul]

theorem complement_weight_lower
    {α : Type*} [DecidableEq α] {P S : Finset α}
    {w : α → ℝ} {m W : ℝ} (hSP : S ⊆ P)
    (hcard : S.card = r)
    (hW : W = ∑ x ∈ P, w x)
    (hw : ∀ x ∈ P, 0 ≤ w x ∧ w x ≤ m) :
    W - (r : ℝ) * m ≤ ∑ x ∈ P \ S, w x := by
  have hsplit :
      (∑ x ∈ P \ S, w x) + (∑ x ∈ S, w x) = ∑ x ∈ P, w x :=
    Finset.sum_sdiff hSP
  have hSle := subset_sum_le_card_mul hSP hw
  rw [hcard] at hSle
  rw [hW]
  linarith

theorem elementaryMass_step_lower
    {α : Type*} [DecidableEq α] (P : Finset α) (w : α → ℝ)
    {m W : ℝ} (hW : W = ∑ x ∈ P, w x)
    (hw : ∀ x ∈ P, 0 ≤ w x ∧ w x ≤ m) (r : ℕ) :
    (W - (r : ℝ) * m) * elementaryMass P w r ≤
      (r + 1 : ℝ) * elementaryMass P w (r + 1) := by
  rw [elementaryMass_double_count]
  rw [elementaryMass]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  have hSP := (Finset.mem_powersetCard.mp hS).1
  have hcard := (Finset.mem_powersetCard.mp hS).2
  simpa only [subsetWeight, mul_comm] using
    (mul_le_mul_of_nonneg_left
      (complement_weight_lower hSP hcard hW hw)
      (by
      apply Finset.prod_nonneg
      intro x hx
      exact (hw x (hSP hx)).1))

theorem elementaryMass_zero {α : Type*} [DecidableEq α]
    (P : Finset α) (w : α → ℝ) :
    elementaryMass P w 0 = 1 := by
  simp [elementaryMass, subsetWeight]

/-- Weighted sampling without replacement loses at most a factor `2^r` when
the requested sample is small compared with the largest atom. -/
theorem pow_half_total_le_factorial_mul_elementaryMass
    {α : Type*} [DecidableEq α] (P : Finset α) (w : α → ℝ)
    {m W : ℝ} (hW : W = ∑ x ∈ P, w x)
    (hw : ∀ x ∈ P, 0 ≤ w x ∧ w x ≤ m)
    {r : ℕ} (hr : (r : ℝ) * m ≤ W / 2) :
    (W / 2) ^ r ≤ (r.factorial : ℝ) * elementaryMass P w r := by
  have hWnonneg : 0 ≤ W := by
    rw [hW]
    exact Finset.sum_nonneg fun x hx ↦ (hw x hx).1
  induction r with
  | zero => simp [elementaryMass_zero]
  | succ r ihr =>
      have hr' : (r : ℝ) * m ≤ W / 2 := by
        by_cases hP : P.Nonempty
        · obtain ⟨x, hx⟩ := hP
          have hmnonneg : 0 ≤ m := (hw x hx).1.trans (hw x hx).2
          have : (r : ℝ) * m ≤ (r + 1 : ℝ) * m := by
            nlinarith
          exact this.trans (by simpa [Nat.cast_succ] using hr)
        · have hPempty := Finset.not_nonempty_iff_eq_empty.mp hP
          have hWzero : W = 0 := by
            rw [hW, hPempty, Finset.sum_empty]
          rw [hWzero] at hr ⊢
          have hrnonneg : (0 : ℝ) ≤ r := by positivity
          have hcoef : (0 : ℝ) < (r : ℝ) + 1 := by positivity
          have hmle : m ≤ 0 := by
            have : m ≤ 0 / ((r : ℝ) + 1) := by
              apply (le_div_iff₀ hcoef).2
              simpa only [Nat.cast_succ, zero_div, zero_mul, mul_comm] using hr
            simpa using this
          simpa using mul_nonpos_of_nonneg_of_nonpos hrnonneg hmle
      have hi := ihr hr'
      have hstep := elementaryMass_step_lower P w hW hw r
      have hfactor : W / 2 ≤ W - (r : ℝ) * m := by linarith
      have hEnonneg := elementaryMass_nonneg_of_mem
        (fun x hx ↦ (hw x hx).1) r
      have hscaled :
          (W / 2) * elementaryMass P w r ≤
            (r + 1 : ℝ) * elementaryMass P w (r + 1) :=
        (mul_le_mul_of_nonneg_right hfactor hEnonneg).trans hstep
      calc
        (W / 2) ^ (r + 1) = (W / 2) ^ r * (W / 2) := by
          rw [pow_succ]
        _ ≤ ((r.factorial : ℝ) * elementaryMass P w r) * (W / 2) := by
          exact mul_le_mul_of_nonneg_right hi
            (div_nonneg hWnonneg (by norm_num))
        _ = (r.factorial : ℝ) *
            ((W / 2) * elementaryMass P w r) := by ring
        _ ≤ (r.factorial : ℝ) *
            ((r + 1 : ℝ) * elementaryMass P w (r + 1)) := by
          exact mul_le_mul_of_nonneg_left hscaled (by positivity)
        _ = ((r + 1).factorial : ℝ) *
            elementaryMass P w (r + 1) := by
          rw [Nat.factorial_succ]
          push_cast
          ring

theorem half_total_pow_div_factorial_le_elementaryMass
    {α : Type*} [DecidableEq α] (P : Finset α) (w : α → ℝ)
    {m W : ℝ} (hW : W = ∑ x ∈ P, w x)
    (hw : ∀ x ∈ P, 0 ≤ w x ∧ w x ≤ m)
    {r : ℕ} (hr : (r : ℝ) * m ≤ W / 2) :
    (W / 2) ^ r / (r.factorial : ℝ) ≤ elementaryMass P w r := by
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < r.factorial)).2
    (by simpa [mul_comm] using
      pow_half_total_le_factorial_mul_elementaryMass P w hW hw hr)

/-- Sharp without-replacement lower bound: the successive available masses
are `W, W-m, ..., W-(r-1)m`.  Unlike the coarse half-mass corollary above,
this form permits all block losses to be combined into one bounded factor. -/
theorem fallingMass_le_factorial_mul_elementaryMass
    {α : Type*} [DecidableEq α] (P : Finset α) (w : α → ℝ)
    {m W : ℝ} (hW : W = ∑ x ∈ P, w x)
    (hw : ∀ x ∈ P, 0 ≤ w x ∧ w x ≤ m) (hm : 0 ≤ m)
    (r : ℕ) (hr : (r : ℝ) * m ≤ W) :
    (∏ j ∈ Finset.range r, (W - (j : ℝ) * m)) ≤
      (r.factorial : ℝ) * elementaryMass P w r := by
  induction r with
  | zero => simp [elementaryMass_zero]
  | succ r ih =>
      have hr0 : (r : ℝ) * m ≤ W := by
        calc
          (r : ℝ) * m ≤ (r + 1 : ℝ) * m := by nlinarith
          _ ≤ W := by simpa [Nat.cast_succ] using hr
      have hfactor : 0 ≤ W - (r : ℝ) * m := sub_nonneg.mpr hr0
      have hprev := ih hr0
      have hstep := elementaryMass_step_lower P w hW hw r
      rw [Finset.prod_range_succ]
      calc
        (∏ j ∈ Finset.range r, (W - (j : ℝ) * m)) *
            (W - (r : ℝ) * m) ≤
            ((r.factorial : ℝ) * elementaryMass P w r) *
              (W - (r : ℝ) * m) :=
          mul_le_mul_of_nonneg_right hprev hfactor
        _ = (r.factorial : ℝ) *
            ((W - (r : ℝ) * m) * elementaryMass P w r) := by ring
        _ ≤ (r.factorial : ℝ) *
            ((r + 1 : ℝ) * elementaryMass P w (r + 1)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = ((r + 1).factorial : ℝ) *
            elementaryMass P w (r + 1) := by
          rw [Nat.factorial_succ]
          push_cast
          ring

theorem fallingMass_div_factorial_le_elementaryMass
    {α : Type*} [DecidableEq α] (P : Finset α) (w : α → ℝ)
    {m W : ℝ} (hW : W = ∑ x ∈ P, w x)
    (hw : ∀ x ∈ P, 0 ≤ w x ∧ w x ≤ m) (hm : 0 ≤ m)
    (r : ℕ) (hr : (r : ℝ) * m ≤ W) :
    (∏ j ∈ Finset.range r, (W - (j : ℝ) * m)) /
        (r.factorial : ℝ) ≤ elementaryMass P w r := by
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < r.factorial)).2
    (by simpa [mul_comm] using
      fallingMass_le_factorial_mul_elementaryMass P w hW hw hm r hr)

end Erdos446
