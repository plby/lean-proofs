/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.WeightedOccupancyBridge
import ErdosProblems.Erdos446.SmirnovWordBarrierBridge

/-!
# Erdős Problem 446: finite quantile comparison for weighted words

This file contains the fixed-`M` replacement for a pointwise comparison of
prime-block masses.  A categorical law is compared with a second law through
its cumulative masses.  Discrete summation by parts gives the one-coordinate
comparison, and induction on the word length lifts it to every coordinatewise
upward-closed event.  In particular, the argument never multiplies a
pointwise block-mass error `k` times.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-! ## One-dimensional finite stochastic comparison -/

/-- Discrete summation by parts on `range (n+1)`. -/
theorem sum_range_mul_eq_prefix_last_sub
    (r f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), r i * f i) =
      (∑ i ∈ Finset.range (n + 1), r i) * f n -
        ∑ h ∈ Finset.range n,
          (∑ i ∈ Finset.range (h + 1), r i) *
            (f (h + 1) - f h) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (∑ i ∈ Finset.range (n + 1 + 1), r i * f i) =
            (∑ i ∈ Finset.range (n + 1), r i * f i) +
              r (n + 1) * f (n + 1) := by
                rw [Finset.sum_range_succ]
        _ = ((∑ i ∈ Finset.range (n + 1), r i) * f n -
              ∑ h ∈ Finset.range n,
                (∑ i ∈ Finset.range (h + 1), r i) *
                  (f (h + 1) - f h)) +
              r (n + 1) * f (n + 1) := by rw [ih]
        _ = (∑ i ∈ Finset.range (n + 1 + 1), r i) * f (n + 1) -
              ∑ h ∈ Finset.range (n + 1),
                (∑ i ∈ Finset.range (h + 1), r i) *
                  (f (h + 1) - f h) := by
            have hR : (∑ i ∈ Finset.range (n + 1 + 1), r i) =
                (∑ i ∈ Finset.range (n + 1), r i) + r (n + 1) := by
              rw [Finset.sum_range_succ]
            have hH :
                (∑ h ∈ Finset.range (n + 1),
                  (∑ i ∈ Finset.range (h + 1), r i) *
                    (f (h + 1) - f h)) =
                  (∑ h ∈ Finset.range n,
                    (∑ i ∈ Finset.range (h + 1), r i) *
                      (f (h + 1) - f h)) +
                    (∑ i ∈ Finset.range (n + 1), r i) *
                      (f (n + 1) - f n) := by
              rw [Finset.sum_range_succ]
            rw [hR, hH]
            ring

/-- If `p` has at least as much mass as `q` in every initial segment and
the same total mass, then its expectation against an increasing function is
no larger. -/
theorem sum_range_mul_le_of_prefix_ge
    {p q f : ℕ → ℝ} {n : ℕ}
    (htotal : (∑ i ∈ Finset.range (n + 1), p i) =
      ∑ i ∈ Finset.range (n + 1), q i)
    (hprefix : ∀ h : ℕ, h ≤ n →
      (∑ i ∈ Finset.range (h + 1), q i) ≤
        ∑ i ∈ Finset.range (h + 1), p i)
    (hf : ∀ h : ℕ, h < n → f h ≤ f (h + 1)) :
    (∑ i ∈ Finset.range (n + 1), p i * f i) ≤
      ∑ i ∈ Finset.range (n + 1), q i * f i := by
  let r : ℕ → ℝ := fun i ↦ p i - q i
  have htotalR : (∑ i ∈ Finset.range (n + 1), r i) = 0 := by
    dsimp [r]
    rw [Finset.sum_sub_distrib, htotal]
    ring
  have hprefR : ∀ h : ℕ, h ≤ n →
      0 ≤ ∑ i ∈ Finset.range (h + 1), r i := by
    intro h hhn
    dsimp [r]
    rw [Finset.sum_sub_distrib]
    linarith [hprefix h hhn]
  have hinc : ∀ h ∈ Finset.range n,
      0 ≤ (∑ i ∈ Finset.range (h + 1), r i) *
        (f (h + 1) - f h) := by
    intro h hh
    exact mul_nonneg (hprefR h (Nat.le_of_lt (Finset.mem_range.mp hh)))
      (sub_nonneg.mpr (hf h (Finset.mem_range.mp hh)))
  have hparts := sum_range_mul_eq_prefix_last_sub r f n
  rw [htotalR, zero_mul, zero_sub] at hparts
  have hnonneg : 0 ≤ ∑ h ∈ Finset.range n,
      (∑ i ∈ Finset.range (h + 1), r i) *
        (f (h + 1) - f h) := Finset.sum_nonneg hinc
  have hdiff :
      (∑ i ∈ Finset.range (n + 1), p i * f i) -
          (∑ i ∈ Finset.range (n + 1), q i * f i) =
        ∑ i ∈ Finset.range (n + 1), r i * f i := by
    dsimp [r]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  linarith [hdiff, hparts, hnonneg]

/-- Initial mass of a law on `Fin v`. -/
noncomputable def finPrefixMass {v : ℕ} (p : Fin v → ℝ) (h : ℕ) : ℝ :=
  ∑ i ∈ (Finset.univ.filter fun i : Fin v ↦ i.val < h), p i

theorem sum_range_restrict_eq_finPrefixMass
    {v h : ℕ} (p : Fin v → ℝ) (hhv : h ≤ v) :
    (∑ i ∈ Finset.range h,
      if hi : i < v then p ⟨i, hi⟩ else 0) = finPrefixMass p h := by
  classical
  rw [finPrefixMass]
  apply Finset.sum_bij
      (fun i hi ↦ (⟨i, (Finset.mem_range.mp hi).trans_le hhv⟩ : Fin v))
  · intro i hi
    simp [Finset.mem_range.mp hi]
  · intro i₁ hi₁ i₂ hi₂ heq
    exact Fin.ext_iff.mp heq
  · intro j hj
    have hjlt : j.val < h := (Finset.mem_filter.mp hj).2
    refine ⟨j.val, Finset.mem_range.mpr hjlt, ?_⟩
    exact Fin.ext rfl
  · intro i hi
    have hiv : i < v := (Finset.mem_range.mp hi).trans_le hhv
    simp [hiv]

theorem finPrefixMass_eq_sum_of_le {v h : ℕ}
    (p : Fin v → ℝ) (hvh : v ≤ h) :
    finPrefixMass p h = ∑ i, p i := by
  rw [finPrefixMass, Finset.filter_eq_self.2]
  intro i hi
  exact i.isLt.trans_le hvh

/-- Finite stochastic comparison in `Fin` notation. -/
theorem fin_expectation_le_of_prefix_ge
    {v : ℕ} (hv : 0 < v) {p q f : Fin v → ℝ}
    (htotal : (∑ i, p i) = ∑ i, q i)
    (hprefix : ∀ h : ℕ, 1 ≤ h → h ≤ v →
      finPrefixMass q h ≤ finPrefixMass p h)
    (hf : Monotone f) :
    (∑ i, p i * f i) ≤ ∑ i, q i * f i := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hv)
  let p' : ℕ → ℝ := fun i ↦ if hi : i < n + 1 then p ⟨i, hi⟩ else 0
  let q' : ℕ → ℝ := fun i ↦ if hi : i < n + 1 then q ⟨i, hi⟩ else 0
  let f' : ℕ → ℝ := fun i ↦ if hi : i < n + 1 then f ⟨i, hi⟩ else 0
  have hpSum : (∑ i ∈ Finset.range (n + 1), p' i) = ∑ i, p i := by
    exact (sum_range_restrict_eq_finPrefixMass p le_rfl).trans
      (finPrefixMass_eq_sum_of_le p le_rfl)
  have hqSum : (∑ i ∈ Finset.range (n + 1), q' i) = ∑ i, q i := by
    exact (sum_range_restrict_eq_finPrefixMass q le_rfl).trans
      (finPrefixMass_eq_sum_of_le q le_rfl)
  have hpfSum : (∑ i ∈ Finset.range (n + 1), p' i * f' i) =
      ∑ i, p i * f i := by
    calc
      (∑ i ∈ Finset.range (n + 1), p' i * f' i) =
          ∑ i ∈ Finset.range (n + 1),
            if hi : i < n + 1 then p ⟨i, hi⟩ * f ⟨i, hi⟩ else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              have hil : i < n + 1 := Finset.mem_range.mp hi
              have hil' : i ≤ n := by omega
              simp [p', f', hil, hil']
      _ = finPrefixMass (fun i ↦ p i * f i) (n + 1) :=
        sum_range_restrict_eq_finPrefixMass (fun i ↦ p i * f i) le_rfl
      _ = ∑ i, p i * f i :=
        finPrefixMass_eq_sum_of_le (fun i ↦ p i * f i) le_rfl
  have hqfSum : (∑ i ∈ Finset.range (n + 1), q' i * f' i) =
      ∑ i, q i * f i := by
    calc
      (∑ i ∈ Finset.range (n + 1), q' i * f' i) =
          ∑ i ∈ Finset.range (n + 1),
            if hi : i < n + 1 then q ⟨i, hi⟩ * f ⟨i, hi⟩ else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              have hil : i < n + 1 := Finset.mem_range.mp hi
              have hil' : i ≤ n := by omega
              simp [q', f', hil, hil']
      _ = finPrefixMass (fun i ↦ q i * f i) (n + 1) :=
        sum_range_restrict_eq_finPrefixMass (fun i ↦ q i * f i) le_rfl
      _ = ∑ i, q i * f i :=
        finPrefixMass_eq_sum_of_le (fun i ↦ q i * f i) le_rfl
  have hpref' : ∀ h : ℕ, h ≤ n →
      (∑ i ∈ Finset.range (h + 1), q' i) ≤
        ∑ i ∈ Finset.range (h + 1), p' i := by
    intro h hhn
    have hhpos : 1 ≤ h + 1 := by omega
    have hhle : h + 1 ≤ n + 1 := by omega
    have hqPrefix : (∑ i ∈ Finset.range (h + 1), q' i) =
        finPrefixMass q (h + 1) := by
      exact sum_range_restrict_eq_finPrefixMass q hhle
    have hpPrefix : (∑ i ∈ Finset.range (h + 1), p' i) =
        finPrefixMass p (h + 1) := by
      exact sum_range_restrict_eq_finPrefixMass p hhle
    rw [hqPrefix, hpPrefix]
    exact hprefix (h + 1) hhpos hhle
  have hf' : ∀ h : ℕ, h < n → f' h ≤ f' (h + 1) := by
    intro h hhn
    have hh : h < n + 1 := by omega
    have hh1 : h + 1 < n + 1 := by omega
    simp only [f', dif_pos hh, dif_pos hh1]
    exact hf (by exact_mod_cast (show h ≤ h + 1 by omega))
  have hcmp := sum_range_mul_le_of_prefix_ge
    (p := p') (q := q') (f := f') (n := n)
    (by simpa [hpSum, hqSum] using htotal) hpref' hf'
  simpa [hpfSum, hqfSum] using hcmp

/-! ## Product words -/

/-- The product weight of a labelled word. -/
noncomputable def weightedWordMass {k v : ℕ}
    (p : Fin v → ℝ) (f : Fin k → Fin v) : ℝ :=
  ∏ i, p (f i)

/-- Mass of a predicate on labelled words. -/
noncomputable def weightedWordEventMass {k v : ℕ}
    (p : Fin v → ℝ) (P : (Fin k → Fin v) → Prop) : ℝ := by
  classical
  exact ∑ f, if P f then weightedWordMass p f else 0

/-- A word event preserved by moving every letter to the right. -/
def UpwardClosedWordEvent {k v : ℕ}
    (P : (Fin k → Fin v) → Prop) : Prop :=
  ∀ ⦃f g : Fin k → Fin v⦄, (∀ i, f i ≤ g i) → P f → P g

theorem weightedWordEventMass_succ {k v : ℕ}
    (p : Fin v → ℝ) (P : (Fin (k + 1) → Fin v) → Prop) :
    weightedWordEventMass p P =
      ∑ x : Fin v, p x * weightedWordEventMass p
        (fun t : Fin k → Fin v ↦ P (Fin.cons x t)) := by
  classical
  rw [weightedWordEventMass]
  have hsplit :
      (∑ f : Fin (k + 1) → Fin v,
          if P f then weightedWordMass p f else 0) =
        ∑ z : Fin v × (Fin k → Fin v),
          if P (Fin.cons z.1 z.2) then
            weightedWordMass p (Fin.cons z.1 z.2) else 0 := by
    apply Fintype.sum_equiv
      (Fin.consEquiv (fun _ : Fin (k + 1) ↦ Fin v)).symm
    intro f
    simp [Fin.consEquiv, Fin.cons_self_tail]
  rw [hsplit, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  rw [weightedWordEventMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [weightedWordMass, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  split_ifs <;> simp [weightedWordMass]

/-- Prefix stochastic dominance lifts to every upward-closed event of an
i.i.d. word. -/
theorem weightedWordEventMass_le_of_prefix_ge
    {k v : ℕ} (hv : 0 < v) {p q : Fin v → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (htotal : (∑ i, p i) = ∑ i, q i)
    (hprefix : ∀ h : ℕ, 1 ≤ h → h ≤ v →
      finPrefixMass q h ≤ finPrefixMass p h)
    {P : (Fin k → Fin v) → Prop} (hP : UpwardClosedWordEvent P) :
    weightedWordEventMass p P ≤ weightedWordEventMass q P := by
  induction k with
  | zero =>
      simp [weightedWordEventMass, weightedWordMass]
  | succ k ih =>
      rw [weightedWordEventMass_succ, weightedWordEventMass_succ]
      let Ap : Fin v → ℝ := fun x ↦ weightedWordEventMass p
        (fun t : Fin k → Fin v ↦ P (Fin.cons x t))
      let Aq : Fin v → ℝ := fun x ↦ weightedWordEventMass q
        (fun t : Fin k → Fin v ↦ P (Fin.cons x t))
      have hslice (x : Fin v) : Ap x ≤ Aq x := by
        apply ih
        · intro f g hfg hfP
          apply hP (f := Fin.cons x f) (g := Fin.cons x g)
          · intro i
            refine Fin.cases ?_ (fun j ↦ ?_) i
            · simp
            · simpa using hfg j
          · exact hfP
      have hfirst : (∑ x : Fin v, p x * Ap x) ≤
          ∑ x : Fin v, p x * Aq x := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hslice x) (hp x)
      apply hfirst.trans
      apply fin_expectation_le_of_prefix_ge hv htotal hprefix
      intro x y hxy
      dsimp [Aq, weightedWordEventMass]
      apply Finset.sum_le_sum
      intro t ht
      have hmonoP : P (Fin.cons x t) → P (Fin.cons y t) := by
        intro hPt
        apply hP (f := Fin.cons x t) (g := Fin.cons y t)
        · intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simpa using hxy
          · simp
        · exact hPt
      by_cases hxP : P (Fin.cons x t)
      · have hyP := hmonoP hxP
        simp [hxP, hyP]
      · simp [hxP]
        split_ifs
        · exact Finset.prod_nonneg fun i hi ↦ hq _
        · exact le_rfl

/-! ## The one-cell shifted uniform law -/

/-- Move a uniform cell one step to the right, keeping the final cell fixed. -/
def shiftRightCell {v : ℕ} (hv : 0 < v) (i : Fin v) : Fin v :=
  ⟨min (i.val + 1) (v - 1), by
    have hm : min (i.val + 1) (v - 1) ≤ v - 1 := min_le_right _ _
    omega⟩

theorem le_shiftRightCell {v : ℕ} (hv : 0 < v) (i : Fin v) :
    i ≤ shiftRightCell hv i := by
  rw [Fin.le_iff_val_le_val]
  dsimp [shiftRightCell]
  have hi : i.val ≤ v - 1 := by omega
  omega

theorem shiftRightCell_lt_iff {v h : ℕ} (hv : 0 < v)
    (hh : 1 ≤ h) (hhv : h < v) (i : Fin v) :
    (shiftRightCell hv i).val < h ↔ i.val < h - 1 := by
  dsimp [shiftRightCell]
  omega

/-- The pushforward of the uniform law by `shiftRightCell`. -/
noncomputable def rightShiftUniformMass {v : ℕ} (hv : 0 < v) : Fin v → ℝ :=
  fun j ↦ ∑ i : Fin v,
    if shiftRightCell hv i = j then 1 / (v : ℝ) else 0

theorem rightShiftUniformMass_nonneg {v : ℕ} (hv : 0 < v)
    (j : Fin v) : 0 ≤ rightShiftUniformMass hv j := by
  dsimp [rightShiftUniformMass]
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · positivity
  · exact le_rfl

theorem sum_rightShiftUniformMass {v : ℕ} (hv : 0 < v) :
    (∑ j, rightShiftUniformMass hv j) = 1 := by
  simp only [rightShiftUniformMass]
  rw [Finset.sum_comm]
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  simp [hvR]

theorem finPrefixMass_rightShiftUniformMass_of_lt
    {v h : ℕ} (hv : 0 < v) (hh : 1 ≤ h) (hhv : h < v) :
    finPrefixMass (rightShiftUniformMass hv) h =
      ((h - 1 : ℕ) : ℝ) / (v : ℝ) := by
  rw [finPrefixMass]
  simp only [rightShiftUniformMass]
  rw [Finset.sum_comm]
  have hinner (i : Fin v) :
      (∑ j ∈ (Finset.univ.filter fun j : Fin v ↦ j.val < h),
        if shiftRightCell hv i = j then 1 / (v : ℝ) else 0) =
        if i.val < h - 1 then 1 / (v : ℝ) else 0 := by
    by_cases hi : i.val < h - 1
    · have hs : (shiftRightCell hv i).val < h :=
        (shiftRightCell_lt_iff hv hh hhv i).2 hi
      simp [hs, hi]
    · have hs : ¬(shiftRightCell hv i).val < h := by
        simpa [shiftRightCell_lt_iff hv hh hhv i] using hi
      simp [hs, hi]
  simp_rw [hinner]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    Fin.card_filter_val_lt]
  have hsuble : h - 1 ≤ v := by omega
  rw [min_eq_right hsuble]
  ring

theorem finPrefixMass_rightShiftUniformMass
    {v h : ℕ} (hv : 0 < v) (hh : 1 ≤ h) (hhv : h ≤ v) :
    finPrefixMass (rightShiftUniformMass hv) h =
      if h < v then ((h - 1 : ℕ) : ℝ) / (v : ℝ) else 1 := by
  by_cases hlt : h < v
  · rw [if_pos hlt]
    exact finPrefixMass_rightShiftUniformMass_of_lt hv hh hlt
  · rw [if_neg hlt, finPrefixMass_eq_sum_of_le]
    · exact sum_rightShiftUniformMass hv
    · omega

/-! ## Pushforward identity on words -/

theorem weightedWordEventMass_rightShiftUniform {k v : ℕ}
    (hv : 0 < v) (P : (Fin k → Fin v) → Prop) :
    weightedWordEventMass (rightShiftUniformMass hv) P =
      weightedWordEventMass (fun _ : Fin v ↦ 1 / (v : ℝ))
        (fun f ↦ P (fun i ↦ shiftRightCell hv (f i))) := by
  classical
  induction k with
  | zero =>
      simp only [weightedWordEventMass, weightedWordMass,
        Fintype.prod_empty]
      apply Finset.sum_congr rfl
      intro f hf
      have heq : (fun i ↦ shiftRightCell hv (f i)) = f :=
        Subsingleton.elim _ _
      simp [heq]
  | succ k ih =>
      rw [weightedWordEventMass_succ, weightedWordEventMass_succ]
      simp_rw [ih]
      simp only [rightShiftUniformMass, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_eq_single (shiftRightCell hv x)]
      · simp only [one_div]
        congr 1
        apply congrArg (weightedWordEventMass (fun _ : Fin v ↦ (v : ℝ)⁻¹))
        funext t
        congr 1
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
      · intro y hy hne
        simp [hne.symm]
      · simp

noncomputable def wordEventFinset {k v : ℕ}
    (P : (Fin k → Fin v) → Prop) : Finset (Fin k → Fin v) := by
  classical
  exact Finset.univ.filter P

theorem weightedWordEventMass_eq_sum_wordEventFinset {k v : ℕ}
    (p : Fin v → ℝ) (P : (Fin k → Fin v) → Prop) :
    weightedWordEventMass p P =
      ∑ f ∈ wordEventFinset P, weightedWordMass p f := by
  classical
  rw [weightedWordEventMass, wordEventFinset, Finset.sum_filter]

theorem weightedWordEventMass_const {k v : ℕ} (a : ℝ)
    (P : (Fin k → Fin v) → Prop) :
    weightedWordEventMass (fun _ : Fin v ↦ a) P =
      a ^ k * ((wordEventFinset P).card : ℝ) := by
  classical
  rw [weightedWordEventMass, wordEventFinset]
  calc
    (∑ f, if P f then weightedWordMass (fun _ : Fin v ↦ a) f else 0) =
        ∑ f, if P f then a ^ k else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [weightedWordMass, Fin.prod_const]
    _ = ∑ f ∈ Finset.univ.filter P, a ^ k := by
      rw [Finset.sum_filter]
    _ = a ^ k * ((Finset.univ.filter P).card : ℝ) := by
      simp [mul_comm]

theorem weightedWordMass_eq_occupancyProduct {k v : ℕ}
    (lam : Fin v → ℝ) (f : Fin k → Fin v) :
    weightedWordMass lam f = ∏ j : Fin v, lam j ^ wordOccupancy f j := by
  classical
  rw [weightedWordMass, ← Finset.prod_fiberwise
    (s := (Finset.univ : Finset (Fin k))) (g := f) (f := fun i ↦ lam (f i))]
  apply Finset.prod_congr rfl
  intro j hj
  calc
    (∏ i ∈ (Finset.univ.filter fun i : Fin k ↦ f i = j), lam (f i)) =
        ∏ i ∈ (Finset.univ.filter fun i : Fin k ↦ f i = j), lam j := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = lam j ^ wordOccupancy f j := by
      rw [wordOccupancy, Finset.prod_const]

/-- The labelled-word form of the weighted multinomial identity, restricted
to an arbitrary family of compositions. -/
theorem weightedWordEventMass_occupancy_eq
    {k v : ℕ} (lam : Fin v → ℝ) (I : Finset (Fin v → ℕ))
    (hI : I ⊆ compositionsOf v k) :
    weightedWordEventMass lam
        (fun f : Fin k → Fin v ↦ wordOccupancy f ∈ I) =
      (k.factorial : ℝ) * weightedOccupancyMassOver lam I := by
  classical
  rw [weightedWordEventMass_eq_sum_wordEventFinset,
    weightedOccupancyMassOver, Finset.mul_sum]
  have hset : wordEventFinset
      (fun f : Fin k → Fin v ↦ wordOccupancy f ∈ I) =
      (Finset.univ.filter fun f : Fin k → Fin v ↦ wordOccupancy f ∈ I) := by
    ext f
    simp [wordEventFinset]
  rw [hset]
  have hgroup :
      (∑ f ∈ (Finset.univ.filter fun f : Fin k → Fin v ↦
        wordOccupancy f ∈ I), weightedWordMass lam f) =
        ∑ c ∈ I,
          ∑ f ∈ (Finset.univ.filter fun f : Fin k → Fin v ↦
            wordOccupancy f = c), weightedWordMass lam f := by
    simpa only using (Finset.sum_fiberwise_eq_sum_filter
      (s := (Finset.univ : Finset (Fin k → Fin v)))
      (t := I) (g := wordOccupancy)
      (f := weightedWordMass lam)).symm
  have hrest :
      (∑ c ∈ I,
        ∑ f ∈ (Finset.univ.filter fun f : Fin k → Fin v ↦
          wordOccupancy f = c), weightedWordMass lam f) =
        ∑ c ∈ I, (k.factorial : ℝ) * weightedCompositionMass lam c := by
    calc
    (∑ c ∈ I,
        ∑ f ∈ (Finset.univ.filter fun f : Fin k → Fin v ↦
          wordOccupancy f = c), weightedWordMass lam f) = ∑ c ∈ I,
        (Nat.multinomial Finset.univ c : ℝ) *
          ∏ j : Fin v, lam j ^ c j := by
      apply Finset.sum_congr rfl
      intro c hc
      have hcsum : ∑ j, c j = k := mem_compositionsOf.mp (hI hc)
      calc
        (∑ f ∈ (Finset.univ.filter fun f : Fin k → Fin v ↦
            wordOccupancy f = c), weightedWordMass lam f) =
            ∑ f ∈ (Finset.univ.filter fun f : Fin k → Fin v ↦
              wordOccupancy f = c), ∏ j : Fin v, lam j ^ c j := by
          apply Finset.sum_congr rfl
          intro f hf
          rw [weightedWordMass_eq_occupancyProduct,
            (Finset.mem_filter.mp hf).2]
        _ = ((Finset.univ.filter fun f : Fin k → Fin v ↦
              wordOccupancy f = c).card : ℝ) *
              ∏ j : Fin v, lam j ^ c j := by simp
        _ = (Nat.multinomial Finset.univ c : ℝ) *
              ∏ j : Fin v, lam j ^ c j := by
          rw [card_wordOccupancy_fiber c hcsum]
    _ = ∑ c ∈ I,
        (k.factorial : ℝ) * weightedCompositionMass lam c := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [weightedCompositionMass, div_eq_mul_inv,
        ← one_div (compositionFactorial c),
        inv_compositionFactorial_eq_multinomial_div_of_mem (hI hc)]
      field_simp
  exact hgroup.trans hrest

theorem weightedWordEventMass_scale {k v : ℕ}
    (L : ℝ) (p : Fin v → ℝ) (P : (Fin k → Fin v) → Prop) :
    weightedWordEventMass (fun i ↦ L * p i) P =
      L ^ k * weightedWordEventMass p P := by
  classical
  rw [weightedWordEventMass, weightedWordEventMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  split_ifs
  · rw [weightedWordMass, weightedWordMass, Finset.prod_mul_distrib,
      Fin.prod_const]
  · ring

theorem weightedWordSmirnov_eq_factorial_mul
    (k u v : ℕ) (lam : Fin v → ℝ) :
    weightedWordEventMass lam
        (SatisfiesWordBarrier (k := k) (v := v) u) =
      (k.factorial : ℝ) *
        weightedOccupancyMassOver lam (smirnovOccupancies k u v) := by
  rw [← weightedWordEventMass_occupancy_eq lam
    (smirnovOccupancies k u v) (fun c hc ↦ by
      rw [mem_compositionsOf]
      exact (mem_smirnovOccupancies.mp hc).1)]
  congr 1
  funext f
  apply propext
  exact ((wordOccupancy_mem_smirnovOccupancies_iff f).trans
    (satisfiesWordBarrier_iff_mem_smirnovWords f).symm).symm

/-! ## Normalized prime-block law -/

/-- The actual cell mass divided by the total mass of the retained window. -/
noncomputable def normalizedPrimeBlockCellMass (M v : ℕ) : Fin v → ℝ :=
  fun i ↦ primeBlockCellMass M v i / primeBlockWindowMass M v

theorem sum_primeBlockCellMass (M v : ℕ) :
    (∑ i, primeBlockCellMass M v i) = primeBlockWindowMass M v := by
  rw [primeBlockWindowMass, primeBlockPrefixMass,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

theorem sum_normalizedPrimeBlockCellMass
    {M v : ℕ} (hwindow : primeBlockWindowMass M v ≠ 0) :
    (∑ i, normalizedPrimeBlockCellMass M v i) = 1 := by
  simp only [normalizedPrimeBlockCellMass]
  rw [← Finset.sum_div,
    sum_primeBlockCellMass]
  exact div_self hwindow

theorem finPrefixMass_primeBlockCellMass
    {M v h : ℕ} (hhv : h ≤ v) :
    finPrefixMass (primeBlockCellMass M v) h =
      primeBlockPrefixMass M h := by
  have hrange := sum_range_restrict_eq_finPrefixMass
    (primeBlockCellMass M v) hhv
  rw [← hrange, primeBlockPrefixMass]
  apply Finset.sum_congr rfl
  intro i hi
  have hiv : i < v := (Finset.mem_range.mp hi).trans_le hhv
  simp [primeBlockCellMass, hiv]

theorem finPrefixMass_normalizedPrimeBlockCellMass
    {M v h : ℕ} (hhv : h ≤ v) :
    finPrefixMass (normalizedPrimeBlockCellMass M v) h =
      primeBlockPrefixMass M h / primeBlockWindowMass M v := by
  rw [finPrefixMass]
  simp only [normalizedPrimeBlockCellMass]
  rw [← Finset.sum_div,
    ← finPrefixMass, finPrefixMass_primeBlockCellMass hhv]

theorem normalizedPrimeBlockCellMass_nonneg {M v : ℕ}
    (hwindow : 0 < primeBlockWindowMass M v) (i : Fin v) :
    0 ≤ normalizedPrimeBlockCellMass M v i := by
  exact div_nonneg (primeBlockMass_nonneg _) hwindow.le

/-! ## Smirnov barriers are increasing and shift by one cell -/

theorem satisfiesWordBarrier_upward {k u v : ℕ} :
    UpwardClosedWordEvent (SatisfiesWordBarrier (k := k) (v := v) u) := by
  intro f g hfg hf h hh hhv
  apply lt_of_le_of_lt _ (hf h hh hhv)
  rw [wordPrefix, wordPrefix]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact lt_of_le_of_lt (hfg i) hi

theorem satisfiesWordBarrier_shiftRight_of_succ
    {k u v : ℕ} (hv : 0 < v) {f : Fin k → Fin v}
    (hk : k < u + v)
    (hf : SatisfiesWordBarrier (u + 1) f) :
    SatisfiesWordBarrier u (fun i ↦ shiftRightCell hv (f i)) := by
  intro h hh hhv
  by_cases hlt : h < v
  · have hpred : h - 1 + 1 = h := by omega
    have hpref : wordPrefix (fun i ↦ shiftRightCell hv (f i)) h =
        wordPrefix f (h - 1) := by
      rw [wordPrefix, wordPrefix]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact shiftRightCell_lt_iff hv hh hlt (f i)
    rw [hpref]
    by_cases hone : h = 1
    · subst h
      simp [wordPrefix_zero]
    · have hpredPos : 1 ≤ h - 1 := by omega
      have hpredLe : h - 1 ≤ v := by omega
      have := hf (h - 1) hpredPos hpredLe
      omega
  · have heq : h = v := by omega
    subst h
    have htotal : wordPrefix (fun i ↦ shiftRightCell hv (f i)) v = k :=
      wordPrefix_eq_k_of_length_le _ le_rfl
    rw [htotal]
    exact hk

theorem satisfiesWordBarrier_succ_of_shiftRight
    {k u v : ℕ} (hv : 0 < v) {f : Fin k → Fin v}
    (hk : k < u + v)
    (hf : SatisfiesWordBarrier u
      (fun i ↦ shiftRightCell hv (f i))) :
    SatisfiesWordBarrier (u + 1) f := by
  intro h hh hhv
  by_cases hlt : h < v
  · have hsuccPos : 1 ≤ h + 1 := by omega
    have hsuccLe : h + 1 ≤ v := by omega
    have hpref : wordPrefix f h ≤
        wordPrefix (fun i ↦ shiftRightCell hv (f i)) (h + 1) := by
      rw [wordPrefix, wordPrefix]
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      dsimp [shiftRightCell]
      omega
    have hgood := hf (h + 1) hsuccPos hsuccLe
    omega
  · have heq : h = v := by omega
    subst h
    rw [wordPrefix_eq_k_of_length_le f le_rfl]
    omega

theorem weightedWordSmirnovMass_le_shiftedUniform
    {k u v : ℕ} (hv : 0 < v) {p : Fin v → ℝ}
    (hk : k < u + v)
    (hp : ∀ i, 0 ≤ p i) (hsum : (∑ i, p i) = 1)
    (hprefix : ∀ h : ℕ, 1 ≤ h → h ≤ v →
      ((h - 1 : ℕ) : ℝ) / (v : ℝ) ≤ finPrefixMass p h) :
    weightedWordEventMass p
        (SatisfiesWordBarrier (k := k) (v := v) u) ≤
      (1 / (v : ℝ)) ^ k *
        ((barrierWords k (u + 1) v).card : ℝ) := by
  have hqsum := sum_rightShiftUniformMass hv
  have hpref : ∀ h : ℕ, 1 ≤ h → h ≤ v →
      finPrefixMass (rightShiftUniformMass hv) h ≤ finPrefixMass p h := by
    intro h hh hhv
    rw [finPrefixMass_rightShiftUniformMass hv hh hhv]
    split_ifs with hlt
    · exact hprefix h hh hhv
    · rw [finPrefixMass_eq_sum_of_le p (by omega), hsum]
  have hstoch := weightedWordEventMass_le_of_prefix_ge hv hp
    (rightShiftUniformMass_nonneg hv) (by rw [hsum, hqsum]) hpref
    (satisfiesWordBarrier_upward (k := k) (u := u) (v := v))
  apply hstoch.trans
  rw [weightedWordEventMass_rightShiftUniform]
  calc
    weightedWordEventMass (fun _ : Fin v ↦ 1 / (v : ℝ))
        (fun f ↦ SatisfiesWordBarrier u
          (fun i ↦ shiftRightCell hv (f i))) ≤
        weightedWordEventMass (fun _ : Fin v ↦ 1 / (v : ℝ))
          (SatisfiesWordBarrier (u + 1)) := by
      rw [weightedWordEventMass, weightedWordEventMass]
      apply Finset.sum_le_sum
      intro f hfmem
      by_cases hs : SatisfiesWordBarrier u
          (fun i ↦ shiftRightCell hv (f i))
      · have hfbar : SatisfiesWordBarrier (u + 1) f := by
          exact satisfiesWordBarrier_succ_of_shiftRight hv hk hs
        simp [hs, hfbar]
      · simp [hs]
        split_ifs
        · exact Finset.prod_nonneg fun i hi ↦ by positivity
        · exact le_rfl
    _ = (1 / (v : ℝ)) ^ k *
        ((barrierWords k (u + 1) v).card : ℝ) := by
      rw [weightedWordEventMass_const]
      congr 2

/-- Global fixed-window comparison: no relation between `u` (or `k`) and
`2^M` occurs.  The entire nonuniform law is normalized first, and its
cumulative cells are compared to the one-cell shifted uniform law. -/
theorem primeBlockWindowMass_pos_of_geometric_error
    {M v : ℕ} (hv : 0 < v) {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ i : ℕ,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i))
    (hsmall : 4 * C ≤ Real.log 2 * (2 : ℝ) ^ M) :
    0 < primeBlockWindowMass M v := by
  let E : ℝ := 2 * C / (2 : ℝ) ^ M
  have hpow : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  have hEhalf : E ≤ Real.log 2 / 2 := by
    dsimp [E]
    apply (div_le_iff₀ hpow).2
    nlinarith
  have htotalAbs := primeBlockPrefixMass_error_le hC hmass v
  change |primeBlockWindowMass M v - (v : ℝ) * Real.log 2| ≤ E at htotalAbs
  have htotalLower : (v : ℝ) * Real.log 2 - E ≤
      primeBlockWindowMass M v := by
    linarith [neg_le_of_abs_le htotalAbs]
  have hvOne : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have hlog := Real.log_pos one_lt_two
  nlinarith

theorem weightedOccupancyMassOver_smirnov_le_quantile
    {M k u v : ℕ} (hv : 0 < v) (hk : k < u + v)
    {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ i : ℕ,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i))
    (hsmall : 4 * C ≤ Real.log 2 * (2 : ℝ) ^ M)
    (hwindow : 0 < primeBlockWindowMass M v) :
    weightedOccupancyMassOver (primeBlockCellMass M v)
        (smirnovOccupancies k u v) ≤
      primeBlockWindowMass M v ^ k *
        smirnovProbability k (u + 1) v / (k.factorial : ℝ) := by
  let p := normalizedPrimeBlockCellMass M v
  have hp : ∀ i, 0 ≤ p i :=
    normalizedPrimeBlockCellMass_nonneg hwindow
  have hpsum : (∑ i, p i) = 1 :=
    sum_normalizedPrimeBlockCellMass hwindow.ne'
  have hpref : ∀ h : ℕ, 1 ≤ h → h ≤ v →
      ((h - 1 : ℕ) : ℝ) / (v : ℝ) ≤ finPrefixMass p h := by
    intro h hh hhv
    rw [finPrefixMass_normalizedPrimeBlockCellMass hhv]
    exact normalizedPrimeBlockPrefix_oneCellOffset hC hv hhv hmass
      hsmall hwindow
  have hnorm := weightedWordSmirnovMass_le_shiftedUniform
    hv hk hp hpsum hpref
  have hprob :
      (1 / (v : ℝ)) ^ k * ((barrierWords k (u + 1) v).card : ℝ) =
        smirnovProbability k (u + 1) v := by
    rw [smirnovProbability_eq_card_barrierWords_div]
    have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
    rw [div_eq_mul_inv]
    calc
      (1 / (v : ℝ)) ^ k * ((barrierWords k (u + 1) v).card : ℝ) =
          ((barrierWords k (u + 1) v).card : ℝ) *
            ((v : ℝ) ^ k)⁻¹ := by
        rw [one_div, inv_pow]
        ring
      _ = _ := by ring
  rw [hprob] at hnorm
  have hcell : primeBlockCellMass M v =
      fun i ↦ primeBlockWindowMass M v * p i := by
    funext i
    dsimp [p, normalizedPrimeBlockCellMass]
    field_simp
  have hscale :
      weightedWordEventMass (primeBlockCellMass M v)
          (SatisfiesWordBarrier (k := k) (v := v) u) =
        primeBlockWindowMass M v ^ k *
          weightedWordEventMass p
            (SatisfiesWordBarrier (k := k) (v := v) u) := by
    rw [hcell, weightedWordEventMass_scale]
  have hword := weightedWordSmirnov_eq_factorial_mul
    k u v (primeBlockCellMass M v)
  have hraw :
      (k.factorial : ℝ) *
          weightedOccupancyMassOver (primeBlockCellMass M v)
            (smirnovOccupancies k u v) ≤
        primeBlockWindowMass M v ^ k *
          smirnovProbability k (u + 1) v := by
    rw [← hword, hscale]
    exact mul_le_mul_of_nonneg_left hnorm (pow_nonneg hwindow.le k)
  have hfact : (0 : ℝ) < k.factorial := by positivity
  rw [le_div_iff₀ hfact]
  simpa [mul_comm] using hraw

/-- The global quantile comparison with positivity of the normalizing mass
deduced from the same geometric Mertens estimate. -/
theorem weightedOccupancyMassOver_smirnov_le_quantile_of_error
    {M k u v : ℕ} (hv : 0 < v) (hk : k < u + v)
    {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ i : ℕ,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i))
    (hsmall : 4 * C ≤ Real.log 2 * (2 : ℝ) ^ M) :
    weightedOccupancyMassOver (primeBlockCellMass M v)
        (smirnovOccupancies k u v) ≤
      primeBlockWindowMass M v ^ k *
        smirnovProbability k (u + 1) v / (k.factorial : ℝ) := by
  exact weightedOccupancyMassOver_smirnov_le_quantile hv hk hC hmass hsmall
    (primeBlockWindowMass_pos_of_geometric_error hv hC hmass hsmall)

end Erdos446
