/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.LowerColoring

/-!
# Balance estimates for rank hues

The rank classes modulo `h` interlace.  This file records the two elementary
consequences used in the CFP obstruction.  An increasing sequence contributes
to one hue at most its average plus two terminal blocks.  A decreasing
nonnegative sequence contributes at most its average plus one initial block.
-/

namespace Erdos55

open scoped BigOperators

def residueIndices (m h s : ℕ) : Finset ℕ :=
  (Finset.range m).filter fun k ↦ k % h = s

def residuePairs (m h s : ℕ) : Finset (ℕ × ℕ) :=
  (residueIndices m h s).product (Finset.range h)

def nextAlignedIndex (h k t : ℕ) : ℕ :=
  (k / h + 1) * h + t

private theorem nextAlignedIndex_injectiveOn {m h s : ℕ} (hh : 0 < h) :
    Set.InjOn (fun p : ℕ × ℕ ↦ nextAlignedIndex h p.1 p.2)
      (residuePairs m h s) := by
  rintro ⟨k₁, t₁⟩ hk₁ ⟨k₂, t₂⟩ hk₂ heq
  change (k₁, t₁) ∈ residuePairs m h s at hk₁
  change (k₂, t₂) ∈ residuePairs m h s at hk₂
  change (k₁, t₁) ∈ (residueIndices m h s).product (Finset.range h) at hk₁
  change (k₂, t₂) ∈ (residueIndices m h s).product (Finset.range h) at hk₂
  have hk₁p := Finset.mem_product.mp hk₁
  have hk₂p := Finset.mem_product.mp hk₂
  have hk₁r := Finset.mem_filter.mp hk₁p.1
  have hk₂r := Finset.mem_filter.mp hk₂p.1
  have ht₁r := Finset.mem_range.mp hk₁p.2
  have ht₂r := Finset.mem_range.mp hk₂p.2
  have hdiv := congrArg (fun z : ℕ ↦ z / h) heq
  have hmod := congrArg (fun z : ℕ ↦ z % h) heq
  have hdiv₁ : nextAlignedIndex h k₁ t₁ / h = k₁ / h + 1 := by
    rw [nextAlignedIndex, Nat.mul_comm (k₁ / h + 1) h,
      Nat.mul_add_div hh, Nat.div_eq_of_lt ht₁r, add_zero]
  have hdiv₂ : nextAlignedIndex h k₂ t₂ / h = k₂ / h + 1 := by
    rw [nextAlignedIndex, Nat.mul_comm (k₂ / h + 1) h,
      Nat.mul_add_div hh, Nat.div_eq_of_lt ht₂r, add_zero]
  have hmod₁ : nextAlignedIndex h k₁ t₁ % h = t₁ := by
    rw [nextAlignedIndex, Nat.mul_comm (k₁ / h + 1) h,
      Nat.mul_add_mod, Nat.mod_eq_of_lt ht₁r]
  have hmod₂ : nextAlignedIndex h k₂ t₂ % h = t₂ := by
    rw [nextAlignedIndex, Nat.mul_comm (k₂ / h + 1) h,
      Nat.mul_add_mod, Nat.mod_eq_of_lt ht₂r]
  rw [hdiv₁, hdiv₂] at hdiv
  rw [hmod₁, hmod₂] at hmod
  have hquot : k₁ / h = k₂ / h := by omega
  have hk : k₁ = k₂ := by
    calc
      k₁ = k₁ % h + h * (k₁ / h) := (Nat.mod_add_div k₁ h).symm
      _ = k₂ % h + h * (k₂ / h) := by rw [hk₁r.2, hk₂r.2, hquot]
      _ = k₂ := Nat.mod_add_div k₂ h
  exact Prod.ext hk hmod

private theorem lt_nextAlignedIndex {h k t : ℕ} (hh : 0 < h) :
    k < nextAlignedIndex h k t := by
  calc
    k = k % h + h * (k / h) := (Nat.mod_add_div k h).symm
    _ < h + h * (k / h) := Nat.add_lt_add_right (Nat.mod_lt k hh) _
    _ = (k / h + 1) * h := by ring
    _ ≤ nextAlignedIndex h k t := by simp [nextAlignedIndex]

private theorem nextAlignedIndex_lt {m h k t : ℕ} (hk : k < m) (ht : t < h) :
    nextAlignedIndex h k t < m + 2 * h := by
  have hmul := Nat.div_mul_le_self k h
  calc
    nextAlignedIndex h k t < (k / h + 2) * h := by
      simp only [nextAlignedIndex]
      nlinarith
    _ = (k / h) * h + 2 * h := by ring
    _ ≤ k + 2 * h := Nat.add_le_add_right hmul _
    _ < m + 2 * h := Nat.add_lt_add_right hk _

/-- Increasing-sequence form of the hue interlacing estimate.  The harmless
factor `2` in the endpoint term comes from charging a selected rank to the
next aligned block of `h` ranks. -/
theorem mul_sum_residueIndices_le_of_monotone
    (a : ℕ → ℕ) {m h s X : ℕ} (hh : 0 < h)
    (ha : Monotone a) (hX : ∀ k < m, a k ≤ X) :
    h * (∑ k ∈ residueIndices m h s, a k) ≤
      (∑ k ∈ Finset.range m, a k) + 2 * h * X := by
  classical
  let D := residuePairs m h s
  let f : ℕ × ℕ → ℕ := fun p ↦ nextAlignedIndex h p.1 p.2
  let good := D.filter fun p ↦ f p < m
  let bad := D.filter fun p ↦ ¬f p < m
  have hinj : Set.InjOn f D := by
    simpa [D, f] using nextAlignedIndex_injectiveOn (m := m) (s := s) hh
  have hgood :
      (∑ p ∈ good, a p.1) ≤ ∑ k ∈ Finset.range m, a k := by
    have hpoint : (∑ p ∈ good, a p.1) ≤ ∑ p ∈ good, a (f p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpD : p ∈ D := (Finset.mem_filter.mp hp).1
      have hpParts : p.1 ∈ residueIndices m h s ∧ p.2 ∈ Finset.range h := by
        simpa [D, residuePairs] using hpD
      exact ha (Nat.le_of_lt (lt_nextAlignedIndex hh))
    have hgoodInj : Set.InjOn f good := hinj.mono (Finset.filter_subset _ _)
    have himage : good.image f ⊆ Finset.range m := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    calc
      (∑ p ∈ good, a p.1) ≤ ∑ p ∈ good, a (f p) := hpoint
      _ = ∑ z ∈ good.image f, a z := (Finset.sum_image hgoodInj).symm
      _ ≤ ∑ z ∈ Finset.range m, a z :=
        Finset.sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ ↦ Nat.zero_le _)
  have hbadCard : bad.card ≤ 2 * h := by
    have hbadInj : Set.InjOn f bad := hinj.mono (Finset.filter_subset _ _)
    have himage : bad.image f ⊆ Finset.Ico m (m + 2 * h) := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
      have hp' := Finset.mem_filter.mp hp
      have hpD := hp'.1
      have hpParts : p.1 ∈ residueIndices m h s ∧ p.2 ∈ Finset.range h := by
        simpa [D, residuePairs] using hpD
      have hpk : p.1 < m := by
        exact Finset.mem_range.mp (Finset.mem_filter.mp hpParts.1).1
      have hpt : p.2 < h := by
        exact Finset.mem_range.mp hpParts.2
      exact Finset.mem_Ico.mpr ⟨Nat.le_of_not_gt hp'.2,
        nextAlignedIndex_lt hpk hpt⟩
    calc
      bad.card = (bad.image f).card := (Finset.card_image_of_injOn hbadInj).symm
      _ ≤ (Finset.Ico m (m + 2 * h)).card := Finset.card_le_card himage
      _ = 2 * h := by simp
  have hbad : (∑ p ∈ bad, a p.1) ≤ 2 * h * X := by
    calc
      (∑ p ∈ bad, a p.1) ≤ ∑ _p ∈ bad, X := by
        apply Finset.sum_le_sum
        intro p hp
        have hpD : p ∈ D := (Finset.mem_filter.mp hp).1
        have hpParts : p.1 ∈ residueIndices m h s ∧ p.2 ∈ Finset.range h := by
          simpa [D, residuePairs] using hpD
        have hpk : p.1 < m := by
          exact Finset.mem_range.mp (Finset.mem_filter.mp hpParts.1).1
        exact hX p.1 hpk
      _ = bad.card * X := by simp
      _ ≤ 2 * h * X := Nat.mul_le_mul_right X hbadCard
  have hpartition :
      (∑ p ∈ good, a p.1) + (∑ p ∈ bad, a p.1) = ∑ p ∈ D, a p.1 := by
    simpa [good, bad] using
      (Finset.sum_filter_add_sum_filter_not D (fun p ↦ f p < m) fun p ↦ a p.1)
  have hpairSum :
      (∑ p ∈ D, a p.1) = h * (∑ k ∈ residueIndices m h s, a k) := by
    change (∑ p ∈ (residueIndices m h s).product (Finset.range h), a p.1) = _
    calc
      (∑ p ∈ (residueIndices m h s).product (Finset.range h), a p.1) =
          ∑ k ∈ residueIndices m h s, ∑ _t ∈ Finset.range h, a k := by
            simpa using Finset.sum_product'
              (residueIndices m h s) (Finset.range h) (fun k _t ↦ a k)
      _ = ∑ k ∈ residueIndices m h s, h * a k := by simp
      _ = h * (∑ k ∈ residueIndices m h s, a k) := by
        rw [Finset.mul_sum]
  omega

def previousAlignedIndex (h k t : ℕ) : ℕ :=
  (k / h - 1) * h + t

private theorem previousAlignedIndex_injectiveOn {m h s : ℕ} (hh : 0 < h) :
    Set.InjOn (fun p : ℕ × ℕ ↦ previousAlignedIndex h p.1 p.2)
      ((residuePairs m h s).filter fun p ↦ h ≤ p.1) := by
  rintro ⟨k₁, t₁⟩ hk₁ ⟨k₂, t₂⟩ hk₂ heq
  have hk₁f := Finset.mem_filter.mp hk₁
  have hk₂f := Finset.mem_filter.mp hk₂
  have hk₁D := hk₁f.1
  have hk₂D := hk₂f.1
  change (k₁, t₁) ∈ (residueIndices m h s).product (Finset.range h) at hk₁D
  change (k₂, t₂) ∈ (residueIndices m h s).product (Finset.range h) at hk₂D
  have hk₁p := Finset.mem_product.mp hk₁D
  have hk₂p := Finset.mem_product.mp hk₂D
  have hk₁r := Finset.mem_filter.mp hk₁p.1
  have hk₂r := Finset.mem_filter.mp hk₂p.1
  have ht₁r := Finset.mem_range.mp hk₁p.2
  have ht₂r := Finset.mem_range.mp hk₂p.2
  have hq₁ : 0 < k₁ / h := Nat.div_pos hk₁f.2 hh
  have hq₂ : 0 < k₂ / h := Nat.div_pos hk₂f.2 hh
  have hdiv := congrArg (fun z : ℕ ↦ z / h) heq
  have hmod := congrArg (fun z : ℕ ↦ z % h) heq
  have hdiv₁ : previousAlignedIndex h k₁ t₁ / h = k₁ / h - 1 := by
    rw [previousAlignedIndex, Nat.mul_comm (k₁ / h - 1) h,
      Nat.mul_add_div hh, Nat.div_eq_of_lt ht₁r, add_zero]
  have hdiv₂ : previousAlignedIndex h k₂ t₂ / h = k₂ / h - 1 := by
    rw [previousAlignedIndex, Nat.mul_comm (k₂ / h - 1) h,
      Nat.mul_add_div hh, Nat.div_eq_of_lt ht₂r, add_zero]
  have hmod₁ : previousAlignedIndex h k₁ t₁ % h = t₁ := by
    rw [previousAlignedIndex, Nat.mul_comm (k₁ / h - 1) h,
      Nat.mul_add_mod, Nat.mod_eq_of_lt ht₁r]
  have hmod₂ : previousAlignedIndex h k₂ t₂ % h = t₂ := by
    rw [previousAlignedIndex, Nat.mul_comm (k₂ / h - 1) h,
      Nat.mul_add_mod, Nat.mod_eq_of_lt ht₂r]
  rw [hdiv₁, hdiv₂] at hdiv
  rw [hmod₁, hmod₂] at hmod
  have hquot : k₁ / h = k₂ / h := by omega
  have hk : k₁ = k₂ := by
    calc
      k₁ = k₁ % h + h * (k₁ / h) := (Nat.mod_add_div k₁ h).symm
      _ = k₂ % h + h * (k₂ / h) := by rw [hk₁r.2, hk₂r.2, hquot]
      _ = k₂ := Nat.mod_add_div k₂ h
  exact Prod.ext hk hmod

private theorem previousAlignedIndex_le {h k t : ℕ} (hh : 0 < h)
    (hk : h ≤ k) (ht : t < h) : previousAlignedIndex h k t ≤ k := by
  have hq : 0 < k / h := Nat.div_pos hk hh
  exact (calc
      previousAlignedIndex h k t < ((k / h - 1) + 1) * h := by
        simp only [previousAlignedIndex]
        nlinarith
      _ = (k / h) * h := by
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq.ne')]
      _ ≤ k := Nat.div_mul_le_self k h).le

/-- Decreasing nonnegative real weights have at most their average mass in
one hue, apart from the first aligned block. -/
theorem natCast_mul_sum_residueIndices_le_of_antitone
    (w : ℕ → ℝ) {m h s : ℕ} (hh : 0 < h)
    (hw : Antitone w) (hw0 : ∀ k, 0 ≤ w k) :
    (h : ℝ) * (∑ k ∈ residueIndices m h s, w k) ≤
      (∑ k ∈ Finset.range m, w k) + (h : ℝ) * w 0 := by
  classical
  let D := residuePairs m h s
  let f : ℕ × ℕ → ℕ := fun p ↦ previousAlignedIndex h p.1 p.2
  let good := D.filter fun p ↦ h ≤ p.1
  let bad := D.filter fun p ↦ ¬h ≤ p.1
  have hinj : Set.InjOn f good := by
    simpa [D, f, good] using
      previousAlignedIndex_injectiveOn (m := m) (s := s) hh
  have hgood :
      (∑ p ∈ good, w p.1) ≤ ∑ k ∈ Finset.range m, w k := by
    have hpoint : (∑ p ∈ good, w p.1) ≤ ∑ p ∈ good, w (f p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpD : p ∈ D := hp'.1
      have hpParts : p.1 ∈ residueIndices m h s ∧ p.2 ∈ Finset.range h := by
        simpa [D, residuePairs] using hpD
      exact hw (previousAlignedIndex_le hh hp'.2 (Finset.mem_range.mp hpParts.2))
    have himage : good.image f ⊆ Finset.range m := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
      have hp' := Finset.mem_filter.mp hp
      have hpParts : p.1 ∈ residueIndices m h s ∧ p.2 ∈ Finset.range h := by
        simpa [D, residuePairs] using hp'.1
      have hpk : p.1 < m :=
        Finset.mem_range.mp (Finset.mem_filter.mp hpParts.1).1
      exact Finset.mem_range.mpr
        ((previousAlignedIndex_le hh hp'.2 (Finset.mem_range.mp hpParts.2)).trans_lt hpk)
    calc
      (∑ p ∈ good, w p.1) ≤ ∑ p ∈ good, w (f p) := hpoint
      _ = ∑ z ∈ good.image f, w z := (Finset.sum_image hinj).symm
      _ ≤ ∑ z ∈ Finset.range m, w z :=
        Finset.sum_le_sum_of_subset_of_nonneg himage (fun z _ _ ↦ hw0 z)
  have hbadCard : bad.card ≤ h := by
    have hsubset : bad ⊆ ({s} : Finset ℕ).product (Finset.range h) := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpParts : p.1 ∈ residueIndices m h s ∧ p.2 ∈ Finset.range h := by
        simpa [D, residuePairs] using hp'.1
      have hpklt : p.1 < h := Nat.lt_of_not_ge hp'.2
      have hpmod : p.1 % h = s := (Finset.mem_filter.mp hpParts.1).2
      have hpEq : p.1 = s := by
        rw [Nat.mod_eq_of_lt hpklt] at hpmod
        exact hpmod
      exact Finset.mem_product.mpr ⟨by simp [hpEq], hpParts.2⟩
    calc
      bad.card ≤ (({s} : Finset ℕ).product (Finset.range h)).card :=
        Finset.card_le_card hsubset
      _ = h := by simp
  have hbad : (∑ p ∈ bad, w p.1) ≤ (h : ℝ) * w 0 := by
    calc
      (∑ p ∈ bad, w p.1) ≤ ∑ _p ∈ bad, w 0 := by
        apply Finset.sum_le_sum
        intro p _hp
        exact hw (Nat.zero_le p.1)
      _ = (bad.card : ℝ) * w 0 := by simp
      _ ≤ (h : ℝ) * w 0 := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hbadCard
        · exact hw0 0
  have hpartition :
      (∑ p ∈ good, w p.1) + (∑ p ∈ bad, w p.1) = ∑ p ∈ D, w p.1 := by
    simpa [good, bad] using
      (Finset.sum_filter_add_sum_filter_not D (fun p ↦ h ≤ p.1) fun p ↦ w p.1)
  have hpairSum :
      (∑ p ∈ D, w p.1) = (h : ℝ) * (∑ k ∈ residueIndices m h s, w k) := by
    change (∑ p ∈ (residueIndices m h s).product (Finset.range h), w p.1) = _
    calc
      (∑ p ∈ (residueIndices m h s).product (Finset.range h), w p.1) =
          ∑ k ∈ residueIndices m h s, ∑ _t ∈ Finset.range h, w k := by
            simpa using Finset.sum_product'
              (residueIndices m h s) (Finset.range h) (fun k _t ↦ w k)
      _ = ∑ k ∈ residueIndices m h s, (h : ℝ) * w k := by simp
      _ = (h : ℝ) * (∑ k ∈ residueIndices m h s, w k) := by
        rw [Finset.mul_sum]
  linarith

end Erdos55
