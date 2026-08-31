/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 781.
https://www.erdosproblems.com/forum/thread/781

Informal authors:
- Noga Alon
- Joel Spencer

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos781.md
-/
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

import Mathlib

/-!
# Erdős Problem 781

Alon and Spencer proved that the two-colour Ramsey number of descending
waves has cubic order of growth.  The detailed mathematical proof and the
map from its lemmas to this development are in `tex/781.tex`.
-/

namespace Erdos781

open scoped BigOperators

/-- An increasing finite sequence whose successive gaps are nonincreasing.

The displayed inequality is the midpoint-free natural-number form of
`x (i+1) ≥ (x i + x (i+2)) / 2` from the problem statement. -/
def IsDescendingWave {k n : ℕ} (x : Fin k → Fin n) : Prop :=
  StrictMono x ∧
    ∀ i : ℕ, ∀ hi : i + 2 < k,
      (x ⟨i, by omega⟩).val + (x ⟨i + 2, hi⟩).val ≤
        2 * (x ⟨i + 1, by omega⟩).val

/-- An increasing finite sequence whose successive gaps are nondecreasing. -/
def IsAscendingWave {k n : ℕ} (x : Fin k → Fin n) : Prop :=
  StrictMono x ∧
    ∀ i : ℕ, ∀ hi : i + 2 < k,
      2 * (x ⟨i + 1, by omega⟩).val ≤
        (x ⟨i, by omega⟩).val + (x ⟨i + 2, hi⟩).val

/-- All entries of `x` have the same Boolean colour. -/
def Monochromatic {k n : ℕ} (c : Fin n → Bool) (x : Fin k → Fin n) : Prop :=
  ∃ colour, ∀ i, c (x i) = colour

/-- Every two-colouring of `[n]` contains a descending wave of length `k`. -/
def ForcesDescending (k n : ℕ) : Prop :=
  ∀ c : Fin n → Bool, ∃ x : Fin k → Fin n,
    IsDescendingWave x ∧ Monochromatic c x

/-- Every two-colouring of `[n]` contains an ascending wave of length `k`. -/
def ForcesAscending (k n : ℕ) : Prop :=
  ∀ c : Fin n → Bool, ∃ x : Fin k → Fin n,
    IsAscendingWave x ∧ Monochromatic c x

/-- Reverse both the positions and values of a sequence in a finite interval. -/
def reverseWave {k n : ℕ} (x : Fin k → Fin n) : Fin k → Fin n :=
  fun i ↦ (x i.rev).rev

@[simp] lemma reverseWave_apply {k n : ℕ} (x : Fin k → Fin n) (i : Fin k) :
    reverseWave x i = (x i.rev).rev := rfl

@[simp] lemma reverseWave_reverseWave {k n : ℕ} (x : Fin k → Fin n) :
    reverseWave (reverseWave x) = x := by
  funext i
  simp [reverseWave]

lemma strictMono_reverseWave {k n : ℕ} {x : Fin k → Fin n}
    (hx : StrictMono x) : StrictMono (reverseWave x) := by
  intro i j hij
  simp only [reverseWave]
  exact Fin.rev_lt_rev.mpr (hx (Fin.rev_lt_rev.mpr hij))

lemma rev_midpoint_of_midpoint {n : ℕ} {a b c : Fin n}
    (h : a.val + c.val ≤ 2 * b.val) :
    2 * b.rev.val ≤ c.rev.val + a.rev.val := by
  simp only [Fin.rev]
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  omega

lemma midpoint_rev_of_rev_midpoint {n : ℕ} {a b c : Fin n}
    (h : 2 * b.val ≤ a.val + c.val) :
    c.rev.val + a.rev.val ≤ 2 * b.rev.val := by
  simp only [Fin.rev]
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  omega

lemma reverseWave_ascending_of_descending {k n : ℕ} {x : Fin k → Fin n}
    (hx : IsDescendingWave x) : IsAscendingWave (reverseWave x) := by
  refine ⟨strictMono_reverseWave hx.1, ?_⟩
  intro i hi
  let j := k - 3 - i
  have hj : j + 2 < k := by simp only [j]; omega
  have h := hx.2 j hj
  have hrev0 : (⟨i, by omega⟩ : Fin k).rev = ⟨j + 2, hj⟩ := by
    ext
    simp only [Fin.rev, j]
    omega
  have hrev1 : (⟨i + 1, by omega⟩ : Fin k).rev =
      ⟨j + 1, by omega⟩ := by
    ext
    simp only [Fin.rev, j]
    omega
  have hrev2 : (⟨i + 2, hi⟩ : Fin k).rev = ⟨j, by omega⟩ := by
    ext
    simp only [Fin.rev, j]
    omega
  have hr := rev_midpoint_of_midpoint h
  simpa only [reverseWave, hrev0, hrev1, hrev2] using hr

lemma reverseWave_descending_of_ascending {k n : ℕ} {x : Fin k → Fin n}
    (hx : IsAscendingWave x) : IsDescendingWave (reverseWave x) := by
  refine ⟨strictMono_reverseWave hx.1, ?_⟩
  intro i hi
  let j := k - 3 - i
  have hj : j + 2 < k := by simp only [j]; omega
  have h := hx.2 j hj
  have hrev0 : (⟨i, by omega⟩ : Fin k).rev = ⟨j + 2, hj⟩ := by
    ext
    simp only [Fin.rev, j]
    omega
  have hrev1 : (⟨i + 1, by omega⟩ : Fin k).rev =
      ⟨j + 1, by omega⟩ := by
    ext
    simp only [Fin.rev, j]
    omega
  have hrev2 : (⟨i + 2, hi⟩ : Fin k).rev = ⟨j, by omega⟩ := by
    ext
    simp only [Fin.rev, j]
    omega
  have hr := midpoint_rev_of_rev_midpoint h
  simpa only [reverseWave, hrev0, hrev1, hrev2, Nat.add_comm] using hr

lemma monochromatic_reverseWave {k n : ℕ} {c : Fin n → Bool}
    {x : Fin k → Fin n} (hx : Monochromatic c x) :
    Monochromatic (fun j ↦ c j.rev) (reverseWave x) := by
  obtain ⟨colour, hcolour⟩ := hx
  exact ⟨colour, fun i ↦ by simp [reverseWave, hcolour]⟩

theorem forcesDescending_iff_forcesAscending (k n : ℕ) :
    ForcesDescending k n ↔ ForcesAscending k n := by
  constructor
  · intro h c
    obtain ⟨x, hx, hmono⟩ := h (fun j ↦ c j.rev)
    refine ⟨reverseWave x, reverseWave_ascending_of_descending hx, ?_⟩
    simpa [Monochromatic, reverseWave] using
      (monochromatic_reverseWave (c := fun j ↦ c j.rev) hmono)
  · intro h c
    obtain ⟨x, hx, hmono⟩ := h (fun j ↦ c j.rev)
    refine ⟨reverseWave x, reverseWave_descending_of_ascending hx, ?_⟩
    simpa [Monochromatic, reverseWave] using
      (monochromatic_reverseWave (c := fun j ↦ c j.rev) hmono)

section BlockColoring

/-- Three independent bits are a convenient coordinate system for the eight
odd-parity colourings of a group of four blocks. -/
abbrev Pattern := Fin 3 → Bool

/-- The odd-parity four-bit pattern determined by three free bits. -/
def patternColor (p : Pattern) (r : Fin 4) : Bool :=
  if h : r.val < 3 then p ⟨r.val, h⟩
  else !((p 0).xor (p 1) |>.xor (p 2))

def patternsWith (r : Fin 4) (colour : Bool) : Finset Pattern :=
  Finset.univ.filter fun p ↦ patternColor p r = colour

def patternsWith₂ (r s : Fin 4) (a b : Bool) : Finset Pattern :=
  Finset.univ.filter fun p ↦ patternColor p r = a ∧ patternColor p s = b

lemma card_patternsWith (r : Fin 4) (colour : Bool) :
    (patternsWith r colour).card = 4 := by
  fin_cases r <;> fin_cases colour <;> decide

lemma card_patternsWith₂ (r s : Fin 4) (a b : Bool) (hrs : r ≠ s) :
    (patternsWith₂ r s a b).card = 2 := by
  fin_cases r <;> fin_cases s
  all_goals try { exfalso; exact hrs rfl }
  all_goals fin_cases a <;> fin_cases b <;> decide

lemma pattern_not_constant (p : Pattern) :
    ¬(∀ r : Fin 4, patternColor p r = true) ∧
      ¬(∀ r : Fin 4, patternColor p r = false) := by
  constructor <;> intro h
  · have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    simp [patternColor] at h0 h1 h2 h3
    simp [h0, h1, h2] at h3
  · have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    simp [patternColor] at h0 h1 h2 h3
    simp [h0, h1, h2] at h3

/-- A seed independently chooses one odd-parity pattern for every group. -/
abbrev Seed (groups : ℕ) := Fin groups → Pattern

/-- The group containing a block. -/
def blockGroup {groups : ℕ} (j : Fin (4 * groups)) : Fin groups :=
  ⟨j.val / 4, by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 4)]
    simpa [mul_comm] using j.isLt⟩

/-- The coordinate of a block inside its four-block group. -/
def blockCoord {groups : ℕ} (j : Fin (4 * groups)) : Fin 4 :=
  ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩

/-- Colour of a block under a seed. -/
def blockColour {groups : ℕ} (ω : Seed groups) (j : Fin (4 * groups)) : Bool :=
  patternColor (ω (blockGroup j)) (blockCoord j)

lemma blockGroup_eq_of_div_eq {groups : ℕ} {i j : Fin (4 * groups)}
    (h : i.val / 4 = j.val / 4) : blockGroup i = blockGroup j := by
  apply Fin.ext
  exact h

lemma blockCoord_ne_of_ne {groups : ℕ} {i j : Fin (4 * groups)}
    (hg : blockGroup i = blockGroup j) (hij : i ≠ j) : blockCoord i ≠ blockCoord j := by
  intro hc
  apply hij
  apply Fin.ext
  have hdiv : i.val / 4 = j.val / 4 := congrArg Fin.val hg
  have hmod : i.val % 4 = j.val % 4 := congrArg Fin.val hc
  omega

lemma four_consecutive_not_monochromatic {groups : ℕ} (ω : Seed groups)
    (q : Fin groups) :
    ¬(∀ r : Fin 4,
      patternColor (ω q) r = true) ∧
      ¬(∀ r : Fin 4, patternColor (ω q) r = false) :=
  pattern_not_constant (ω q)

/-- Patterns allowed in one group by a family of block-colour requests. -/
def groupAllowed {groups r : ℕ} (j : Fin r → Fin (4 * groups))
    (a : Fin r → Bool) (q : Fin groups) : Finset Pattern :=
  Finset.univ.filter fun p ↦
    ∀ i, blockGroup (j i) = q → patternColor p (blockCoord (j i)) = a i

/-- Seeds realizing a family of prescribed block colours. -/
def seedCylinder {groups r : ℕ} (j : Fin r → Fin (4 * groups))
    (a : Fin r → Bool) : Finset (Seed groups) :=
  Finset.univ.filter fun ω ↦ ∀ i, blockColour ω (j i) = a i

lemma groupAllowed_eq_univ {groups r : ℕ} (j : Fin r → Fin (4 * groups))
    (a : Fin r → Bool) (q : Fin groups)
    (hq : ∀ i, blockGroup (j i) ≠ q) :
    groupAllowed j a q = Finset.univ := by
  ext p
  simp only [groupAllowed, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun _ ↦ trivial, fun _ i hi ↦ (hq i hi).elim⟩

lemma groupAllowed_eq_patternsWith {groups r : ℕ}
    (j : Fin r → Fin (4 * groups)) (a : Fin r → Bool)
    (hj : Function.Injective fun i ↦ blockGroup (j i)) (i : Fin r) :
    groupAllowed j a (blockGroup (j i)) = patternsWith (blockCoord (j i)) (a i) := by
  ext p
  simp only [groupAllowed, patternsWith, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact h i rfl
  · intro h i' hi'
    have : i' = i := hj hi'
    subst i'
    exact h

lemma card_groupAllowed {groups r : ℕ} (j : Fin r → Fin (4 * groups))
    (a : Fin r → Bool) (hj : Function.Injective fun i ↦ blockGroup (j i))
    (q : Fin groups) :
    (groupAllowed j a q).card =
      if q ∈ Finset.univ.image (fun i ↦ blockGroup (j i)) then 4 else 8 := by
  classical
  split_ifs with hq
  · rw [Finset.mem_image] at hq
    obtain ⟨i, -, rfl⟩ := hq
    rw [groupAllowed_eq_patternsWith j a hj i, card_patternsWith]
  · rw [groupAllowed_eq_univ j a q]
    · simp
    · intro i hi
      exact hq (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)

lemma seedCylinder_eq_piFinset {groups r : ℕ}
    (j : Fin r → Fin (4 * groups)) (a : Fin r → Bool) :
    seedCylinder j a = Fintype.piFinset (groupAllowed j a) := by
  classical
  ext ω
  constructor
  · intro h
    have hcyl : ∀ i, blockColour ω (j i) = a i :=
      (Finset.mem_filter.mp h).2
    rw [Fintype.mem_piFinset]
    intro q
    rw [groupAllowed, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i hi
    simpa [blockColour, hi] using hcyl i
  · intro h
    rw [seedCylinder, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i
    have hq := Fintype.mem_piFinset.mp h (blockGroup (j i))
    have hp := (Finset.mem_filter.mp hq).2 i rfl
    exact hp

lemma prod_four_eight {groups : ℕ} (s : Finset (Fin groups)) :
    (∏ q : Fin groups, if q ∈ s then 4 else 8) =
      4 ^ s.card * 8 ^ (groups - s.card) := by
  classical
  have hsub : s ⊆ (Finset.univ : Finset (Fin groups)) := Finset.subset_univ _
  calc
    (∏ q : Fin groups, if q ∈ s then 4 else 8) =
        (∏ q ∈ s, if q ∈ s then 4 else 8) *
          ∏ q ∈ (Finset.univ : Finset (Fin groups)) \ s,
            if q ∈ s then 4 else 8 := by
      rw [← Finset.prod_union Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset hsub]
    _ = 4 ^ s.card * 8 ^ (groups - s.card) := by
      have hleft : (∏ q ∈ s, if q ∈ s then 4 else 8) = 4 ^ s.card := by
        calc
          (∏ q ∈ s, if q ∈ s then 4 else 8) = ∏ _q ∈ s, (4 : ℕ) := by
            apply Finset.prod_congr rfl
            intro q hq
            simp [hq]
          _ = 4 ^ s.card := Finset.prod_const 4
      have hright :
          (∏ q ∈ (Finset.univ : Finset (Fin groups)) \ s,
            if q ∈ s then 4 else 8) =
              8 ^ ((Finset.univ : Finset (Fin groups)) \ s).card := by
        calc
          (∏ q ∈ (Finset.univ : Finset (Fin groups)) \ s,
              if q ∈ s then 4 else 8) =
              ∏ _q ∈ (Finset.univ : Finset (Fin groups)) \ s, (8 : ℕ) := by
            apply Finset.prod_congr rfl
            intro q hq
            have hnot : q ∉ s := (Finset.mem_sdiff.mp hq).2
            simp [hnot]
          _ = 8 ^ ((Finset.univ : Finset (Fin groups)) \ s).card :=
            Finset.prod_const 8
      rw [hleft, hright, Finset.card_sdiff]
      simp

lemma card_seedCylinder {groups r : ℕ} (j : Fin r → Fin (4 * groups))
    (a : Fin r → Bool) (hj : Function.Injective fun i ↦ blockGroup (j i)) :
    (seedCylinder j a).card = 4 ^ r * 8 ^ (groups - r) := by
  classical
  rw [seedCylinder_eq_piFinset, Fintype.card_piFinset]
  simp_rw [card_groupAllowed j a hj]
  rw [prod_four_eight]
  have hc : (Finset.univ.image (fun i ↦ blockGroup (j i))).card = r := by
    simpa using Finset.card_image_of_injective Finset.univ hj
  rw [hc]

/-- Requests whose blocks belong to a specified four-block group. -/
def requestFiber {groups r : ℕ} (j : Fin r → Fin (4 * groups))
    (q : Fin groups) : Finset (Fin r) :=
  Finset.univ.filter fun i ↦ blockGroup (j i) = q

lemma groupAllowed_eq_patternsWith_of_fiber_singleton {groups r : ℕ}
    (j : Fin r → Fin (4 * groups)) (a : Fin r → Bool)
    (q : Fin groups) (i : Fin r) (hf : requestFiber j q = {i}) :
    groupAllowed j a q = patternsWith (blockCoord (j i)) (a i) := by
  have hchar : ∀ i', blockGroup (j i') = q ↔ i' = i := by
    intro i'
    have hm := congrArg (fun s : Finset (Fin r) ↦ i' ∈ s) hf
    simpa [requestFiber] using hm
  ext p
  simp only [groupAllowed, patternsWith, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact h i ((hchar i).mpr rfl)
  · intro h i' hi'
    have hii : i' = i := (hchar i').mp hi'
    simpa [hii] using h

lemma groupAllowed_eq_patternsWith₂_of_fiber_pair {groups r : ℕ}
    (j : Fin r → Fin (4 * groups)) (a : Fin r → Bool)
    (q : Fin groups) (i₁ i₂ : Fin r) (hne : i₁ ≠ i₂)
    (hf : requestFiber j q = {i₁, i₂}) :
    groupAllowed j a q =
      patternsWith₂ (blockCoord (j i₁)) (blockCoord (j i₂)) (a i₁) (a i₂) := by
  have hchar : ∀ i, blockGroup (j i) = q ↔ i = i₁ ∨ i = i₂ := by
    intro i
    have hm := congrArg (fun s : Finset (Fin r) ↦ i ∈ s) hf
    simpa [requestFiber] using hm
  ext p
  simp only [groupAllowed, patternsWith₂, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ⟨h i₁ ((hchar i₁).mpr (Or.inl rfl)),
      h i₂ ((hchar i₂).mpr (Or.inr rfl))⟩
  · rintro ⟨h₁, h₂⟩ i hi
    rcases (hchar i).mp hi with rfl | rfl
    · exact h₁
    · exact h₂

lemma card_groupAllowed_of_fiber_le_two {groups r : ℕ}
    (j : Fin r → Fin (4 * groups)) (a : Fin r → Bool)
    (hj : Function.Injective j) (q : Fin groups)
    (hf : (requestFiber j q).card ≤ 2) :
    (groupAllowed j a q).card = 2 ^ (3 - (requestFiber j q).card) := by
  have hcases : (requestFiber j q).card = 0 ∨
      (requestFiber j q).card = 1 ∨ (requestFiber j q).card = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · have he : requestFiber j q = ∅ := Finset.card_eq_zero.mp hzero
    rw [groupAllowed_eq_univ j a q]
    · simp [hzero]
    · intro i hi
      have hm : i ∈ requestFiber j q := by simp [requestFiber, hi]
      simp [he] at hm
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
    rw [groupAllowed_eq_patternsWith_of_fiber_singleton j a q i hi,
      card_patternsWith, hone]
    norm_num
  · obtain ⟨i₁, i₂, hne, hp⟩ := Finset.card_eq_two.mp htwo
    have hg₁ : blockGroup (j i₁) = q := by
      have : i₁ ∈ requestFiber j q := by simp [hp]
      simpa [requestFiber] using this
    have hg₂ : blockGroup (j i₂) = q := by
      have : i₂ ∈ requestFiber j q := by simp [hp]
      simpa [requestFiber] using this
    have hcne : blockCoord (j i₁) ≠ blockCoord (j i₂) :=
      blockCoord_ne_of_ne (hg₁.trans hg₂.symm) (hj.ne hne)
    rw [groupAllowed_eq_patternsWith₂_of_fiber_pair j a q i₁ i₂ hne hp,
      card_patternsWith₂ _ _ _ _ hcne, htwo]
    norm_num

lemma card_seedCylinder_of_fiber_le_two {groups r : ℕ}
    (j : Fin r → Fin (4 * groups)) (a : Fin r → Bool)
    (hj : Function.Injective j)
    (hf : ∀ q, (requestFiber j q).card ≤ 2) :
    (seedCylinder j a).card = 2 ^ (3 * groups - r) := by
  classical
  rw [seedCylinder_eq_piFinset, Fintype.card_piFinset]
  simp_rw [card_groupAllowed_of_fiber_le_two j a hj _ (hf _)]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have hsum : ∑ q : Fin groups, (requestFiber j q).card = r := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := fun i : Fin r ↦ blockGroup (j i))
      (s := Finset.univ) (t := Finset.univ)
      (fun _ _ ↦ Finset.mem_univ _)
    simpa [requestFiber] using h.symm
  rw [Finset.sum_tsub_distrib]
  · simp [hsum, mul_comm]
  · intro q hq
    have hq' := hf q
    omega

/-- Seeds for which a prescribed list of blocks is monochromatic. -/
def monochromaticSeedSet {groups r : ℕ}
    (j : Fin r → Fin (4 * groups)) : Finset (Seed groups) :=
  Finset.univ.filter fun ω ↦ ∃ colour, ∀ i, blockColour ω (j i) = colour

lemma monochromaticSeedSet_subset {groups r : ℕ}
    (j : Fin r → Fin (4 * groups)) :
    monochromaticSeedSet j ⊆
      seedCylinder j (fun _ ↦ false) ∪ seedCylinder j (fun _ ↦ true) := by
  intro ω hω
  rw [monochromaticSeedSet, Finset.mem_filter] at hω
  obtain ⟨-, colour, hcolour⟩ := hω
  cases colour <;> simp [seedCylinder, hcolour]

lemma card_monochromaticSeedSet_le {groups r : ℕ}
    (j : Fin r → Fin (4 * groups))
    (hj : Function.Injective fun i ↦ blockGroup (j i)) :
    (monochromaticSeedSet j).card ≤ 2 * (4 ^ r * 8 ^ (groups - r)) := by
  calc
    (monochromaticSeedSet j).card ≤
        (seedCylinder j (fun _ ↦ false) ∪
          seedCylinder j (fun _ ↦ true)).card :=
      Finset.card_le_card (monochromaticSeedSet_subset j)
    _ ≤ (seedCylinder j (fun _ ↦ false)).card +
        (seedCylinder j (fun _ ↦ true)).card := Finset.card_union_le _ _
    _ = 2 * (4 ^ r * 8 ^ (groups - r)) := by
      rw [card_seedCylinder _ _ hj, card_seedCylinder _ _ hj]
      omega

end BlockColoring

section WaveGaps

/-- The natural-number gap following index `i`. -/
def waveGap {k n : ℕ} (x : Fin k → Fin n) (i : ℕ) (hi : i + 1 < k) : ℕ :=
  (x ⟨i + 1, hi⟩).val - (x ⟨i, by omega⟩).val

lemma ascending_gap_mono {k n : ℕ} {x : Fin k → Fin n}
    (hx : IsAscendingWave x) (i : ℕ) (hi : i + 2 < k) :
    waveGap x i (by omega) ≤ waveGap x (i + 1) (by omega) := by
  let i₀ : Fin k := ⟨i, by omega⟩
  let i₁ : Fin k := ⟨i + 1, by omega⟩
  let i₂ : Fin k := ⟨i + 2, hi⟩
  have hfin₁ : i₀ < i₁ := by simp [i₀, i₁]
  have hfin₂ : i₁ < i₂ := by simp [i₁, i₂]
  have hlt₁ := hx.1 hfin₁
  have hlt₂ := hx.1 hfin₂
  have hmid : 2 * (x i₁).val ≤ (x i₀).val + (x i₂).val := by
    simpa [i₀, i₁, i₂] using hx.2 i hi
  have hgap : (x i₁).val - (x i₀).val ≤ (x i₂).val - (x i₁).val := by omega
  simpa [waveGap, i₀, i₁, i₂] using hgap

lemma first_gap_le {k n : ℕ} {x : Fin k → Fin n}
    (hx : IsAscendingWave x) (i : ℕ) (hi : i + 1 < k) :
    waveGap x 0 (by omega) ≤ waveGap x i hi := by
  induction i with
  | zero => rfl
  | succ i ih =>
      exact le_trans (ih (by omega)) (ascending_gap_mono hx i (by omega))

lemma add_first_gap_le_value {k n : ℕ} {x : Fin k → Fin n}
    (hx : IsAscendingWave x) {i j : Fin k} (hij : i < j) :
    (x i).val + waveGap x 0 (by omega) ≤ (x j).val := by
  have hisucc : i.val + 1 < k := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hgap := first_gap_le hx i.val hisucc
  have hfin : i < (⟨i.val + 1, hisucc⟩ : Fin k) := by
    change i.val < i.val + 1
    omega
  have hxi : (x i).val ≤ (x ⟨i.val + 1, hisucc⟩).val := (hx.1 hfin).le
  have hnextj : (x ⟨i.val + 1, hisucc⟩).val ≤ (x j).val :=
    hx.1.monotone (by
      change i.val + 1 ≤ j.val
      omega)
  have hieq : (⟨i.val, by omega⟩ : Fin k) = i := Fin.eta _ _
  have hsum : (x i).val + waveGap x i.val hisucc ≤
      (x ⟨i.val + 1, hisucc⟩).val := by
    simp [waveGap, hieq]
    omega
  exact le_trans (Nat.add_le_add_left hgap _) (le_trans hsum hnextj)

/-- Block containing a point of an interval made from equal-sized blocks. -/
def pointBlock {b blocks : ℕ} (hb : 0 < b) (x : Fin (b * blocks)) : Fin blocks :=
  ⟨x.val / b, by
    rw [Nat.div_lt_iff_lt_mul hb]
    simp [mul_comm]⟩

lemma pointBlock_add_le {b blocks : ℕ} (hb : 0 < b)
    {x y : Fin (b * blocks)} {d : ℕ} (hxy : x.val + d * b ≤ y.val) :
    (pointBlock hb x).val + d ≤ (pointBlock hb y).val := by
  simp only [pointBlock]
  apply (Nat.le_div_iff_mul_le hb).2
  have hfloor := Nat.div_mul_le_self x.val b
  calc
    (x.val / b + d) * b = (x.val / b) * b + d * b := by ring
    _ ≤ x.val + d * b := Nat.add_le_add_right hfloor _
    _ ≤ y.val := hxy

lemma div_four_ne_of_add_four_le {u v : ℕ} (h : u + 4 ≤ v) : u / 4 ≠ v / 4 := by
  intro heq
  have hu := Nat.mod_lt u (by decide : 0 < 4)
  have hv := Nat.mod_lt v (by decide : 0 < 4)
  have hu' := Nat.mod_add_div u 4
  have hv' := Nat.mod_add_div v 4
  omega

lemma blockGroups_injective_of_large_first_gap {k b groups : ℕ}
    (hb : 0 < b) {x : Fin k → Fin (b * (4 * groups))}
    (hx : IsAscendingWave x) (hk : 2 ≤ k)
    (hfirst : 4 * b ≤ waveGap x 0 (by omega)) :
    Function.Injective fun i ↦ blockGroup (pointBlock hb (x i)) := by
  intro i j hgroup
  rcases lt_trichotomy i j with hij | hij | hij
  · have hval := add_first_gap_le_value hx hij
    have hlarge : (x i).val + 4 * b ≤ (x j).val := le_trans (by omega) hval
    have hb4 := pointBlock_add_le hb (d := 4) hlarge
    exact False.elim ((div_four_ne_of_add_four_le hb4) (congrArg Fin.val hgroup))
  · exact hij
  · have hval := add_first_gap_le_value hx hij
    have hlarge : (x j).val + 4 * b ≤ (x i).val := le_trans (by omega) hval
    have hb4 := pointBlock_add_le hb (d := 4) hlarge
    exact False.elim ((div_four_ne_of_add_four_le hb4) (congrArg Fin.val hgroup).symm)

end WaveGaps

section ProfileUnionBound

/-- Block-index profiles of a finite family of sequences. -/
def sequenceProfiles {k b groups : ℕ} (hb : 0 < b)
    (S : Finset (Fin k → Fin (b * (4 * groups)))) :
    Finset (Fin k → Fin (4 * groups)) :=
  S.image fun x i ↦ pointBlock hb (x i)

/-- Point coloring obtained by making each block monochromatic. -/
def pointColour {b groups : ℕ} (hb : 0 < b) (ω : Seed groups)
    (x : Fin (b * (4 * groups))) : Bool :=
  blockColour ω (pointBlock hb x)

/-- Seeds under which some sequence in `S` is monochromatic. -/
def badSeedsFor {k b groups : ℕ} (hb : 0 < b)
    (S : Finset (Fin k → Fin (b * (4 * groups)))) : Finset (Seed groups) :=
  Finset.univ.filter fun ω ↦
    ∃ x ∈ S, ∃ colour, ∀ i, pointColour hb ω (x i) = colour

lemma badSeedsFor_subset_biUnion {k b groups : ℕ} (hb : 0 < b)
    (S : Finset (Fin k → Fin (b * (4 * groups)))) :
    badSeedsFor hb S ⊆
      (sequenceProfiles hb S).biUnion monochromaticSeedSet := by
  intro ω hω
  rw [badSeedsFor, Finset.mem_filter] at hω
  obtain ⟨-, x, hxS, colour, hcolour⟩ := hω
  rw [Finset.mem_biUnion]
  refine ⟨(fun i ↦ pointBlock hb (x i)), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨x, hxS, rfl⟩
  · rw [monochromaticSeedSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, colour, hcolour⟩

lemma card_badSeedsFor_le {k b groups : ℕ} (hb : 0 < b)
    (S : Finset (Fin k → Fin (b * (4 * groups))))
    (hinj : ∀ x ∈ S,
      Function.Injective fun i ↦ blockGroup (pointBlock hb (x i))) :
    (badSeedsFor hb S).card ≤
      (sequenceProfiles hb S).card *
        (2 * (4 ^ k * 8 ^ (groups - k))) := by
  classical
  calc
    (badSeedsFor hb S).card ≤
        ((sequenceProfiles hb S).biUnion monochromaticSeedSet).card :=
      Finset.card_le_card (badSeedsFor_subset_biUnion hb S)
    _ ≤ ∑ p ∈ sequenceProfiles hb S, (monochromaticSeedSet p).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ sequenceProfiles hb S,
        (2 * (4 ^ k * 8 ^ (groups - k))) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [sequenceProfiles, Finset.mem_image] at hp
      obtain ⟨x, hxS, rfl⟩ := hp
      exact card_monochromaticSeedSet_le _ (hinj x hxS)
    _ = (sequenceProfiles hb S).card *
        (2 * (4 ^ k * 8 ^ (groups - k))) := by
      simp [mul_comm]

end ProfileUnionBound

section FloorProfileEncoding

/-!
The paper bounds floor profiles by rounding the real gaps very finely.  For
integer waves there is a shorter encoding.  Write a gap as `q * b + r` and
record whether adding its remainder crosses a block boundary.  On a run on
which `q` is constant, the remainders are nondecreasing.  The five-bit carry
word `11100` is then impossible.  This single forbidden word already gives
the fixed entropy saving needed below.
-/

/-- The gap, measured in whole blocks. -/
def coarseGap {k n b : ℕ} (x : Fin k → Fin n) (i : ℕ)
    (hi : i + 1 < k) : ℕ := waveGap x i hi / b

lemma coarseGap_mono {k n b : ℕ} {x : Fin k → Fin n}
    (hx : IsAscendingWave x) (i : ℕ) (hi : i + 2 < k) :
    coarseGap (b := b) x i (by omega) ≤
      coarseGap (b := b) x (i + 1) (by omega) := by
  exact Nat.div_le_div_right (ascending_gap_mono hx i hi)

lemma div_add_div_le_div_add_one {a d b : ℕ} :
    a / b + d / b ≤ (a + d) / b ∧
      (a + d) / b ≤ a / b + d / b + 1 := by
  exact ⟨Nat.div_add_div_le_add_div,
    Nat.add_div_le_div_add_div_add_one a d b⟩

lemma add_waveGap_eq {k n : ℕ} {x : Fin k → Fin n}
    (hx : StrictMono x) (i : ℕ) (hi : i + 1 < k) :
    (x ⟨i, by omega⟩).val + waveGap x i hi =
      (x ⟨i + 1, hi⟩).val := by
  have hidx : (⟨i, by omega⟩ : Fin k) < ⟨i + 1, hi⟩ :=
    Fin.mk_lt_mk.mpr (by omega)
  have hltFin := hx hidx
  change (x ⟨i, by omega⟩).val < (x ⟨i + 1, hi⟩).val at hltFin
  have hlt : (x ⟨i, by omega⟩).val < (x ⟨i + 1, hi⟩).val := hltFin
  simp only [waveGap]
  omega

/-- The carry made by a gap when positions are divided into blocks. -/
def blockCarry {k n b : ℕ} (x : Fin k → Fin n)
    (hx : StrictMono x)
    (i : ℕ) (hi : i + 1 < k) : Fin 2 :=
  ⟨(x ⟨i + 1, hi⟩).val / b -
      ((x ⟨i, by omega⟩).val / b + coarseGap (b := b) x i hi), by
    have hsum := add_waveGap_eq hx i hi
    have hbounds := div_add_div_le_div_add_one
      (a := (x ⟨i, by omega⟩).val) (d := waveGap x i hi) (b := b)
    rw [hsum] at hbounds
    simp only [coarseGap]
    omega⟩

lemma blockCarry_congr_index {k n b : ℕ} (x : Fin k → Fin n)
    (hx : StrictMono x) {i j : ℕ} (hi : i + 1 < k) (hj : j + 1 < k)
    (hij : i = j) : blockCarry (b := b) x hx i hi =
      blockCarry (b := b) x hx j hj := by
  subst j
  rfl

lemma blockCarry_spec {k n b : ℕ} (x : Fin k → Fin n)
    (hx : StrictMono x)
    (i : ℕ) (hi : i + 1 < k) :
    (x ⟨i + 1, hi⟩).val / b =
      (x ⟨i, by omega⟩).val / b + coarseGap (b := b) x i hi +
        (blockCarry (b := b) x hx i hi).val := by
  have hsum := add_waveGap_eq hx i hi
  have hbounds := div_add_div_le_div_add_one
    (a := (x ⟨i, by omega⟩).val) (d := waveGap x i hi) (b := b)
  rw [hsum] at hbounds
  simp only [blockCarry, coarseGap]
  omega

lemma blockCarry_eq_ite {k n b : ℕ} (hb : 0 < b)
    (x : Fin k → Fin n) (hx : StrictMono x)
    (i : ℕ) (hi : i + 1 < k) :
    (blockCarry (b := b) x hx i hi).val =
      if b ≤ (x ⟨i, by omega⟩).val % b + waveGap x i hi % b then 1 else 0 := by
  have hsum := add_waveGap_eq hx i hi
  have hdiv := Nat.add_div (a := (x ⟨i, by omega⟩).val)
    (b := waveGap x i hi) hb
  rw [hsum] at hdiv
  simp only [blockCarry, coarseGap]
  rw [hdiv]
  split_ifs <;> omega

lemma mod_le_mod_of_le_of_div_eq {a d b : ℕ} (had : a ≤ d)
    (hdiv : a / b = d / b) : a % b ≤ d % b := by
  have ha : a = a / b * b + a % b := by
    simpa [mul_comm] using (Nat.div_add_mod a b).symm
  have hd : d = d / b * b + d % b := by
    simpa [mul_comm] using (Nat.div_add_mod d b).symm
  rw [← hdiv] at hd
  omega

lemma pointMod_step_of_carry_one {k n b : ℕ} (hb : 0 < b)
    (x : Fin k → Fin n) (hx : StrictMono x)
    (i : ℕ) (hi : i + 1 < k)
    (hc : (blockCarry (b := b) x hx i hi).val = 1) :
    (x ⟨i + 1, hi⟩).val % b + b =
      (x ⟨i, by omega⟩).val % b + waveGap x i hi % b := by
  have hchar := blockCarry_eq_ite hb x hx i hi
  have hge : b ≤ (x ⟨i, by omega⟩).val % b + waveGap x i hi % b := by
    by_contra h
    rw [if_neg h] at hchar
    omega
  have hmod := Nat.add_mod_add_of_le_add_mod hge
  rw [add_waveGap_eq hx i hi] at hmod
  exact hmod

lemma pointMod_step_of_carry_zero {k n b : ℕ} (hb : 0 < b)
    (x : Fin k → Fin n) (hx : StrictMono x)
    (i : ℕ) (hi : i + 1 < k)
    (hc : (blockCarry (b := b) x hx i hi).val = 0) :
    (x ⟨i + 1, hi⟩).val % b =
      (x ⟨i, by omega⟩).val % b + waveGap x i hi % b := by
  have hchar := blockCarry_eq_ite hb x hx i hi
  have hlt : (x ⟨i, by omega⟩).val % b + waveGap x i hi % b < b := by
    by_contra h
    rw [if_pos (by omega)] at hchar
    omega
  have hmod := Nat.add_mod_of_add_mod_lt hlt
  rw [add_waveGap_eq hx i hi] at hmod
  exact hmod

lemma gap_eq_coarse_mul_add_mod {k n b : ℕ} (x : Fin k → Fin n)
    (i : ℕ) (hi : i + 1 < k) :
    waveGap x i hi = coarseGap (b := b) x i hi * b + waveGap x i hi % b := by
  simp only [coarseGap]
  simpa [mul_comm] using (Nat.div_add_mod (waveGap x i hi) b).symm

lemma point_eq_div_mul_add_mod {k n b : ℕ} (x : Fin k → Fin n)
    (i : Fin k) :
    (x i).val = (x i).val / b * b + (x i).val % b := by
  simpa [mul_comm] using (Nat.div_add_mod (x i).val b).symm

/-- Five equal coarse gaps cannot have carries `1,1,1,0,0`. -/
lemma carries_ne_11100 {k n b : ℕ} (hb : 0 < b)
    {x : Fin k → Fin n} (hx : IsAscendingWave x)
    (i : ℕ) (hi : i + 5 < k)
    (heq : ∀ (j : ℕ) (hj : j < 5),
      coarseGap (b := b) x (i + j) (by omega) =
        coarseGap (b := b) x i (by omega)) :
    ¬((blockCarry (b := b) x hx.1 i (by omega)).val = 1 ∧
      (blockCarry (b := b) x hx.1 (i + 1) (by omega)).val = 1 ∧
      (blockCarry (b := b) x hx.1 (i + 2) (by omega)).val = 1 ∧
      (blockCarry (b := b) x hx.1 (i + 3) (by omega)).val = 0 ∧
      (blockCarry (b := b) x hx.1 (i + 4) (by omega)).val = 0) := by
  rintro ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hr01 : waveGap x i (by omega) % b ≤
      waveGap x (i + 1) (by omega) % b :=
    mod_le_mod_of_le_of_div_eq (ascending_gap_mono hx i (by omega))
      (heq 1 (by omega)).symm
  have hr12 : waveGap x (i + 1) (by omega) % b ≤
      waveGap x (i + 2) (by omega) % b :=
    mod_le_mod_of_le_of_div_eq (ascending_gap_mono hx (i + 1) (by omega))
      ((heq 1 (by omega)).trans (heq 2 (by omega)).symm)
  have hr23 : waveGap x (i + 2) (by omega) % b ≤
      waveGap x (i + 3) (by omega) % b :=
    mod_le_mod_of_le_of_div_eq (ascending_gap_mono hx (i + 2) (by omega))
      ((heq 2 (by omega)).trans (heq 3 (by omega)).symm)
  have hr34 : waveGap x (i + 3) (by omega) % b ≤
      waveGap x (i + 4) (by omega) % b :=
    mod_le_mod_of_le_of_div_eq (ascending_gap_mono hx (i + 3) (by omega))
      ((heq 3 (by omega)).trans (heq 4 (by omega)).symm)
  have hstep0 := pointMod_step_of_carry_one hb x hx.1 i (by omega) hc0
  have hstep1 := pointMod_step_of_carry_one hb x hx.1 (i + 1) (by omega) hc1
  have hstep2 := pointMod_step_of_carry_one hb x hx.1 (i + 2) (by omega) hc2
  have hstep3 := pointMod_step_of_carry_zero hb x hx.1 (i + 3) (by omega) hc3
  have hstep4 := pointMod_step_of_carry_zero hb x hx.1 (i + 4) (by omega) hc4
  norm_num [Nat.add_assoc] at hstep0 hstep1 hstep2 hstep3 hstep4
  have hr2 : waveGap x (i + 2) (by omega) % b < b := Nat.mod_lt _ hb
  have hz0 : (x ⟨i, by omega⟩).val % b < b := Nat.mod_lt _ hb
  have hz5 : (x ⟨i + 5, hi⟩).val % b < b := Nat.mod_lt _ hb
  omega

/-! ### Counting the carry words -/

/-- The five-bit words other than the forbidden word `11100`. -/
def AllowedCarry5 :=
  {e : Fin 5 → Fin 2 //
    ¬(e 0).val = 1 ∨ ¬(e 1).val = 1 ∨ ¬(e 2).val = 1 ∨
      ¬(e 3).val = 0 ∨ ¬(e 4).val = 0}

deriving instance Fintype for AllowedCarry5

lemma card_allowedCarry5 : Fintype.card AllowedCarry5 = 31 := by decide

lemma thirty_one_pow_thirty_two_le : 31 ^ 32 ≤ 2 ^ 159 := by norm_num

lemma prod_one_two {l : ℕ} (s : Finset (Fin l)) :
    (∏ q : Fin l, if q ∈ s then 1 else 2) = 2 ^ (l - s.card) := by
  classical
  have hsub : s ⊆ (Finset.univ : Finset (Fin l)) := Finset.subset_univ _
  calc
    (∏ q : Fin l, if q ∈ s then 1 else 2) =
        (∏ q ∈ s, if q ∈ s then 1 else 2) *
          ∏ q ∈ (Finset.univ : Finset (Fin l)) \ s,
            if q ∈ s then 1 else 2 := by
      rw [← Finset.prod_union Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset hsub]
    _ = 2 ^ (l - s.card) := by
      have hleft : (∏ q ∈ s, if q ∈ s then 1 else 2) = 1 := by simp
      have hright :
          (∏ q ∈ (Finset.univ : Finset (Fin l)) \ s,
            if q ∈ s then 1 else 2) =
              2 ^ ((Finset.univ : Finset (Fin l)) \ s).card := by
        calc
          (∏ q ∈ (Finset.univ : Finset (Fin l)) \ s,
              if q ∈ s then 1 else 2) =
              ∏ _q ∈ (Finset.univ : Finset (Fin l)) \ s, (2 : ℕ) := by
            apply Finset.prod_congr rfl
            intro q hq
            simp [(Finset.mem_sdiff.mp hq).2]
          _ = 2 ^ ((Finset.univ : Finset (Fin l)) \ s).card :=
            Finset.prod_const 2
      rw [hleft, one_mul, hright]
      have hcard : ((Finset.univ : Finset (Fin l)) \ s).card = l - s.card := by
        rw [Finset.card_sdiff]
        simp
      rw [hcard]

/-- Bit functions taking prescribed values on an injectively indexed set. -/
def bitCylinder {α : Type*} [Fintype α] {l : ℕ}
    (j : α → Fin l) (a : α → Fin 2) : Finset (Fin l → Fin 2) :=
  Finset.univ.filter fun e ↦ ∀ i, e (j i) = a i

lemma card_bitCylinder {α : Type*} [Fintype α] {l : ℕ}
    (j : α → Fin l) (a : α → Fin 2) (hj : Function.Injective j) :
    (bitCylinder j a).card = 2 ^ (l - Fintype.card α) := by
  classical
  let allowed : Fin l → Finset (Fin 2) := fun q ↦
    if hq : q ∈ Finset.univ.image j then {a (Finset.mem_image.mp hq).choose} else Finset.univ
  have hallowed (q : Fin l) :
      (allowed q).card = if q ∈ Finset.univ.image j then 1 else 2 := by
    simp only [allowed]
    split_ifs <;> simp
  have hcyl : bitCylinder j a = Fintype.piFinset allowed := by
    ext e
    rw [bitCylinder, Finset.mem_filter, Fintype.mem_piFinset]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro he q
      simp only [allowed]
      split_ifs with hq
      · rw [Finset.mem_singleton]
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hq
        have hchoose : (Finset.mem_image.mp hq).choose = i := by
          apply hj
          exact (Finset.mem_image.mp hq).choose_spec.2.trans hi.symm
        calc
          e q = e (j i) := congrArg e hi.symm
          _ = a i := he i
          _ = a (Finset.mem_image.mp hq).choose := congrArg a hchoose.symm
      · exact Finset.mem_univ _
    · intro he i
      have hq := he (j i)
      have hm : j i ∈ Finset.univ.image j := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      simp only [allowed, dif_pos hm, Finset.mem_singleton] at hq
      have hchoose : (Finset.mem_image.mp hm).choose = i := by
        apply hj
        exact (Finset.mem_image.mp hm).choose_spec.2
      calc
        e (j i) = a (Finset.mem_image.mp hm).choose := hq
        _ = a i := congrArg a hchoose
  rw [hcyl, Fintype.card_piFinset]
  simp_rw [hallowed]
  rw [prod_one_two]
  rw [Finset.card_image_of_injective Finset.univ hj]
  simp

def bitRestrictionEvent {α : Type*} [Fintype α] {l : ℕ}
    (j : α → Fin l) (A : Finset (α → Fin 2)) : Finset (Fin l → Fin 2) :=
  Finset.univ.filter fun e ↦ (fun i ↦ e (j i)) ∈ A

lemma card_bitRestrictionEvent_le {α : Type*} [Fintype α] {l : ℕ}
    (j : α → Fin l) (A : Finset (α → Fin 2))
    (hj : Function.Injective j) :
    (bitRestrictionEvent j A).card ≤ A.card * 2 ^ (l - Fintype.card α) := by
  classical
  have hsub : bitRestrictionEvent j A ⊆ A.biUnion (bitCylinder j) := by
    intro e he
    rw [bitRestrictionEvent, Finset.mem_filter] at he
    rw [Finset.mem_biUnion]
    refine ⟨fun i ↦ e (j i), he.2, ?_⟩
    simp [bitCylinder]
  calc
    (bitRestrictionEvent j A).card ≤ (A.biUnion (bitCylinder j)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ a ∈ A, (bitCylinder j a).card := Finset.card_biUnion_le
    _ = ∑ _a ∈ A, 2 ^ (l - Fintype.card α) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact card_bitCylinder j a hj
    _ = A.card * 2 ^ (l - Fintype.card α) := by simp

def macroIndex {l : ℕ} (q : Fin (l / 160)) (u : Fin 160) : Fin l :=
  ⟨q.val * 160 + u.val, by
    have hq : q.val + 1 ≤ l / 160 := by omega
    have hmul : (q.val + 1) * 160 ≤ (l / 160) * 160 :=
      Nat.mul_le_mul_right 160 hq
    have hdiv := Nat.div_mul_le_self l 160
    omega⟩

@[simp] lemma macroIndex_val {l : ℕ} (q : Fin (l / 160)) (u : Fin 160) :
    (macroIndex q u).val = q.val * 160 + u.val := rfl

/-- Macroblocks on which a rounded-gap word is constant. -/
def goodMacros {l : ℕ} (s : Fin l → ℕ) : Finset (Fin (l / 160)) :=
  Finset.univ.filter fun q ↦ ∀ u : Fin 160, s (macroIndex q u) = s (macroIndex q 0)

abbrev SelectedCarryIndex {l : ℕ} (G : Finset (Fin (l / 160))) :=
  ({q : Fin (l / 160) // q ∈ G} × Fin 32) × Fin 5

def selectedCarryIndex {l : ℕ} (G : Finset (Fin (l / 160))) :
    SelectedCarryIndex G → Fin l := fun a ↦
  macroIndex a.1.1.1
    ⟨a.1.2.val * 5 + a.2.val, by
      have hc := a.1.2.isLt
      have hu := a.2.isLt
      omega⟩

lemma selectedCarryIndex_injective {l : ℕ} (G : Finset (Fin (l / 160))) :
    Function.Injective (selectedCarryIndex G) := by
  rintro ⟨⟨q, c⟩, u⟩ ⟨⟨q', c'⟩, u'⟩ h
  have hv := congrArg Fin.val h
  have hq : q.val = q'.val := by
    have hc := c.isLt
    have hc' := c'.isLt
    have hu := u.isLt
    have hu' := u'.isLt
    simp only [selectedCarryIndex, macroIndex_val] at hv
    omega
  have hc : c.val = c'.val := by
    have hcl := c.isLt
    have hcl' := c'.isLt
    have hu := u.isLt
    have hu' := u'.isLt
    simp only [selectedCarryIndex, macroIndex_val] at hv
    omega
  have hu : u.val = u'.val := by
    simp only [selectedCarryIndex, macroIndex_val] at hv
    omega
  have hqq : q = q' := Subtype.ext hq
  have hcc : c = c' := Fin.ext hc
  have huu : u = u' := Fin.ext hu
  simp [hqq, hcc, huu]

abbrev CarryCode {l : ℕ} (G : Finset (Fin (l / 160))) :=
  {q : Fin (l / 160) // q ∈ G} → Fin 32 → AllowedCarry5

def flattenCarryCode {l : ℕ} {G : Finset (Fin (l / 160))}
    (c : CarryCode G) : SelectedCarryIndex G → Fin 2 :=
  fun a ↦ (c a.1.1 a.1.2).val a.2

lemma flattenCarryCode_injective {l : ℕ} (G : Finset (Fin (l / 160))) :
    Function.Injective (flattenCarryCode (G := G)) := by
  intro c d h
  funext q r
  apply Subtype.ext
  funext u
  exact congrFun h ((q, r), u)

def allowedCarryAssignments {l : ℕ} (G : Finset (Fin (l / 160))) :
    Finset (SelectedCarryIndex G → Fin 2) :=
  Finset.univ.image flattenCarryCode

lemma card_allowedCarryAssignments_le {l : ℕ} (G : Finset (Fin (l / 160))) :
    (allowedCarryAssignments G).card ≤ 2 ^ (159 * G.card) := by
  classical
  rw [allowedCarryAssignments, Finset.card_image_of_injective Finset.univ
    (flattenCarryCode_injective G)]
  simp only [Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_coe, card_allowedCarry5]
  have hpow : (31 ^ 32) ^ G.card ≤ (2 ^ 159) ^ G.card :=
    Nat.pow_le_pow_left thirty_one_pow_thirty_two_le G.card
  simpa [pow_mul, mul_comm, mul_left_comm, mul_assoc] using hpow

/-- Carry words satisfying the `11100` restriction in every constant macroblock. -/
def admissibleCarries {l : ℕ} (s : Fin l → ℕ) : Finset (Fin l → Fin 2) :=
  bitRestrictionEvent (selectedCarryIndex (goodMacros s))
    (allowedCarryAssignments (goodMacros s))

lemma card_admissibleCarries_le {l : ℕ} (s : Fin l → ℕ) :
    (admissibleCarries s).card ≤ 2 ^ (l - (goodMacros s).card) := by
  classical
  have hbase := card_bitRestrictionEvent_le
    (selectedCarryIndex (goodMacros s)) (allowedCarryAssignments (goodMacros s))
    (selectedCarryIndex_injective (goodMacros s))
  have hA := card_allowedCarryAssignments_le (goodMacros s)
  calc
    (admissibleCarries s).card ≤
        (allowedCarryAssignments (goodMacros s)).card *
          2 ^ (l - Fintype.card (SelectedCarryIndex (goodMacros s))) := hbase
    _ ≤ 2 ^ (159 * (goodMacros s).card) *
          2 ^ (l - Fintype.card (SelectedCarryIndex (goodMacros s))) :=
      Nat.mul_le_mul_right _ hA
    _ = 2 ^ (l - (goodMacros s).card) := by
      have hcard : Fintype.card (SelectedCarryIndex (goodMacros s)) =
          160 * (goodMacros s).card := by
        simp [SelectedCarryIndex, Fintype.card_coe]
        ring
      rw [hcard, ← pow_add]
      congr 1
      have hle : 160 * (goodMacros s).card ≤ l := by
        calc
          160 * (goodMacros s).card ≤ 160 * (l / 160) := by
            gcongr
            simpa using Finset.card_le_univ (goodMacros s)
          _ ≤ l := by
            have hd := Nat.div_mul_le_self l 160
            omega
      omega

def coarseGapWord {k n b : ℕ} (x : Fin k → Fin n) : Fin (k - 1) → ℕ :=
  fun i ↦ coarseGap (b := b) x i.val (by omega)

def carryWord {k n b : ℕ} (x : Fin k → Fin n)
    (hx : StrictMono x) : Fin (k - 1) → Fin 2 :=
  fun i ↦ blockCarry (b := b) x hx i.val (by omega)

def carrySegment5 {k n b : ℕ} (x : Fin k → Fin n)
    (hx : StrictMono x) (i : ℕ) (hi : i + 5 < k) : Fin 5 → Fin 2 :=
  fun u ↦ blockCarry (b := b) x hx (i + u.val) (by omega)

def carrySegment5Allowed {k n b : ℕ} (hb : 0 < b)
    {x : Fin k → Fin n} (hx : IsAscendingWave x)
    (i : ℕ) (hi : i + 5 < k)
    (heq : ∀ (j : ℕ) (hj : j < 5),
      coarseGap (b := b) x (i + j) (by omega) =
        coarseGap (b := b) x i (by omega)) : AllowedCarry5 := by
  refine ⟨carrySegment5 (b := b) x hx.1 i hi, ?_⟩
  have hforbid := carries_ne_11100 hb hx i hi heq
  change
    ¬ (blockCarry (b := b) x hx.1 i (by omega)).val = 1 ∨
    ¬ (blockCarry (b := b) x hx.1 (i + 1) (by omega)).val = 1 ∨
    ¬ (blockCarry (b := b) x hx.1 (i + 2) (by omega)).val = 1 ∨
    ¬ (blockCarry (b := b) x hx.1 (i + 3) (by omega)).val = 0 ∨
    ¬ (blockCarry (b := b) x hx.1 (i + 4) (by omega)).val = 0
  tauto

@[simp] lemma carrySegment5Allowed_val {k n b : ℕ} (hb : 0 < b)
    {x : Fin k → Fin n} (hx : IsAscendingWave x)
    (i : ℕ) (hi : i + 5 < k)
    (heq : ∀ (j : ℕ) (hj : j < 5),
      coarseGap (b := b) x (i + j) (by omega) =
        coarseGap (b := b) x i (by omega)) :
    (carrySegment5Allowed hb hx i hi heq).val =
      carrySegment5 (b := b) x hx.1 i hi := rfl

def carrySegment5AllowedWord {k n b : ℕ} (hb : 0 < b)
    {x : Fin k → Fin n} (hx : IsAscendingWave x)
    (i : ℕ) (hi : i + 5 < k)
    (heq : ∀ u : Fin 5,
      coarseGapWord (b := b) x ⟨i + u.val, by omega⟩ =
        coarseGapWord (b := b) x ⟨i, by omega⟩) : AllowedCarry5 := by
  apply carrySegment5Allowed hb hx i hi
  intro j hj
  exact heq ⟨j, hj⟩

@[simp] lemma carrySegment5AllowedWord_val {k n b : ℕ} (hb : 0 < b)
    {x : Fin k → Fin n} (hx : IsAscendingWave x)
    (i : ℕ) (hi : i + 5 < k)
    (heq : ∀ u : Fin 5,
      coarseGapWord (b := b) x ⟨i + u.val, by omega⟩ =
        coarseGapWord (b := b) x ⟨i, by omega⟩) :
    (carrySegment5AllowedWord hb hx i hi heq).val =
      carrySegment5 (b := b) x hx.1 i hi := rfl

lemma coarseGap_eq_in_goodMacro {k n b : ℕ} (x : Fin k → Fin n)
    {q : Fin ((k - 1) / 160)}
    (hq : q ∈ goodMacros (coarseGapWord (b := b) x))
    (u v : Fin 160) :
    coarseGap (b := b) x (q.val * 160 + u.val) (by
      have hq' := q.isLt
      have hu := u.isLt
      omega) =
    coarseGap (b := b) x (q.val * 160 + v.val) (by
      have hq' := q.isLt
      have hv := v.isLt
      omega) := by
  have hgood := (Finset.mem_filter.mp hq).2
  have hu := hgood u
  have hv := hgood v
  simp only [coarseGapWord, macroIndex_val] at hu hv
  exact hu.trans hv.symm

lemma coarseGap_le {k n b : ℕ} {x : Fin k → Fin n}
    (hx : IsAscendingWave x) {i j : ℕ}
    (hij : i ≤ j) (hj : j + 1 < k) :
    coarseGap (b := b) x i (by omega) ≤ coarseGap (b := b) x j hj := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
      exact le_trans (ih (by omega)) (coarseGap_mono hx j (by omega))

lemma coarseGapWord_monotone {k n b : ℕ} {x : Fin k → Fin n}
    (hx : IsAscendingWave x) : Monotone (coarseGapWord (b := b) x) := by
  intro i j hij
  exact coarseGap_le hx (show i.val ≤ j.val from hij) (by omega)

def goodMacroBase {k n b : ℕ} {x : Fin k → Fin n}
    (q : {q : Fin ((k - 1) / 160) //
      q ∈ goodMacros (coarseGapWord (b := b) x)}) (r : Fin 32) : ℕ :=
  q.val.val * 160 + r.val * 5

lemma goodMacroBase_room {k n b : ℕ} {x : Fin k → Fin n}
    (q : {q : Fin ((k - 1) / 160) //
      q ∈ goodMacros (coarseGapWord (b := b) x)}) (r : Fin 32) :
    goodMacroBase q r + 5 < k := by
  have hq := q.val.isLt
  have hdiv := Nat.div_mul_le_self (k - 1) 160
  have hr := r.isLt
  simp only [goodMacroBase]
  omega

lemma goodMacro_coarse_eq {k n b : ℕ} {x : Fin k → Fin n}
    (q : {q : Fin ((k - 1) / 160) //
      q ∈ goodMacros (coarseGapWord (b := b) x)}) (r : Fin 32) (u : Fin 5) :
    coarseGapWord (b := b) x
        ⟨goodMacroBase q r + u.val, by
          have h := goodMacroBase_room q r
          omega⟩ =
      coarseGapWord (b := b) x
        ⟨goodMacroBase q r, by
          have h := goodMacroBase_room q r
          omega⟩ := by
  have h := coarseGap_eq_in_goodMacro (b := b) x q.2
    ⟨r.val * 5 + u.val, by
      have hr := r.isLt
      have hu := u.isLt
      omega⟩
    ⟨r.val * 5, by
      have hr := r.isLt
      omega⟩
  change coarseGapWord (b := b) x
      ⟨q.val.val * 160 + (r.val * 5 + u.val), by omega⟩ =
    coarseGapWord (b := b) x
      ⟨q.val.val * 160 + r.val * 5, by omega⟩ at h
  simpa only [goodMacroBase, Nat.add_assoc] using h

def goodMacroCarryEntry {k n b : ℕ} (hb : 0 < b)
    {x : Fin k → Fin n} (hx : IsAscendingWave x)
    (q : {q : Fin ((k - 1) / 160) //
      q ∈ goodMacros (coarseGapWord (b := b) x)}) (r : Fin 32) : AllowedCarry5 := by
  exact carrySegment5AllowedWord hb hx (goodMacroBase q r)
    (goodMacroBase_room q r) (goodMacro_coarse_eq q r)

lemma goodMacroCarryEntry_as_segment {k n b : ℕ} (hb : 0 < b)
    {x : Fin k → Fin n} (hx : IsAscendingWave x)
    (q : {q : Fin ((k - 1) / 160) //
      q ∈ goodMacros (coarseGapWord (b := b) x)}) (r : Fin 32) :
    (goodMacroCarryEntry hb hx q r).val =
      carrySegment5 (b := b) x hx.1 (goodMacroBase q r)
        (goodMacroBase_room q r) := by
  exact carrySegment5AllowedWord_val hb hx (goodMacroBase q r)
    (goodMacroBase_room q r) (goodMacro_coarse_eq q r)

@[simp] lemma goodMacroCarryEntry_val {k n b : ℕ} (hb : 0 < b)
    {x : Fin k → Fin n} (hx : IsAscendingWave x)
    (q : {q : Fin ((k - 1) / 160) //
      q ∈ goodMacros (coarseGapWord (b := b) x)}) (r : Fin 32) (u : Fin 5) :
    (goodMacroCarryEntry hb hx q r).val u =
      carryWord (b := b) x hx.1 (selectedCarryIndex
        (goodMacros (coarseGapWord (b := b) x)) ((q, r), u)) := by
  rw [congrFun (goodMacroCarryEntry_as_segment hb hx q r) u]
  have hidx : goodMacroBase q r + u.val =
      (selectedCarryIndex (goodMacros (coarseGapWord (b := b) x))
        ((q, r), u)).val := by
    simp only [selectedCarryIndex, macroIndex_val, goodMacroBase]
    omega
  change blockCarry (b := b) x hx.1 (goodMacroBase q r + u.val) _ =
    blockCarry (b := b) x hx.1
      (selectedCarryIndex (goodMacros (coarseGapWord (b := b) x))
        ((q, r), u)).val _
  exact blockCarry_congr_index (b := b) x hx.1 _ _ hidx

lemma carryWord_mem_admissible {k n b : ℕ} (hb : 0 < b)
    {x : Fin k → Fin n} (hx : IsAscendingWave x) :
    carryWord (b := b) x hx.1 ∈ admissibleCarries (coarseGapWord (b := b) x) := by
  classical
  rw [admissibleCarries, bitRestrictionEvent, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  let code : CarryCode (goodMacros (coarseGapWord (b := b) x)) :=
    fun q r ↦ goodMacroCarryEntry hb hx q r
  rw [allowedCarryAssignments, Finset.mem_image]
  refine ⟨code, Finset.mem_univ _, ?_⟩
  funext a
  rcases a with ⟨⟨q, r⟩, u⟩
  exact goodMacroCarryEntry_val hb hx q r u

lemma badMacro_start_lt_end {l : ℕ} {s : Fin l → ℕ}
    (hs : Monotone s) {q : Fin (l / 160)} (hq : q ∉ goodMacros s) :
    s (macroIndex q 0) < s (macroIndex q ⟨159, by omega⟩) := by
  rw [goodMacros, Finset.mem_filter] at hq
  have hq' : ¬ ∀ u : Fin 160, s (macroIndex q u) = s (macroIndex q 0) := by
    intro h
    exact hq ⟨Finset.mem_univ _, h⟩
  push Not at hq'
  obtain ⟨u, hu⟩ := hq'
  have hsu : s (macroIndex q 0) ≤ s (macroIndex q u) := hs (by
    apply Fin.mk_le_mk.mpr
    simp)
  have hue : s (macroIndex q u) ≤ s (macroIndex q ⟨159, by omega⟩) := hs (by
    apply Fin.mk_le_mk.mpr
    have hu' := u.isLt
    simp
    omega)
  omega

lemma card_goodMacros_ge {l D : ℕ} {s : Fin l → ℕ}
    (hs : Monotone s) (hD : ∀ i, s i ≤ D) :
    l / 160 - D ≤ (goodMacros s).card := by
  classical
  let bad := (Finset.univ : Finset (Fin (l / 160))) \ goodMacros s
  have hbadD : bad.card ≤ D := by
    let code : {q : Fin (l / 160) // q ∈ bad} → Fin D := fun q ↦
      ⟨s (macroIndex q.1 ⟨159, by omega⟩) - 1, by
        have hnot : q.1 ∉ goodMacros s := (Finset.mem_sdiff.mp q.2).2
        have hpos := badMacro_start_lt_end hs hnot
        have hbnd := hD (macroIndex q.1 ⟨159, by omega⟩)
        omega⟩
    have hinj : Function.Injective code := by
      intro q r hcode
      apply Subtype.ext
      apply Fin.ext
      rcases lt_trichotomy q.1.val r.1.val with hqr | hqr | hqr
      · have hnotq : q.1 ∉ goodMacros s := (Finset.mem_sdiff.mp q.2).2
        have hnotr : r.1 ∉ goodMacros s := (Finset.mem_sdiff.mp r.2).2
        have hincq := badMacro_start_lt_end hs hnotq
        have hinc := badMacro_start_lt_end hs hnotr
        have hbetween : s (macroIndex q.1 ⟨159, by omega⟩) ≤
            s (macroIndex r.1 0) := hs (by
          apply Fin.mk_le_mk.mpr
          simp
          omega)
        have hv := congrArg Fin.val hcode
        simp only [code] at hv
        omega
      · exact hqr
      · have hnotq : q.1 ∉ goodMacros s := (Finset.mem_sdiff.mp q.2).2
        have hnotr : r.1 ∉ goodMacros s := (Finset.mem_sdiff.mp r.2).2
        have hinc := badMacro_start_lt_end hs hnotq
        have hincr := badMacro_start_lt_end hs hnotr
        have hbetween : s (macroIndex r.1 ⟨159, by omega⟩) ≤
            s (macroIndex q.1 0) := hs (by
          apply Fin.mk_le_mk.mpr
          simp
          omega)
        have hv := congrArg Fin.val hcode
        simp only [code] at hv
        omega
    have hc := Fintype.card_le_of_injective code hinj
    rw [Fintype.card_coe] at hc
    simpa using hc
  have hpartition : bad.card + (goodMacros s).card = l / 160 := by
    have hle : (goodMacros s).card ≤ l / 160 := by
      simpa using Finset.card_le_univ (goodMacros s)
    simp only [bad, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin]
    omega
  omega

/-! ### Counting the monotone coarse-gap words -/

/-- A nondecreasing word of length `l` with entries between `0` and `D`. -/
abbrev BoundedMonoWord (l D : ℕ) :=
  {s : Fin l → Fin (D + 1) // Monotone s}

noncomputable instance (l D : ℕ) : Fintype (BoundedMonoWord l D) :=
  Fintype.ofFinite _

/-- Stars-and-bars: add the position to each entry to make the word strictly
increasing. -/
def shiftedMonoWord {l D : ℕ} (s : BoundedMonoWord l D) : Fin l → Fin (l + D) :=
  fun i ↦ ⟨i.val + (s.val i).val, by
    have hi := i.isLt
    have hs := (s.val i).isLt
    omega⟩

lemma shiftedMonoWord_strictMono {l D : ℕ} (s : BoundedMonoWord l D) :
    StrictMono (shiftedMonoWord s) := by
  intro i j hij
  have hs := s.2 hij.le
  change i.val + (s.val i).val < j.val + (s.val j).val
  change (s.val i).val ≤ (s.val j).val at hs
  omega

def monoWordSetCode {l D : ℕ} (s : BoundedMonoWord l D) :
    {t : Finset (Fin (l + D)) // t.card = l} := by
  classical
  refine ⟨Finset.univ.image (shiftedMonoWord s), ?_⟩
  rw [Finset.card_image_of_injective Finset.univ
    (shiftedMonoWord_strictMono s).injective]
  simp

lemma monoWordSetCode_injective (l D : ℕ) :
    Function.Injective (monoWordSetCode : BoundedMonoWord l D →
      {t : Finset (Fin (l + D)) // t.card = l}) := by
  intro s t hcode
  have hfin : Finset.univ.image (shiftedMonoWord s) =
      Finset.univ.image (shiftedMonoWord t) := congrArg Subtype.val hcode
  have hrange : Set.range (shiftedMonoWord s) = Set.range (shiftedMonoWord t) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      have hm : shiftedMonoWord s i ∈
          Finset.univ.image (shiftedMonoWord s) :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      rw [hfin] at hm
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hm
      exact ⟨j, hj⟩
    · rintro ⟨i, rfl⟩
      have hm : shiftedMonoWord t i ∈
          Finset.univ.image (shiftedMonoWord t) :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      rw [← hfin] at hm
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hm
      exact ⟨j, hj⟩
  have hshift : shiftedMonoWord s = shiftedMonoWord t :=
    ((shiftedMonoWord_strictMono s).range_inj
      (shiftedMonoWord_strictMono t)).mp hrange
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hi := congrArg Fin.val (congrFun hshift i)
  simp only [shiftedMonoWord] at hi
  omega

lemma card_boundedMonoWord (l D : ℕ) :
    Fintype.card (BoundedMonoWord l D) ≤ (l + D).choose l := by
  have hcard := Fintype.card_le_of_injective
    (monoWordSetCode : BoundedMonoWord l D →
      {t : Finset (Fin (l + D)) // t.card = l})
    (monoWordSetCode_injective l D)
  simpa only [Fintype.card_finset_len, Fintype.card_fin] using hcard

/-! ### Encoding complete block-index profiles -/

abbrev WaveProfileCode (l D blocks : ℕ) :=
  Fin blocks × Σ s : BoundedMonoWord l D,
    {e : Fin l → Fin 2 //
      e ∈ admissibleCarries (fun i ↦ (s.val i).val)}

lemma card_waveProfileCode_le (l D blocks : ℕ) :
    Fintype.card (WaveProfileCode l D blocks) ≤
      blocks * ((l + D).choose l * 2 ^ (l - (l / 160 - D))) := by
  classical
  change Fintype.card (Fin blocks ×
    (Σ s : BoundedMonoWord l D,
      {e : Fin l → Fin 2 // e ∈ admissibleCarries (fun i ↦ (s.val i).val)})) ≤ _
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma]
  apply Nat.mul_le_mul_left
  calc
    ∑ s : BoundedMonoWord l D,
        Fintype.card {e : Fin l → Fin 2 //
          e ∈ admissibleCarries (fun i ↦ (s.val i).val)} ≤
        ∑ _s : BoundedMonoWord l D, 2 ^ (l - (l / 160 - D)) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [Fintype.card_coe]
      have hmono : Monotone (fun i ↦ (s.val i).val) := by
        intro i j hij
        exact s.2 hij
      have hbound : ∀ i, (s.val i).val ≤ D := by
        intro i
        have hi := (s.val i).isLt
        omega
      have hgood := card_goodMacros_ge hmono hbound
      calc
        (admissibleCarries (fun i ↦ (s.val i).val)).card ≤
            2 ^ (l - (goodMacros (fun i ↦ (s.val i).val)).card) :=
          card_admissibleCarries_le _
        _ ≤ 2 ^ (l - (l / 160 - D)) := by
          gcongr
          omega
    _ = Fintype.card (BoundedMonoWord l D) *
        2 ^ (l - (l / 160 - D)) := by simp
    _ ≤ (l + D).choose l * 2 ^ (l - (l / 160 - D)) := by
      exact Nat.mul_le_mul_right _ (card_boundedMonoWord l D)

def waveCoarseWord {k b blocks D : ℕ}
    (x : Fin k → Fin (b * blocks)) (hx : IsAscendingWave x)
    (hD : ∀ i : Fin (k - 1), coarseGapWord (b := b) x i ≤ D) :
    BoundedMonoWord (k - 1) D :=
  ⟨fun i ↦ ⟨coarseGapWord (b := b) x i, by
      have hi := hD i
      omega⟩, by
    exact fun _ _ hij ↦ Fin.mk_le_mk.mpr (coarseGapWord_monotone hx hij)⟩

@[simp] lemma waveCoarseWord_val {k b blocks D : ℕ}
    (x : Fin k → Fin (b * blocks)) (hx : IsAscendingWave x)
    (hD : ∀ i : Fin (k - 1), coarseGapWord (b := b) x i ≤ D)
    (i : Fin (k - 1)) :
    ((waveCoarseWord x hx hD).val i).val =
      coarseGapWord (b := b) x i := rfl

def waveCarryWord {k b blocks : ℕ} (x : Fin k → Fin (b * blocks))
    (hx : StrictMono x) : Fin (k - 1) → Fin 2 := carryWord (b := b) x hx

lemma waveCarryWord_mem {k b blocks D : ℕ} (hb : 0 < b)
    (x : Fin k → Fin (b * blocks)) (hx : IsAscendingWave x)
    (hD : ∀ i : Fin (k - 1), coarseGapWord (b := b) x i ≤ D) :
    waveCarryWord (b := b) x hx.1 ∈
      admissibleCarries (fun i ↦ ((waveCoarseWord x hx hD).val i).val) := by
  simpa only [waveCarryWord, waveCoarseWord_val] using
    (carryWord_mem_admissible hb hx)

def encodeWaveProfile {k b blocks D : ℕ} (hb : 0 < b)
    (hk : 0 < k) (x : Fin k → Fin (b * blocks)) (hx : IsAscendingWave x)
    (hD : ∀ i : Fin (k - 1), coarseGapWord (b := b) x i ≤ D) :
    WaveProfileCode (k - 1) D blocks :=
  (pointBlock hb (x ⟨0, hk⟩), ⟨waveCoarseWord x hx hD,
    waveCarryWord (b := b) x hx.1, waveCarryWord_mem hb x hx hD⟩)

lemma pointBlock_profile_eq_of_code_eq {k b blocks D : ℕ} (hb : 0 < b)
    (hk : 0 < k)
    {x y : Fin k → Fin (b * blocks)}
    (hx : IsAscendingWave x) (hy : IsAscendingWave y)
    (hDx : ∀ i : Fin (k - 1), coarseGapWord (b := b) x i ≤ D)
    (hDy : ∀ i : Fin (k - 1), coarseGapWord (b := b) y i ≤ D)
    (hcode : encodeWaveProfile hb hk x hx hDx = encodeWaveProfile hb hk y hy hDy) :
    (fun i ↦ pointBlock hb (x i)) = fun i ↦ pointBlock hb (y i) := by
  have hfirst : pointBlock hb (x ⟨0, hk⟩) = pointBlock hb (y ⟨0, hk⟩) :=
    congrArg Prod.fst hcode
  have hsigma := congrArg Prod.snd hcode
  have hs : waveCoarseWord x hx hDx = waveCoarseWord y hy hDy :=
    congrArg Sigma.fst hsigma
  have he : waveCarryWord (b := b) x hx.1 = waveCarryWord (b := b) y hy.1 := by
    have hdep := congrArg (fun z ↦ z.2.1) hsigma
    exact hdep
  funext i
  apply Fin.ext
  have hall : ∀ j : ℕ, ∀ hj : j < k,
      (pointBlock hb (x ⟨j, hj⟩)).val =
        (pointBlock hb (y ⟨j, hj⟩)).val := by
    intro j hj
    induction j with
    | zero => exact congrArg Fin.val hfirst
    | succ j ih =>
        have hjl : j < k - 1 := by omega
        have hstepx := blockCarry_spec (b := b) x hx.1 j (by omega)
        have hstepy := blockCarry_spec (b := b) y hy.1 j (by omega)
        have hsj := congrArg
          (fun s : BoundedMonoWord (k - 1) D ↦ (s.val ⟨j, hjl⟩).val) hs
        have hej := congrArg (fun e : Fin (k - 1) → Fin 2 ↦ (e ⟨j, hjl⟩).val) he
        change (x ⟨j + 1, by omega⟩).val / b =
            (x ⟨j, by omega⟩).val / b +
              coarseGap (b := b) x j (by omega) +
                (blockCarry (b := b) x hx.1 j (by omega)).val at hstepx
        change (y ⟨j + 1, by omega⟩).val / b =
            (y ⟨j, by omega⟩).val / b +
              coarseGap (b := b) y j (by omega) +
                (blockCarry (b := b) y hy.1 j (by omega)).val at hstepy
        simp only [waveCoarseWord_val, coarseGapWord] at hsj
        change (blockCarry (b := b) x hx.1 j (by omega)).val =
          (blockCarry (b := b) y hy.1 j (by omega)).val at hej
        change (x ⟨j + 1, by omega⟩).val / b =
          (y ⟨j + 1, by omega⟩).val / b
        have ih' := ih (by omega)
        change (x ⟨j, by omega⟩).val / b =
          (y ⟨j, by omega⟩).val / b at ih'
        omega
  exact hall i.val i.isLt

/-- Ascending waves all of whose whole-block gap quotients are at most `D`. -/
noncomputable def smallGapWaves {k b blocks : ℕ} (D : ℕ) :
    Finset (Fin k → Fin (b * blocks)) := by
  classical
  exact Finset.univ.filter fun x ↦ IsAscendingWave x ∧
    ∀ i : Fin (k - 1), coarseGapWord (b := b) x i ≤ D

lemma mem_smallGapWaves {k b blocks D : ℕ}
    {x : Fin k → Fin (b * blocks)} :
    x ∈ smallGapWaves D ↔ IsAscendingWave x ∧
      ∀ i : Fin (k - 1), coarseGapWord (b := b) x i ≤ D := by
  simp [smallGapWaves]

abbrev SmallGapProfile {k b groups : ℕ} (hb : 0 < b) (D : ℕ) :=
  {p : Fin k → Fin (4 * groups) //
    p ∈ sequenceProfiles hb (@smallGapWaves k b (4 * groups) D)}

noncomputable def smallGapProfileWitness {k b groups D : ℕ} (hb : 0 < b)
    (p : @SmallGapProfile k b groups hb D) : Fin k → Fin (b * (4 * groups)) :=
  (Finset.mem_image.mp p.2).choose

lemma smallGapProfileWitness_mem {k b groups D : ℕ} (hb : 0 < b)
    (p : @SmallGapProfile k b groups hb D) :
    smallGapProfileWitness hb p ∈ @smallGapWaves k b (4 * groups) D := by
  exact (Finset.mem_image.mp p.2).choose_spec.1

lemma smallGapProfileWitness_profile {k b groups D : ℕ} (hb : 0 < b)
    (p : @SmallGapProfile k b groups hb D) :
    (fun i ↦ pointBlock hb (smallGapProfileWitness hb p i)) = p.val := by
  exact (Finset.mem_image.mp p.2).choose_spec.2

noncomputable def encodeSmallGapProfile {k b groups D : ℕ} (hb : 0 < b)
    (hk : 0 < k) (p : @SmallGapProfile k b groups hb D) :
    WaveProfileCode (k - 1) D (4 * groups) :=
  encodeWaveProfile hb hk (smallGapProfileWitness hb p)
    ((mem_smallGapWaves.mp (smallGapProfileWitness_mem hb p)).1)
    ((mem_smallGapWaves.mp (smallGapProfileWitness_mem hb p)).2)

lemma encodeSmallGapProfile_injective {k b groups D : ℕ} (hb : 0 < b)
    (hk : 0 < k) : Function.Injective (encodeSmallGapProfile hb hk :
      @SmallGapProfile k b groups hb D → WaveProfileCode (k - 1) D (4 * groups)) := by
  intro p q hcode
  apply Subtype.ext
  rw [← smallGapProfileWitness_profile hb p,
    ← smallGapProfileWitness_profile hb q]
  exact pointBlock_profile_eq_of_code_eq hb hk
    (mem_smallGapWaves.mp (smallGapProfileWitness_mem hb p)).1
    (mem_smallGapWaves.mp (smallGapProfileWitness_mem hb q)).1
    (mem_smallGapWaves.mp (smallGapProfileWitness_mem hb p)).2
    (mem_smallGapWaves.mp (smallGapProfileWitness_mem hb q)).2 hcode

lemma card_smallGapProfiles_le {k b groups D : ℕ} (hb : 0 < b) (hk : 0 < k) :
    (sequenceProfiles hb (@smallGapWaves k b (4 * groups) D)).card ≤
      (4 * groups) * (((k - 1 + D).choose (k - 1)) *
        2 ^ (k - 1 - ((k - 1) / 160 - D))) := by
  have hinj := encodeSmallGapProfile_injective (groups := groups) (D := D) hb hk
  have hc := Fintype.card_le_of_injective
    (encodeSmallGapProfile (groups := groups) (D := D) hb hk) hinj
  rw [Fintype.card_coe] at hc
  exact hc.trans (card_waveProfileCode_le (k - 1) D (4 * groups))

/-- The waves relevant to the second Alon--Spencer union bound. -/
noncomputable def controlledWaves {k b groups : ℕ} (D : ℕ) :
    Finset (Fin k → Fin (b * (4 * groups))) := by
  classical
  exact Finset.univ.filter fun x ↦
    IsAscendingWave x ∧ ∃ hk : 2 ≤ k,
      4 * b ≤ waveGap x 0 (by omega) ∧
        ∀ i : Fin (k - 1), coarseGapWord (b := b) x i ≤ D

lemma mem_controlledWaves {k b groups D : ℕ}
    {x : Fin k → Fin (b * (4 * groups))} :
    x ∈ controlledWaves D ↔ IsAscendingWave x ∧ ∃ hk : 2 ≤ k,
      4 * b ≤ waveGap x 0 (by omega) ∧
        ∀ i : Fin (k - 1), coarseGapWord (b := b) x i ≤ D := by
  classical
  simp [controlledWaves]

lemma controlledWaves_subset_smallGapWaves {k b groups D : ℕ} :
    controlledWaves D ⊆ @smallGapWaves k b (4 * groups) D := by
  intro x hx
  rw [mem_smallGapWaves]
  obtain ⟨hwave, -, -, hD⟩ := mem_controlledWaves.mp hx
  exact ⟨hwave, hD⟩

lemma sequenceProfiles_controlled_subset {k b groups D : ℕ} (hb : 0 < b) :
    sequenceProfiles hb (controlledWaves D) ⊆
      sequenceProfiles hb (@smallGapWaves k b (4 * groups) D) := by
  intro p hp
  rw [sequenceProfiles, Finset.mem_image] at hp ⊢
  obtain ⟨x, hx, rfl⟩ := hp
  exact ⟨x, controlledWaves_subset_smallGapWaves hx, rfl⟩

lemma card_badSeedsFor_controlled_le {k b groups D : ℕ}
    (hb : 0 < b) (hk : 2 ≤ k) :
    (badSeedsFor hb (@controlledWaves k b groups D)).card ≤
      ((4 * groups) * (((k - 1 + D).choose (k - 1)) *
        2 ^ (k - 1 - ((k - 1) / 160 - D)))) *
          (2 * (4 ^ k * 8 ^ (groups - k))) := by
  have hinj : ∀ x ∈ @controlledWaves k b groups D,
      Function.Injective fun i ↦ blockGroup (pointBlock hb (x i)) := by
    intro x hx
    obtain ⟨hwave, hk', hfirst, -⟩ := mem_controlledWaves.mp hx
    exact blockGroups_injective_of_large_first_gap hb hwave hk' hfirst
  calc
    (badSeedsFor hb (@controlledWaves k b groups D)).card ≤
        (sequenceProfiles hb (@controlledWaves k b groups D)).card *
          (2 * (4 ^ k * 8 ^ (groups - k))) :=
      card_badSeedsFor_le hb (@controlledWaves k b groups D) hinj
    _ ≤ ((4 * groups) * (((k - 1 + D).choose (k - 1)) *
        2 ^ (k - 1 - ((k - 1) / 160 - D)))) *
          (2 * (4 ^ k * 8 ^ (groups - k))) := by
      gcongr
      exact (Finset.card_le_card (sequenceProfiles_controlled_subset hb)).trans
        (card_smallGapProfiles_le hb (by omega))

/-! ### A natural-number entropy estimate -/

lemma choose_mul_pow_le_add_pow (n k A : ℕ) (hk : k ≤ n) :
    n.choose k * A ^ (n - k) ≤ (1 + A) ^ n := by
  rw [add_pow]
  calc
    n.choose k * A ^ (n - k) =
        1 ^ k * A ^ (n - k) * n.choose k := by simp [mul_comm]
    _ ≤ ∑ m ∈ Finset.range (n + 1),
        1 ^ m * A ^ (n - m) * n.choose m := by
      exact Finset.single_le_sum (s := Finset.range (n + 1)) (a := k)
        (f := fun m ↦ 1 ^ m * A ^ (n - m) * n.choose m)
        (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))

lemma base4097_entropy : 4097 ^ 4097 ≤ 2 ^ 14 * 4096 ^ 4096 := by
  have hexp : (1 + (4096 : ℝ)⁻¹) ^ 4096 < 3 :=
    (Real.one_add_inv_pow_le_exp (n := 4096)).trans_lt Real.exp_one_lt_three
  have hratio : ((4097 : ℝ) / 4096) ^ 4096 < 3 := by
    convert hexp using 1
    all_goals norm_num
  rw [div_pow] at hratio
  have hpow : (4097 : ℝ) ^ 4096 < 3 * (4096 : ℝ) ^ 4096 :=
    (div_lt_iff₀ (by positivity : (0 : ℝ) < 4096 ^ 4096)).mp hratio
  have hmain : (4097 : ℝ) ^ 4097 < 16384 * (4096 : ℝ) ^ 4096 := by
    rw [show 4097 = 4096 + 1 by omega, pow_succ]
    calc
      (4097 : ℝ) ^ 4096 * 4097 <
          (3 * 4096 ^ 4096) * 4097 := by gcongr
      _ ≤ 16384 * 4096 ^ 4096 := by
        rw [mul_assoc, mul_comm (4096 ^ 4096) 4097, ← mul_assoc]
        gcongr
        norm_num
  rw [show (2 : ℕ) ^ 14 = 16384 by norm_num]
  exact_mod_cast hmain.le

lemma choose_4097_mul_le (t : ℕ) :
    (4097 * t).choose t ≤ 2 ^ (14 * t) := by
  have hw := choose_mul_pow_le_add_pow (4097 * t) t 4096 (by omega)
  have hp := Nat.pow_le_pow_left base4097_entropy t
  rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at hp
  norm_num at hw
  rw [show 4097 * t - t = 4096 * t by omega] at hw
  have hcombined := hw.trans hp
  exact Nat.le_of_mul_le_mul_right hcombined (by positivity)

lemma choose_div_4096 (l : ℕ) :
    (l + l / 4096).choose l ≤ 2 ^ (14 * (l / 4096 + 1)) := by
  let t := l / 4096
  have hlt : l < 4096 * (t + 1) := by
    dsimp [t]
    exact Nat.lt_mul_div_succ l (by decide : 0 < 4096)
  have hn : l + t ≤ 4097 * (t + 1) := by omega
  calc
    (l + l / 4096).choose l = (l + t).choose t := by
      change (l + t).choose l = (l + t).choose t
      simpa only [Nat.add_sub_cancel_left] using
        (Nat.choose_symm (Nat.le_add_right l t)).symm
    _ ≤ (4097 * (t + 1)).choose t := Nat.choose_le_choose t hn
    _ ≤ (4097 * (t + 1)).choose (t + 1) := by
      apply Nat.choose_le_succ_of_lt_half_left
      omega
    _ ≤ 2 ^ (14 * (t + 1)) := choose_4097_mul_le (t + 1)
    _ = 2 ^ (14 * (l / 4096 + 1)) := by rfl


end FloorProfileEncoding

section GoodProgressions

/-- A progression long enough to retain `q` terms five spacings apart, plus
one further term which keeps every following block inside the interval. -/
abbrev APCandidate (b groups q : ℕ) :=
  {p : Fin (b * (4 * groups)) × Fin (b * (4 * groups)) //
    b < p.2.val ∧ p.1.val + 5 * q * p.2.val < b * (4 * groups)}

def apTerm {b groups q : ℕ} (p : APCandidate b groups q) (i : Fin q) :
    Fin (b * (4 * groups)) :=
  ⟨p.val.1.val + 5 * i.val * p.val.2.val, by
    have hi := i.isLt
    have hfit := p.2.2
    nlinarith⟩

def apBaseBlock {b groups q : ℕ} (hb : 0 < b)
    (p : APCandidate b groups q) (i : Fin q) : Fin (4 * groups) :=
  pointBlock hb (apTerm p i)

lemma apBaseBlock_succ_lt {b groups q : ℕ} (hb : 0 < b)
    (p : APCandidate b groups q) (i : Fin q) :
    (apBaseBlock hb p i).val + 1 < 4 * groups := by
  have hi := i.isLt
  have hfit := p.2.2
  have hd : b < p.val.2.val := p.2.1
  have hroom : (apTerm p i).val + b < b * (4 * groups) := by
    simp only [apTerm]
    nlinarith
  have hfloor := Nat.div_mul_le_self (apTerm p i).val b
  have hmul : ((apTerm p i).val / b + 1) * b < b * (4 * groups) := by
    calc
      ((apTerm p i).val / b + 1) * b =
          ((apTerm p i).val / b) * b + b := by ring
      _ ≤ (apTerm p i).val + b := Nat.add_le_add_right hfloor b
      _ < b * (4 * groups) := hroom
  simp only [apBaseBlock, pointBlock]
  nlinarith

def apRequestBlock {b groups q : ℕ} (hb : 0 < b)
    (p : APCandidate b groups q) (z : Fin (2 * q)) : Fin (4 * groups) :=
  let i : Fin q := ⟨z.val / 2, by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
    simpa [mul_comm] using z.isLt⟩
  ⟨(apBaseBlock hb p i).val + z.val % 2, by
    have hnext := apBaseBlock_succ_lt hb p i
    have hmod := Nat.mod_lt z.val (by decide : 0 < 2)
    omega⟩

lemma apBaseBlock_separated {b groups q : ℕ} (hb : 0 < b)
    (p : APCandidate b groups q) {i j : Fin q} (hij : i < j) :
    (apBaseBlock hb p i).val + 5 ≤ (apBaseBlock hb p j).val := by
  apply pointBlock_add_le hb (d := 5)
  simp only [apTerm]
  have hij' : i.val + 1 ≤ j.val := by omega
  have hd : b ≤ p.val.2.val := p.2.1.le
  nlinarith

lemma apRequestBlock_injective {b groups q : ℕ} (hb : 0 < b)
    (p : APCandidate b groups q) : Function.Injective (apRequestBlock hb p) := by
  intro z w hzw
  let iz : Fin q := ⟨z.val / 2, by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
    simpa [mul_comm] using z.isLt⟩
  let iw : Fin q := ⟨w.val / 2, by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
    simpa [mul_comm] using w.isLt⟩
  have hv := congrArg Fin.val hzw
  change (apBaseBlock hb p iz).val + z.val % 2 =
    (apBaseBlock hb p iw).val + w.val % 2 at hv
  have hzmod := Nat.mod_lt z.val (by decide : 0 < 2)
  have hwmod := Nat.mod_lt w.val (by decide : 0 < 2)
  rcases lt_trichotomy iz iw with hiw | hiw | hiw
  · have hsep := apBaseBlock_separated hb p hiw
    omega
  · have hdiv : z.val / 2 = w.val / 2 := congrArg Fin.val hiw
    have hbase : (apBaseBlock hb p iz).val = (apBaseBlock hb p iw).val :=
      congrArg (fun v ↦ (apBaseBlock hb p v).val) hiw
    have hmod : z.val % 2 = w.val % 2 := by omega
    apply Fin.ext
    have hz := Nat.mod_add_div z.val 2
    have hw := Nat.mod_add_div w.val 2
    omega
  · have hsep := apBaseBlock_separated hb p hiw
    omega

lemma apRequestFiber_card_le_two {b groups q : ℕ} (hb : 0 < b)
    (p : APCandidate b groups q) (g : Fin groups) :
    (requestFiber (apRequestBlock hb p) g).card ≤ 2 := by
  let code : {z : Fin (2 * q) // z ∈ requestFiber (apRequestBlock hb p) g} →
      Fin 2 := fun z ↦ ⟨z.val.val % 2, Nat.mod_lt _ (by decide)⟩
  have hinj : Function.Injective code := by
    intro z w hcode
    apply Subtype.ext
    apply Fin.ext
    have hmod := congrArg Fin.val hcode
    simp only [code] at hmod
    have hgroup : blockGroup (apRequestBlock hb p z.val) =
        blockGroup (apRequestBlock hb p w.val) := by
      have hz := (Finset.mem_filter.mp z.2).2
      have hw := (Finset.mem_filter.mp w.2).2
      exact hz.trans hw.symm
    let iz : Fin q := ⟨z.val.val / 2, by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
      simpa [mul_comm] using z.val.isLt⟩
    let iw : Fin q := ⟨w.val.val / 2, by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
      simpa [mul_comm] using w.val.isLt⟩
    rcases lt_trichotomy iz iw with hiw | hiw | hiw
    · have hsep := apBaseBlock_separated hb p hiw
      have hreq : (apRequestBlock hb p z.val).val + 4 ≤
          (apRequestBlock hb p w.val).val := by
        change (apBaseBlock hb p iz).val + z.val.val % 2 + 4 ≤
          (apBaseBlock hb p iw).val + w.val.val % 2
        have hzmod := Nat.mod_lt z.val.val (by decide : 0 < 2)
        omega
      exact False.elim ((div_four_ne_of_add_four_le hreq)
        (congrArg Fin.val hgroup))
    · have hdiv : z.val.val / 2 = w.val.val / 2 := congrArg Fin.val hiw
      have hz := Nat.mod_add_div z.val.val 2
      have hw := Nat.mod_add_div w.val.val 2
      omega
    · have hsep := apBaseBlock_separated hb p hiw
      have hreq : (apRequestBlock hb p w.val).val + 4 ≤
          (apRequestBlock hb p z.val).val := by
        change (apBaseBlock hb p iw).val + w.val.val % 2 + 4 ≤
          (apBaseBlock hb p iz).val + z.val.val % 2
        have hwmod := Nat.mod_lt w.val.val (by decide : 0 < 2)
        omega
      exact False.elim ((div_four_ne_of_add_four_le hreq)
        (congrArg Fin.val hgroup).symm)
  have hc := Fintype.card_le_of_injective code hinj
  rw [Fintype.card_coe, Fintype.card_fin] at hc
  exact hc

def pairStateColors (colour : Bool) (s : Fin 3) (u : Fin 2) : Bool :=
  if s.val = 0 then (if u.val = 0 then !colour else colour)
  else if s.val = 1 then (if u.val = 0 then colour else !colour)
  else !colour

lemma pairStateColors_not_both (colour : Bool) (s : Fin 3) :
    ¬(pairStateColors colour s 0 = colour ∧
      pairStateColors colour s 1 = colour) := by
  fin_cases colour <;> fin_cases s <;> decide

lemma exists_pairStateColors (colour a b : Bool)
    (h : ¬(a = colour ∧ b = colour)) :
    ∃ s : Fin 3, pairStateColors colour s 0 = a ∧
      pairStateColors colour s 1 = b := by
  by_cases ha : a = colour
  · by_cases hb : b = colour
    · exact (h ⟨ha, hb⟩).elim
    · refine ⟨1, ?_⟩
      subst a
      cases colour <;> cases b <;> simp_all [pairStateColors]
  · by_cases hb : b = colour
    · refine ⟨0, ?_⟩
      subst b
      cases colour <;> cases a <;> simp_all [pairStateColors]
    · refine ⟨2, ?_⟩
      cases colour <;> cases a <;> cases b <;> simp_all [pairStateColors]

def apRequestColours {q : ℕ} (colour : Bool) (state : Fin q → Fin 3)
    (z : Fin (2 * q)) : Bool :=
  pairStateColors colour
    (state ⟨z.val / 2, by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
      simpa [mul_comm] using z.isLt⟩)
    ⟨z.val % 2, Nat.mod_lt _ (by decide)⟩

def apAvoidSeeds {b groups q : ℕ} (hb : 0 < b)
    (p : APCandidate b groups q) (colour : Bool) : Finset (Seed groups) :=
  Finset.univ.filter fun ω ↦ ∀ i : Fin q,
    ¬(blockColour ω (apBaseBlock hb p i) = colour ∧
      blockColour ω ⟨(apBaseBlock hb p i).val + 1,
        apBaseBlock_succ_lt hb p i⟩ = colour)

lemma apAvoidSeeds_subset_biUnion {b groups q : ℕ} (hb : 0 < b)
    (p : APCandidate b groups q) (colour : Bool) :
    apAvoidSeeds hb p colour ⊆
      (Finset.univ : Finset (Fin q → Fin 3)).biUnion fun state ↦
        seedCylinder (apRequestBlock hb p) (apRequestColours colour state) := by
  classical
  intro ω hω
  have hav : ∀ i : Fin q,
      ¬(blockColour ω (apBaseBlock hb p i) = colour ∧
        blockColour ω ⟨(apBaseBlock hb p i).val + 1,
          apBaseBlock_succ_lt hb p i⟩ = colour) :=
    (Finset.mem_filter.mp hω).2
  choose state hstate using fun i ↦ exists_pairStateColors colour
    (blockColour ω (apBaseBlock hb p i))
    (blockColour ω ⟨(apBaseBlock hb p i).val + 1,
      apBaseBlock_succ_lt hb p i⟩) (hav i)
  rw [Finset.mem_biUnion]
  refine ⟨state, Finset.mem_univ _, ?_⟩
  rw [seedCylinder, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro z
  let i : Fin q := ⟨z.val / 2, by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
    simpa [mul_comm] using z.isLt⟩
  have hzmod := Nat.mod_lt z.val (by decide : 0 < 2)
  have hs := hstate i
  change blockColour ω
      ⟨(apBaseBlock hb p i).val + z.val % 2, by
        have hn := apBaseBlock_succ_lt hb p i
        omega⟩ =
    pairStateColors colour (state i) ⟨z.val % 2, hzmod⟩
  by_cases hz : z.val % 2 = 0
  · have hu : (⟨z.val % 2, hzmod⟩ : Fin 2) = 0 := Fin.ext hz
    have hb' : (⟨(apBaseBlock hb p i).val + z.val % 2, by
        have hn := apBaseBlock_succ_lt hb p i
        omega⟩ : Fin (4 * groups)) = apBaseBlock hb p i := by
      apply Fin.ext
      simp [hz]
    rw [hu, hb']
    exact hs.1.symm
  · have hz' : z.val % 2 = 1 := by omega
    have hu : (⟨z.val % 2, hzmod⟩ : Fin 2) = 1 := Fin.ext hz'
    have hb' : (⟨(apBaseBlock hb p i).val + z.val % 2, by
        have hn := apBaseBlock_succ_lt hb p i
        omega⟩ : Fin (4 * groups)) =
        ⟨(apBaseBlock hb p i).val + 1, apBaseBlock_succ_lt hb p i⟩ := by
      apply Fin.ext
      simp [hz']
    rw [hu, hb']
    exact hs.2.symm

lemma card_apAvoidSeeds_le {b groups q : ℕ} (hb : 0 < b)
    (p : APCandidate b groups q) (colour : Bool) :
    (apAvoidSeeds hb p colour).card ≤
      3 ^ q * 2 ^ (3 * groups - 2 * q) := by
  classical
  calc
    (apAvoidSeeds hb p colour).card ≤
        ((Finset.univ : Finset (Fin q → Fin 3)).biUnion fun state ↦
          seedCylinder (apRequestBlock hb p)
            (apRequestColours colour state)).card :=
      Finset.card_le_card (apAvoidSeeds_subset_biUnion hb p colour)
    _ ≤ ∑ state : Fin q → Fin 3,
        (seedCylinder (apRequestBlock hb p)
          (apRequestColours colour state)).card := Finset.card_biUnion_le
    _ = ∑ _state : Fin q → Fin 3, 2 ^ (3 * groups - 2 * q) := by
      apply Finset.sum_congr rfl
      intro state hstate
      exact card_seedCylinder_of_fiber_le_two
        (apRequestBlock hb p) (apRequestColours colour state)
        (apRequestBlock_injective hb p) (apRequestFiber_card_le_two hb p)
    _ = 3 ^ q * 2 ^ (3 * groups - 2 * q) := by
      simp

def badProgressionSeeds {b groups q : ℕ} (hb : 0 < b) :
    Finset (Seed groups) :=
  (Finset.univ : Finset (APCandidate b groups q)).biUnion fun p ↦
    apAvoidSeeds hb p false ∪ apAvoidSeeds hb p true

lemma card_apCandidates_le (b groups q : ℕ) :
    Fintype.card (APCandidate b groups q) ≤ (b * (4 * groups)) ^ 2 := by
  calc
    Fintype.card (APCandidate b groups q) ≤
        Fintype.card (Fin (b * (4 * groups)) × Fin (b * (4 * groups))) :=
      Fintype.card_subtype_le _
    _ = (b * (4 * groups)) ^ 2 := by
      simp [pow_two]

lemma card_badProgressionSeeds_le {b groups q : ℕ} (hb : 0 < b) :
    (@badProgressionSeeds b groups q hb).card ≤
      (b * (4 * groups)) ^ 2 *
        (2 * (3 ^ q * 2 ^ (3 * groups - 2 * q))) := by
  classical
  calc
    (@badProgressionSeeds b groups q hb).card ≤
        ∑ p : APCandidate b groups q,
          (apAvoidSeeds hb p false ∪ apAvoidSeeds hb p true).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p : APCandidate b groups q,
          2 * (3 ^ q * 2 ^ (3 * groups - 2 * q)) := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        (apAvoidSeeds hb p false ∪ apAvoidSeeds hb p true).card ≤
            (apAvoidSeeds hb p false).card +
              (apAvoidSeeds hb p true).card := Finset.card_union_le _ _
        _ ≤ 2 * (3 ^ q * 2 ^ (3 * groups - 2 * q)) := by
          have hfalse := card_apAvoidSeeds_le hb p false
          have htrue := card_apAvoidSeeds_le hb p true
          omega
    _ = Fintype.card (APCandidate b groups q) *
        (2 * (3 ^ q * 2 ^ (3 * groups - 2 * q))) := by simp
    _ ≤ (b * (4 * groups)) ^ 2 *
        (2 * (3 ^ q * 2 ^ (3 * groups - 2 * q))) := by
      gcongr
      exact card_apCandidates_le b groups q

lemma card_seed (groups : ℕ) : Fintype.card (Seed groups) = 8 ^ groups := by
  simp [Seed, Pattern]

def GoodProgressions {b groups q : ℕ} (hb : 0 < b) (ω : Seed groups) : Prop :=
  ∀ p : APCandidate b groups q, ∀ colour : Bool,
    ∃ i : Fin q,
      blockColour ω (apBaseBlock hb p i) = colour ∧
        blockColour ω ⟨(apBaseBlock hb p i).val + 1,
          apBaseBlock_succ_lt hb p i⟩ = colour

lemma goodProgressions_of_not_mem_bad {b groups q : ℕ} (hb : 0 < b)
    {ω : Seed groups} (hω : ω ∉ badProgressionSeeds (q := q) hb) :
    @GoodProgressions b groups q hb ω := by
  intro p colour
  by_contra hnone
  push Not at hnone
  have hav : ω ∈ apAvoidSeeds hb p colour := by
    rw [apAvoidSeeds, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i hi
    exact hnone i hi.1 hi.2
  apply hω
  rw [badProgressionSeeds, Finset.mem_biUnion]
  refine ⟨p, Finset.mem_univ _, ?_⟩
  cases colour <;> simp_all

lemma waveGap_le {k n : ℕ} {x : Fin k → Fin n}
    (hx : IsAscendingWave x) {i j : ℕ} (hij : i ≤ j) (hj : j + 1 < k) :
    waveGap x i (by omega) ≤ waveGap x j hj := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
      exact le_trans (ih (by omega)) (ascending_gap_mono hx j (by omega))

lemma waveGap_congr_index {k n : ℕ} (x : Fin k → Fin n)
    {i j : ℕ} (hi : i + 1 < k) (hj : j + 1 < k) (hij : i = j) :
    waveGap x i hi = waveGap x j hj := by
  subst j
  rfl

lemma value_add_mul_gap_le {k n : ℕ} {x : Fin k → Fin n}
    (hx : IsAscendingWave x) (h r : ℕ) (hh : h + 1 < k) (hr : h + r < k) :
    (x ⟨h, by omega⟩).val + r * waveGap x h (by omega) ≤
      (x ⟨h + r, hr⟩).val := by
  revert hr
  induction r with
  | zero => intro hr; simp
  | succ r ih =>
      intro hr
      have ihr := ih (by omega)
      have hgap := waveGap_le hx (show h ≤ h + r by omega) (by omega)
      have hadd := add_waveGap_eq hx.1 (h + r) (by omega)
      change (x ⟨h, by omega⟩).val + r * waveGap x h (by omega) ≤
        (x ⟨h + r, by omega⟩).val at ihr
      change waveGap x h (by omega) ≤ waveGap x (h + r) (by omega) at hgap
      change (x ⟨h + r, by omega⟩).val + waveGap x (h + r) (by omega) =
        (x ⟨h + (r + 1), by omega⟩).val at hadd
      change (x ⟨h, by omega⟩).val + (r + 1) * waveGap x h (by omega) ≤
        (x ⟨h + (r + 1), by omega⟩).val
      simp only [Nat.add_mul, Nat.one_mul]
      omega

lemma value_le_add_mul_later_gap {k n : ℕ} {x : Fin k → Fin n}
    (hx : IsAscendingWave x) (h r H : ℕ) (hr : h + r < k)
    (hH : H + 1 < k) (hle : h + r ≤ H + 1) :
    (x ⟨h + r, hr⟩).val ≤
      (x ⟨h, by omega⟩).val + r * waveGap x H hH := by
  revert hr hle
  induction r with
  | zero => intro hr hle; simp
  | succ r ih =>
      intro hr hle
      have ih' := ih (by omega) (by omega)
      have hgap := waveGap_le hx (i := h + r) (j := H) (by omega) hH
      have hadd := add_waveGap_eq hx.1 (h + r) (by omega)
      change (x ⟨h + r, by omega⟩).val ≤
        (x ⟨h, by omega⟩).val + r * waveGap x H hH at ih'
      change waveGap x (h + r) (by omega) ≤ waveGap x H hH at hgap
      change (x ⟨h + r, by omega⟩).val + waveGap x (h + r) (by omega) =
        (x ⟨h + (r + 1), by omega⟩).val at hadd
      change (x ⟨h + (r + 1), by omega⟩).val ≤
        (x ⟨h, by omega⟩).val + (r + 1) * waveGap x H hH
      simp only [Nat.add_mul, Nat.one_mul]
      omega

def waveAPCandidate {k b groups q : ℕ}
    {x : Fin k → Fin (b * (4 * groups))} (hx : IsAscendingWave x)
    (hq : 0 < q) (h : ℕ) (hroom : h + 5 * q < k)
    (hlarge : b < waveGap x h (by omega)) : APCandidate b groups q := by
  have hh : h + 1 < k := by omega
  have hdlt : waveGap x h hh < b * (4 * groups) := by
    have hadd := add_waveGap_eq hx.1 h hh
    have hv := (x ⟨h + 1, hh⟩).isLt
    omega
  refine ⟨(x ⟨h, by omega⟩, ⟨waveGap x h hh, hdlt⟩), hlarge, ?_⟩
  have hreach := value_add_mul_gap_le hx h (5 * q) hh hroom
  have hv := (x ⟨h + 5 * q, hroom⟩).isLt
  exact lt_of_le_of_lt hreach hv

lemma goodProgression_gap_step {k b groups q : ℕ} (hb : 0 < b)
    {ω : Seed groups} (hgood : @GoodProgressions b groups q hb ω)
    {x : Fin k → Fin (b * (4 * groups))} (hx : IsAscendingWave x)
    {colour : Bool} (hmono : ∀ i, pointColour hb ω (x i) = colour)
    (hq : 0 < q) (h : ℕ) (hroom : h + 5 * q + 1 < k)
    (hlarge : b < waveGap x h (by omega)) :
    5 * q * waveGap x h (by omega) + b ≤
      5 * q * waveGap x (h + 5 * q) (by omega) := by
  let p := waveAPCandidate hx hq h (by omega) hlarge
  obtain ⟨i, hpair0, hpair1⟩ := hgood p (!colour)
  let j := h + 5 * i.val
  have hj : j < k := by
    have hi := i.isLt
    dsimp [j]
    omega
  have hh : h + 1 < k := by omega
  have hlower := value_add_mul_gap_le hx h (5 * i.val) hh (by
    dsimp [j] at hj
    omega)
  have hterm : (apTerm p i).val =
      (x ⟨h, by omega⟩).val + 5 * i.val * waveGap x h hh := by
    rfl
  have hblockge : (apBaseBlock hb p i).val ≤
      (pointBlock hb (x ⟨j, hj⟩)).val := by
    apply pointBlock_add_le hb (d := 0)
    simp only [Nat.zero_mul, Nat.add_zero]
    rw [hterm]
    exact hlower
  have hblockgt : (apBaseBlock hb p i).val + 1 <
      (pointBlock hb (x ⟨j, hj⟩)).val := by
    by_contra hnot
    have hle : (pointBlock hb (x ⟨j, hj⟩)).val ≤
        (apBaseBlock hb p i).val + 1 := by omega
    have heq : pointBlock hb (x ⟨j, hj⟩) = apBaseBlock hb p i ∨
        pointBlock hb (x ⟨j, hj⟩) =
          ⟨(apBaseBlock hb p i).val + 1, apBaseBlock_succ_lt hb p i⟩ := by
      have hv : (pointBlock hb (x ⟨j, hj⟩)).val =
          (apBaseBlock hb p i).val ∨
          (pointBlock hb (x ⟨j, hj⟩)).val = (apBaseBlock hb p i).val + 1 := by
        omega
      rcases hv with hv | hv
      · exact Or.inl (Fin.ext hv)
      · exact Or.inr (Fin.ext hv)
    have hc := hmono ⟨j, hj⟩
    simp only [pointColour] at hc
    rcases heq with heq | heq
    · rw [heq, hpair0] at hc
      cases colour <;> simp at hc
    · rw [heq, hpair1] at hc
      cases colour <;> simp at hc
  have hxlower : ((apBaseBlock hb p i).val + 2) * b ≤
      (x ⟨j, hj⟩).val := by
    apply (Nat.le_div_iff_mul_le hb).mp
    simp only [pointBlock] at hblockgt ⊢
    omega
  have htermupper : (apTerm p i).val <
      ((apBaseBlock hb p i).val + 1) * b := by
    have hm := Nat.mod_lt (apTerm p i).val hb
    have hd := Nat.mod_add_div (apTerm p i).val b
    simp only [apBaseBlock, pointBlock]
    nlinarith
  have hgain : (apTerm p i).val + b < (x ⟨j, hj⟩).val := by
    nlinarith
  have hupper := value_le_add_mul_later_gap hx h (5 * i.val) (h + 5 * q)
    (by omega) (by omega) (by
      have hi := i.isLt
      omega)
  rw [hterm] at hgain
  dsimp [j] at hgain
  have hlocal : 5 * i.val * waveGap x h (by omega) + b ≤
      5 * i.val * waveGap x (h + 5 * q) (by omega) := by
    omega
  have hgaple := waveGap_le hx (i := h) (j := h + 5 * q)
    (by omega) (by omega)
  have hiq : i.val ≤ q := i.isLt.le
  have hrest : 5 * (q - i.val) * waveGap x h (by omega) ≤
      5 * (q - i.val) * waveGap x (h + 5 * q) (by omega) := by
    gcongr
  have hsplit (d : ℕ) : 5 * q * d =
      5 * i.val * d + 5 * (q - i.val) * d := by
    calc
      5 * q * d = 5 * ((q - i.val) + i.val) * d := by
        rw [Nat.sub_add_cancel hiq]
      _ = 5 * i.val * d + 5 * (q - i.val) * d := by ring
  have hsplitStart : 5 * q * waveGap x h (by omega) =
      5 * i.val * waveGap x h (by omega) +
        5 * (q - i.val) * waveGap x h (by omega) := by
    exact hsplit _
  have hsplitEnd : 5 * q * waveGap x (h + 5 * q) (by omega) =
      5 * i.val * waveGap x (h + 5 * q) (by omega) +
        5 * (q - i.val) * waveGap x (h + 5 * q) (by omega) := by
    exact hsplit _
  calc
    5 * q * waveGap x h (by omega) + b =
        (5 * i.val * waveGap x h (by omega) + b) +
          5 * (q - i.val) * waveGap x h (by omega) := by
      omega
    _ ≤ 5 * i.val * waveGap x (h + 5 * q) (by omega) +
          5 * (q - i.val) * waveGap x (h + 5 * q) (by omega) :=
      Nat.add_le_add hlocal hrest
    _ = 5 * q * waveGap x (h + 5 * q) (by omega) := by
      exact hsplitEnd.symm

lemma exists_fin_eq_of_between {k : ℕ} (f : Fin k → ℕ)
    (target last : ℕ)
    (hstep : ∀ i : ℕ, ∀ hi : i + 1 < k, i < last →
      f ⟨i + 1, hi⟩ ≤ f ⟨i, by omega⟩ + 1)
    (hlast : last < k)
    (hstart : f ⟨0, by omega⟩ ≤ target)
    (hend : target ≤ f ⟨last, hlast⟩) :
    ∃ i : Fin k, f i = target := by
  classical
  let P : ℕ → Prop := fun i ↦ ∃ hi : i < k, target ≤ f ⟨i, hi⟩
  have hex : ∃ i, P i := ⟨last, hlast, hend⟩
  let m := Nat.find hex
  have hmdef : m = Nat.find hex := rfl
  obtain ⟨hmk, htarget⟩ := Nat.find_spec hex
  change m < k at hmk
  change target ≤ f ⟨m, hmk⟩ at htarget
  by_cases hm : m = 0
  · have hmfind : Nat.find hex = 0 := by omega
    have htarget0 : target ≤ f ⟨0, by omega⟩ := by
      have hfin : (⟨m, hmk⟩ : Fin k) = ⟨0, by omega⟩ := Fin.ext hm
      simpa only [hfin] using htarget
    exact ⟨⟨0, by omega⟩, by
      apply le_antisymm
      · exact hstart
      · exact htarget0⟩
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hprevlt : m - 1 < m := by omega
    have hnot := Nat.find_min hex hprevlt
    have hprevk : m - 1 < k := by omega
    have hprev : f ⟨m - 1, hprevk⟩ < target := by
      by_contra hn
      apply hnot
      exact ⟨hprevk, by omega⟩
    have hmle := Nat.find_min' hex ⟨hlast, hend⟩
    change m ≤ last at hmle
    have hst := hstep (m - 1) (by omega) (by omega)
    have heqFin : (⟨m - 1 + 1, by omega⟩ : Fin k) = ⟨m, hmk⟩ := by
      apply Fin.ext
      change m - 1 + 1 = m
      omega
    have hst' : f ⟨m, hmk⟩ ≤ f ⟨m - 1, hprevk⟩ + 1 := by
      rw [heqFin] at hst
      exact hst
    exact ⟨⟨m, hmk⟩, le_antisymm (by omega) htarget⟩

lemma exists_gap_gt_blockLength {k b groups : ℕ} (hb : 0 < b)
    (ω : Seed groups) {x : Fin k → Fin (b * (4 * groups))}
    (hx : IsAscendingWave x) {colour : Bool}
    (hmono : ∀ i, pointColour hb ω (x i) = colour)
    (hroom : 6 * b + 1 < k) :
    ∃ h : ℕ, ∃ hh : h + 1 < k, h ≤ 6 * b ∧ b < waveGap x h hh := by
  by_contra hnone
  push Not at hnone
  have hsmall : ∀ h : ℕ, ∀ hh : h + 1 < k, h ≤ 6 * b →
      waveGap x h hh ≤ b := by
    intro h hh hle
    exact hnone h hh hle
  let last := 6 * b + 1
  have hlast : last < k := hroom
  let f : Fin k → ℕ := fun i ↦ (pointBlock hb (x i)).val
  have hstep : ∀ i : ℕ, ∀ hi : i + 1 < k, i ≤ 6 * b →
      f ⟨i + 1, hi⟩ ≤ f ⟨i, by omega⟩ + 1 := by
    intro i hi hile
    have hs := hsmall i hi hile
    have hadd := add_waveGap_eq hx.1 i hi
    have hval : (x ⟨i + 1, hi⟩).val ≤ (x ⟨i, by omega⟩).val + b := by omega
    dsimp [f]
    simp only [pointBlock]
    calc
      (x ⟨i + 1, hi⟩).val / b ≤
          ((x ⟨i, by omega⟩).val + b) / b := Nat.div_le_div_right hval
      _ = (x ⟨i, by omega⟩).val / b + 1 := Nat.add_div_right _ hb
  have hindexLower : (x ⟨0, by omega⟩).val + last ≤
      (x ⟨last, hlast⟩).val := by
    have hgap0 : 1 ≤ waveGap x 0 (by omega) := by
      have hs := hx.1 (show (⟨0, by omega⟩ : Fin k) < ⟨1, by omega⟩ by simp)
      have hsv : (x ⟨0, by omega⟩).val < (x ⟨1, by omega⟩).val :=
        Fin.mk_lt_mk.mp hs
      simp only [waveGap]
      apply Nat.sub_pos_of_lt
      simpa only [Nat.zero_add] using hsv
    have hv := value_add_mul_gap_le hx 0 last (by omega) (by omega)
    have hv' : (x ⟨0, by omega⟩).val + last * waveGap x 0 (by omega) ≤
        (x ⟨last, hlast⟩).val := by
      simpa only [Nat.zero_add] using hv
    have hmul : last ≤ last * waveGap x 0 (by omega) := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left last hgap0
    omega
  let A := f ⟨0, by omega⟩
  let Z := f ⟨last, hlast⟩
  have hspan : A + 6 ≤ Z := by
    by_contra hn
    have hZ : Z ≤ A + 5 := by omega
    have hx0lower : A * b ≤ (x ⟨0, by omega⟩).val := by
      exact (Nat.le_div_iff_mul_le hb).mp (by rfl)
    have hxlastupper : (x ⟨last, hlast⟩).val < (Z + 1) * b := by
      have hm := Nat.mod_lt (x ⟨last, hlast⟩).val hb
      have hd := Nat.mod_add_div (x ⟨last, hlast⟩).val b
      dsimp [Z, f]
      simp only [pointBlock]
      nlinarith
    dsimp [last] at hindexLower
    nlinarith
  let S := 4 * ((A + 3) / 4)
  have hAS : A ≤ S ∧ S ≤ A + 3 := by
    have hm := Nat.mod_lt (A + 3) (by decide : 0 < 4)
    have hd := Nat.mod_add_div (A + 3) 4
    dsimp [S]
    omega
  have hSZ : S + 3 ≤ Z := by omega
  have hSbound : S + 3 < 4 * groups := by
    have hzlt : Z < 4 * groups := (pointBlock hb (x ⟨last, hlast⟩)).isLt
    exact lt_of_le_of_lt hSZ hzlt
  let g : Fin groups := ⟨S / 4, by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 4)]
    omega⟩
  have hSg : S = 4 * g.val := by
    simp [S, g]
  have hall : ∀ r : Fin 4, patternColor (ω g) r = colour := by
    intro r
    let target := S + r.val
    have htargetStart : f ⟨0, by omega⟩ ≤ target := by
      dsimp [A] at hAS
      dsimp [target]
      omega
    have htargetEnd : target ≤ f ⟨last, hlast⟩ := by
      dsimp [Z] at hSZ
      dsimp [target]
      have hr := r.isLt
      omega
    obtain ⟨i, hi⟩ := exists_fin_eq_of_between f target last
      (fun j hj hjlast ↦ hstep j hj (by
        dsimp [last] at hjlast
        omega)) hlast htargetStart htargetEnd
    have hc := hmono i
    simp only [pointColour] at hc
    have hbidx : pointBlock hb (x i) =
        ⟨S + r.val, by
          have hr := r.isLt
          omega⟩ := Fin.ext hi
    rw [hbidx] at hc
    have hgidx : blockGroup (⟨S + r.val, by
        have hr := r.isLt
        omega⟩ : Fin (4 * groups)) = g := by
      apply Fin.ext
      simp only [blockGroup]
      rw [hSg]
      omega
    have hridx : blockCoord (⟨S + r.val, by
        have hr := r.isLt
        omega⟩ : Fin (4 * groups)) = r := by
      apply Fin.ext
      simp only [blockCoord]
      rw [hSg]
      omega
    simpa only [blockColour, hgidx, hridx] using hc
  have hnot := four_consecutive_not_monochromatic ω g
  cases colour
  · exact hnot.2 hall
  · exact hnot.1 hall

lemma goodProgression_gap_iterate {k b groups q : ℕ} (hb : 0 < b)
    {ω : Seed groups} (hgood : @GoodProgressions b groups q hb ω)
    {x : Fin k → Fin (b * (4 * groups))} (hx : IsAscendingWave x)
    {colour : Bool} (hmono : ∀ i, pointColour hb ω (x i) = colour)
    (hq : 0 < q) (h R : ℕ) (hroom : h + R * (5 * q) + 1 < k)
    (hlarge : b < waveGap x h (by omega)) :
    5 * q * waveGap x h (by omega) + R * b ≤
      5 * q * waveGap x (h + R * (5 * q)) (by omega) := by
  revert hroom hlarge
  induction R with
  | zero => intro hroom hlarge; simp
  | succ R ih =>
      intro hroom hlarge
      have hroomR : h + R * (5 * q) + 1 < k := by
        nlinarith
      have hi := ih hroomR hlarge
      have hlargeR : b < waveGap x (h + R * (5 * q)) (by omega) :=
        lt_of_lt_of_le hlarge (waveGap_le hx (i := h)
          (j := h + R * (5 * q)) (by omega) (by omega))
      have hs := goodProgression_gap_step hb hgood hx hmono hq
        (h + R * (5 * q)) (by
          nlinarith) hlargeR
      have hidx : h + R * (5 * q) + 5 * q =
          h + (R + 1) * (5 * q) := by ring
      have hs' : 5 * q * waveGap x (h + R * (5 * q)) (by omega) + b ≤
          5 * q * waveGap x (h + (R + 1) * (5 * q)) (by omega) := by
        calc
          5 * q * waveGap x (h + R * (5 * q)) (by omega) + b ≤
              5 * q * waveGap x (h + R * (5 * q) + 5 * q) (by omega) := hs
          _ = 5 * q * waveGap x (h + (R + 1) * (5 * q)) (by omega) := by
            rw [waveGap_congr_index x _ _ hidx]
      calc
        5 * q * waveGap x h (by omega) + (R + 1) * b =
            (5 * q * waveGap x h (by omega) + R * b) + b := by ring
        _ ≤ 5 * q * waveGap x (h + R * (5 * q)) (by omega) + b :=
          Nat.add_le_add_right hi b
        _ ≤ 5 * q * waveGap x (h + (R + 1) * (5 * q)) (by omega) := hs'

lemma largeGap_of_goodProgressions {k b groups q : ℕ} (hb : 0 < b)
    {ω : Seed groups} (hgood : @GoodProgressions b groups q hb ω)
    {x : Fin k → Fin (b * (4 * groups))} (hx : IsAscendingWave x)
    {colour : Bool} (hmono : ∀ i, pointColour hb ω (x i) = colour)
    (hq : 0 < q) (hsize : 6 * b + 75 * q ^ 2 + 2 < k) :
    ∃ H : ℕ, ∃ hH : H + 1 < k,
      H ≤ 6 * b + 75 * q ^ 2 ∧ 4 * b ≤ waveGap x H hH := by
  obtain ⟨h, hh, hhle, hlarge⟩ :=
    exists_gap_gt_blockLength hb ω hx hmono (by omega)
  let R := 15 * q
  have hroom : h + R * (5 * q) + 1 < k := by
    dsimp [R]
    nlinarith
  have hi := goodProgression_gap_iterate hb hgood hx hmono hq h R hroom hlarge
  let H := h + R * (5 * q)
  have hH : H + 1 < k := hroom
  have hstart : 5 * q * b ≤ 5 * q * waveGap x h hh := by
    gcongr
  have hscaled : 5 * q * (4 * b) ≤ 5 * q * waveGap x H hH := by
    dsimp [H, R] at hi ⊢
    nlinarith
  have hfour : 4 * b ≤ waveGap x H hH := by
    exact Nat.le_of_mul_le_mul_left (by
      simpa [mul_assoc] using hscaled) (by positivity)
  refine ⟨H, hH, ?_, hfour⟩
  dsimp [H, R]
  nlinarith

/-! ### Explicit power-of-two parameters -/

def Kparam (s : ℕ) := 2 ^ s
def Bparam (s : ℕ) := 2 ^ (s - 7)
def Qparam (s : ℕ) := 20 * s
def Gparam (s : ℕ) := 2 ^ (2 * s - 40)
def Rparam (s : ℕ) := 2 ^ (s - 2)
def Lparam (s : ℕ) := Rparam s - 1
def Dparam (s : ℕ) := Lparam s / 65536

lemma param_pos {s : ℕ} :
    0 < Bparam s ∧ 0 < Gparam s ∧ 0 < Kparam s ∧ 0 < Rparam s := by
  simp [Bparam, Gparam, Kparam, Rparam]

lemma forty_mul_le_Gparam {s : ℕ} (hs : 50 ≤ s) : 40 * s ≤ Gparam s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num [Gparam]
  | succ s hs ih =>
      have he : 2 * (s + 1) - 40 = (2 * s - 40) + 2 := by omega
      change 40 * s ≤ 2 ^ (2 * s - 40) at ih
      rw [Gparam, he, pow_add]
      norm_num
      omega

lemma linear_le_small_power {s : ℕ} (hs : 50 ≤ s) :
    2 * s + 15 ≤ 2 ^ (s - 15) := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      have he : s + 1 - 15 = (s - 15) + 1 := by omega
      rw [he, pow_succ]
      nlinarith [Nat.one_le_two_pow (n := s - 15)]

lemma linear_le_Lparam_div {s : ℕ} (hs : 50 ≤ s) :
    2 * s + 15 ≤ Lparam s / 4096 := by
  have hlin := linear_le_small_power hs
  have he : s - 2 = (s - 15) + 13 := by omega
  have hp : 2 ^ (s - 15) * 4096 ≤ 2 ^ (s - 2) - 1 := by
    rw [he, pow_add]
    norm_num
    have hpos : 1 ≤ 2 ^ (s - 15) := Nat.one_le_two_pow
    omega
  apply le_trans hlin
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 4096)]
  simpa only [Lparam, Rparam] using hp

lemma profile_exponent_saving {s : ℕ} (hs : 50 ≤ s) :
    2 * s + 14 * (Lparam s / 4096 + 1) + 1 ≤
      Lparam s / 160 - Dparam s := by
  let l := Lparam s
  let t := l / 4096
  have hlin : 2 * s + 15 ≤ t := by
    simpa only [l, t] using linear_le_Lparam_div hs
  have hD : Dparam s ≤ t := by
    dsimp [Dparam, t, l]
    exact Nat.div_le_div_left (by decide : 4096 ≤ 65536) (by decide)
  have h16 : 16 * t ≤ l / 256 := by
    dsimp [t]
    have hm := Nat.div_mul_le_self l 4096
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 256)).2
    nlinarith
  have h160 : l / 256 ≤ l / 160 :=
    Nat.div_le_div_left (by decide : 160 ≤ 256) (by decide)
  dsimp [l] at hlin hD h16 h160 ⊢
  omega

lemma three_pow_Qparam_le {s : ℕ} : 3 ^ Qparam s ≤ 2 ^ (32 * s) := by
  change 3 ^ (20 * s) ≤ 2 ^ (32 * s)
  have hbase : 3 ^ 5 ≤ 2 ^ 8 := by norm_num
  have hp := Nat.pow_le_pow_left hbase (4 * s)
  rw [← pow_mul, ← pow_mul] at hp
  convert hp using 1 <;> congr 1 <;> omega

lemma intervalSize_param (s : ℕ) (hs : 50 ≤ s) :
    Bparam s * (4 * Gparam s) = 2 ^ (3 * s - 45) := by
  have h1 : s - 7 + 2 + (2 * s - 40) = 3 * s - 45 := by omega
  simp only [Bparam, Gparam]
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add]
  congr 1
  omega

lemma Rparam_sub_one (s : ℕ) : Rparam s - 1 = Lparam s := rfl

lemma card_badProgressionSeeds_param {s : ℕ} (hs : 50 ≤ s) :
    (badProgressionSeeds (groups := Gparam s) (q := Qparam s)
      (param_pos (s := s)).1).card ≤
      2 ^ (3 * Gparam s - 2) := by
  let b := Bparam s
  let g := Gparam s
  let q := Qparam s
  have hb : 0 < b := by simpa only [b] using (param_pos (s := s)).1
  have hq : q = 20 * s := rfl
  have h40 : 2 * q ≤ 3 * g := by
    have hg := forty_mul_le_Gparam hs
    dsimp [q, g] at hg ⊢
    omega
  have hN : b * (4 * g) = 2 ^ (3 * s - 45) := by
    simpa only [b, g] using intervalSize_param s hs
  have h3 : 3 ^ q ≤ 2 ^ (32 * s) := by
    simpa only [q] using three_pow_Qparam_le (s := s)
  have hexp :
      (3 * s - 45 + (3 * s - 45)) +
          (1 + (32 * s + (3 * g - 2 * q))) ≤ 3 * g - 2 := by
    omega
  have hc := card_badProgressionSeeds_le (groups := g) (q := q) hb
  change (badProgressionSeeds (q := q) hb).card ≤ 2 ^ (3 * g - 2)
  calc
    (badProgressionSeeds (q := q) hb).card ≤
        (b * (4 * g)) ^ 2 *
          (2 * (3 ^ q * 2 ^ (3 * g - 2 * q))) := hc
    _ ≤ (2 ^ (3 * s - 45)) ^ 2 *
          (2 * (2 ^ (32 * s) * 2 ^ (3 * g - 2 * q))) := by
      rw [hN]
      gcongr
    _ = 2 ^ ((3 * s - 45 + (3 * s - 45)) +
          (1 + (32 * s + (3 * g - 2 * q)))) := by
      rw [pow_two, ← pow_add]
      change 2 ^ (3 * s - 45 + (3 * s - 45)) *
        (2 ^ 1 * (2 ^ (32 * s) * 2 ^ (3 * g - 2 * q))) = _
      repeat' rw [← pow_add]
    _ ≤ 2 ^ (3 * g - 2) := Nat.pow_le_pow_right (by decide) hexp

lemma Rparam_le_Gparam {s : ℕ} (hs : 50 ≤ s) : Rparam s ≤ Gparam s := by
  apply Nat.pow_le_pow_right (by decide)
  omega

lemma four_mul_Gparam_le {s : ℕ} (hs : 50 ≤ s) :
    4 * Gparam s ≤ 2 ^ (2 * s) := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Gparam, ← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  omega

lemma Dparam_le_div_4096 (s : ℕ) :
    Dparam s ≤ Lparam s / 4096 := by
  exact Nat.div_le_div_left (by decide : 4096 ≤ 65536) (by decide)

lemma choose_param_le {s : ℕ} :
    (Lparam s + Dparam s).choose (Lparam s) ≤
      2 ^ (14 * (Lparam s / 4096 + 1)) := by
  have hd := Dparam_le_div_4096 s
  calc
    (Lparam s + Dparam s).choose (Lparam s) ≤
        (Lparam s + Lparam s / 4096).choose (Lparam s) := by
      apply Nat.choose_le_choose
      omega
    _ ≤ 2 ^ (14 * (Lparam s / 4096 + 1)) :=
      choose_div_4096 (Lparam s)

lemma tail_colour_power {s : ℕ} (hs : 50 ≤ s) :
    4 ^ Rparam s * 8 ^ (Gparam s - Rparam s) =
      2 ^ (3 * Gparam s - Rparam s) := by
  have hrg := Rparam_le_Gparam hs
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
    show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  omega

lemma card_badControlledSeeds_param {s : ℕ} (hs : 50 ≤ s) :
    (badSeedsFor (groups := Gparam s) (param_pos (s := s)).1
      (@controlledWaves (Rparam s) (Bparam s) (Gparam s) (Dparam s))).card ≤
        2 ^ (3 * Gparam s - 1) := by
  let b := Bparam s
  let g := Gparam s
  let r := Rparam s
  let l := Lparam s
  let d := Dparam s
  let t := l / 4096
  have hb : 0 < b := by simpa only [b] using (param_pos (s := s)).1
  have hr : 0 < r := by simpa only [r] using (param_pos (s := s)).2.2.2
  have hrl : l + 1 = r := by
    dsimp [l, r, Lparam]
    omega
  have hrg : r ≤ g := by simpa only [r, g] using Rparam_le_Gparam hs
  have h4g : 4 * g ≤ 2 ^ (2 * s) := by
    simpa only [g] using four_mul_Gparam_le hs
  have hchoose : (l + d).choose l ≤ 2 ^ (14 * (t + 1)) := by
    simpa only [l, d, t] using choose_param_le (s := s)
  have hsave : 2 * s + 14 * (t + 1) + 1 ≤ l / 160 - d := by
    simpa only [l, d, t] using profile_exponent_saving hs
  have htail : 4 ^ r * 8 ^ (g - r) = 2 ^ (3 * g - r) := by
    simpa only [r, g] using tail_colour_power hs
  have hexp :
      2 * s + (14 * (t + 1) + (l - (l / 160 - d))) +
          (1 + (3 * g - r)) ≤ 3 * g - 1 := by
    omega
  have hc := card_badSeedsFor_controlled_le (groups := g) (D := d) hb
    (show 2 ≤ r by omega)
  change (badSeedsFor hb (@controlledWaves r b g d)).card ≤ 2 ^ (3 * g - 1)
  calc
    (badSeedsFor hb (@controlledWaves r b g d)).card ≤
        ((4 * g) * (((r - 1 + d).choose (r - 1)) *
          2 ^ (r - 1 - ((r - 1) / 160 - d)))) *
            (2 * (4 ^ r * 8 ^ (g - r))) := hc
    _ = ((4 * g) * (((l + d).choose l) *
          2 ^ (l - (l / 160 - d)))) *
            (2 * (4 ^ r * 8 ^ (g - r))) := by rw [show r - 1 = l by omega]
    _ ≤ (2 ^ (2 * s) * (2 ^ (14 * (t + 1)) *
          2 ^ (l - (l / 160 - d)))) *
            (2 * (4 ^ r * 8 ^ (g - r))) := by
      gcongr
    _ = 2 ^ (2 * s + (14 * (t + 1) + (l - (l / 160 - d))) +
          (1 + (3 * g - r))) := by
      rw [htail]
      change (2 ^ (2 * s) * (2 ^ (14 * (t + 1)) *
        2 ^ (l - (l / 160 - d)))) * (2 ^ 1 * 2 ^ (3 * g - r)) = _
      repeat' rw [← pow_add]
    _ ≤ 2 ^ (3 * g - 1) := Nat.pow_le_pow_right (by decide) hexp

lemma card_seed_as_two_power (groups : ℕ) :
    Fintype.card (Seed groups) = 2 ^ (3 * groups) := by
  rw [card_seed, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]

theorem exists_goodSeed {s : ℕ} (hs : 50 ≤ s) :
    ∃ ω : Seed (Gparam s),
      @GoodProgressions (Bparam s) (Gparam s) (Qparam s)
        (param_pos (s := s)).1 ω ∧
      ω ∉ badSeedsFor (param_pos (s := s)).1
        (@controlledWaves (Rparam s) (Bparam s) (Gparam s) (Dparam s)) := by
  let hb : 0 < Bparam s := (param_pos (s := s)).1
  let A := badProgressionSeeds (groups := Gparam s) (q := Qparam s) hb
  let B := badSeedsFor hb
    (@controlledWaves (Rparam s) (Bparam s) (Gparam s) (Dparam s))
  have hA : A.card ≤ 2 ^ (3 * Gparam s - 2) := by
    simpa only [A, hb] using card_badProgressionSeeds_param hs
  have hB : B.card ≤ 2 ^ (3 * Gparam s - 1) := by
    simpa only [B, hb] using card_badControlledSeeds_param hs
  have hg : 0 < Gparam s := (param_pos (s := s)).2.1
  have hsum :
      2 ^ (3 * Gparam s - 2) + 2 ^ (3 * Gparam s - 1) <
        2 ^ (3 * Gparam s) := by
    have he1 : 3 * Gparam s - 1 = (3 * Gparam s - 2) + 1 := by omega
    have he2 : 3 * Gparam s = (3 * Gparam s - 2) + 2 := by omega
    have hp : 0 < 2 ^ (3 * Gparam s - 2) := by positivity
    rw [he1, he2, pow_succ, pow_add]
    norm_num
    omega
  have hcard : (A ∪ B).card < Fintype.card (Seed (Gparam s)) := by
    rw [card_seed_as_two_power]
    calc
      (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
      _ ≤ 2 ^ (3 * Gparam s - 2) + 2 ^ (3 * Gparam s - 1) :=
        Nat.add_le_add hA hB
      _ < 2 ^ (3 * Gparam s) := hsum
  have hexists : ∃ ω : Seed (Gparam s), ω ∉ A ∪ B := by
    by_contra hn
    push Not at hn
    have hsub : (Finset.univ : Finset (Seed (Gparam s))) ⊆ A ∪ B := by
      intro ω hω
      exact hn ω
    have hc := Finset.card_le_card hsub
    simpa only [Finset.card_univ] using (not_le_of_gt hcard hc)
  obtain ⟨ω, hω⟩ := hexists
  have hωA : ω ∉ A := fun h ↦ hω (Finset.mem_union_left B h)
  have hωB : ω ∉ B := fun h ↦ hω (Finset.mem_union_right A h)
  refine ⟨ω, ?_, ?_⟩
  · apply goodProgressions_of_not_mem_bad hb
    simpa only [A] using hωA
  · simpa only [B] using hωB

def Halfparam (s : ℕ) := 2 ^ (s - 1)

lemma polynomial_le_small_power {s : ℕ} (hs : 50 ≤ s) :
    75 * (20 * s) ^ 2 + 2 ≤ 2 ^ (s - 10) := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      have he : s + 1 - 10 = (s - 10) + 1 := by omega
      rw [he]
      conv_rhs => rw [pow_succ]
      nlinarith

lemma polynomial_le_Bparam {s : ℕ} (hs : 50 ≤ s) :
    75 * Qparam s ^ 2 + 2 ≤ Bparam s := by
  calc
    75 * Qparam s ^ 2 + 2 = 75 * (20 * s) ^ 2 + 2 := rfl
    _ ≤ 2 ^ (s - 10) := polynomial_le_small_power hs
    _ ≤ 2 ^ (s - 7) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = Bparam s := rfl

lemma param_factor_relations {s : ℕ} (hs : 50 ≤ s) :
    32 * Bparam s = Rparam s ∧
    64 * Bparam s = Halfparam s ∧
    128 * Bparam s = Kparam s := by
  constructor
  · rw [show (32 : ℕ) = 2 ^ 5 by norm_num, Bparam, Rparam, ← pow_add]
    congr 1
    omega
  constructor
  · rw [show (64 : ℕ) = 2 ^ 6 by norm_num, Bparam, Halfparam, ← pow_add]
    congr 1
    omega
  · rw [show (128 : ℕ) = 2 ^ 7 by norm_num, Bparam, Kparam, ← pow_add]
    congr 1
    omega

lemma param_wave_room {s : ℕ} (hs : 50 ≤ s) :
    6 * Bparam s + 75 * Qparam s ^ 2 + 2 + Rparam s + Halfparam s <
      Kparam s := by
  have hp := polynomial_le_Bparam hs
  obtain ⟨hr, hh, hk⟩ := param_factor_relations hs
  omega

lemma Dparam_lower {s : ℕ} (hs : 50 ≤ s) :
    2 ^ (s - 19) ≤ Dparam s := by
  rw [Dparam, Nat.le_div_iff_mul_le (by decide : 0 < 65536)]
  have he1 : s - 19 + 16 = s - 3 := by omega
  have he2 : s - 2 = (s - 3) + 1 := by omega
  rw [show (65536 : ℕ) = 2 ^ 16 by norm_num, ← pow_add, he1,
    Lparam, Rparam, he2, pow_succ]
  have hp : 0 < 2 ^ (s - 3) := by positivity
  omega

lemma interval_le_gap_product {s : ℕ} (hs : 50 ≤ s) :
    Bparam s * (4 * Gparam s) ≤
      Halfparam s * Dparam s * Bparam s := by
  have hd := Dparam_lower hs
  have hpow : 2 ^ (3 * s - 45) ≤ 2 ^ (3 * s - 27) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have he : (s - 1) + (s - 19) + (s - 7) = 3 * s - 27 := by omega
  calc
    Bparam s * (4 * Gparam s) = 2 ^ (3 * s - 45) := intervalSize_param s hs
    _ ≤ 2 ^ (3 * s - 27) := hpow
    _ = Halfparam s * 2 ^ (s - 19) * Bparam s := by
      simp only [Halfparam, Bparam]
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ Halfparam s * Dparam s * Bparam s := by gcongr

/-- A consecutive slice of a finite wave. -/
def waveSlice {k n : ℕ} (x : Fin k → Fin n) (start length : ℕ)
    (hfit : start + length ≤ k) : Fin length → Fin n :=
  fun i ↦ x ⟨start + i.val, by omega⟩

lemma waveSlice_ascending {k n : ℕ} {x : Fin k → Fin n}
    (hx : IsAscendingWave x) (start length : ℕ) (hfit : start + length ≤ k) :
    IsAscendingWave (waveSlice x start length hfit) := by
  constructor
  · intro i j hij
    apply hx.1
    simpa only [waveSlice, Fin.mk_lt_mk] using Nat.add_lt_add_left hij start
  · intro i hi
    simpa only [waveSlice, Nat.add_assoc] using hx.2 (start + i) (by omega)

lemma waveSlice_monochromatic {k n : ℕ} {c : Fin n → Bool}
    {x : Fin k → Fin n} {colour : Bool} (hmono : ∀ i, c (x i) = colour)
    (start length : ℕ) (hfit : start + length ≤ k) :
    ∀ i, c (waveSlice x start length hfit i) = colour := by
  intro i
  exact hmono _

lemma waveGap_waveSlice {k n : ℕ} (x : Fin k → Fin n)
    (start length : ℕ) (hfit : start + length ≤ k)
    (i : ℕ) (hi : i + 1 < length) :
    waveGap (waveSlice x start length hfit) i hi =
      waveGap x (start + i) (by omega) := by
  rfl

theorem exists_coloring_no_power_ascending_wave {s : ℕ} (hs : 50 ≤ s) :
    ∃ c : Fin (Bparam s * (4 * Gparam s)) → Bool,
      ¬ ∃ x : Fin (Kparam s) → Fin (Bparam s * (4 * Gparam s)),
        IsAscendingWave x ∧ Monochromatic c x := by
  let hb : 0 < Bparam s := (param_pos (s := s)).1
  obtain ⟨ω, hgood, hnotControlled⟩ := exists_goodSeed hs
  refine ⟨pointColour hb ω, ?_⟩
  rintro ⟨x, hx, colour, hmono⟩
  have hq : 0 < Qparam s := by dsimp [Qparam]; omega
  have hroom := param_wave_room hs
  have hsize :
      6 * Bparam s + 75 * Qparam s ^ 2 + 2 < Kparam s := by omega
  obtain ⟨H, hH, hHle, hlarge⟩ :=
    largeGap_of_goodProgressions hb hgood hx hmono hq hsize
  have hfit : H + Rparam s ≤ Kparam s := by omega
  let y := waveSlice x H (Rparam s) hfit
  have hy : IsAscendingWave y := waveSlice_ascending hx H (Rparam s) hfit
  have hr : 2 ≤ Rparam s := by
    have hr32 := (param_factor_relations hs).1
    have hbpos := (param_pos (s := s)).1
    omega
  have hyfirst : 4 * Bparam s ≤ waveGap y 0 (by omega) := by
    dsimp [y]
    rw [waveGap_waveSlice]
    simpa only [Nat.add_zero] using hlarge
  have hexceed :
      ∃ i : Fin (Rparam s - 1),
        Dparam s < coarseGapWord (b := Bparam s) y i := by
    by_contra hn
    have hall : ∀ i : Fin (Rparam s - 1),
        coarseGapWord (b := Bparam s) y i ≤ Dparam s := by
      intro i
      exact Nat.le_of_not_gt (fun hi ↦ hn ⟨i, hi⟩)
    have hymem : y ∈ @controlledWaves (Rparam s) (Bparam s)
        (Gparam s) (Dparam s) := by
      rw [mem_controlledWaves]
      exact ⟨hy, hr, hyfirst, hall⟩
    apply hnotControlled
    rw [badSeedsFor, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, y, hymem, colour, ?_⟩
    exact waveSlice_monochromatic hmono H (Rparam s) hfit
  obtain ⟨i, hi⟩ := hexceed
  let last : Fin (Rparam s - 1) := ⟨Rparam s - 2, by omega⟩
  have hilast : i ≤ last := by
    apply Fin.mk_le_mk.mpr
    have hi' := i.isLt
    omega
  have hlastMono := coarseGapWord_monotone (b := Bparam s) hy hilast
  have hlast :
      Dparam s < coarseGapWord (b := Bparam s) y last :=
    lt_of_lt_of_le hi hlastMono
  have hdiv : Dparam s <
      waveGap y (Rparam s - 2) (by omega) / Bparam s := by
    simpa only [coarseGapWord, coarseGap, last] using hlast
  have hgapY : Dparam s * Bparam s <
      waveGap y (Rparam s - 2) (by omega) := by
    have hmul := (Nat.mul_lt_mul_right hb).2 hdiv
    exact lt_of_lt_of_le hmul (Nat.div_mul_le_self _ _)
  let J := H + (Rparam s - 2)
  have hgap : Dparam s * Bparam s < waveGap x J (by omega) := by
    dsimp [J]
    rw [← waveGap_waveSlice x H (Rparam s) hfit (Rparam s - 2)]
    exact hgapY
  have hJroom : J + Halfparam s < Kparam s := by
    dsimp [J]
    omega
  have hreach := value_add_mul_gap_le hx J (Halfparam s) (by omega) hJroom
  have hgapUpper : Halfparam s * waveGap x J (by omega) <
      Bparam s * (4 * Gparam s) := by
    have hv := (x ⟨J + Halfparam s, hJroom⟩).isLt
    omega
  have hhalf : 0 < Halfparam s := by simp [Halfparam]
  have hproduct : Halfparam s * Dparam s * Bparam s <
      Halfparam s * waveGap x J (by omega) := by
    have hm := (Nat.mul_lt_mul_left hhalf).2 hgap
    simpa only [mul_assoc] using hm
  have hlower := interval_le_gap_product hs
  omega

theorem cubic_lower_bound_ascending (k : ℕ) (hk : 2 ^ 50 ≤ k) :
    ∃ n : ℕ, k ^ 3 ≤ 2 ^ 48 * n ∧ ¬ ForcesAscending k n := by
  let s := Nat.log 2 k
  have hk0 : k ≠ 0 := by omega
  have hs : 50 ≤ s := by
    dsimp [s]
    exact (Nat.le_log_iff_pow_le (by decide) hk0).2 hk
  have hKle : Kparam s ≤ k := by
    dsimp [Kparam, s]
    exact Nat.pow_log_le_self 2 hk0
  have hklt : k < 2 ^ (s + 1) := by
    simpa only [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1 < 2) k)
  let n := Bparam s * (4 * Gparam s)
  have hn : n = 2 ^ (3 * s - 45) := by
    simpa only [n] using intervalSize_param s hs
  have hcubic : k ^ 3 ≤ 2 ^ 48 * n := by
    have hp : k ^ 3 < (2 ^ (s + 1)) ^ 3 :=
      Nat.pow_lt_pow_left hklt (by decide)
    have he : 48 + (3 * s - 45) = (s + 1) * 3 := by omega
    rw [hn, ← pow_add, he, pow_mul]
    exact Nat.le_of_lt hp
  obtain ⟨c, hc⟩ := exists_coloring_no_power_ascending_wave hs
  refine ⟨n, hcubic, ?_⟩
  intro hforces
  obtain ⟨x, hx, hmono⟩ := hforces c
  have hKfit : 0 + Kparam s ≤ k := by omega
  let y := waveSlice x 0 (Kparam s) hKfit
  apply hc
  refine ⟨y, waveSlice_ascending hx 0 (Kparam s) hKfit, ?_⟩
  obtain ⟨colour, hcolour⟩ := hmono
  exact ⟨colour, waveSlice_monochromatic hcolour 0 (Kparam s) hKfit⟩

theorem cubic_lower_bound_descending (k : ℕ) (hk : 2 ^ 50 ≤ k) :
    ∃ n : ℕ, k ^ 3 ≤ 2 ^ 48 * n ∧ ¬ ForcesDescending k n := by
  obtain ⟨n, hn, hnot⟩ := cubic_lower_bound_ascending k hk
  refine ⟨n, hn, ?_⟩
  rwa [forcesDescending_iff_forcesAscending] 

/-! ### A deterministic cubic upper bound -/

/-- The first offset below `k` (if one exists) at which a prescribed colour
occurs; it is set to zero when the searched interval has no such point. -/
noncomputable def sameColourOffset {N : ℕ} (c : Fin N → Bool)
    (base : Bool) (k y : ℕ) : ℕ :=
  if h : ∃ j : Fin k, ∃ hj : y + j.val < N,
      c ⟨y + j.val, hj⟩ = base then
    (Classical.choose h).val
  else 0

lemma sameColourOffset_lt {N : ℕ} (c : Fin N → Bool) (base : Bool)
    {k y : ℕ} (hk : 0 < k) : sameColourOffset c base k y < k := by
  rw [sameColourOffset]
  split_ifs with h
  · exact (Classical.choose h).isLt
  · exact hk

lemma sameColourOffset_spec {N : ℕ} (c : Fin N → Bool) (base : Bool)
    {k y : ℕ} (h : ∃ j : Fin k, ∃ hj : y + j.val < N,
      c ⟨y + j.val, hj⟩ = base) :
    ∃ hj : y + sameColourOffset c base k y < N,
      c ⟨y + sameColourOffset c base k y, hj⟩ = base := by
  rw [sameColourOffset, dif_pos h]
  exact (Classical.choose_spec h)

def consecutiveWave {N k y : ℕ} (hfit : y + k ≤ N) : Fin k → Fin N :=
  fun i ↦ ⟨y + i.val, by omega⟩

lemma consecutiveWave_ascending {N k y : ℕ} (hfit : y + k ≤ N) :
    IsAscendingWave (consecutiveWave hfit) := by
  constructor
  · intro i j hij
    simp only [consecutiveWave, Fin.mk_lt_mk]
    omega
  · intro i hi
    simp only [consecutiveWave]
    omega

lemma exists_sameColourOffset_of_no_wave {N k y : ℕ} {c : Fin N → Bool}
    {base : Bool} (hfit : y + k ≤ N)
    (havoid : ¬ ∃ x : Fin k → Fin N,
      IsAscendingWave x ∧ Monochromatic c x) :
    ∃ j : Fin k, ∃ hj : y + j.val < N,
      c ⟨y + j.val, hj⟩ = base := by
  by_contra hn
  apply havoid
  let x := consecutiveWave hfit
  refine ⟨x, consecutiveWave_ascending hfit, !base, ?_⟩
  intro i
  have hne : c (x i) ≠ base := by
    intro heq
    apply hn
    refine ⟨i, ?_, ?_⟩
    · exact (x i).isLt
    · simpa only [x, consecutiveWave] using heq
  cases hci : c (x i) <;> cases base <;> simp_all

/-- `(point,gap)` after a prescribed number of greedy steps. -/
noncomputable def greedyState {N : ℕ} (c : Fin N → Bool) (base : Bool)
    (k : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | t + 1 =>
      let st := greedyState c base k t
      let o := sameColourOffset c base k (st.1 + st.2)
      (st.1 + st.2 + o, st.2 + o)

noncomputable def greedyPoint {N : ℕ} (c : Fin N → Bool)
    (base : Bool) (k t : ℕ) : ℕ := (greedyState c base k t).1

noncomputable def greedyGap {N : ℕ} (c : Fin N → Bool)
    (base : Bool) (k t : ℕ) : ℕ := (greedyState c base k t).2

@[simp] lemma greedyPoint_zero {N : ℕ} (c : Fin N → Bool) (base : Bool) (k : ℕ) :
    greedyPoint c base k 0 = 0 := rfl

@[simp] lemma greedyGap_zero {N : ℕ} (c : Fin N → Bool) (base : Bool) (k : ℕ) :
    greedyGap c base k 0 = 1 := rfl

lemma greedyPoint_succ {N : ℕ} (c : Fin N → Bool) (base : Bool) (k t : ℕ) :
    greedyPoint c base k (t + 1) =
      greedyPoint c base k t + greedyGap c base k t +
        sameColourOffset c base k
          (greedyPoint c base k t + greedyGap c base k t) := by
  rfl

lemma greedyGap_succ {N : ℕ} (c : Fin N → Bool) (base : Bool) (k t : ℕ) :
    greedyGap c base k (t + 1) = greedyGap c base k t +
      sameColourOffset c base k
        (greedyPoint c base k t + greedyGap c base k t) := by
  rfl

lemma greedyPoint_succ_eq_add_gap {N : ℕ} (c : Fin N → Bool)
    (base : Bool) (k t : ℕ) :
    greedyPoint c base k (t + 1) =
      greedyPoint c base k t + greedyGap c base k (t + 1) := by
  rw [greedyPoint_succ, greedyGap_succ]
  omega

lemma greedy_bounds {N : ℕ} (c : Fin N → Bool) (base : Bool)
    {k : ℕ} (hk : 0 < k) (t : ℕ) :
    greedyGap c base k t ≤ 1 + t * k ∧
      greedyPoint c base k t ≤ t * (1 + t * k) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have ho := sameColourOffset_lt c base (y :=
        greedyPoint c base k t + greedyGap c base k t) hk
      rw [greedyGap_succ, greedyPoint_succ]
      constructor <;> nlinarith

lemma greedyGap_pos {N : ℕ} (c : Fin N → Bool) (base : Bool)
    (k t : ℕ) : 0 < greedyGap c base k t := by
  induction t with
  | zero => simp
  | succ t ih => rw [greedyGap_succ]; omega

lemma greedyGap_monotone {N : ℕ} (c : Fin N → Bool) (base : Bool)
    (k t : ℕ) : greedyGap c base k t ≤ greedyGap c base k (t + 1) := by
  rw [greedyGap_succ]
  omega

lemma le_cube {k : ℕ} (hk : 1 ≤ k) : k ≤ k ^ 3 := by
  have hsq : 1 ≤ k * k := by nlinarith
  calc
    k = k * 1 := by omega
    _ ≤ k * (k * k) := Nat.mul_le_mul_left k hsq
    _ = k ^ 3 := by ring

lemma sq_le_cube {k : ℕ} (hk : 1 ≤ k) : k * k ≤ k ^ 3 := by
  calc
    k * k = k * k * 1 := by omega
    _ ≤ k * k * k := Nat.mul_le_mul_left (k * k) hk
    _ = k ^ 3 := by ring

lemma greedyPoint_lt_cubicUniverse {k t : ℕ} (hk : 2 ≤ k) (ht : t < k)
    (c : Fin (8 * k ^ 3 + 1) → Bool) (base : Bool) :
    greedyPoint c base k t < 8 * k ^ 3 + 1 := by
  have hb := (greedy_bounds c base (k := k) (by omega) t).2
  have hmono : t * (1 + t * k) ≤ k * (1 + k * k) := by gcongr
  have hc := le_cube (show 1 ≤ k by omega)
  have hk2 := sq_le_cube (show 1 ≤ k by omega)
  have hcoarse : k * (1 + k * k) ≤ 2 * k ^ 3 := by
    nlinarith
  omega

lemma greedySearch_fits {k t : ℕ} (hk : 2 ≤ k) (ht : t + 1 < k)
    (c : Fin (8 * k ^ 3 + 1) → Bool) (base : Bool) :
    greedyPoint c base k t + greedyGap c base k t + k ≤
      8 * k ^ 3 + 1 := by
  obtain ⟨hd, ha⟩ := greedy_bounds c base (k := k) (by omega) t
  have ht' : t < k := by omega
  have hmono : t * (1 + t * k) ≤ k * (1 + k * k) := by gcongr
  have hdmono : 1 + t * k ≤ 1 + k * k := by gcongr
  have hc := le_cube (show 1 ≤ k by omega)
  have hk2 := sq_le_cube (show 1 ≤ k by omega)
  have ha' : greedyPoint c base k t ≤ 2 * k ^ 3 := by
    nlinarith
  have hd' : greedyGap c base k t ≤ k ^ 3 + 1 := by omega
  omega

lemma greedyPoint_strictMono {N k : ℕ} (c : Fin N → Bool) (base : Bool) :
    StrictMono (greedyPoint c base k) := by
  apply strictMono_nat_of_lt_succ
  intro t
  rw [greedyPoint_succ_eq_add_gap]
  exact Nat.lt_add_of_pos_right (greedyGap_pos c base k (t + 1))

lemma greedyPoint_colour {k t : ℕ} (hk : 2 ≤ k) (ht : t < k)
    (c : Fin (8 * k ^ 3 + 1) → Bool) (base : Bool)
    (hzero : c ⟨0, by omega⟩ = base)
    (havoid : ¬ ∃ x : Fin k → Fin (8 * k ^ 3 + 1),
      IsAscendingWave x ∧ Monochromatic c x) :
    c ⟨greedyPoint c base k t,
      greedyPoint_lt_cubicUniverse hk ht c base⟩ = base := by
  cases t with
  | zero => simpa using hzero
  | succ t =>
      have ht' : t + 1 < k := by omega
      have hfit := greedySearch_fits hk ht' c base
      have hexists := exists_sameColourOffset_of_no_wave (base := base) hfit havoid
      obtain ⟨hj, hspec⟩ := sameColourOffset_spec c base hexists
      simpa only [greedyPoint_succ] using hspec

theorem forcesAscending_cubic (k : ℕ) (hk : 2 ≤ k) :
    ForcesAscending k (8 * k ^ 3 + 1) := by
  intro c
  by_contra havoid
  let base : Bool := c ⟨0, by omega⟩
  let x : Fin k → Fin (8 * k ^ 3 + 1) := fun i ↦
    ⟨greedyPoint c base k i.val,
      greedyPoint_lt_cubicUniverse hk i.isLt c base⟩
  have hx : IsAscendingWave x := by
    constructor
    · intro i j hij
      change greedyPoint c base k i.val < greedyPoint c base k j.val
      exact greedyPoint_strictMono c base hij
    · intro i hi
      have h0 := greedyPoint_succ_eq_add_gap c base k i
      have h1 := greedyPoint_succ_eq_add_gap c base k (i + 1)
      have hg := greedyGap_monotone c base k (i + 1)
      change 2 * greedyPoint c base k (i + 1) ≤
        greedyPoint c base k i + greedyPoint c base k (i + 2)
      rw [show i + 2 = (i + 1) + 1 by omega, h1, h0]
      omega
  have hmono : Monochromatic c x := by
    refine ⟨base, ?_⟩
    intro i
    dsimp [x]
    exact greedyPoint_colour hk i.isLt c base rfl havoid
  exact havoid ⟨x, hx, hmono⟩

theorem forcesDescending_cubic (k : ℕ) (hk : 2 ≤ k) :
    ForcesDescending k (8 * k ^ 3 + 1) := by
  rw [forcesDescending_iff_forcesAscending]
  exact forcesAscending_cubic k hk

lemma forcesDescending_zero : ForcesDescending 0 0 := by
  intro c
  let x : Fin 0 → Fin 0 := fun i ↦ Fin.elim0 i
  refine ⟨x, ?_, ?_⟩
  · constructor
    · intro i
      exact Fin.elim0 i
    · intro i hi
      omega
  · exact ⟨false, fun i ↦ Fin.elim0 i⟩

lemma forcesDescending_one : ForcesDescending 1 1 := by
  intro c
  let x : Fin 1 → Fin 1 := fun i ↦ i
  refine ⟨x, ?_, ?_⟩
  · constructor
    · intro i j hij
      exact hij
    · intro i hi
      omega
  · exact ⟨c 0, fun i ↦ by fin_cases i; rfl⟩

theorem exists_forcing_descending (k : ℕ) : ∃ n, ForcesDescending k n := by
  by_cases hk : 2 ≤ k
  · exact ⟨8 * k ^ 3 + 1, forcesDescending_cubic k hk⟩
  · have hsmall : k = 0 ∨ k = 1 := by omega
    rcases hsmall with rfl | rfl
    · exact ⟨0, forcesDescending_zero⟩
    · exact ⟨1, forcesDescending_one⟩

/-- The exact Ramsey number in Problem 781: the least interval size forcing
a monochromatic descending wave of length `k`. -/
noncomputable def waveRamsey (k : ℕ) : ℕ :=
  sInf {n : ℕ | ForcesDescending k n}

theorem waveRamsey_spec (k : ℕ) : ForcesDescending k (waveRamsey k) := by
  exact csInf_mem (exists_forcing_descending k)

theorem waveRamsey_minimal {k n : ℕ} (h : ForcesDescending k n) :
    waveRamsey k ≤ n := by
  exact csInf_le' h

lemma forcesDescending_mono_interval {k m n : ℕ} (hmn : m ≤ n)
    (h : ForcesDescending k m) : ForcesDescending k n := by
  intro c
  obtain ⟨x, hx, colour, hmono⟩ := h (fun i ↦ c (Fin.castLE hmn i))
  let y : Fin k → Fin n := fun i ↦ Fin.castLE hmn (x i)
  refine ⟨y, ?_, colour, ?_⟩
  · constructor
    · intro i j hij
      change (x i).val < (x j).val
      exact hx.1 hij
    · intro i hi
      change (x ⟨i, by omega⟩).val + (x ⟨i + 2, hi⟩).val ≤
        2 * (x ⟨i + 1, by omega⟩).val
      exact hx.2 i hi
  · intro i
    exact hmono i

theorem waveRamsey_cubic_lower (k : ℕ) (hk : 2 ^ 50 ≤ k) :
    k ^ 3 ≤ 2 ^ 48 * waveRamsey k := by
  obtain ⟨n, hkn, hn⟩ := cubic_lower_bound_descending k hk
  have hnf : n ≤ waveRamsey k := by
    by_contra hnot
    have hfn : waveRamsey k ≤ n := by omega
    exact hn (forcesDescending_mono_interval hfn (waveRamsey_spec k))
  exact hkn.trans (Nat.mul_le_mul_left (2 ^ 48) hnf)

theorem waveRamsey_cubic_upper (k : ℕ) (hk : 2 ≤ k) :
    waveRamsey k ≤ 8 * k ^ 3 + 1 :=
  waveRamsey_minimal (forcesDescending_cubic k hk)

/-- Resolution of Erdős Problem 781.  The first conjunct is an explicit
two-sided cubic estimate for the exact minimal number.  The second conjunct
disproves the proposed quadratic formula. -/
theorem erdos_781 :
    (∀ k : ℕ, 2 ^ 50 ≤ k →
      k ^ 3 ≤ 2 ^ 48 * waveRamsey k ∧
        waveRamsey k ≤ 8 * k ^ 3 + 1) ∧
    ¬ (∀ k : ℕ, waveRamsey k = k ^ 2 - k + 1) := by
  constructor
  · intro k hk
    exact ⟨waveRamsey_cubic_lower k hk,
      waveRamsey_cubic_upper k (by omega)⟩
  · intro hquadratic
    have hlower := waveRamsey_cubic_lower (2 ^ 50) (by omega)
    rw [hquadratic (2 ^ 50)] at hlower
    have hstrict :
        2 ^ 48 * ((2 ^ 50) ^ 2 - 2 ^ 50 + 1) < (2 ^ 50) ^ 3 := by
      norm_num
    omega

#print axioms erdos_781

end GoodProgressions

end Erdos781
