/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
MIT License

Copyright (c) 2026 Axiom Math.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

This file has been modified for Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 403.
Informal argument: AxiomProver; the historical result is due to Frankl and Lin.
Formal proof: AxiomProver, published by Axiom Math.
Source: https://www.erdosproblems.com/forum/thread/403#post-7067
https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos403/solution.lean
Original Lean/Mathlib version: 4.27.0.
-/
import Mathlib

set_option linter.mathlibStandardSet false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos403

/-
# Problem Description

Erdos Problem 403: Characterize all solutions to the equation
$2^m = a_1! + a_2! + \cdots + a_k!$
where $m \geq 0$, $k \geq 1$, and $1 \leq a_1 < a_2 < \cdots < a_k$ are strictly
increasing positive integers.

The complete list of solutions is:
1. $2^0 = 1!$
2. $2^1 = 2!$
3. $2^3 = 2! + 3!$
4. $2^5 = 2! + 3! + 4!$
5. $2^7 = 2! + 3! + 5!$
-/

def IsErdos403Solution (m : ℕ) (s : Finset ℕ) : Prop :=
  s.Nonempty ∧ (∀ a ∈ s, 1 ≤ a) ∧ 2 ^ m = s.sum Nat.factorial

lemma erdos403_backward (m : ℕ) (s : Finset ℕ) :
    (m = 0 ∧ s = {1}) ∨
    (m = 1 ∧ s = {2}) ∨
    (m = 3 ∧ s = {2, 3}) ∨
    (m = 5 ∧ s = {2, 3, 4}) ∨
    (m = 7 ∧ s = {2, 3, 5}) →
    IsErdos403Solution m s := by
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
  refine ⟨by simp, fun a ha => ?_, by decide⟩ <;>
  simp [Finset.mem_insert, Finset.mem_singleton] at ha <;>
  omega

lemma three_dvd_sum_factorial (s : Finset ℕ) (hs : ∀ a ∈ s, 3 ≤ a) :
    3 ∣ s.sum Nat.factorial := by
  apply Finset.dvd_sum
  intro a ha
  exact Nat.Prime.dvd_factorial Nat.prime_three |>.mpr (hs a ha)

lemma min_le_two (m : ℕ) (s : Finset ℕ)
    (hne : s.Nonempty) (hsum : 2 ^ m = s.sum Nat.factorial) :
    s.min' hne ≤ 2 := by
  by_contra h
  push Not at h
  have h3 : ∀ a ∈ s, 3 ≤ a := by
    intro a ha
    have := Finset.min'_le s a ha
    omega
  have hdvd : 3 ∣ s.sum Nat.factorial := three_dvd_sum_factorial s h3
  rw [← hsum] at hdvd
  have hprime3 : Nat.Prime 3 := by decide
  have : ¬ 3 ∣ 2 ^ m := by
    intro h3dvd
    have := (Nat.Prime.dvd_of_dvd_pow hprime3 h3dvd)
    omega
  exact this hdvd

lemma one_mem_case (m : ℕ) (s : Finset ℕ)
    (hpos : ∀ a ∈ s, 1 ≤ a) (hsum : 2 ^ m = s.sum Nat.factorial)
    (h1 : 1 ∈ s) :
    m = 0 ∧ s = {1} := by
  have hsplit : s.sum Nat.factorial = 1 + (s.erase 1).sum Nat.factorial := by
    rw [← Finset.add_sum_erase s Nat.factorial h1]; simp
  have hrest_even : 2 ∣ (s.erase 1).sum Nat.factorial := by
    apply Finset.dvd_sum; intro a ha
    have ha_ge : 2 ≤ a := by
      have := hpos a (Finset.mem_erase.mp ha).2
      have := (Finset.mem_erase.mp ha).1; omega
    exact (Nat.Prime.dvd_factorial (by decide : Nat.Prime 2)).mpr ha_ge
  obtain ⟨k, hk⟩ := hrest_even
  have hsum2 : 2 ^ m = 1 + 2 * k := by omega
  have hm0 : m = 0 := by
    by_contra hm; have : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega : m ≠ 0); omega
  subst hm0; simp at hsum2
  have hrest0 : (s.erase 1).sum Nat.factorial = 0 := by omega
  constructor
  · rfl
  · have hempty : s.erase 1 = ∅ := by
      by_contra hne_erase
      have hne' : (s.erase 1).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne_erase
      linarith [Finset.sum_pos (fun a (_ : a ∈ s.erase 1) => Nat.factorial_pos a) hne']
    ext a; simp only [Finset.mem_singleton]; constructor
    · intro ha; by_contra hne1
      have := hempty ▸ (Finset.mem_erase.mpr ⟨hne1, ha⟩); simp at this
    · rintro rfl; exact h1

lemma two_singleton_case (m : ℕ) (hsum : 2 ^ m = ({2} : Finset ℕ).sum Nat.factorial) :
    m = 1 := by
  simp at hsum
  have : 2 ^ m = 2 ^ 1 := by linarith
  exact Nat.pow_right_injective (by omega) this

lemma must_contain_three (m : ℕ) (s : Finset ℕ)
    (hpos : ∀ a ∈ s, 1 ≤ a) (hsum : 2 ^ m = s.sum Nat.factorial)
    (h2 : 2 ∈ s) (h1 : 1 ∉ s) (hcard : 1 < s.card) :
    3 ∈ s := by
  by_contra h3
  set t := s.erase 2
  have ht_ne : t.Nonempty := by
    rw [Finset.one_lt_card] at hcard
    obtain ⟨a, ha, b, hb, hab⟩ := hcard
    by_cases ha2 : a = 2
    · subst ha2; exact ⟨b, Finset.mem_erase.mpr ⟨hab.symm, hb⟩⟩
    · exact ⟨a, Finset.mem_erase.mpr ⟨ha2, ha⟩⟩
  have ht_ge : ∀ a ∈ t, 4 ≤ a := by
    intro a ha
    have ha_ne2 : a ≠ 2 := (Finset.mem_erase.mp ha).1
    have ha_mem : a ∈ s := (Finset.mem_erase.mp ha).2
    have ha_ne1 : a ≠ 1 := fun h => h1 (h ▸ ha_mem)
    have ha_ne3 : a ≠ 3 := fun h => h3 (h ▸ ha_mem)
    have := hpos a ha_mem; omega
  have h8dvd : 8 ∣ t.sum Nat.factorial := by
    apply Finset.dvd_sum; intro a ha
    exact dvd_trans (by decide : 8 ∣ (4 : ℕ).factorial) (Nat.factorial_dvd_factorial (ht_ge a ha))
  have hsplit : s.sum Nat.factorial = 2 + t.sum Nat.factorial := by
    have h := Finset.add_sum_erase s Nat.factorial h2
    have : Nat.factorial 2 = 2 := by decide
    linarith
  obtain ⟨k, hk⟩ := h8dvd
  have hsum2 : 2 ^ m = 2 + 8 * k := by omega
  have hm1 : m = 1 := by
    have hm_lt : m < 3 := by
      by_contra hle; push Not at hle
      have : (2 : ℕ) ^ 3 ∣ 2 ^ m := Nat.pow_dvd_pow 2 hle
      simp at this; omega
    interval_cases m <;> omega
  subst hm1
  linarith [Finset.sum_pos (fun a (_ : a ∈ t) => Nat.factorial_pos a) ht_ne]

private lemma pow2_mod_1008_mem (m : ℕ) :
    2 ^ m % 1008 ∈ ({1, 2, 4, 8, 16, 32, 64, 128, 256, 512} : Finset ℕ) := by
  induction m with
  | zero => decide
  | succ n ih =>
    have key : 2 ^ (n + 1) % 1008 = ((2 ^ n % 1008) * 2) % 1008 := by
      rw [pow_succ, Nat.mul_mod]
    rw [key]
    simp only [Finset.mem_insert, Finset.mem_singleton] at ih ⊢
    omega

private lemma dvd_1008_factorial (n : ℕ) (hn : 7 ≤ n) :
    1008 ∣ n.factorial :=
  dvd_trans (by decide : 1008 ∣ (7 : ℕ).factorial) (Nat.factorial_dvd_factorial hn)

private lemma sum_factorial_subset_45 (s : Finset ℕ) (hs : s ⊆ {4, 5}) :
    s.sum Nat.factorial ∈ ({0, 24, 120, 144} : Finset ℕ) := by
  have hsub : ∀ a ∈ s, a = 4 ∨ a = 5 := by
    intro a ha; have := hs ha; simp at this; exact this
  by_cases h4 : 4 ∈ s <;> by_cases h5 : 5 ∈ s
  · have : s = {4, 5} := by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor
      · intro ha; exact hsub a ha
      · rintro (rfl | rfl) <;> assumption
    rw [this]; decide
  · have : s = {4} := by
      ext a; simp only [Finset.mem_singleton]; constructor
      · intro ha
        rcases hsub a ha with rfl | rfl
        · rfl
        · exact absurd ha h5
      · rintro rfl; exact h4
    rw [this]; decide
  · have : s = {5} := by
      ext a; simp only [Finset.mem_singleton]; constructor
      · intro ha
        rcases hsub a ha with rfl | rfl
        · exact absurd ha h4
        · rfl
      · rintro rfl; exact h5
    rw [this]; decide
  · have hemp : s = ∅ := by
      ext a; constructor
      · intro ha; rcases hsub a ha with rfl | rfl <;> contradiction
      · intro ha; exact absurd ha (Finset.notMem_empty a)
    rw [hemp]; simp

lemma six_not_mem (m : ℕ) (s : Finset ℕ)
    (hpos : ∀ a ∈ s, 1 ≤ a) (hsum : 2 ^ m = s.sum Nat.factorial)
    (h2 : 2 ∈ s) (h1 : 1 ∉ s) (h3 : 3 ∈ s) :
    6 ∉ s := by
  intro h6
  have h3e : 3 ∈ s.erase 2 := Finset.mem_erase.mpr ⟨by omega, h3⟩
  have h6e : 6 ∈ (s.erase 2).erase 3 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega, h6⟩⟩
  set t := ((s.erase 2).erase 3).erase 6
  have hsum_eq : s.sum Nat.factorial = 728 + t.sum Nat.factorial := by
    have hsplit := Finset.add_sum_erase s Nat.factorial h2
    have hsplit2 := Finset.add_sum_erase (s.erase 2) Nat.factorial h3e
    have hsplit3 := Finset.add_sum_erase ((s.erase 2).erase 3) Nat.factorial h6e
    have h2f : Nat.factorial 2 = 2 := by decide
    have h3f : Nat.factorial 3 = 6 := by decide
    have h6f : Nat.factorial 6 = 720 := by decide
    linarith
  have ht_range : ∀ a ∈ t, a = 4 ∨ a = 5 ∨ 7 ≤ a := by
    intro a ha
    have h₁ := Finset.mem_erase.mp ha
    have h₂ := Finset.mem_erase.mp h₁.2
    have h₃ := Finset.mem_erase.mp h₂.2
    have ha_s := h₃.2
    have ha2 := h₃.1
    have ha3 := h₂.1
    have ha6 := h₁.1
    have ha1 : a ≠ 1 := fun heq => h1 (heq ▸ ha_s)
    have hage := hpos a ha_s
    omega
  have h1008_dvd : 1008 ∣ (t.filter (· ≥ 7)).sum Nat.factorial := by
    apply Finset.dvd_sum; intro a ha
    exact dvd_1008_factorial a (by simp [Finset.mem_filter] at ha; exact ha.2)
  have ht_small_sub : t.filter (· < 7) ⊆ {4, 5} := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    have := ht_range a ha.1
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have ht_split : t.sum Nat.factorial =
      (t.filter (· < 7)).sum Nat.factorial + (t.filter (· ≥ 7)).sum Nat.factorial := by
    rw [← Finset.sum_filter_add_sum_filter_not t (· < 7)]
    congr 1
    exact Finset.sum_congr (Finset.filter_congr (fun a _ => by omega)) (fun _ _ => rfl)
  obtain ⟨k, hk⟩ := h1008_dvd
  have hmod_eq : (s.sum Nat.factorial) % 1008 =
      (728 + (t.filter (· < 7)).sum Nat.factorial) % 1008 := by
    rw [hsum_eq, ht_split, hk]; omega
  have hsmall := sum_factorial_subset_45 _ ht_small_sub
  have hsum_mod : s.sum Nat.factorial % 1008 ∈ ({728, 752, 848, 872} : Finset ℕ) := by
    rw [hmod_eq]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsmall ⊢; omega
  have hpow_mod : 2 ^ m % 1008 ∈ ({728, 752, 848, 872} : Finset ℕ) := by
    rw [hsum]; exact hsum_mod
  have hpow_mem := pow2_mod_1008_mem m
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpow_mod hpow_mem; omega

private lemma mod32_contra (base rest : ℕ) (h1 : 32 ∣ base + rest) (h2 : 32 ∣ rest)
    (h3 : base % 32 ≠ 0) : False := by
  obtain ⟨a, ha⟩ := h2; obtain ⟨b, hb⟩ := h1; omega

lemma seven_not_mem (m : ℕ) (s : Finset ℕ)
    (hpos : ∀ a ∈ s, 1 ≤ a) (hsum : 2 ^ m = s.sum Nat.factorial)
    (h2 : 2 ∈ s) (h1 : 1 ∉ s) (h3 : 3 ∈ s) (h6 : 6 ∉ s) :
    7 ∉ s := by
  intro h7
  have h3e : 3 ∈ s.erase 7 := Finset.mem_erase.mpr ⟨by omega, h3⟩
  have h2e : 2 ∈ (s.erase 7).erase 3 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega, h2⟩⟩
  have h7s := Finset.add_sum_erase s Nat.factorial h7
  have h3s := Finset.add_sum_erase (s.erase 7) Nat.factorial h3e
  have h2s := Finset.add_sum_erase ((s.erase 7).erase 3) Nat.factorial h2e
  set t := ((s.erase 7).erase 3).erase 2 with ht_def
  have hf7 : Nat.factorial 7 = 5040 := by decide
  have hf3 : Nat.factorial 3 = 6 := by decide
  have hf2 : Nat.factorial 2 = 2 := by decide
  have htotal : s.sum Nat.factorial = 5048 + t.sum Nat.factorial := by
    rw [ht_def]; linarith
  have ht_mem_s : ∀ a ∈ t, a ∈ s := by
    intro a ha; rw [ht_def] at ha
    exact (Finset.mem_erase.mp ((Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).2)).2
  have ht_ne : ∀ a ∈ t, a ≠ 2 ∧ a ≠ 3 ∧ a ≠ 7 := by
    intro a ha; rw [ht_def] at ha
    exact ⟨(Finset.mem_erase.mp ha).1,
           (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1,
           (Finset.mem_erase.mp ((Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).2)).1⟩
  have ht_cases : ∀ a ∈ t, a = 4 ∨ a = 5 ∨ 8 ≤ a := by
    intro a ha
    have hs := ht_mem_s a ha
    have ⟨h2a, h3a, h7a⟩ := ht_ne a ha
    have h1a : a ≠ 1 := fun h => h1 (h ▸ hs)
    have h6a : a ≠ 6 := fun h => h6 (h ▸ hs)
    have := hpos a hs; omega
  have h32_ge8 : ∀ a, 8 ≤ a → 32 ∣ a.factorial :=
    fun a ha => dvd_trans (by decide : (32 : ℕ) ∣ Nat.factorial 8) (Nat.factorial_dvd_factorial ha)
  have hm_ge : 13 ≤ m := by
    by_contra hlt; push Not at hlt
    have := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) (show m ≤ 12 by omega)
    norm_num at this; omega
  have h32_total : 32 ∣ s.sum Nat.factorial := by
    rw [← hsum]; change 2 ^ 5 ∣ 2 ^ m; exact Nat.pow_dvd_pow 2 (by omega)
  have hge8_of_not45 : ∀ a ∈ t, a ≠ 4 → a ≠ 5 → 8 ≤ a := by
    intro a ha h4a h5a
    rcases ht_cases a ha with rfl | rfl | h
    · exact absurd rfl h4a
    · exact absurd rfl h5a
    · exact h
  have mem_erase_t4 : ∀ a, a ∈ t.erase 4 → a ∈ t ∧ a ≠ 4 := fun a ha =>
    ⟨(Finset.mem_erase.mp ha).2, (Finset.mem_erase.mp ha).1⟩
  have mem_erase_t5 : ∀ a, a ∈ t.erase 5 → a ∈ t ∧ a ≠ 5 := fun a ha =>
    ⟨(Finset.mem_erase.mp ha).2, (Finset.mem_erase.mp ha).1⟩
  have mem_erase_t45 : ∀ a, a ∈ (t.erase 4).erase 5 → a ∈ t ∧ a ≠ 4 ∧ a ≠ 5 := by
    intro a ha
    have h1 := Finset.mem_erase.mp ha
    have h2 := Finset.mem_erase.mp h1.2
    exact ⟨h2.2, h2.1, h1.1⟩
  by_cases h4 : 4 ∈ t <;> by_cases h5 : 5 ∈ t
  · -- Both 4 and 5
    have h4s := Finset.add_sum_erase t Nat.factorial h4
    have h5e : 5 ∈ t.erase 4 := Finset.mem_erase.mpr ⟨by omega, h5⟩
    have h5s := Finset.add_sum_erase (t.erase 4) Nat.factorial h5e
    have hf4 : Nat.factorial 4 = 24 := by decide
    have hf5 : Nat.factorial 5 = 120 := by decide
    have hu_ge8 : ∀ a ∈ (t.erase 4).erase 5, 8 ≤ a := by
      intro a ha
      have ⟨hat, h4a, h5a⟩ := mem_erase_t45 a ha
      exact hge8_of_not45 a hat h4a h5a
    have h32u : 32 ∣ ((t.erase 4).erase 5).sum Nat.factorial :=
      Finset.dvd_sum (fun a ha => h32_ge8 a (hu_ge8 a ha))
    have : s.sum Nat.factorial = 5192 + ((t.erase 4).erase 5).sum Nat.factorial := by
      linarith
    exact mod32_contra 5192 _ (this ▸ h32_total) h32u (by decide)
  · -- 4 yes, 5 no
    have h4s := Finset.add_sum_erase t Nat.factorial h4
    have hf4 : Nat.factorial 4 = 24 := by decide
    have hu_ge8 : ∀ a ∈ t.erase 4, 8 ≤ a := by
      intro a ha
      have ⟨hat, h4a⟩ := mem_erase_t4 a ha
      have h5a : a ≠ 5 := fun heq => h5 (heq ▸ hat)
      exact hge8_of_not45 a hat h4a h5a
    have h32u : 32 ∣ (t.erase 4).sum Nat.factorial :=
      Finset.dvd_sum (fun a ha => h32_ge8 a (hu_ge8 a ha))
    have : s.sum Nat.factorial = 5072 + (t.erase 4).sum Nat.factorial := by linarith
    exact mod32_contra 5072 _ (this ▸ h32_total) h32u (by decide)
  · -- 4 no, 5 yes
    have h5s := Finset.add_sum_erase t Nat.factorial h5
    have hf5 : Nat.factorial 5 = 120 := by decide
    have hu_ge8 : ∀ a ∈ t.erase 5, 8 ≤ a := by
      intro a ha
      have ⟨hat, h5a⟩ := mem_erase_t5 a ha
      have h4a : a ≠ 4 := fun heq => h4 (heq ▸ hat)
      exact hge8_of_not45 a hat h4a h5a
    have h32u : 32 ∣ (t.erase 5).sum Nat.factorial :=
      Finset.dvd_sum (fun a ha => h32_ge8 a (hu_ge8 a ha))
    have : s.sum Nat.factorial = 5168 + (t.erase 5).sum Nat.factorial := by linarith
    exact mod32_contra 5168 _ (this ▸ h32_total) h32u (by decide)
  · -- Neither
    have hu_ge8 : ∀ a ∈ t, 8 ≤ a := by
      intro a ha
      exact hge8_of_not45 a ha (fun h => h4 (h ▸ ha)) (fun h => h5 (h ▸ ha))
    have h32u : 32 ∣ t.sum Nat.factorial :=
      Finset.dvd_sum (fun a ha => h32_ge8 a (hu_ge8 a ha))
    exact mod32_contra 5048 _ (htotal ▸ h32_total) h32u (by decide)

lemma dvd_1024_factorial (n : ℕ) (hn : 12 ≤ n) :
    1024 ∣ n.factorial := by
  have h12 : 1024 ∣ (12 : ℕ).factorial := by decide
  exact dvd_trans h12 (Nat.factorial_dvd_factorial hn)

lemma dvd_1024_sum_large (s : Finset ℕ) (hs : ∀ a ∈ s, 12 ≤ a) :
    1024 ∣ s.sum Nat.factorial := by
  apply Finset.dvd_sum
  intro a ha
  exact dvd_1024_factorial a (hs a ha)

set_option maxRecDepth 4096 in
lemma no_element_ge_eight_aux (m : ℕ) (s : Finset ℕ)
    (hpos : ∀ a ∈ s, 1 ≤ a)
    (hsum : 2 ^ m = s.sum Nat.factorial)
    (h2 : 2 ∈ s) (h1 : 1 ∉ s) (h3 : 3 ∈ s)
    (h6 : 6 ∉ s) (h7 : 7 ∉ s)
    (hlarge : ∃ a ∈ s, 8 ≤ a) : False := by
  obtain ⟨a₀, ha₀_mem, ha₀_ge⟩ := hlarge
  have ha₀_ne2 : a₀ ≠ 2 := by omega
  have ha₀_ne3 : a₀ ≠ 3 := by omega
  have hsub : {2, 3, a₀} ⊆ s := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h8fact : Nat.factorial 8 ≤ Nat.factorial a₀ := Nat.factorial_le (by omega)
  have htotal_lb : 40328 ≤ s.sum Nat.factorial := by
    have hge : ({2, 3, a₀} : Finset ℕ).sum Nat.factorial ≥ 40328 := by
      simp only [Finset.sum_insert (show 2 ∉ ({3, a₀} : Finset ℕ) by simp; omega),
                 Finset.sum_insert (show 3 ∉ ({a₀} : Finset ℕ) by simp; omega),
                 Finset.sum_singleton]
      have : Nat.factorial 8 = 40320 := by decide
      have : Nat.factorial 2 = 2 := by decide
      have : Nat.factorial 3 = 6 := by decide
      omega
    calc s.sum Nat.factorial
        ≥ ({2, 3, a₀} : Finset ℕ).sum Nat.factorial :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      _ ≥ 40328 := hge
  have hm_ge : 16 ≤ m := by
    by_contra hlt; push Not at hlt
    have : 2 ^ m ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hpow_dvd : 1024 ∣ 2 ^ m := by
    change 2 ^ 10 ∣ 2 ^ m; exact Nat.pow_dvd_pow 2 (by omega)
  have htotal_dvd : 1024 ∣ s.sum Nat.factorial := hsum ▸ hpow_dvd
  set small := s.filter (fun a => a ∈ ({2, 3, 4, 5, 8, 9, 10, 11} : Finset ℕ)) with hsmall_def
  set large := s.filter (fun a => a ∉ ({2, 3, 4, 5, 8, 9, 10, 11} : Finset ℕ)) with hlarge_def
  have hdecomp : s.sum Nat.factorial = small.sum Nat.factorial + large.sum Nat.factorial := by
    rw [hsmall_def, hlarge_def]
    exact (Finset.sum_filter_add_sum_filter_not s
      (fun a => a ∈ ({2, 3, 4, 5, 8, 9, 10, 11} : Finset ℕ)) Nat.factorial).symm
  have hlarge_ge12 : ∀ a ∈ large, 12 ≤ a := by
    intro a ha
    simp only [hlarge_def, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at ha
    have ha_mem := ha.1
    have ha_not := ha.2
    push Not at ha_not
    have := hpos a ha_mem
    have ha1 : a ≠ 1 := fun h => h1 (h ▸ ha_mem)
    have ha6 : a ≠ 6 := fun h => h6 (h ▸ ha_mem)
    have ha7 : a ≠ 7 := fun h => h7 (h ▸ ha_mem)
    omega
  have hlarge_dvd : 1024 ∣ large.sum Nat.factorial := dvd_1024_sum_large large hlarge_ge12
  have hsmall_dvd : 1024 ∣ small.sum Nat.factorial := by
    rw [hdecomp] at htotal_dvd
    have := hlarge_dvd
    omega
  have hsmall_sub : small ⊆ {2, 3, 4, 5, 8, 9, 10, 11} := by
    intro a ha; simp only [hsmall_def, Finset.mem_filter] at ha; exact ha.2
  have h2_small : 2 ∈ small := by
    simp only [hsmall_def, Finset.mem_filter]; exact ⟨h2, by simp⟩
  have h3_small : 3 ∈ small := by
    simp only [hsmall_def, Finset.mem_filter]; exact ⟨h3, by simp⟩
  have hfinite : ∀ t ∈ ({2, 3, 4, 5, 8, 9, 10, 11} : Finset ℕ).powerset,
      2 ∈ t → 3 ∈ t → t.sum Nat.factorial % 1024 ≠ 0 := by decide
  have hsmall_ps : small ∈ ({2, 3, 4, 5, 8, 9, 10, 11} : Finset ℕ).powerset :=
    Finset.mem_powerset.mpr hsmall_sub
  have hne0 := hfinite small hsmall_ps h2_small h3_small
  exact hne0 (Nat.mod_eq_zero_of_dvd hsmall_dvd)

lemma no_element_ge_eight (m : ℕ) (s : Finset ℕ)
    (hpos : ∀ a ∈ s, 1 ≤ a) (hsum : 2 ^ m = s.sum Nat.factorial)
    (h2 : 2 ∈ s) (h1 : 1 ∉ s) (h3 : 3 ∈ s) (h6 : 6 ∉ s) (h7 : 7 ∉ s) :
    ∀ a ∈ s, a < 8 := by
  by_contra h
  push Not at h
  obtain ⟨a, ha_mem, ha_ge⟩ := h
  exact no_element_ge_eight_aux m s hpos hsum h2 h1 h3 h6 h7
    ⟨a, ha_mem, ha_ge⟩

lemma max_le_five (m : ℕ) (s : Finset ℕ)
    (hpos : ∀ a ∈ s, 1 ≤ a) (hsum : 2 ^ m = s.sum Nat.factorial)
    (h2 : 2 ∈ s) (h1 : 1 ∉ s) (h3 : 3 ∈ s) :
    ∀ a ∈ s, a ≤ 5 := by
  have h6 : 6 ∉ s := six_not_mem m s hpos hsum h2 h1 h3
  have h7 : 7 ∉ s := seven_not_mem m s hpos hsum h2 h1 h3 h6
  have h8 : ∀ a ∈ s, a < 8 := no_element_ge_eight m s hpos hsum h2 h1 h3 h6 h7
  intro a ha
  have ha8 := h8 a ha
  by_contra hle
  push Not at hle
  interval_cases a <;> contradiction

lemma enumerate_small_cases (m : ℕ) (s : Finset ℕ)
    (hpos : ∀ a ∈ s, 1 ≤ a) (hsum : 2 ^ m = s.sum Nat.factorial)
    (h2 : 2 ∈ s) (h1 : 1 ∉ s) (h3 : 3 ∈ s) (hmax : ∀ a ∈ s, a ≤ 5) :
    (m = 3 ∧ s = {2, 3}) ∨
    (m = 5 ∧ s = {2, 3, 4}) ∨
    (m = 7 ∧ s = {2, 3, 5}) := by
  have hsub : s ⊆ {2, 3, 4, 5} := by
    intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton]
    have := hpos a ha; have := hmax a ha; have : a ≠ 1 := fun heq => h1 (heq ▸ ha); omega
  by_cases h4 : 4 ∈ s <;> by_cases h5 : 5 ∈ s
  · exfalso
    have hs : s = {2, 3, 4, 5} := Finset.Subset.antisymm hsub
      (fun a ha => by simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> assumption)
    rw [hs] at hsum
    have : ({2, 3, 4, 5} : Finset ℕ).sum Nat.factorial = 152 := by decide
    rw [this] at hsum
    have hm_le : m ≤ 7 := by
      by_contra hle; push Not at hle
      have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hle; omega
    interval_cases m <;> omega
  · have hs : s = {2, 3, 4} := by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor
      · intro ha
        have hmem := hsub ha; simp at hmem
        have hne5 : a ≠ 5 := fun heq => h5 (heq ▸ ha)
        rcases hmem with rfl | rfl | rfl | rfl <;> simp_all
      · rintro (rfl | rfl | rfl) <;> assumption
    right; left
    rw [hs] at hsum
    have : ({2, 3, 4} : Finset ℕ).sum Nat.factorial = 32 := by decide
    rw [this] at hsum
    exact ⟨Nat.pow_right_injective (by omega) (by omega : 2 ^ m = 2 ^ 5), hs⟩
  · have hs : s = {2, 3, 5} := by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor
      · intro ha
        have hmem := hsub ha; simp at hmem
        have hne4 : a ≠ 4 := fun heq => h4 (heq ▸ ha)
        rcases hmem with rfl | rfl | rfl | rfl <;> simp_all
      · rintro (rfl | rfl | rfl) <;> assumption
    right; right
    rw [hs] at hsum
    have : ({2, 3, 5} : Finset ℕ).sum Nat.factorial = 128 := by decide
    rw [this] at hsum
    exact ⟨Nat.pow_right_injective (by omega) (by omega : 2 ^ m = 2 ^ 7), hs⟩
  · have hs : s = {2, 3} := by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor
      · intro ha
        have hmem := hsub ha; simp at hmem
        have hne4 : a ≠ 4 := fun heq => h4 (heq ▸ ha)
        have hne5 : a ≠ 5 := fun heq => h5 (heq ▸ ha)
        rcases hmem with rfl | rfl | rfl | rfl <;> simp_all
      · rintro (rfl | rfl) <;> assumption
    left
    rw [hs] at hsum
    have : ({2, 3} : Finset ℕ).sum Nat.factorial = 8 := by decide
    rw [this] at hsum
    exact ⟨Nat.pow_right_injective (by omega) (by omega : 2 ^ m = 2 ^ 3), hs⟩

lemma singleton_of_card_one_mem (s : Finset ℕ) (h2 : 2 ∈ s) (hcard : s.card = 1) :
    s = {2} := by
  rw [Finset.card_eq_one] at hcard
  obtain ⟨a, ha⟩ := hcard
  subst ha
  simp at h2
  subst h2
  rfl

lemma two_mem_case (m : ℕ) (s : Finset ℕ)
    (hne : s.Nonempty) (hpos : ∀ a ∈ s, 1 ≤ a) (hsum : 2 ^ m = s.sum Nat.factorial)
    (h2 : 2 ∈ s) (h1 : 1 ∉ s) :
    (m = 1 ∧ s = {2}) ∨
    (m = 3 ∧ s = {2, 3}) ∨
    (m = 5 ∧ s = {2, 3, 4}) ∨
    (m = 7 ∧ s = {2, 3, 5}) := by
  by_cases hcard : s.card ≤ 1
  · have hcard1 : s.card = 1 := by
      have := Finset.card_pos.mpr hne; omega
    have hs2 : s = {2} := singleton_of_card_one_mem s h2 hcard1
    left; exact ⟨two_singleton_case m (hs2 ▸ hsum), hs2⟩
  · push Not at hcard
    have h3 : 3 ∈ s := must_contain_three m s hpos hsum h2 h1 hcard
    have hmax : ∀ a ∈ s, a ≤ 5 := max_le_five m s hpos hsum h2 h1 h3
    right
    exact enumerate_small_cases m s hpos hsum h2 h1 h3 hmax

lemma erdos403_forward (m : ℕ) (s : Finset ℕ) :
    IsErdos403Solution m s →
    (m = 0 ∧ s = {1}) ∨
    (m = 1 ∧ s = {2}) ∨
    (m = 3 ∧ s = {2, 3}) ∨
    (m = 5 ∧ s = {2, 3, 4}) ∨
    (m = 7 ∧ s = {2, 3, 5}) := by
  intro ⟨hne, hpos, hsum⟩
  have hmin := min_le_two m s hne hsum
  have hmin_mem := Finset.min'_mem s hne
  have hmin_pos := hpos _ hmin_mem
  rcases Nat.eq_or_lt_of_le hmin_pos with h1 | h2
  · have : 1 ∈ s := h1 ▸ hmin_mem
    left; exact one_mem_case m s hpos hsum this
  · have hmin2 : s.min' hne = 2 := by omega
    have : 2 ∈ s := hmin2 ▸ hmin_mem
    have h1 : 1 ∉ s := by
      intro h1mem; have := Finset.min'_le s 1 h1mem; omega
    rcases two_mem_case m s hne hpos hsum this h1 with h | h
    · right; left; exact h
    · right; right; exact h

theorem erdos403_complete (m : ℕ) (s : Finset ℕ) :
    IsErdos403Solution m s ↔
      (m = 0 ∧ s = {1}) ∨
      (m = 1 ∧ s = {2}) ∨
      (m = 3 ∧ s = {2, 3}) ∨
      (m = 5 ∧ s = {2, 3, 4}) ∨
      (m = 7 ∧ s = {2, 3, 5}) := by
  exact ⟨erdos403_forward m s, erdos403_backward m s⟩

theorem erdos403 (m : ℕ) :
    (∃ s : Finset ℕ, IsErdos403Solution m s) ↔ m ∈ ({0, 1, 3, 5, 7} : Finset ℕ) := by
  constructor
  · rintro ⟨s, hs⟩
    rw [erdos403_complete] at hs
    rcases hs with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  · intro hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact ⟨{1}, (erdos403_complete 0 {1}).mpr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨{2}, (erdos403_complete 1 {2}).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨{2, 3}, (erdos403_complete 3 {2, 3}).mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    · exact ⟨{2, 3, 4}, (erdos403_complete 5 {2, 3, 4}).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
    · exact ⟨{2, 3, 5}, (erdos403_complete 7 {2, 3, 5}).mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))⟩

end Erdos403
