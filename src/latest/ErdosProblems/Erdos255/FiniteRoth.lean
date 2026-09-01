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

open Filter Finset Set
open scoped BigOperators

namespace Erdos255

noncomputable section

def prefixCount (y : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℕ :=
  ((Finset.range N).filter fun n ↦ y n < u).card

def starDisc (y : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  prefixCount y N u - N * u

private def halfSize (q d : ℕ) : ℕ := 2 ^ (q + 1 - d)

private def haar (q d i A : ℕ) : ℝ :=
  let h := halfSize q d
  (if A ∈ Finset.Ico (2 * i * h) ((2 * i + 1) * h) then 1 else 0) -
    (if A ∈ Finset.Ico ((2 * i + 1) * h) (2 * (i + 1) * h) then 1 else 0)

private lemma pow_two_pos (n : ℕ) : 0 < 2 ^ n := by positivity

private lemma two_mul_halfSize (q d : ℕ) (hd : d ≤ q + 1) :
    2 * halfSize q d = 2 ^ (q + 2 - d) := by
  unfold halfSize
  rw [show q + 2 - d = (q + 1 - d) + 1 by omega, pow_succ]
  ring

private lemma blocks_end (q d i : ℕ) (hd : d ≤ q + 1) (hi : i < 2 ^ d) :
    2 * (i + 1) * halfSize q d ≤ 2 ^ (q + 2) := by
  have hip : i + 1 ≤ 2 ^ d := by omega
  calc
    2 * (i + 1) * halfSize q d = (i + 1) * (2 * halfSize q d) := by ring
    _ ≤ 2 ^ d * 2 ^ (q + 2 - d) := Nat.mul_le_mul hip (le_of_eq (two_mul_halfSize q d hd))
    _ = 2 ^ (q + 2) := by
      rw [← pow_add]
      congr 1
      omega

private lemma block_lo_le_mid (q d i : ℕ) :
    2 * i * halfSize q d ≤ (2 * i + 1) * halfSize q d := by
  have hh := pow_two_pos (q + 1 - d)
  dsimp [halfSize]
  nlinarith

private lemma block_mid_le_hi (q d i : ℕ) :
    (2 * i + 1) * halfSize q d ≤ 2 * (i + 1) * halfSize q d := by
  have hh := pow_two_pos (q + 1 - d)
  dsimp [halfSize]
  nlinarith

private lemma sum_ite_mem_Ico_one (Q a b : ℕ) (ha : a ≤ b) (hb : b ≤ Q) :
    ∑ A ∈ Finset.range Q, (if A ∈ Finset.Ico a b then (1 : ℝ) else 0) = b - a := by
  rw [← Finset.sum_filter]
  have heq : (Finset.range Q).filter (fun A ↦ A ∈ Finset.Ico a b) = Finset.Ico a b := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [heq]
  simp [Nat.cast_sub ha]

private lemma haar_sum (q d i : ℕ) (hd : d ≤ q + 1) (hi : i < 2 ^ d) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d i A = 0 := by
  unfold haar
  simp_rw [Finset.sum_sub_distrib]
  rw [sum_ite_mem_Ico_one, sum_ite_mem_Ico_one]
  · push_cast
    ring
  · exact block_mid_le_hi q d i
  · exact blocks_end q d i hd hi
  · exact block_lo_le_mid q d i
  · exact (block_mid_le_hi q d i).trans (blocks_end q d i hd hi)

private lemma haar_sq_point (q d i A : ℕ) :
    haar q d i A ^ 2 =
      (if A ∈ Finset.Ico (2 * i * halfSize q d) ((2 * i + 1) * halfSize q d)
        then (1 : ℝ) else 0) +
      (if A ∈ Finset.Ico ((2 * i + 1) * halfSize q d) (2 * (i + 1) * halfSize q d)
        then (1 : ℝ) else 0) := by
  unfold haar
  simp only [Finset.mem_Ico]
  by_cases h₁ : 2 * i * halfSize q d ≤ A ∧ A < (2 * i + 1) * halfSize q d
  · have h₂ : ¬ ((2 * i + 1) * halfSize q d ≤ A ∧
        A < 2 * (i + 1) * halfSize q d) := by omega
    simp [h₁, h₂]
  · by_cases h₂ : (2 * i + 1) * halfSize q d ≤ A ∧
        A < 2 * (i + 1) * halfSize q d
    · simp [h₁, h₂]
    · simp [h₁, h₂]

private lemma haar_sq_sum (q d i : ℕ) (hd : d ≤ q + 1) (hi : i < 2 ^ d) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d i A ^ 2 =
      2 * halfSize q d := by
  simp_rw [haar_sq_point, Finset.sum_add_distrib]
  rw [sum_ite_mem_Ico_one, sum_ite_mem_Ico_one]
  · push_cast
    ring
  · exact block_mid_le_hi q d i
  · exact blocks_end q d i hd hi
  · exact block_lo_le_mid q d i
  · exact (block_mid_le_hi q d i).trans (blocks_end q d i hd hi)

private lemma sum_Ico_id (a h : ℕ) :
    ∑ A ∈ Finset.Ico a (a + h), A = h * a + h * (h - 1) / 2 := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  calc
    ∑ k ∈ Finset.range h, (a + k) =
        (∑ _k ∈ Finset.range h, a) + ∑ k ∈ Finset.range h, k := by
          rw [Finset.sum_add_distrib]
    _ = h * a + h * (h - 1) / 2 := by simp [Finset.sum_range_id, Nat.mul_comm]

private lemma sum_cast_ite_mem_Ico (Q a b : ℕ) (hb : b ≤ Q) :
    ∑ A ∈ Finset.range Q, (A : ℝ) * (if A ∈ Finset.Ico a b then (1 : ℝ) else 0) =
      ∑ A ∈ Finset.Ico a b, (A : ℝ) := by
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

private lemma sum_Ico_cast (a h : ℕ) :
    ∑ A ∈ Finset.Ico a (a + h), (A : ℝ) =
      (h : ℝ) * a + (h * (h - 1) / 2 : ℕ) := by
  calc
    ∑ A ∈ Finset.Ico a (a + h), (A : ℝ) =
        ((∑ A ∈ Finset.Ico a (a + h), A : ℕ) : ℝ) := by
          exact (Nat.cast_sum (Finset.Ico a (a + h)) fun A ↦ A).symm
    _ = (h * a + h * (h - 1) / 2 : ℕ) := by rw [sum_Ico_id]
    _ = (h : ℝ) * a + (h * (h - 1) / 2 : ℕ) := by push_cast; ring

private lemma haar_moment_nat (q d i : ℕ) (hd : d ≤ q + 1) (hi : i < 2 ^ d) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), (A : ℝ) * haar q d i A =
      -(halfSize q d : ℝ) ^ 2 := by
  let h := halfSize q d
  have hmid_hi : (2 * i + 1) * h ≤ 2 * (i + 1) * h := block_mid_le_hi q d i
  have hend : 2 * (i + 1) * h ≤ 2 ^ (q + 2) := blocks_end q d i hd hi
  have hleft_end : 2 * i * h + h = (2 * i + 1) * h := by ring
  have hright_end : (2 * i + 1) * h + h = 2 * (i + 1) * h := by ring
  unfold haar
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [sum_cast_ite_mem_Ico, sum_cast_ite_mem_Ico]
  · change
      (∑ A ∈ Finset.Ico (2 * i * h) ((2 * i + 1) * h), (A : ℝ)) -
        (∑ A ∈ Finset.Ico ((2 * i + 1) * h) (2 * (i + 1) * h), (A : ℝ)) =
          -(h : ℝ) ^ 2
    have hleft :
        ∑ A ∈ Finset.Ico (2 * i * h) ((2 * i + 1) * h), (A : ℝ) =
          (h : ℝ) * (2 * i * h) + (h * (h - 1) / 2 : ℕ) := by
      convert sum_Ico_cast (2 * i * h) h using 1 <;> push_cast <;> ring
    have hright :
        ∑ A ∈ Finset.Ico ((2 * i + 1) * h) (2 * (i + 1) * h), (A : ℝ) =
          (h : ℝ) * ((2 * i + 1) * h) + (h * (h - 1) / 2 : ℕ) := by
      convert sum_Ico_cast ((2 * i + 1) * h) h using 1 <;> push_cast <;> ring
    rw [hleft, hright]
    dsimp [h]
    ring
  · simpa [h] using hend
  · simpa [h] using hmid_hi.trans hend

private lemma halfSize_relation (q d e : ℕ) (hde : d < e) (he : e ≤ q + 1) :
    halfSize q d = 2 * 2 ^ (e - d - 1) * halfSize q e := by
  unfold halfSize
  have hexp : q + 1 - d = (e - d - 1) + 1 + (q + 1 - e) := by omega
  rw [hexp, pow_add, pow_add]
  ring

private lemma no_cross_aligned (h p j k : ℕ) :
    2 * (j + 1) * h ≤ k * (2 * p * h) ∨
      k * (2 * p * h) ≤ 2 * j * h := by
  by_cases hj : j < k * p
  · left
    have : j + 1 ≤ k * p := by omega
    nlinarith
  · right
    have : k * p ≤ j := by omega
    nlinarith

private lemma comparison_constant_on_block
    {s t b A A' : ℕ} (hcross : t ≤ b ∨ b ≤ s)
    (hA : s ≤ A ∧ A < t) (hA' : s ≤ A' ∧ A' < t) :
    (b ≤ A ↔ b ≤ A') ∧ (A < b ↔ A' < b) := by
  rcases hcross with htb | hbs <;> omega

private lemma haar_eq_zero_of_outside (q d i A : ℕ)
    (hA : ¬ (2 * i * halfSize q d ≤ A ∧
      A < 2 * (i + 1) * halfSize q d)) :
    haar q d i A = 0 := by
  unfold haar
  simp only [Finset.mem_Ico]
  have hleft : ¬ (2 * i * halfSize q d ≤ A ∧
      A < (2 * i + 1) * halfSize q d) := by
    intro h
    apply hA
    exact ⟨h.1, h.2.trans_le (block_mid_le_hi q d i)⟩
  have hright : ¬ ((2 * i + 1) * halfSize q d ≤ A ∧
      A < 2 * (i + 1) * halfSize q d) := by
    intro h
    apply hA
    exact ⟨(block_lo_le_mid q d i).trans h.1, h.2⟩
  simp [hleft, hright]

private lemma haar_coarse_constant_on_fine
    (q d e i j A : ℕ) (hde : d < e) (he : e ≤ q + 1)
    (hA : 2 * j * halfSize q e ≤ A ∧
      A < 2 * (j + 1) * halfSize q e) :
    haar q d i A = haar q d i (2 * j * halfSize q e) := by
  let h := halfSize q e
  let p := 2 ^ (e - d - 1)
  change haar q d i A = haar q d i (2 * j * h)
  have hh : 0 < h := by dsimp [h, halfSize]; positivity
  have hp : 0 < p := by dsimp [p]; positivity
  have hrel : halfSize q d = 2 * p * h := by
    simpa [h, p] using halfSize_relation q d e hde he
  have hs_mem : 2 * j * h ≤ 2 * j * h ∧ 2 * j * h < 2 * (j + 1) * h := by
    constructor
    · rfl
    · nlinarith
  have cross_lo :
      2 * (j + 1) * h ≤ 2 * i * halfSize q d ∨
        2 * i * halfSize q d ≤ 2 * j * h := by
    simpa [hrel, mul_assoc] using no_cross_aligned h p j (2 * i)
  have cross_mid :
      2 * (j + 1) * h ≤ (2 * i + 1) * halfSize q d ∨
        (2 * i + 1) * halfSize q d ≤ 2 * j * h := by
    simpa [hrel, mul_assoc] using no_cross_aligned h p j (2 * i + 1)
  have cross_hi :
      2 * (j + 1) * h ≤ 2 * (i + 1) * halfSize q d ∨
        2 * (i + 1) * halfSize q d ≤ 2 * j * h := by
    simpa [hrel, mul_assoc] using no_cross_aligned h p j (2 * (i + 1))
  have c_lo := comparison_constant_on_block cross_lo hA hs_mem
  have c_mid := comparison_constant_on_block cross_mid hA hs_mem
  have c_hi := comparison_constant_on_block cross_hi hA hs_mem
  unfold haar
  simp only [Finset.mem_Ico]
  simp only [c_lo.1, c_mid.1, c_mid.2, c_hi.2]

private lemma haar_mul_fine (q d e i j A : ℕ)
    (hde : d < e) (he : e ≤ q + 1) :
    haar q d i A * haar q e j A =
      haar q d i (2 * j * halfSize q e) * haar q e j A := by
  by_cases hA : 2 * j * halfSize q e ≤ A ∧
      A < 2 * (j + 1) * halfSize q e
  · rw [haar_coarse_constant_on_fine q d e i j A hde he hA]
  · rw [haar_eq_zero_of_outside q e j A hA]
    ring

private lemma haar_orthogonal_of_lt
    (q d e i j : ℕ) (hde : d < e) (he : e ≤ q + 1) (hj : j < 2 ^ e) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d i A * haar q e j A = 0 := by
  calc
    ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d i A * haar q e j A =
        ∑ A ∈ Finset.range (2 ^ (q + 2)),
          haar q d i (2 * j * halfSize q e) * haar q e j A := by
            apply Finset.sum_congr rfl
            intro A hA
            exact haar_mul_fine q d e i j A hde he
    _ = haar q d i (2 * j * halfSize q e) *
        ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q e j A := by
          rw [Finset.mul_sum]
    _ = 0 := by rw [haar_sum q e j he hj, mul_zero]

private lemma haar_mul_eq_zero_of_same_depth_ne
    (q d i j A : ℕ) (hij : i ≠ j) :
    haar q d i A * haar q d j A = 0 := by
  have hh : 0 < halfSize q d := by unfold halfSize; positivity
  rcases lt_or_gt_of_ne hij with hij' | hij'
  · have hsep : 2 * (i + 1) * halfSize q d ≤ 2 * j * halfSize q d := by
      have : i + 1 ≤ j := by omega
      nlinarith
    by_cases hAi : 2 * i * halfSize q d ≤ A ∧
        A < 2 * (i + 1) * halfSize q d
    · have hAj : ¬ (2 * j * halfSize q d ≤ A ∧
          A < 2 * (j + 1) * halfSize q d) := by omega
      rw [haar_eq_zero_of_outside q d j A hAj, mul_zero]
    · rw [haar_eq_zero_of_outside q d i A hAi, zero_mul]
  · have hsep : 2 * (j + 1) * halfSize q d ≤ 2 * i * halfSize q d := by
      have : j + 1 ≤ i := by omega
      nlinarith
    by_cases hAj : 2 * j * halfSize q d ≤ A ∧
        A < 2 * (j + 1) * halfSize q d
    · have hAi : ¬ (2 * i * halfSize q d ≤ A ∧
          A < 2 * (i + 1) * halfSize q d) := by omega
      rw [haar_eq_zero_of_outside q d i A hAi, zero_mul]
    · rw [haar_eq_zero_of_outside q d j A hAj, mul_zero]

private lemma haar_orthogonal
    (q d e i j : ℕ) (hd : d ≤ q + 1) (he : e ≤ q + 1)
    (hi : i < 2 ^ d) (hj : j < 2 ^ e) (hne : (d, i) ≠ (e, j)) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d i A * haar q e j A = 0 := by
  rcases lt_trichotomy d e with hde | hde | hde
  · exact haar_orthogonal_of_lt q d e i j hde he hj
  · subst e
    have hij : i ≠ j := by simpa using hne
    simp_rw [haar_mul_eq_zero_of_same_depth_ne q d i j _ hij]
    simp
  · calc
      ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d i A * haar q e j A =
          ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q e j A * haar q d i A := by
            apply Finset.sum_congr rfl
            intro A hA
            ring
      _ = 0 := haar_orthogonal_of_lt q e d j i hde hd hi

private abbrev Rect (q d : ℕ) := Fin (2 ^ d) × Fin (2 ^ (q + 1 - d))

private def inCell (q d i : ℕ) (x : ℝ) : Prop :=
  ((2 * i * halfSize q d : ℕ) : ℝ) / 2 ^ (q + 2) ≤ x ∧
    x < ((2 * (i + 1) * halfSize q d : ℕ) : ℝ) / 2 ^ (q + 2)

private lemma inCell_unique (q d i j : ℕ) (x : ℝ)
    (hi : inCell q d i x) (hj : inCell q d j x) : i = j := by
  by_contra hij
  have hQ : (0 : ℝ) < 2 ^ (q + 2) := by positivity
  rcases lt_or_gt_of_ne hij with hij | hij
  · have hindex : i + 1 ≤ j := by omega
    have hsep : ((2 * (i + 1) * halfSize q d : ℕ) : ℝ) ≤
        ((2 * j * halfSize q d : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * (i + 1) * halfSize q d ≤ 2 * j * halfSize q d by
        gcongr)
    have := (div_le_div_iff_of_pos_right hQ).mpr hsep
    linarith [hi.2, hj.1]
  · have hindex : j + 1 ≤ i := by omega
    have hsep : ((2 * (j + 1) * halfSize q d : ℕ) : ℝ) ≤
        ((2 * i * halfSize q d : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * (j + 1) * halfSize q d ≤ 2 * i * halfSize q d by
        gcongr)
    have := (div_le_div_iff_of_pos_right hQ).mpr hsep
    linarith [hj.2, hi.1]

private def rectsAtPoint (q d : ℕ) (x v : ℝ) : Finset (Rect q d) :=
  by
    classical
    exact Finset.univ.filter fun R ↦ inCell q d R.1 x ∧ inCell q (q + 1 - d) R.2 v

private lemma rectsAtPoint_card_le_one (q d : ℕ) (x v : ℝ) :
    (rectsAtPoint q d x v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro R hR S hS
  simp only [rectsAtPoint, Finset.mem_filter, Finset.mem_univ, true_and] at hR hS
  apply Prod.ext
  · apply Fin.ext
    exact inCell_unique q d R.1 S.1 x hR.1 hS.1
  · apply Fin.ext
    exact inCell_unique q (q + 1 - d) R.2 S.2 v hR.2 hS.2

private def occupiedRects (y : ℕ → ℝ) (q d : ℕ) : Finset (Rect q d) :=
  (Finset.range (2 ^ q)).biUnion fun n ↦
    rectsAtPoint q d (y n) ((n : ℝ) / (2 ^ q : ℕ))

private lemma occupiedRects_card_le (y : ℕ → ℝ) (q d : ℕ) :
    (occupiedRects y q d).card ≤ 2 ^ q := by
  calc
    (occupiedRects y q d).card ≤
        ∑ n ∈ Finset.range (2 ^ q),
          (rectsAtPoint q d (y n) ((n : ℝ) / (2 ^ q : ℕ))).card := by
            exact Finset.card_biUnion_le
    _ ≤ ∑ _n ∈ Finset.range (2 ^ q), 1 := by
      exact Finset.sum_le_sum fun n hn ↦ rectsAtPoint_card_le_one q d _ _
    _ = 2 ^ q := by simp

private lemma rect_card (q d : ℕ) (hd : d ≤ q + 1) :
    Fintype.card (Rect q d) = 2 * 2 ^ q := by
  simp only [Rect, Fintype.card_prod, Fintype.card_fin]
  rw [← pow_add]
  have : d + (q + 1 - d) = q + 1 := by omega
  rw [this, pow_succ]
  ring

private def emptyRects (y : ℕ → ℝ) (q d : ℕ) : Finset (Rect q d) :=
  Finset.univ \ occupiedRects y q d

private lemma emptyRects_card_ge (y : ℕ → ℝ) (q d : ℕ) (hd : d ≤ q + 1) :
    2 ^ q ≤ (emptyRects y q d).card := by
  rw [emptyRects, Finset.card_sdiff]
  have hinter : occupiedRects y q d ∩ Finset.univ = occupiedRects y q d := by simp
  rw [hinter, Finset.card_univ, rect_card q d hd]
  have hoc := occupiedRects_card_le y q d
  omega

private lemma emptyRects_card_le (y : ℕ → ℝ) (q d : ℕ) (hd : d ≤ q + 1) :
    (emptyRects y q d).card ≤ 2 * 2 ^ q := by
  calc
    (emptyRects y q d).card ≤ (Finset.univ : Finset (Rect q d)).card :=
      Finset.card_le_card (Finset.sdiff_subset)
    _ = 2 * 2 ^ q := by rw [Finset.card_univ, rect_card q d hd]

private def tailHaar (q d i : ℕ) (x : ℝ) : ℝ :=
  ∑ A ∈ Finset.range (2 ^ (q + 2)),
    (if x < (A : ℝ) / 2 ^ (q + 2) then 1 else 0) * haar q d i A

private lemma tailHaar_eq_zero_of_not_inCell (q d i : ℕ) (x : ℝ)
    (hd : d ≤ q + 1) (hi : i < 2 ^ d) (hx : ¬ inCell q d i x) :
    tailHaar q d i x = 0 := by
  have hQ : (0 : ℝ) < 2 ^ (q + 2) := by positivity
  simp only [inCell, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · have hpoint : ∀ A ∈ Finset.range (2 ^ (q + 2)),
        (if x < (A : ℝ) / 2 ^ (q + 2) then 1 else 0) * haar q d i A =
          haar q d i A := by
      intro A hA
      by_cases hsupp : 2 * i * halfSize q d ≤ A ∧
          A < 2 * (i + 1) * halfSize q d
      · have hcast : ((2 * i * halfSize q d : ℕ) : ℝ) ≤ A := by exact_mod_cast hsupp.1
        have hdiv := (div_le_div_iff_of_pos_right hQ).mpr hcast
        simp [hx.trans_le hdiv]
      · rw [haar_eq_zero_of_outside q d i A hsupp]
        simp
    rw [tailHaar]
    calc
      ∑ A ∈ Finset.range (2 ^ (q + 2)),
          (if x < (A : ℝ) / 2 ^ (q + 2) then 1 else 0) * haar q d i A =
          ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d i A :=
            Finset.sum_congr rfl hpoint
      _ = 0 := haar_sum q d i hd hi
  · have hpoint : ∀ A ∈ Finset.range (2 ^ (q + 2)),
        (if x < (A : ℝ) / 2 ^ (q + 2) then 1 else 0) * haar q d i A = 0 := by
      intro A hA
      by_cases hsupp : 2 * i * halfSize q d ≤ A ∧
          A < 2 * (i + 1) * halfSize q d
      · have hcast : (A : ℝ) ≤ ((2 * (i + 1) * halfSize q d : ℕ) : ℝ) := by
          exact_mod_cast hsupp.2.le
        have hdiv := (div_le_div_iff_of_pos_right hQ).mpr hcast
        simp [not_lt_of_ge (hdiv.trans (le_of_not_gt hx))]
      · rw [haar_eq_zero_of_outside q d i A hsupp]
        simp
    rw [tailHaar]
    exact Finset.sum_eq_zero hpoint

private lemma not_occupied_product_tailHaar_eq_zero
    (y : ℕ → ℝ) (q d : ℕ) (hd : d ≤ q + 1)
    (R : Rect q d) (hR : R ∈ emptyRects y q d) (n : ℕ) (hn : n < 2 ^ q) :
    tailHaar q d R.1 (y n) *
      tailHaar q (q + 1 - d) R.2 ((n : ℝ) / (2 ^ q : ℕ)) = 0 := by
  classical
  have hnot : R ∉ occupiedRects y q d := (Finset.mem_sdiff.mp hR).2
  have hnotcell : ¬ (inCell q d R.1 (y n) ∧
      inCell q (q + 1 - d) R.2 ((n : ℝ) / (2 ^ q : ℕ))) := by
    intro hcell
    apply hnot
    simp only [occupiedRects, Finset.mem_biUnion, Finset.mem_range]
    refine ⟨n, hn, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcell⟩
  rcases not_and_or.mp hnotcell with hleft | hright
  · rw [tailHaar_eq_zero_of_not_inCell q d R.1 (y n) hd R.1.isLt hleft, zero_mul]
  · have hvd : q + 1 - d ≤ q + 1 := Nat.sub_le _ _
    rw [tailHaar_eq_zero_of_not_inCell q (q + 1 - d) R.2
      ((n : ℝ) / (2 ^ q : ℕ)) hvd R.2.isLt hright, mul_zero]

private def rectHaar (q d : ℕ) (R : Rect q d) (A C : ℕ) : ℝ :=
  haar q d R.1 A * haar q (q + 1 - d) R.2 C

private lemma halfSize_mul_complement (q d : ℕ) (hd : d ≤ q + 1) :
    halfSize q d * halfSize q (q + 1 - d) = 2 ^ (q + 1) := by
  rw [halfSize, halfSize, ← pow_add]
  congr 1
  omega

private lemma rectHaar_sq_sum (q d : ℕ) (R : Rect q d) (hd : d ≤ q + 1) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      rectHaar q d R A C ^ 2 = (8 * 2 ^ q : ℝ) := by
  have hvd : q + 1 - d ≤ q + 1 := Nat.sub_le _ _
  rw [show (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      rectHaar q d R A C ^ 2) =
      (∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d R.1 A ^ 2) *
      (∑ C ∈ Finset.range (2 ^ (q + 2)), haar q (q + 1 - d) R.2 C ^ 2) by
    simp only [rectHaar, mul_pow]
    calc
      (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
          haar q d R.1 A ^ 2 * haar q (q + 1 - d) R.2 C ^ 2) =
          ∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d R.1 A ^ 2 *
            (∑ C ∈ Finset.range (2 ^ (q + 2)), haar q (q + 1 - d) R.2 C ^ 2) := by
              apply Finset.sum_congr rfl
              intro A hA
              rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]]
  rw [haar_sq_sum q d R.1 hd R.1.isLt,
    haar_sq_sum q (q + 1 - d) R.2 hvd R.2.isLt]
  norm_cast
  calc
    2 * halfSize q d * (2 * halfSize q (q + 1 - d)) =
        4 * (halfSize q d * halfSize q (q + 1 - d)) := by ring
    _ = 4 * 2 ^ (q + 1) := by rw [halfSize_mul_complement q d hd]
    _ = 8 * 2 ^ q := by rw [pow_succ]; ring

private lemma rectHaar_orthogonal (q d e : ℕ) (R : Rect q d) (S : Rect q e)
    (hd : d ≤ q + 1) (he : e ≤ q + 1)
    (hne : (d, R.1.val, R.2.val) ≠ (e, S.1.val, S.2.val)) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      rectHaar q d R A C * rectHaar q e S A C = 0 := by
  rw [show (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      rectHaar q d R A C * rectHaar q e S A C) =
      (∑ A ∈ Finset.range (2 ^ (q + 2)), haar q d R.1 A * haar q e S.1 A) *
      (∑ C ∈ Finset.range (2 ^ (q + 2)),
        haar q (q + 1 - d) R.2 C * haar q (q + 1 - e) S.2 C) by
    simp only [rectHaar]
    calc
      (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
          (haar q d R.1 A * haar q (q + 1 - d) R.2 C) *
            (haar q e S.1 A * haar q (q + 1 - e) S.2 C)) =
          ∑ A ∈ Finset.range (2 ^ (q + 2)),
            (haar q d R.1 A * haar q e S.1 A) *
              (∑ C ∈ Finset.range (2 ^ (q + 2)),
                haar q (q + 1 - d) R.2 C * haar q (q + 1 - e) S.2 C) := by
            apply Finset.sum_congr rfl
            intro A hA
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro C hC
            ring
      _ = _ := by rw [Finset.sum_mul]]
  by_cases hde : d = e
  · subst e
    by_cases hhor : R.1.val = S.1.val
    · have hver : R.2.val ≠ S.2.val := by
        intro hv
        exact hne (by simp [hhor, hv])
      have hvd : q + 1 - d ≤ q + 1 := Nat.sub_le _ _
      rw [haar_orthogonal q (q + 1 - d) (q + 1 - d) R.2 S.2 hvd hvd
          R.2.isLt S.2.isLt (by
          intro h; exact hver (congrArg Prod.snd h))]
      simp
    · rw [haar_orthogonal q d d R.1 S.1 hd hd R.1.isLt S.1.isLt (by
          intro h; exact hhor (congrArg Prod.snd h))]
      simp
  · rw [haar_orthogonal q d e R.1 S.1 hd he R.1.isLt S.1.isLt (by
        intro h; exact hde (congrArg Prod.fst h))]
    simp

private abbrev TaggedRect (q : ℕ) := Σ d : Fin (q + 2), Rect q d

private def taggedEmpty (y : ℕ → ℝ) (q : ℕ) : Finset (TaggedRect q) :=
  (Finset.univ : Finset (Fin (q + 2))).sigma fun d ↦ emptyRects y q d

private def taggedHaar (q : ℕ) (T : TaggedRect q) (A C : ℕ) : ℝ :=
  rectHaar q T.1 T.2 A C

private lemma taggedEmpty_card_ge (y : ℕ → ℝ) (q : ℕ) :
    (q + 2) * 2 ^ q ≤ (taggedEmpty y q).card := by
  rw [taggedEmpty, Finset.card_sigma]
  calc
    (q + 2) * 2 ^ q = ∑ _d ∈ (Finset.univ : Finset (Fin (q + 2))), 2 ^ q := by simp
    _ ≤ ∑ d ∈ (Finset.univ : Finset (Fin (q + 2))), (emptyRects y q d).card := by
      exact Finset.sum_le_sum fun d hd ↦ emptyRects_card_ge y q d (by omega)

private lemma taggedHaar_inner (q : ℕ) (T S : TaggedRect q) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      taggedHaar q T A C * taggedHaar q S A C =
        if T = S then (8 * 2 ^ q : ℝ) else 0 := by
  by_cases hTS : T = S
  · subst S
    rw [if_pos rfl]
    simpa only [taggedHaar, pow_two] using rectHaar_sq_sum q T.1 T.2 (by omega)
  · rw [if_neg hTS]
    apply rectHaar_orthogonal q T.1 S.1 T.2 S.2 (by omega) (by omega)
    intro h
    apply hTS
    have hdval : T.1.val = S.1.val := congrArg (fun z ↦ z.1) h
    have hd : T.1 = S.1 := Fin.ext hdval
    cases T with
    | mk d R =>
      cases S with
      | mk e U =>
        simp only at hd
        subst e
        congr 1
        apply Prod.ext <;> apply Fin.ext
        · exact congrArg (fun z ↦ z.2.1) h
        · exact congrArg (fun z ↦ z.2.2) h

private def testFunction (y : ℕ → ℝ) (q A C : ℕ) : ℝ :=
  ∑ T ∈ taggedEmpty y q, taggedHaar q T A C

private lemma testFunction_sq_sum (y : ℕ → ℝ) (q : ℕ) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      testFunction y q A C ^ 2 =
        ((taggedEmpty y q).card : ℝ) * (8 * 2 ^ q) := by
  classical
  simp only [testFunction, pow_two]
  simp_rw [Finset.sum_mul_sum]
  rw [show (∑ A ∈ Finset.range (2 ^ (q + 2)),
      ∑ C ∈ Finset.range (2 ^ (q + 2)),
        ∑ T ∈ taggedEmpty y q, ∑ S ∈ taggedEmpty y q,
          taggedHaar q T A C * taggedHaar q S A C) =
      ∑ T ∈ taggedEmpty y q, ∑ S ∈ taggedEmpty y q,
        ∑ A ∈ Finset.range (2 ^ (q + 2)),
          ∑ C ∈ Finset.range (2 ^ (q + 2)),
            taggedHaar q T A C * taggedHaar q S A C by
    calc
      _ = ∑ A ∈ Finset.range (2 ^ (q + 2)),
          ∑ T ∈ taggedEmpty y q, ∑ C ∈ Finset.range (2 ^ (q + 2)),
            ∑ S ∈ taggedEmpty y q, taggedHaar q T A C * taggedHaar q S A C := by
              apply Finset.sum_congr rfl
              intro A hA
              rw [Finset.sum_comm]
      _ = ∑ T ∈ taggedEmpty y q, ∑ A ∈ Finset.range (2 ^ (q + 2)),
          ∑ C ∈ Finset.range (2 ^ (q + 2)), ∑ S ∈ taggedEmpty y q,
            taggedHaar q T A C * taggedHaar q S A C := by rw [Finset.sum_comm]
      _ = ∑ T ∈ taggedEmpty y q, ∑ A ∈ Finset.range (2 ^ (q + 2)),
          ∑ S ∈ taggedEmpty y q, ∑ C ∈ Finset.range (2 ^ (q + 2)),
            taggedHaar q T A C * taggedHaar q S A C := by
              apply Finset.sum_congr rfl
              intro T hT
              apply Finset.sum_congr rfl
              intro A hA
              rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [Finset.sum_comm]]
  simp_rw [taggedHaar_inner]
  simp

private def ceilQuarter (C : ℕ) : ℕ := (C + 3) / 4

private lemma pow_q_add_two (q : ℕ) : 2 ^ (q + 2) = 4 * 2 ^ q := by
  rw [pow_add]
  norm_num
  ring

private lemma ceilQuarter_error (q C : ℕ) :
    abs ((ceilQuarter C : ℝ) - (2 ^ q : ℕ) * (C : ℝ) / (2 ^ (q + 2) : ℕ)) ≤ 1 := by
  have hlow : C ≤ 4 * ceilQuarter C := by
    unfold ceilQuarter
    omega
  have hhigh : 4 * ceilQuarter C < C + 4 := by
    unfold ceilQuarter
    omega
  have hM : (0 : ℝ) < (2 ^ q : ℕ) := by positivity
  have hideal : (2 ^ q : ℕ) * (C : ℝ) / (2 ^ (q + 2) : ℕ) = (C : ℝ) / 4 := by
    rw [pow_q_add_two]
    push_cast
    field_simp
  have hlowR : (C : ℝ) ≤ 4 * (ceilQuarter C : ℝ) := by exact_mod_cast hlow
  have hhighR : 4 * (ceilQuarter C : ℝ) < (C : ℝ) + 4 := by exact_mod_cast hhigh
  rw [hideal, abs_le]
  constructor <;> linarith

private def gridDisc (y : ℕ → ℝ) (q A C : ℕ) : ℝ :=
  starDisc y (ceilQuarter C) ((A : ℝ) / (2 ^ (q + 2) : ℕ)) +
    ((ceilQuarter C : ℝ) - (2 ^ q : ℕ) * (C : ℝ) / (2 ^ (q + 2) : ℕ)) *
      ((A : ℝ) / (2 ^ (q + 2) : ℕ))

private lemma gridDisc_abs_le (y : ℕ → ℝ) (B : ℝ)
    (hB : ∀ N u, u ∈ Set.Icc (0 : ℝ) 1 → abs (starDisc y N u) ≤ B)
    (q A C : ℕ) (hA : A < 2 ^ (q + 2)) :
    abs (gridDisc y q A C) ≤ B + 1 := by
  have hQ : (0 : ℝ) < (2 ^ (q + 2) : ℕ) := by positivity
  have hu : (A : ℝ) / (2 ^ (q + 2) : ℕ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hQ).mpr
      exact_mod_cast hA.le
  have hstar := hB (ceilQuarter C) ((A : ℝ) / (2 ^ (q + 2) : ℕ)) hu
  have herr := ceilQuarter_error q C
  have huabs : abs ((A : ℝ) / (2 ^ (q + 2) : ℕ)) ≤ 1 := by
    rw [abs_of_nonneg hu.1]
    exact hu.2
  rw [gridDisc]
  calc
    abs (starDisc y (ceilQuarter C) ((A : ℝ) / (2 ^ (q + 2) : ℕ)) +
        ((ceilQuarter C : ℝ) - (2 ^ q : ℕ) * (C : ℝ) / (2 ^ (q + 2) : ℕ)) *
          ((A : ℝ) / (2 ^ (q + 2) : ℕ))) ≤
        abs (starDisc y (ceilQuarter C) ((A : ℝ) / (2 ^ (q + 2) : ℕ))) +
          abs (((ceilQuarter C : ℝ) - (2 ^ q : ℕ) * (C : ℝ) / (2 ^ (q + 2) : ℕ)) *
            ((A : ℝ) / (2 ^ (q + 2) : ℕ))) := abs_add_le _ _
    _ ≤ B + 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg ((ceilQuarter C : ℝ) -
        (2 ^ q : ℕ) * (C : ℝ) / (2 ^ (q + 2) : ℕ)),
        abs_nonneg ((A : ℝ) / (2 ^ (q + 2) : ℕ))]

/-! A self-contained finite-grid Roth inequality. -/

private def lowerTailHaar (q d i : ℕ) (x : ℝ) : ℝ :=
  ∑ A ∈ Finset.range (2 ^ (q + 2)),
    (if 0 ≤ x ∧ x < (A : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) * haar q d i A

private lemma lowerTailHaar_eq (q d i : ℕ) (x : ℝ) :
    lowerTailHaar q d i x = if 0 ≤ x then tailHaar q d i x else 0 := by
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, lowerTailHaar, tailHaar]
    apply Finset.sum_congr rfl
    intro A hA
    simp [hx]
  · rw [if_neg hx, lowerTailHaar]
    simp [hx]

private lemma not_occupied_product_lower_tail_eq_zero
    (y : ℕ → ℝ) (q d : ℕ) (hd : d ≤ q + 1)
    (R : Rect q d) (hR : R ∈ emptyRects y q d) (n : ℕ) (hn : n < 2 ^ q) :
    lowerTailHaar q d R.1 (y n) *
      tailHaar q (q + 1 - d) R.2 ((n : ℝ) / (2 ^ q : ℕ)) = 0 := by
  rw [lowerTailHaar_eq]
  split_ifs with hy
  · exact not_occupied_product_tailHaar_eq_zero y q d hd R hR n hn
  · simp

def gridCount (y : ℕ → ℝ) (q A C : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (2 ^ q),
    (if 0 ≤ y n ∧ y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
      (if (n : ℝ) / (2 ^ q : ℕ) < (C : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0)

def gridDiscrepancy (y : ℕ → ℝ) (lam : ℝ) (q A C : ℕ) : ℝ :=
  gridCount y q A C - lam *
    ((A : ℝ) / (2 ^ (q + 2) : ℕ)) * ((C : ℝ) / (2 ^ (q + 2) : ℕ))

private lemma rawCount_rectHaar_sum_eq_zero
    (y : ℕ → ℝ) (q d : ℕ) (hd : d ≤ q + 1)
    (R : Rect q d) (hR : R ∈ emptyRects y q d) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      gridCount y q A C * rectHaar q d R A C = 0 := by
  classical
  simp only [gridCount, rectHaar]
  rw [show (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      (∑ n ∈ Finset.range (2 ^ q),
        (if 0 ≤ y n ∧ y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
        (if (n : ℝ) / (2 ^ q : ℕ) < (C : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0)) *
        (haar q d R.1 A * haar q (q + 1 - d) R.2 C)) =
      ∑ n ∈ Finset.range (2 ^ q),
        lowerTailHaar q d R.1 (y n) *
          tailHaar q (q + 1 - d) R.2 ((n : ℝ) / (2 ^ q : ℕ)) by
    simp only [lowerTailHaar, tailHaar]
    simp_rw [Finset.sum_mul]
    calc
      _ = ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
          ∑ n ∈ Finset.range (2 ^ q),
            ((if 0 ≤ y n ∧ y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
              haar q d R.1 A) *
            ((if (n : ℝ) / (2 ^ q : ℕ) < (C : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
              haar q (q + 1 - d) R.2 C) := by
                apply Finset.sum_congr rfl
                intro A hA
                apply Finset.sum_congr rfl
                intro C hC
                apply Finset.sum_congr rfl
                intro n hn
                ring
      _ = ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ n ∈ Finset.range (2 ^ q),
          ∑ C ∈ Finset.range (2 ^ (q + 2)),
            ((if 0 ≤ y n ∧ y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
              haar q d R.1 A) *
            ((if (n : ℝ) / (2 ^ q : ℕ) < (C : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
              haar q (q + 1 - d) R.2 C) := by
                apply Finset.sum_congr rfl
                intro A hA
                rw [Finset.sum_comm]
      _ = ∑ n ∈ Finset.range (2 ^ q), ∑ A ∈ Finset.range (2 ^ (q + 2)),
          ∑ C ∈ Finset.range (2 ^ (q + 2)),
            ((if 0 ≤ y n ∧ y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
              haar q d R.1 A) *
            ((if (n : ℝ) / (2 ^ q : ℕ) < (C : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
              haar q (q + 1 - d) R.2 C) := by
                rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro A hA
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro C hC
        simp only [Nat.cast_pow, Nat.cast_ofNat]]
  exact Finset.sum_eq_zero fun n hn ↦
    not_occupied_product_lower_tail_eq_zero y q d hd R hR n (Finset.mem_range.mp hn)

private lemma normalized_haar_moment (q d i : ℕ) (hd : d ≤ q + 1) (hi : i < 2 ^ d) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)),
      ((A : ℝ) / (2 ^ (q + 2) : ℕ)) * haar q d i A =
        -((halfSize q d : ℝ) ^ 2) / (2 ^ (q + 2) : ℕ) := by
  calc
    _ = (∑ A ∈ Finset.range (2 ^ (q + 2)), (A : ℝ) * haar q d i A) /
        (2 ^ (q + 2) : ℕ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro A hA
          ring
    _ = _ := by rw [haar_moment_nat q d i hd hi]

private lemma normalized_moments_product (q d : ℕ) (hd : d ≤ q + 1)
    (R : Rect q d) :
    (∑ A ∈ Finset.range (2 ^ (q + 2)),
      ((A : ℝ) / (2 ^ (q + 2) : ℕ)) * haar q d R.1 A) *
    (∑ C ∈ Finset.range (2 ^ (q + 2)),
      ((C : ℝ) / (2 ^ (q + 2) : ℕ)) * haar q (q + 1 - d) R.2 C) = 1 / 4 := by
  have hvd : q + 1 - d ≤ q + 1 := Nat.sub_le _ _
  rw [normalized_haar_moment q d R.1 hd R.1.isLt,
    normalized_haar_moment q (q + 1 - d) R.2 hvd R.2.isLt]
  have hm := halfSize_mul_complement q d hd
  have hQ : (0 : ℝ) < (2 ^ (q + 2) : ℕ) := by positivity
  rw [pow_q_add_two]
  push_cast
  have hmR : (halfSize q d : ℝ) * (halfSize q (q + 1 - d) : ℝ) =
      (2 ^ (q + 1) : ℕ) := by exact_mod_cast hm
  field_simp
  rw [← mul_pow, hmR]
  norm_cast
  rw [pow_succ]
  ring

private lemma rawGridDisc_rectHaar_sum
    (y : ℕ → ℝ) (lam : ℝ) (q d : ℕ) (hd : d ≤ q + 1)
    (R : Rect q d) (hR : R ∈ emptyRects y q d) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      gridDiscrepancy y lam q A C * rectHaar q d R A C = -lam / 4 := by
  rw [show (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      gridDiscrepancy y lam q A C * rectHaar q d R A C) =
      (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
        gridCount y q A C * rectHaar q d R A C) - lam *
        ((∑ A ∈ Finset.range (2 ^ (q + 2)),
          ((A : ℝ) / (2 ^ (q + 2) : ℕ)) * haar q d R.1 A) *
        (∑ C ∈ Finset.range (2 ^ (q + 2)),
          ((C : ℝ) / (2 ^ (q + 2) : ℕ)) * haar q (q + 1 - d) R.2 C)) by
    simp only [gridDiscrepancy, rectHaar]
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    congr 1
    calc
      _ = lam * ∑ A ∈ Finset.range (2 ^ (q + 2)),
          ∑ C ∈ Finset.range (2 ^ (q + 2)),
            (((A : ℝ) / (2 ^ (q + 2) : ℕ)) * haar q d R.1 A) *
            (((C : ℝ) / (2 ^ (q + 2) : ℕ)) * haar q (q + 1 - d) R.2 C) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro A hA
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro C hC
              ring
      _ = _ := by
        rw [Finset.sum_mul_sum]
        ]
  rw [rawCount_rectHaar_sum_eq_zero y q d hd R hR,
    normalized_moments_product q d hd R]
  ring

private lemma rawDisc_testFunction_sum (y : ℕ → ℝ) (lam : ℝ) (q : ℕ) :
    ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      gridDiscrepancy y lam q A C * testFunction y q A C =
        -((taggedEmpty y q).card : ℝ) * lam / 4 := by
  classical
  simp only [testFunction]
  simp_rw [Finset.mul_sum]
  rw [show (∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ C ∈ Finset.range (2 ^ (q + 2)),
      ∑ T ∈ taggedEmpty y q,
        gridDiscrepancy y lam q A C * taggedHaar q T A C) =
      ∑ T ∈ taggedEmpty y q, ∑ A ∈ Finset.range (2 ^ (q + 2)),
        ∑ C ∈ Finset.range (2 ^ (q + 2)),
          gridDiscrepancy y lam q A C * taggedHaar q T A C by
    calc
      _ = ∑ A ∈ Finset.range (2 ^ (q + 2)), ∑ T ∈ taggedEmpty y q,
          ∑ C ∈ Finset.range (2 ^ (q + 2)),
            gridDiscrepancy y lam q A C * taggedHaar q T A C := by
              apply Finset.sum_congr rfl
              intro A hA
              rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]]
  rw [taggedEmpty, Finset.sum_sigma]
  simp only [taggedHaar]
  calc
    _ = ∑ d ∈ (Finset.univ : Finset (Fin (q + 2))),
        ∑ _R ∈ emptyRects y q d, -lam / 4 := by
          apply Finset.sum_congr rfl
          intro d hdmem
          apply Finset.sum_congr rfl
          intro R hR
          exact rawGridDisc_rectHaar_sum y lam q d (by omega) R hR
    _ = (∑ d ∈ (Finset.univ : Finset (Fin (q + 2))),
        ((emptyRects y q d).card : ℝ)) * (-lam / 4) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro d hd
          simp
    _ = _ := by
      rw [← Nat.cast_sum, ← Finset.card_sigma]
      ring

/-- The finite-grid form of Roth's orthogonal-function argument used for
Erdős Problem 255.  `gridCount y q A C` counts the first `2^q` points in
the anchored rectangle `[0,A/Q) × [0,C/Q)`, where `Q=2^(q+2)` and the second
coordinate of point `n` is `n/2^q`. -/
theorem finite_roth_grid (y : ℕ → ℝ) (lam B : ℝ) (q : ℕ)
    (hB0 : 0 ≤ B)
    (hB : ∀ A C, A < 2 ^ (q + 2) → C < 2 ^ (q + 2) →
      abs (gridDiscrepancy y lam q A C) ≤ B) :
    ((q + 2 : ℕ) : ℝ) * lam ^ 2 ≤
      4096 * ((2 ^ q : ℕ) : ℝ) ^ 2 * B ^ 2 := by
  classical
  let Q : ℕ := 2 ^ (q + 2)
  let M : ℕ := 2 ^ q
  let E : ℕ := (taggedEmpty y q).card
  have hMpos : (0 : ℝ) < M := by
    dsimp [M]
    positivity
  have hE_nat : (q + 2) * M ≤ E := by
    simpa [M, E] using taggedEmpty_card_ge y q
  have hE : (((q + 2) * M : ℕ) : ℝ) ≤ E := by exact_mod_cast hE_nat
  have hEpos : (0 : ℝ) < E := by
    have : 0 < (q + 2) * M := by dsimp [M]; positivity
    exact lt_of_lt_of_le (by exact_mod_cast this) hE
  have hGsquare :
      ∑ p ∈ (Finset.range Q ×ˢ Finset.range Q),
        gridDiscrepancy y lam q p.1 p.2 ^ 2 ≤ (Q : ℝ) ^ 2 * B ^ 2 := by
    calc
      _ ≤ ∑ _p ∈ (Finset.range Q ×ˢ Finset.range Q), B ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := Finset.mem_product.mp hp
        have habs := hB p.1 p.2 (by simpa [Q] using Finset.mem_range.mp hp'.1)
          (by simpa [Q] using Finset.mem_range.mp hp'.2)
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) hB0).mpr habs
      _ = (Q : ℝ) ^ 2 * B ^ 2 := by
        simp [Q, pow_two]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.range Q ×ˢ Finset.range Q)
    (fun p ↦ gridDiscrepancy y lam q p.1 p.2)
    (fun p ↦ testFunction y q p.1 p.2)
  have hpair :
      ∑ p ∈ (Finset.range Q ×ˢ Finset.range Q),
        gridDiscrepancy y lam q p.1 p.2 * testFunction y q p.1 p.2 =
          -(E : ℝ) * lam / 4 := by
    rw [Finset.sum_product]
    simpa [Q, E] using rawDisc_testFunction_sum y lam q
  have hFnorm :
      ∑ p ∈ (Finset.range Q ×ˢ Finset.range Q),
        testFunction y q p.1 p.2 ^ 2 = (E : ℝ) * (8 * M) := by
    rw [Finset.sum_product]
    simpa [Q, M, E] using testFunction_sq_sum y q
  rw [hpair, hFnorm] at hCS
  have hQeq : (Q : ℝ) = 4 * M := by
    dsimp [Q, M]
    rw [pow_q_add_two]
    norm_cast
  have hcore : (E : ℝ) * ((E : ℝ) * lam ^ 2) ≤
      (E : ℝ) * (2048 * (M : ℝ) ^ 3 * B ^ 2) := by
    calc
      (E : ℝ) * ((E : ℝ) * lam ^ 2) = 16 * (-(E : ℝ) * lam / 4) ^ 2 := by ring
      _ ≤ 16 * (((Q : ℝ) ^ 2 * B ^ 2) * ((E : ℝ) * (8 * M))) := by
        gcongr
        exact hCS.trans (mul_le_mul_of_nonneg_right hGsquare (by positivity))
      _ = (E : ℝ) * (2048 * (M : ℝ) ^ 3 * B ^ 2) := by rw [hQeq]; ring
  have hcancel : (E : ℝ) * lam ^ 2 ≤ 2048 * (M : ℝ) ^ 3 * B ^ 2 :=
    (mul_le_mul_iff_of_pos_left hEpos).mp hcore
  have hlower : (((q + 2) * M : ℕ) : ℝ) * lam ^ 2 ≤ (E : ℝ) * lam ^ 2 :=
    mul_le_mul_of_nonneg_right hE (sq_nonneg lam)
  have hpre : ((q + 2 : ℕ) : ℝ) * lam ^ 2 ≤
      2048 * (M : ℝ) ^ 2 * B ^ 2 := by
    apply (mul_le_mul_iff_of_pos_left hMpos).mp
    calc
      (M : ℝ) * (((q + 2 : ℕ) : ℝ) * lam ^ 2) =
          (((q + 2) * M : ℕ) : ℝ) * lam ^ 2 := by push_cast; ring
      _ ≤ (E : ℝ) * lam ^ 2 := hlower
      _ ≤ 2048 * (M : ℝ) ^ 3 * B ^ 2 := hcancel
      _ = (M : ℝ) * (2048 * (M : ℝ) ^ 2 * B ^ 2) := by ring
  calc
    ((q + 2 : ℕ) : ℝ) * lam ^ 2 ≤ 2048 * (M : ℝ) ^ 2 * B ^ 2 := hpre
    _ ≤ 4096 * (M : ℝ) ^ 2 * B ^ 2 := by
      have hnon : 0 ≤ (M : ℝ) ^ 2 * B ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      nlinarith
    _ = 4096 * ((2 ^ q : ℕ) : ℝ) ^ 2 * B ^ 2 := by rfl

end


end Erdos255
