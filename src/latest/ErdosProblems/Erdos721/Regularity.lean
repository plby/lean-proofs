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

import ErdosProblems.Erdos721.Cardinality

/-!
# A fixed-scale regularization lemma for cyclic Bohr sets

For the density-increment argument it is enough to select a center scale and
one perturbation scale at which the outer and inner Bohr sets have comparable
cardinality.  This file obtains such a scale by combining the
radius-independent `9^rank` doubling estimate with a finite telescoping
argument.
-/

namespace Erdos721

open Finset
open scoped BigOperators

namespace CyclicBohr

/-- A numerical inequality used in the regularization pigeonhole argument. -/
lemma nine_mul_ten_pow_hundred_lt_eleven_pow_hundred :
    9 * 10 ^ 100 < 11 ^ 100 := by norm_num

/-- Parameterized numerical input for arbitrarily fine regularity grids. -/
lemma nine_mul_ten_mul_pow_lt_succ_pow (m : ℕ) (hm : 0 < m) :
    9 * (10 * m) ^ (100 * m) < (10 * m + 1) ^ (100 * m) := by
  have hmR : (0 : ℝ) < 10 * m := by positivity
  have hbern := one_add_mul_le_pow (R := ℝ)
    (a := (10 * (m : ℝ))⁻¹) (by
      have : 0 ≤ (10 * (m : ℝ))⁻¹ := by positivity
      linarith) (100 * m)
  have hratio : (9 : ℝ) <
      (1 + (10 * (m : ℝ))⁻¹) ^ (100 * m) := by
    calc
      (9 : ℝ) < 11 := by norm_num
      _ = 1 + (100 * (m : ℝ)) * (10 * (m : ℝ))⁻¹ := by
        field_simp
        ring
      _ ≤ (1 + (10 * (m : ℝ))⁻¹) ^ (100 * m) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbern
  have hcast :
      (9 : ℝ) * (10 * (m : ℝ)) ^ (100 * m) <
        (10 * (m : ℝ) + 1) ^ (100 * m) := by
    rw [show 10 * (m : ℝ) + 1 =
      (10 * (m : ℝ)) * (1 + (10 * (m : ℝ))⁻¹) by field_simp]
    calc
      9 * (10 * (m : ℝ)) ^ (100 * m) <
          (10 * (m : ℝ)) ^ (100 * m) *
            (1 + (10 * (m : ℝ))⁻¹) ^ (100 * m) := by
        simpa only [mul_comm] using
          mul_lt_mul_of_pos_left hratio (pow_pos hmR (100 * m))
      _ = ((10 * (m : ℝ)) *
            (1 + (10 * (m : ℝ))⁻¹)) ^ (100 * m) := by
        exact (mul_pow (10 * (m : ℝ))
          (1 + (10 * (m : ℝ))⁻¹) (100 * m)).symm
  exact_mod_cast hcast

/-- Fine-grid form of the adjacent-ratio pigeonhole lemma. -/
lemma exists_controlled_adjacent_ratio_fine
    (a : ℕ → ℕ) {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (ha0 : 0 < a 0)
    (hend : a (100 * m * d) ≤ 9 ^ d * a 0) :
    ∃ j < 100 * m * d,
      (10 * m) * a (j + 1) ≤ (10 * m + 1) * a j := by
  by_contra h
  push_neg at h
  have hgrowth : ∀ j ≤ 100 * m * d,
      (10 * m + 1) ^ j * a 0 ≤ (10 * m) ^ j * a j := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
        have hj' : j ≤ 100 * m * d := Nat.le_trans (Nat.le_succ j) hj
        have hstep : (10 * m + 1) * a j < (10 * m) * a (j + 1) := by
          exact h j (Nat.lt_of_succ_le hj)
        calc
          (10 * m + 1) ^ (j + 1) * a 0 =
              (10 * m + 1) * ((10 * m + 1) ^ j * a 0) := by
            rw [pow_succ]
            ring
          _ ≤ (10 * m + 1) * ((10 * m) ^ j * a j) :=
            Nat.mul_le_mul_left _ (ih hj')
          _ ≤ (10 * m) ^ j * ((10 * m) * a (j + 1)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (Nat.mul_lt_mul_of_pos_left hstep
                (pow_pos (by positivity : 0 < 10 * m) j)).le
          _ = (10 * m) ^ (j + 1) * a (j + 1) := by
            rw [pow_succ]
            ring
  let L := 100 * m * d
  have hL : 0 < L := by simp [L, hm, hd]
  have hstepLast := h (L - 1) (by omega)
  have hLstep : L - 1 + 1 = L := by omega
  have hprev := hgrowth (L - 1) (by omega)
  have hstrict : (10 * m + 1) ^ L * a 0 <
      (10 * m) ^ L * a L := by
    calc
      (10 * m + 1) ^ L * a 0 =
          (10 * m + 1) * ((10 * m + 1) ^ (L - 1) * a 0) := by
        conv_lhs => rw [← hLstep, pow_succ]
        ring
      _ ≤ (10 * m + 1) * ((10 * m) ^ (L - 1) * a (L - 1)) :=
        Nat.mul_le_mul_left _ hprev
      _ < (10 * m) ^ (L - 1) * ((10 * m) * a L) := by
        have hs : (10 * m + 1) * a (L - 1) < (10 * m) * a L := by
          simpa [hLstep] using hstepLast
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          Nat.mul_lt_mul_of_pos_left hs
            (pow_pos (by positivity : 0 < 10 * m) (L - 1))
      _ = (10 * m) ^ L * a L := by
        have hpow : (10 * m) ^ L =
            (10 * m) ^ (L - 1) * (10 * m) := by
          conv_lhs => rw [← hLstep, pow_succ]
        rw [hpow]
        ring
  have hupper : (10 * m) ^ L * a L ≤
      ((10 * m) ^ L * 9 ^ d) * a 0 := by
    calc
      (10 * m) ^ L * a L ≤ (10 * m) ^ L * (9 ^ d * a 0) :=
        Nat.mul_le_mul_left _ hend
      _ = ((10 * m) ^ L * 9 ^ d) * a 0 := by ring
  have hbase : (10 * m) ^ L * 9 ^ d < (10 * m + 1) ^ L := by
    calc
      (10 * m) ^ L * 9 ^ d =
          (9 * (10 * m) ^ (100 * m)) ^ d := by
        simp only [L, mul_pow, pow_mul]
        ring
      _ < ((10 * m + 1) ^ (100 * m)) ^ d :=
        pow_lt_pow_left₀ (nine_mul_ten_mul_pow_lt_succ_pow m hm)
          (by positivity) hd.ne'
      _ = (10 * m + 1) ^ L := by simp [L, pow_mul]
  have hcontr : (10 * m + 1) ^ L * a 0 <
      (10 * m + 1) ^ L * a 0 :=
    hstrict.trans_le (hupper.trans (Nat.mul_le_mul_right (a 0) hbase.le))
  exact (lt_irrefl _ hcontr)

/-- If a positive sequence grows by an endpoint factor at most `9^d` over
`100d` steps, one adjacent ratio is at most `11/10`. -/
lemma exists_controlled_adjacent_ratio
    (a : ℕ → ℕ) {d : ℕ} (hd : 0 < d) (ha0 : 0 < a 0)
    (hend : a (100 * d) ≤ 9 ^ d * a 0) :
    ∃ j < 100 * d, 10 * a (j + 1) ≤ 11 * a j := by
  by_contra h
  push_neg at h
  have hgrowth : ∀ j ≤ 100 * d,
      11 ^ j * a 0 ≤ 10 ^ j * a j := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
        have hj' : j ≤ 100 * d := Nat.le_trans (Nat.le_succ j) hj
        have hstep : 11 * a j < 10 * a (j + 1) := by
          have := h j (Nat.lt_of_succ_le hj)
          omega
        calc
          11 ^ (j + 1) * a 0 = 11 * (11 ^ j * a 0) := by
            rw [pow_succ]
            ring
          _ ≤ 11 * (10 ^ j * a j) := Nat.mul_le_mul_left 11 (ih hj')
          _ ≤ 10 ^ j * (10 * a (j + 1)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (Nat.mul_lt_mul_of_pos_left hstep
                (pow_pos (by norm_num : (0 : ℕ) < 10) j)).le
          _ = 10 ^ (j + 1) * a (j + 1) := by
            rw [pow_succ]
            ring
  have hstrict : 11 ^ (100 * d) * a 0 <
      10 ^ (100 * d) * a (100 * d) := by
    have hlast := h (100 * d - 1) (by omega)
    have hdstep : 100 * d - 1 + 1 = 100 * d := by omega
    have hprev := hgrowth (100 * d - 1) (by omega)
    calc
      11 ^ (100 * d) * a 0 =
          11 * (11 ^ (100 * d - 1) * a 0) := by
        conv_lhs => rw [← hdstep, pow_succ]
        ring
      _ ≤ 11 * (10 ^ (100 * d - 1) * a (100 * d - 1)) :=
        Nat.mul_le_mul_left 11 hprev
      _ < 10 ^ (100 * d - 1) * (10 * a (100 * d)) := by
        have hs : 11 * a (100 * d - 1) < 10 * a (100 * d) := by
          simpa [hdstep] using hlast
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          Nat.mul_lt_mul_of_pos_left hs
            (pow_pos (by norm_num : (0 : ℕ) < 10) (100 * d - 1))
      _ = 10 ^ (100 * d) * a (100 * d) := by
        have hpowstep : 10 ^ (100 * d) =
            10 ^ (100 * d - 1) * 10 := by
          conv_lhs => rw [← hdstep, pow_succ]
        rw [hpowstep]
        ring
  have hupper : 10 ^ (100 * d) * a (100 * d) ≤
      (10 ^ (100 * d) * 9 ^ d) * a 0 := by
    calc
      10 ^ (100 * d) * a (100 * d) ≤
          10 ^ (100 * d) * (9 ^ d * a 0) :=
        Nat.mul_le_mul_left _ hend
      _ = (10 ^ (100 * d) * 9 ^ d) * a 0 := by ring
  have hbase : 10 ^ (100 * d) * 9 ^ d < 11 ^ (100 * d) := by
    calc
      10 ^ (100 * d) * 9 ^ d = (9 * 10 ^ 100) ^ d := by
        rw [mul_pow, pow_mul]
        ring
      _ < (11 ^ 100) ^ d :=
        pow_lt_pow_left₀ nine_mul_ten_pow_hundred_lt_eleven_pow_hundred
          (by positivity) hd.ne'
      _ = 11 ^ (100 * d) := by rw [pow_mul]
  have hcontr : 11 ^ (100 * d) * a 0 <
      11 ^ (100 * d) * a 0 := by
    exact hstrict.trans_le (hupper.trans (Nat.mul_le_mul_right (a 0) hbase.le))
  exact (lt_irrefl _ hcontr)

section BohrGrid

variable {N : ℕ} [NeZero N]

/-- The evenly spaced grid from `1/2` to `1`. -/
noncomputable def regularityGrid (L j : ℕ) : ℝ :=
  1 / 2 + (j : ℝ) / (2 * L)

lemma regularityGrid_zero (L : ℕ) : regularityGrid L 0 = 1 / 2 := by
  simp [regularityGrid]

lemma regularityGrid_self {L : ℕ} (hL : 0 < L) : regularityGrid L L = 1 := by
  unfold regularityGrid
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  field_simp
  ring

lemma regularityGrid_nonneg (L j : ℕ) : 0 ≤ regularityGrid L j := by
  unfold regularityGrid
  positivity

lemma carrier_dilate_one (B : Set N) : (B.dilate 1).carrier = B.carrier := by
  ext x
  simp only [Set.mem_carrier, Set.frequencies_dilate, Set.radius_dilate]
  norm_num

/-- A Bohr set of positive rank has an adjacent pair of grid dilates whose
cardinalities differ by a factor at most `11/10`. -/
theorem exists_controlled_grid_step (B : Set N) (hB : 0 < B.radius)
    (hrank : 0 < B.rank) :
    ∃ j < 100 * B.rank,
      10 * (B.dilate (regularityGrid (100 * B.rank) (j + 1))).carrier.card ≤
        11 * (B.dilate (regularityGrid (100 * B.rank) j)).carrier.card := by
  let L := 100 * B.rank
  let a : ℕ → ℕ := fun j ↦ (B.dilate (regularityGrid L j)).carrier.card
  have hL : 0 < L := by simp [L, hrank]
  have ha0 : 0 < a 0 := Set.card_pos _
  have hend : a L ≤ 9 ^ B.rank * a 0 := by
    have hdoubling := card_carrier_le_nine_pow_rank_mul_card_half B hB
    have htop : a L = B.carrier.card := by
      dsimp only [a]
      rw [show regularityGrid L L = 1 from regularityGrid_self hL]
      exact congrArg Finset.card (carrier_dilate_one B)
    have hbottom : a 0 = (B.dilate (1 / 2 : ℝ)).carrier.card := by
      dsimp only [a]
      rw [regularityGrid_zero]
    simpa [htop, hbottom] using hdoubling
  simpa [L, a] using
    exists_controlled_adjacent_ratio a hrank ha0 hend

/-- Fixed-scale regularization in centered form. -/
theorem exists_fixed_regular_scale (B : Set N) (hB : 0 < B.radius)
    (hrank : 0 < B.rank) :
    ∃ t δ : ℝ,
      1 / 2 ≤ t ∧ t ≤ 1 ∧ 0 < δ ∧ δ < t ∧
      10 * (B.dilate (t + δ)).carrier.card ≤
        11 * (B.dilate (t - δ)).carrier.card := by
  obtain ⟨j, hj, hcard⟩ := exists_controlled_grid_step B hB hrank
  let L := 100 * B.rank
  let u := regularityGrid L j
  let v := regularityGrid L (j + 1)
  let t := (u + v) / 2
  let δ := (v - u) / 2
  have hL : (0 : ℝ) < L := by
    exact_mod_cast (by simp [L, hrank] : 0 < L)
  have hjR : (j : ℝ) < L := by exact_mod_cast hj
  have huv : 0 < v - u := by
    dsimp only [u, v, regularityGrid]
    rw [sub_pos]
    gcongr
    exact_mod_cast Nat.lt_succ_self j
  have hu : 1 / 2 ≤ u := by
    dsimp only [u, regularityGrid]
    exact le_add_of_nonneg_right (div_nonneg (by positivity) (by positivity))
  have hv : v ≤ 1 := by
    dsimp only [v, regularityGrid]
    have hjone : (j + 1 : ℝ) ≤ L := by exact_mod_cast hj
    have hden : (0 : ℝ) < 2 * L := by positivity
    have hfrac : (j + 1 : ℝ) / (2 * L) ≤ 1 / 2 := by
      rw [div_le_iff₀ hden]
      nlinarith
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith
  refine ⟨t, δ, ?_, ?_, (div_pos huv (by norm_num)), ?_, ?_⟩
  · dsimp only [t, δ]
    linarith
  · dsimp only [t, δ]
    linarith
  · dsimp only [t, δ]
    linarith
  · have htplus : t + δ = v := by dsimp only [t, δ]; ring
    have htminus : t - δ = u := by dsimp only [t, δ]; ring
    rw [htplus, htminus]
    simpa [L, u, v] using hcard

/-- Quantitative fixed-scale regularization.  The perturbation scale selected
by the grid argument is exactly the reciprocal of `400 * rank`. -/
theorem exists_fixed_regular_scale_quantitative (B : Set N) (hB : 0 < B.radius)
    (hrank : 0 < B.rank) :
    ∃ t δ : ℝ,
      1 / 2 ≤ t ∧ t ≤ 1 ∧
      δ = (400 * (B.rank : ℝ))⁻¹ ∧
      0 < δ ∧ δ < t ∧
      10 * (B.dilate (t + δ)).carrier.card ≤
        11 * (B.dilate (t - δ)).carrier.card := by
  obtain ⟨j, hj, hcard⟩ := exists_controlled_grid_step B hB hrank
  let L := 100 * B.rank
  let u := regularityGrid L j
  let v := regularityGrid L (j + 1)
  let t := (u + v) / 2
  let δ := (v - u) / 2
  have hLnat : 0 < L := by simp [L, hrank]
  have hL : (0 : ℝ) < L := by exact_mod_cast hLnat
  have hjR : (j : ℝ) < L := by exact_mod_cast hj
  have huv : 0 < v - u := by
    dsimp only [u, v, regularityGrid]
    rw [sub_pos]
    gcongr
    exact_mod_cast Nat.lt_succ_self j
  have hu : 1 / 2 ≤ u := by
    dsimp only [u, regularityGrid]
    exact le_add_of_nonneg_right (div_nonneg (by positivity) (by positivity))
  have hv : v ≤ 1 := by
    dsimp only [v, regularityGrid]
    have hjone : (j + 1 : ℝ) ≤ L := by exact_mod_cast hj
    have hden : (0 : ℝ) < 2 * L := by positivity
    have hfrac : (j + 1 : ℝ) / (2 * L) ≤ 1 / 2 := by
      rw [div_le_iff₀ hden]
      nlinarith
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith
  have hδformula : δ = (400 * (B.rank : ℝ))⁻¹ := by
    dsimp only [δ, u, v, regularityGrid, L]
    have hrankR : (0 : ℝ) < B.rank := by exact_mod_cast hrank
    field_simp
    norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  refine ⟨t, δ, ?_, ?_, hδformula, (div_pos huv (by norm_num)), ?_, ?_⟩
  · dsimp only [t, δ]
    linarith
  · dsimp only [t, δ]
    linarith
  · dsimp only [t, δ]
    linarith
  · have htplus : t + δ = v := by dsimp only [t, δ]; ring
    have htminus : t - δ = u := by dsimp only [t, δ]; ring
    rw [htplus, htminus]
    simpa [L, u, v] using hcard

/-- An arbitrarily fine controlled grid step.  Increasing `m` replaces the
fixed factor `11/10` by `1 + 1/(10m)`. -/
theorem exists_controlled_grid_step_fine (B : Set N) (m : ℕ)
    (hB : 0 < B.radius) (hrank : 0 < B.rank) (hm : 0 < m) :
    ∃ j < 100 * m * B.rank,
      (10 * m) *
          (B.dilate (regularityGrid (100 * m * B.rank) (j + 1))).carrier.card ≤
        (10 * m + 1) *
          (B.dilate (regularityGrid (100 * m * B.rank) j)).carrier.card := by
  let L := 100 * m * B.rank
  let a : ℕ → ℕ := fun j ↦ (B.dilate (regularityGrid L j)).carrier.card
  have hL : 0 < L := by simp [L, hm, hrank]
  have ha0 : 0 < a 0 := Set.card_pos _
  have hend : a L ≤ 9 ^ B.rank * a 0 := by
    have hdoubling := card_carrier_le_nine_pow_rank_mul_card_half B hB
    have htop : a L = B.carrier.card := by
      dsimp only [a]
      rw [show regularityGrid L L = 1 from regularityGrid_self hL]
      exact congrArg Finset.card (carrier_dilate_one B)
    have hbottom : a 0 = (B.dilate (1 / 2 : ℝ)).carrier.card := by
      dsimp only [a]
      rw [regularityGrid_zero]
    simpa [htop, hbottom] using hdoubling
  simpa [L, a] using
    exists_controlled_adjacent_ratio_fine a hrank hm ha0 hend

/-- Fine quantitative regularization.  The selected perturbation has width
`(400*m*rank)⁻¹` and adjacent carrier ratio at most `1 + 1/(10m)`. -/
theorem exists_fixed_regular_scale_fine (B : Set N) (m : ℕ)
    (hB : 0 < B.radius) (hrank : 0 < B.rank) (hm : 0 < m) :
    ∃ t δ : ℝ,
      1 / 2 ≤ t ∧ t ≤ 1 ∧
      δ = (400 * (m : ℝ) * (B.rank : ℝ))⁻¹ ∧
      0 < δ ∧ δ < t ∧
      (10 * m) * (B.dilate (t + δ)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - δ)).carrier.card := by
  obtain ⟨j, hj, hcard⟩ := exists_controlled_grid_step_fine B m hB hrank hm
  let L := 100 * m * B.rank
  let u := regularityGrid L j
  let v := regularityGrid L (j + 1)
  let t := (u + v) / 2
  let δ := (v - u) / 2
  have hLnat : 0 < L := by simp [L, hm, hrank]
  have hL : (0 : ℝ) < L := by exact_mod_cast hLnat
  have hjR : (j : ℝ) < L := by exact_mod_cast hj
  have huv : 0 < v - u := by
    dsimp only [u, v, regularityGrid]
    rw [sub_pos]
    gcongr
    exact_mod_cast Nat.lt_succ_self j
  have hu : 1 / 2 ≤ u := by
    dsimp only [u, regularityGrid]
    exact le_add_of_nonneg_right (div_nonneg (by positivity) (by positivity))
  have hv : v ≤ 1 := by
    dsimp only [v, regularityGrid]
    have hjone : (j + 1 : ℝ) ≤ L := by exact_mod_cast hj
    have hden : (0 : ℝ) < 2 * L := by positivity
    have hfrac : (j + 1 : ℝ) / (2 * L) ≤ 1 / 2 := by
      rw [div_le_iff₀ hden]
      nlinarith
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith
  have hδformula : δ = (400 * (m : ℝ) * (B.rank : ℝ))⁻¹ := by
    dsimp only [δ, u, v, regularityGrid, L]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hrankR : (0 : ℝ) < B.rank := by exact_mod_cast hrank
    field_simp
    norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  refine ⟨t, δ, ?_, ?_, hδformula, (div_pos huv (by norm_num)), ?_, ?_⟩
  · dsimp only [t, δ]
    linarith
  · dsimp only [t, δ]
    linarith
  · dsimp only [t, δ]
    linarith
  · have htplus : t + δ = v := by dsimp only [t, δ]; ring
    have htminus : t - δ = u := by dsimp only [t, δ]; ring
    rw [htplus, htminus]
    simpa [L, u, v] using hcard

end BohrGrid

end CyclicBohr
end Erdos721
