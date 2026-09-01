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

import ErdosProblems.Erdos255.FiniteRoth

open Filter Finset Set
open scoped BigOperators

namespace Erdos255

noncomputable section

private def timeCut (C : ℕ) : ℕ := (C + 3) / 4

private lemma pow_q_add_two' (q : ℕ) : 2 ^ (q + 2) = 4 * 2 ^ q := by
  rw [pow_add]
  norm_num
  ring

private lemma time_lt_iff (q C n : ℕ) :
    (n : ℝ) / (2 ^ q : ℕ) < (C : ℝ) / (2 ^ (q + 2) : ℕ) ↔ n < timeCut C := by
  have hM : (0 : ℝ) < (2 ^ q : ℕ) := by positivity
  have hQ : (0 : ℝ) < (2 ^ (q + 2) : ℕ) := by positivity
  rw [div_lt_div_iff₀ hM hQ]
  norm_cast
  rw [pow_q_add_two']
  have hp : 0 < 2 ^ q := by positivity
  constructor
  · intro h
    have : 4 * n < C := by
      apply (Nat.mul_lt_mul_right hp).mp
      nlinarith
    simp only [timeCut]
    omega
  · intro h
    have hfour : 4 * n < C := by
      simp only [timeCut] at h
      omega
    calc
      n * (4 * 2 ^ q) = (4 * n) * 2 ^ q := by ring
      _ < C * 2 ^ q := (Nat.mul_lt_mul_right hp).mpr hfour

private lemma timeCut_le (q C : ℕ) (hC : C < 2 ^ (q + 2)) : timeCut C ≤ 2 ^ q := by
  rw [pow_q_add_two'] at hC
  simp only [timeCut]
  omega

private lemma timeCut_error (q C : ℕ) :
    |(timeCut C : ℝ) - (((2 ^ q : ℕ) : ℝ) *
      ((C : ℝ) / ((2 ^ (q + 2) : ℕ) : ℝ)))| ≤ 1 := by
  rw [pow_q_add_two']
  have heq : (((2 ^ q : ℕ) : ℝ) *
      ((C : ℝ) / ((4 * 2 ^ q : ℕ) : ℝ))) = C / 4 := by
    push_cast
    field_simp
  rw [show (((2 ^ q : ℕ) : ℝ) *
      ((C : ℝ) / ((4 * 2 ^ q : ℕ) : ℝ))) = C / 4 from heq]
  simp only [timeCut]
  have hlo : (C : ℝ) / 4 ≤ ((C + 3) / 4 : ℕ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    norm_cast
    omega
  have hhi : (((C + 3) / 4 : ℕ) : ℝ) ≤ (C : ℝ) / 4 + 1 := by
    have hn : ((C + 3) / 4) * 4 ≤ C + 4 := by omega
    have hr : ((((C + 3) / 4) * 4 : ℕ) : ℝ) ≤ C + 4 := by exact_mod_cast hn
    push_cast at hr
    linarith
  rw [abs_le]
  constructor <;> linarith

private lemma gridCount_eq_prefixCount (y : ℕ → ℝ)
    (hy : ∀ n, y n ∈ Ico (0 : ℝ) 1) (q A C : ℕ) (hC : C < 2 ^ (q + 2)) :
    gridCount y q A C = prefixCount y (timeCut C) ((A : ℝ) / (2 ^ (q + 2) : ℕ)) := by
  have hK := timeCut_le q C hC
  rw [gridCount]
  have hcast : (prefixCount y (timeCut C) ((A : ℝ) / (2 ^ (q + 2) : ℕ)) : ℝ) =
      ∑ n ∈ range (timeCut C),
        if y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then (1 : ℝ) else 0 := by
    rw [sum_boole]
    simp [prefixCount]
  rw [hcast]
  calc
    ∑ n ∈ range (2 ^ q),
        (if 0 ≤ y n ∧ y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then 1 else 0) *
        (if (n : ℝ) / (2 ^ q : ℕ) < (C : ℝ) / (2 ^ (q + 2) : ℕ)
          then 1 else 0) =
      ∑ n ∈ range (2 ^ q), if n < timeCut C then
        (if y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then (1 : ℝ) else 0) else 0 := by
      apply sum_congr rfl
      intro n hn
      simp only [time_lt_iff]
      have hyn := (hy n).1
      split_ifs <;> simp_all
      linarith
    _ = ∑ n ∈ range (timeCut C), if n < timeCut C then
        (if y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then (1 : ℝ) else 0) else 0 := by
      symm
      apply sum_subset
      · intro n hn
        simp only [Finset.mem_range] at hn ⊢
        omega
      · intro n hnM hnK
        simp only [Finset.mem_range] at hnM hnK
        simp [hnK]
    _ = ∑ n ∈ range (timeCut C),
        if y n < (A : ℝ) / (2 ^ (q + 2) : ℕ) then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro n hn
      simp only [Finset.mem_range] at hn
      simp [hn]

private lemma gridDiscrepancy_eq (y : ℕ → ℝ)
    (hy : ∀ n, y n ∈ Ico (0 : ℝ) 1) (q A C : ℕ) (hC : C < 2 ^ (q + 2)) :
    gridDiscrepancy y (2 ^ q : ℕ) q A C =
      starDisc y (timeCut C) ((A : ℝ) / (2 ^ (q + 2) : ℕ)) +
        ((timeCut C : ℝ) - ((2 ^ q : ℕ) : ℝ) *
          ((C : ℝ) / (2 ^ (q + 2) : ℕ))) *
          ((A : ℝ) / (2 ^ (q + 2) : ℕ)) := by
  rw [gridDiscrepancy, gridCount_eq_prefixCount y hy q A C hC]
  unfold starDisc
  ring

private lemma gridDiscrepancy_abs_le (y : ℕ → ℝ)
    (hy : ∀ n, y n ∈ Ico (0 : ℝ) 1) (B : ℝ)
    (hB : ∀ N u, u ∈ Icc (0 : ℝ) 1 → |starDisc y N u| ≤ B)
    (q A C : ℕ) (hA : A < 2 ^ (q + 2)) (hC : C < 2 ^ (q + 2)) :
    |gridDiscrepancy y (2 ^ q : ℕ) q A C| ≤ B + 1 := by
  have hQ : (0 : ℝ) < (2 ^ (q + 2) : ℕ) := by positivity
  let u : ℝ := (A : ℝ) / (2 ^ (q + 2) : ℕ)
  have hu : u ∈ Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [u]; positivity
    · dsimp [u]
      apply (div_le_one hQ).mpr
      exact_mod_cast hA.le
  rw [gridDiscrepancy_eq y hy q A C hC]
  calc
    |starDisc y (timeCut C) u +
        ((timeCut C : ℝ) - ((2 ^ q : ℕ) : ℝ) *
          ((C : ℝ) / (2 ^ (q + 2) : ℕ))) * u| ≤
      |starDisc y (timeCut C) u| +
        |((timeCut C : ℝ) - ((2 ^ q : ℕ) : ℝ) *
          ((C : ℝ) / (2 ^ (q + 2) : ℕ))) * u| := abs_add_le _ _
    _ ≤ B + 1 := by
      rw [abs_mul]
      have he := timeCut_error q C
      have huabs : |u| ≤ 1 := by rw [abs_of_nonneg hu.1]; exact hu.2
      nlinarith [hB (timeCut C) u hu, abs_nonneg u]

/-- No sequence in `[0,1)` has uniformly bounded anchored discrepancy. -/
theorem no_uniform_star_discrepancy (y : ℕ → ℝ)
    (hy : ∀ n, y n ∈ Ico (0 : ℝ) 1) (B : ℝ) :
    ∃ N : ℕ, ∃ u ∈ Icc (0 : ℝ) 1, B < |starDisc y N u| := by
  by_cases hBneg : B < 0
  · exact ⟨0, 0, by simp, by simpa [starDisc, prefixCount] using hBneg⟩
  have hB0 : 0 ≤ B := le_of_not_gt hBneg
  by_contra hlarge
  push Not at hlarge
  obtain ⟨q, hq⟩ := exists_nat_gt (4096 * (B + 1) ^ 2)
  let M : ℝ := (2 ^ q : ℕ)
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hroth := finite_roth_grid y M (B + 1) q (by linarith)
    (fun A C hA hC ↦ gridDiscrepancy_abs_le y hy B hlarge q A C hA hC)
  have hcancel : ((q + 2 : ℕ) : ℝ) ≤ 4096 * (B + 1) ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hMpos)).mp
    calc
      ((q + 2 : ℕ) : ℝ) * M ^ 2 ≤ 4096 * ((2 ^ q : ℕ) : ℝ) ^ 2 * (B + 1) ^ 2 := hroth
      _ = (4096 * (B + 1) ^ 2) * M ^ 2 := by dsimp [M]; ring
  have hqR : 4096 * (B + 1) ^ 2 < (q : ℝ) := hq
  norm_num [Nat.cast_add, Nat.cast_ofNat] at hcancel
  linarith

end
end Erdos255
