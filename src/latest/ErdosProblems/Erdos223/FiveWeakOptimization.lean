/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos223.LenzOptimization

/-!
# The dimension-five weak Lenz optimization

This file isolates the finite arithmetic in Swanepoel's optimization of
diameter-one weak Lenz configurations in dimension five.  The geometric layer
supplies either a common-pole decomposition or a disjoint-sphere
decomposition, together with the local circle and sphere bounds recorded in
the data structures below.

The source leaves the last disjoint-sphere estimate as an `O(1)` argument.
Here it is made explicit: a non-strong profile would have off-equator counts
at most three and two, giving correction at most eight.  Thus `n ≥ 18`
already suffices for this numerical layer.
-/

open Erdos223

open Erdos223

namespace Erdos223.FiveWeakOptimization

theorem turanNumber_two_add_two (n : ℕ) :
    turanNumber 2 (n + 2) = turanNumber 2 n + n + 1 := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    turanNumber_two_succ, turanNumber_two_succ]
  have hceil : ceilQuot n 2 + ceilQuot (n + 1) 2 = n + 1 := by
    unfold ceilQuot
    omega
  omega

theorem correction_le_nine
    {k₁ k₂ : ℕ} (hk₁pos : 1 ≤ k₁) (hk₁ : k₁ ≤ 3)
    (hk₂pos : 1 ≤ k₂) (hk₂ : k₂ ≤ 2) :
    3 * k₁ + 3 * k₂ ≤ k₁ * k₂ + 9 := by
  interval_cases k₁ <;> interval_cases k₂ <;> omega

theorem commonPole_both_small_impossible
    {n n₁ n₂ k₁ k₂ local₁ local₂ edges : ℕ}
    (hn : 5 ≤ n) (hsum : n₁ + n₂ + 1 = n)
    (hcount : edges + k₁ * k₂ ≤ n₁ * n₂ + local₁ + local₂)
    (hlocal₁ : local₁ ≤ n₁ + 1) (hlocal₂ : local₂ ≤ n₂ + 1)
    (hlower : turanNumber 2 n + n ≤ edges) : False := by
  have hshift : (n₁ + 1) + (n₂ + 1) = n + 1 := by omega
  have hprod := mul_le_turanNumber_two hshift
  rw [turanNumber_two_succ] at hprod
  simp only [add_mul, mul_add, one_mul] at hprod
  have hceil : ceilQuot n 2 + 1 < n := by
    unfold ceilQuot
    omega
  omega

theorem commonPole_high_branch_strong
    {n n₁ n₂ k₁ k₂ local₁ local₂ edges : ℕ}
    (hsum : n₁ + n₂ + 1 = n)
    (hcount : edges + k₁ * k₂ ≤ n₁ * n₂ + local₁ + local₂)
    (hlocal₁ : local₁ ≤ 2 * n₁) (hlocal₂ : local₂ ≤ n₂ + 1)
    (hlower : turanNumber 2 n + n ≤ edges) :
    k₁ * k₂ = 0 ∧ edges = turanNumber 2 n + n := by
  have hshift : (n₁ + 1) + (n₂ + 2) = n + 2 := by omega
  have hprod := mul_le_turanNumber_two hshift
  rw [turanNumber_two_add_two] at hprod
  simp only [add_mul, mul_add, one_mul] at hprod
  omega

theorem nonstrong_disjoint_impossible_aux
    {n m₁ m₂ k₁ k₂ local₁ local₂ edges : ℕ}
    (hn : 18 ≤ n) (hsum : m₁ + m₂ = n)
    (hk₁pos : 1 ≤ k₁) (hk₁ : k₁ ≤ 3)
    (hk₂pos : 1 ≤ k₂) (hk₂ : k₂ ≤ 2)
    (hcount : edges + k₁ * k₂ ≤ m₁ * m₂ + local₁ + local₂)
    (hlocal₁ : local₁ + 2 ≤ m₁ + 3 * k₁)
    (hlocal₂ : local₂ ≤ 1 + 3 * k₂)
    (hlower : turanNumber 2 n + n ≤ edges) : False := by
  have hcorr := correction_le_nine hk₁pos hk₁ hk₂pos hk₂
  have hedge : edges ≤ m₁ * (m₂ + 1) + 8 := by
    rw [mul_add]
    omega
  have hshift : m₁ + (m₂ + 1) = n + 1 := by omega
  have hprod := mul_le_turanNumber_two hshift
  rw [turanNumber_two_succ] at hprod
  have hceil : ceilQuot n 2 + 8 < n := by
    unfold ceilQuot
    omega
  omega

theorem disjoint_nonstrong_impossible_of_source_bounds_aux
    {n m₁ m₂ k₁ k₂ local₁ local₂ edges : ℕ}
    (hn : 18 ≤ n) (hsum : m₁ + m₂ = n)
    (hk₁pos : 1 ≤ k₁) (hk₂pos : 1 ≤ k₂)
    (hcount : edges + k₁ * k₂ ≤ m₁ * m₂ + local₁ + local₂)
    (hlocal₁coarse : local₁ + 2 ≤ 2 * m₁)
    (hlocal₂coarse : local₂ ≤ m₂)
    (hlocal₁fine : local₁ + 2 ≤ m₁ + 3 * k₁)
    (hlocal₂fine : local₂ ≤ 1 + 3 * k₂)
    (hlower : turanNumber 2 n + n ≤ edges) : False := by
  have hadd := turanNumber_two_add_two n
  have hk₂ : k₂ ≤ 2 := by
    by_contra hnot
    have hk₂three : 3 ≤ k₂ := by omega
    have hshift : (m₁ + 1) + (m₂ + 1) = n + 2 := by omega
    have hprod := mul_le_turanNumber_two hshift
    rw [hadd] at hprod
    simp only [add_mul, mul_add, one_mul, mul_one] at hprod
    have hmul : 3 * k₁ ≤ k₁ * k₂ := by nlinarith
    omega
  have hk₁ : k₁ ≤ 3 := by
    by_contra hnot
    have hk₁four : 4 ≤ k₁ := by omega
    have hshift : m₁ + (m₂ + 2) = n + 2 := by omega
    have hprod := mul_le_turanNumber_two hshift
    rw [hadd] at hprod
    rw [mul_add] at hprod
    have hmul : 4 * k₂ ≤ k₁ * k₂ := by nlinarith
    omega
  exact nonstrong_disjoint_impossible_aux hn hsum hk₁pos hk₁ hk₂pos hk₂
    hcount hlocal₁fine hlocal₂fine hlower

/-- All numerical information needed from the common-pole decomposition of
a diameter-one weak five-dimensional carrier. -/
structure CommonPoleData (n edges k₁ k₂ : ℕ) where
  n₁ : ℕ
  n₂ : ℕ
  local₁ : ℕ
  local₂ : ℕ
  card_eq : n₁ + n₂ + 1 = n
  count : edges + k₁ * k₂ ≤ n₁ * n₂ + local₁ + local₂
  local₁_coarse : local₁ ≤ 2 * n₁
  local₂_coarse : local₂ ≤ 2 * n₂
  one_local_small : local₁ ≤ n₁ + 1 ∨ local₂ ≤ n₂ + 1

/-- All numerical information needed from the disjoint-sphere decomposition.
The conditional `largeFine` fields encode that if one sphere violates the
one-edge-per-vertex bound, its complementary sphere has radius strictly
larger than `1 / sqrt 2`. -/
structure DisjointData (n edges k₁ k₂ : ℕ) where
  m₁ : ℕ
  m₂ : ℕ
  local₁ : ℕ
  local₂ : ℕ
  card_eq : m₁ + m₂ = n
  count : edges + k₁ * k₂ ≤ m₁ * m₂ + local₁ + local₂
  local₁_coarse : local₁ + 2 ≤ 2 * m₁
  local₂_coarse : local₂ + 2 ≤ 2 * m₂
  one_local_small : local₁ ≤ m₁ ∨ local₂ ≤ m₂
  local₁_fine : 0 < k₁ → local₁ + 2 ≤ m₁ + 3 * k₁
  local₂_fine : 0 < k₂ → local₂ + 2 ≤ m₂ + 3 * k₂
  local₂_largeFine : m₁ < local₁ → local₂ ≤ 1 + 3 * k₂
  local₁_largeFine : m₂ < local₂ → local₁ ≤ 1 + 3 * k₁
  off₁_pos_of_excess : m₁ < local₁ → 0 < k₁
  off₂_pos_of_excess : m₂ < local₂ → 0 < k₂

inductive WeakFiveData (n edges k₁ k₂ : ℕ) where
  | commonPole (D : CommonPoleData n edges k₁ k₂)
  | disjoint (D : DisjointData n edges k₁ k₂)

theorem commonPole_extremal_strong
    {n edges k₁ k₂ : ℕ} (hn : 5 ≤ n)
    (D : CommonPoleData n edges k₁ k₂)
    (hlower : turanNumber 2 n + n ≤ edges) :
    k₁ * k₂ = 0 ∧ edges = turanNumber 2 n + n := by
  by_cases h₁ : D.local₁ ≤ D.n₁ + 1
  · by_cases h₂ : D.local₂ ≤ D.n₂ + 1
    · exact (commonPole_both_small_impossible hn D.card_eq D.count h₁ h₂ hlower).elim
    · have h := commonPole_high_branch_strong
        (n₁ := D.n₂) (n₂ := D.n₁) (k₁ := k₂) (k₂ := k₁)
        (local₁ := D.local₂) (local₂ := D.local₁) (edges := edges)
        (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using D.card_eq)
        (by simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using D.count)
        D.local₂_coarse h₁ hlower
      simpa [Nat.mul_comm] using h
  · have h₂ : D.local₂ ≤ D.n₂ + 1 := D.one_local_small.resolve_left h₁
    exact commonPole_high_branch_strong D.card_eq D.count
      D.local₁_coarse h₂ hlower

theorem smallSphere_numeric_upper
    {n sphere circle sphereLocal circleLocal edges : ℕ}
    (hsum : sphere + circle = n)
    (hsphere : sphereLocal + 2 ≤ 2 * sphere)
    (hcircle : circleLocal ≤ 1)
    (hcount : edges ≤ sphere * circle + sphereLocal + circleLocal) :
    edges ≤ turanNumber 2 n + n := by
  have hshift : sphere + (circle + 2) = n + 2 := by omega
  have hprod := mul_le_turanNumber_two hshift
  rw [turanNumber_two_add_two] at hprod
  rw [mul_add] at hprod
  omega

theorem disjoint_extremal_strong
    {n edges k₁ k₂ : ℕ} (hn : 18 ≤ n)
    (D : DisjointData n edges k₁ k₂)
    (hlower : turanNumber 2 n + n ≤ edges) :
    k₁ * k₂ = 0 ∧ edges = turanNumber 2 n + n := by
  have hstrong : k₁ * k₂ = 0 := by
    by_contra hk
    have hk₁ : k₁ ≠ 0 := by
      intro hk₁
      simp [hk₁] at hk
    have hk₂ : k₂ ≠ 0 := by
      intro hk₂
      simp [hk₂] at hk
    have hk₁pos : 1 ≤ k₁ := Nat.one_le_iff_ne_zero.mpr hk₁
    have hk₂pos : 1 ≤ k₂ := Nat.one_le_iff_ne_zero.mpr hk₂
    by_cases h₁ : D.local₁ ≤ D.m₁
    · by_cases h₂ : D.local₂ ≤ D.m₂
      · have hprod := mul_le_turanNumber_two D.card_eq
        have hcount := D.count
        have hsum := D.card_eq
        omega
      · have h₂gt : D.m₂ < D.local₂ := lt_of_not_ge h₂
        exact disjoint_nonstrong_impossible_of_source_bounds_aux
          (n := n) (m₁ := D.m₂) (m₂ := D.m₁)
          (k₁ := k₂) (k₂ := k₁)
          (local₁ := D.local₂) (local₂ := D.local₁) (edges := edges)
          hn (by simpa [Nat.add_comm] using D.card_eq) hk₂pos hk₁pos
          (by simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using D.count)
          D.local₂_coarse h₁ (D.local₂_fine hk₂pos)
          (D.local₁_largeFine h₂gt) hlower
    · have h₁gt : D.m₁ < D.local₁ := lt_of_not_ge h₁
      have h₂ : D.local₂ ≤ D.m₂ := D.one_local_small.resolve_left h₁
      exact disjoint_nonstrong_impossible_of_source_bounds_aux hn D.card_eq
        hk₁pos hk₂pos D.count D.local₁_coarse h₂
        (D.local₁_fine hk₁pos) (D.local₂_largeFine h₁gt) hlower
  refine ⟨hstrong, le_antisymm ?_ hlower⟩
  by_cases h₁ : D.local₁ ≤ D.m₁
  · by_cases h₂ : D.local₂ ≤ D.m₂
    · have hprod := mul_le_turanNumber_two D.card_eq
      have hcount := D.count
      have hsum := D.card_eq
      omega
    · have h₂gt : D.m₂ < D.local₂ := lt_of_not_ge h₂
      have hk₂pos := D.off₂_pos_of_excess h₂gt
      have hk₁zero : k₁ = 0 := (Nat.mul_eq_zero.mp hstrong).resolve_right
        (Nat.ne_of_gt hk₂pos)
      have hcircle : D.local₁ ≤ 1 := by
        simpa [hk₁zero] using D.local₁_largeFine h₂gt
      apply smallSphere_numeric_upper (sphere := D.m₂) (circle := D.m₁)
        (sphereLocal := D.local₂) (circleLocal := D.local₁)
      · simpa [Nat.add_comm] using D.card_eq
      · exact D.local₂_coarse
      · exact hcircle
      · simpa [hstrong, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using D.count
  · have h₁gt : D.m₁ < D.local₁ := lt_of_not_ge h₁
    have hk₁pos := D.off₁_pos_of_excess h₁gt
    have hk₂zero : k₂ = 0 := (Nat.mul_eq_zero.mp hstrong).resolve_left
      (Nat.ne_of_gt hk₁pos)
    have hcircle : D.local₂ ≤ 1 := by
      simpa [hk₂zero] using D.local₂_largeFine h₁gt
    apply smallSphere_numeric_upper (sphere := D.m₁) (circle := D.m₂)
      (sphereLocal := D.local₁) (circleLocal := D.local₂)
    · exact D.card_eq
    · exact D.local₁_coarse
    · exact hcircle
    · simpa [hstrong] using D.count

/-- Complete abstract optimizer for a weak five-dimensional diameter carrier.
At `n ≥ 18`, the exact decomposition and local spherical bounds force the
off-equator defect product to vanish and force the sharp value. -/
theorem weak_five_upper
    {n edges k₁ k₂ : ℕ} (hn : 18 ≤ n)
    (D : WeakFiveData n edges k₁ k₂)
    (hlower : turanNumber 2 n + n ≤ edges) :
    k₁ * k₂ = 0 ∧ edges = turanNumber 2 n + n := by
  cases D with
  | commonPole D => exact commonPole_extremal_strong (by omega) D hlower
  | disjoint D => exact disjoint_extremal_strong hn D hlower

end Erdos223.FiveWeakOptimization
