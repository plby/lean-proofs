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

import ErdosProblems.Erdos1165.Basic

/-!
# Finite killed Green functions

This file isolates the algebraic part of the Green-function argument used for
planar simple random walk.  A discrete-time kernel is represented by its
matrix of one-step weights.  Killing on a finite set makes every convolution
a finite sum, even when the ambient state space is infinite.

We prove Chapman--Kolmogorov, the two finite resolvent identities, and the
finite first-entrance/last-exit decomposition.  No recurrence, local central
limit theorem, potential-kernel asymptotic, or limiting interchange is used.
The final section instantiates the definitions with the four-neighbour planar
simple-random-walk kernel.
-/

open scoped BigOperators ENNReal

namespace Erdos1165
namespace GreenFunction

/-! ## Finite-state killing for a matrix kernel -/

variable {State R : Type*} [DecidableEq State] [CommSemiring R]

/-- The mass of the length-`n` paths from `x` to `y` which stay in `A` at
all times, for a one-step weight matrix `κ`.  The state space need not be
finite: all intermediate states are summed over the finite killing set `A`. -/
def killedPower (κ : State → State → R) (A : Finset State) :
    ℕ → State → State → R
  | 0, x, y => if x ∈ A ∧ x = y then 1 else 0
  | n + 1, x, y =>
      if x ∈ A then ∑ z ∈ A, κ x z * killedPower κ A n z y else 0

@[simp] theorem killedPower_zero (κ : State → State → R) (A : Finset State)
    (x y : State) :
    killedPower κ A 0 x y = if x ∈ A ∧ x = y then 1 else 0 := by
  rfl

theorem killedPower_succ (κ : State → State → R) (A : Finset State)
    (n : ℕ) (x y : State) :
    killedPower κ A (n + 1) x y =
      if x ∈ A then ∑ z ∈ A, κ x z * killedPower κ A n z y else 0 := by
  rfl

@[simp] theorem killedPower_eq_zero_of_notMem_left (κ : State → State → R)
    (A : Finset State) {x : State} (hx : x ∉ A) (n : ℕ) (y : State) :
    killedPower κ A n x y = 0 := by
  cases n <;> simp [killedPower, hx]

@[simp] theorem killedPower_eq_zero_of_notMem_right (κ : State → State → R)
    (A : Finset State) {y : State} (hy : y ∉ A) (n : ℕ) (x : State) :
    killedPower κ A n x y = 0 := by
  induction n generalizing x with
  | zero =>
      by_cases hxy : x = y
      · subst x
        simp [killedPower, hy]
      · simp [killedPower, hxy]
  | succ n ih => simp [killedPower, ih]

@[simp] theorem killedPower_zero_self (κ : State → State → R) (A : Finset State)
    {x : State} (hx : x ∈ A) : killedPower κ A 0 x x = 1 := by
  simp [killedPower, hx]

@[simp] theorem killedPower_zero_ne (κ : State → State → R) (A : Finset State)
    {x y : State} (hxy : x ≠ y) : killedPower κ A 0 x y = 0 := by
  simp [killedPower, hxy]

/-- Chapman--Kolmogorov for the killed powers. -/
theorem killedPower_add (κ : State → State → R) (A : Finset State)
    (m n : ℕ) (x y : State) :
    killedPower κ A (m + n) x y =
      ∑ z ∈ A, killedPower κ A m x z * killedPower κ A n z y := by
  induction m generalizing x with
  | zero =>
      by_cases hx : x ∈ A
      · simp [killedPower, hx]
      · simp [killedPower, hx]
  | succ m ih =>
      rw [Nat.succ_add, killedPower_succ]
      by_cases hx : x ∈ A
      · rw [if_pos hx]
        have hstep (z : State) :
            killedPower κ A (m + 1) x z =
              ∑ w ∈ A, κ x w * killedPower κ A m w z := by
          rw [killedPower_succ, if_pos hx]
        simp_rw [ih]
        simp_rw [Finset.mul_sum]
        simp_rw [hstep]
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro w hw
        ac_rfl
      · simp [hx, killedPower_eq_zero_of_notMem_left]

/-- The killed one-step matrix is the original matrix with both endpoints
restricted to `A`. -/
theorem killedPower_one (κ : State → State → R) (A : Finset State)
    (x y : State) :
    killedPower κ A 1 x y =
      if x ∈ A ∧ y ∈ A then κ x y else 0 := by
  by_cases hx : x ∈ A
  · by_cases hy : y ∈ A
    · rw [killedPower_succ, if_pos hx, if_pos ⟨hx, hy⟩]
      rw [Finset.sum_eq_single y]
      · simp [hy]
      · intro z hz hzy
        simp [killedPower, hzy]
      · exact fun h ↦ (h hy).elim
    · simp [hy, killedPower_eq_zero_of_notMem_right]
  · simp [hx, killedPower_eq_zero_of_notMem_left]

/-- The right-hand Chapman--Kolmogorov recursion. -/
theorem killedPower_succ_right (κ : State → State → R) (A : Finset State)
    (n : ℕ) (x y : State) :
    killedPower κ A (n + 1) x y =
      if y ∈ A then ∑ z ∈ A, killedPower κ A n x z * κ z y else 0 := by
  rw [show n + 1 = n + 1 by rfl, killedPower_add]
  by_cases hy : y ∈ A
  · rw [if_pos hy]
    apply Finset.sum_congr rfl
    intro z hz
    simp [killedPower_one, hy, hz]
  · simp [hy, killedPower_eq_zero_of_notMem_right]

/-- The finite-horizon Green function, including time `0`. -/
def finiteGreen (κ : State → State → R) (A : Finset State)
    (N : ℕ) (x y : State) : R :=
  ∑ n ∈ Finset.range (N + 1), killedPower κ A n x y

@[simp] theorem finiteGreen_zero (κ : State → State → R) (A : Finset State)
    (x y : State) :
    finiteGreen κ A 0 x y = killedPower κ A 0 x y := by
  simp [finiteGreen]

theorem finiteGreen_succ (κ : State → State → R) (A : Finset State)
    (N : ℕ) (x y : State) :
    finiteGreen κ A (N + 1) x y =
      finiteGreen κ A N x y + killedPower κ A (N + 1) x y := by
  simp [finiteGreen, Finset.sum_range_succ]

/-- Left finite resolvent identity: `G_(N+1) = I + K G_N`. -/
theorem finiteGreen_succ_left (κ : State → State → R) (A : Finset State)
    (N : ℕ) (x y : State) :
    finiteGreen κ A (N + 1) x y =
      killedPower κ A 0 x y +
        if x ∈ A then ∑ z ∈ A, κ x z * finiteGreen κ A N z y else 0 := by
  rw [finiteGreen]
  rw [show N + 1 + 1 = (N + 1) + 1 by omega, Finset.sum_range_succ']
  rw [add_comm]
  congr 1
  simp only [finiteGreen, killedPower_succ]
  by_cases hx : x ∈ A
  · simp only [if_pos hx]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  · simp [hx]

/-- Right finite resolvent identity: `G_(N+1) = I + G_N K`. -/
theorem finiteGreen_succ_right (κ : State → State → R) (A : Finset State)
    (N : ℕ) (x y : State) :
    finiteGreen κ A (N + 1) x y =
      killedPower κ A 0 x y +
        if y ∈ A then ∑ z ∈ A, finiteGreen κ A N x z * κ z y else 0 := by
  rw [finiteGreen]
  rw [show N + 1 + 1 = (N + 1) + 1 by omega, Finset.sum_range_succ']
  rw [add_comm]
  congr 1
  simp only [finiteGreen]
  simp_rw [killedPower_succ_right]
  by_cases hy : y ∈ A
  · simp only [if_pos hy]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  · simp [hy]

/-! ## First entrance and the finite last-exit identity -/

/-- Weight of paths whose first visit to `y` occurs exactly at time `n`,
with every state through that time in `A`. -/
def firstHitWeight (κ : State → State → R) (A : Finset State) (y : State) :
    ℕ → State → R
  | 0, x => if x ∈ A ∧ x = y then 1 else 0
  | n + 1, x =>
      if x ∈ A ∧ x ≠ y then
        ∑ z ∈ A, κ x z * firstHitWeight κ A y n z
      else 0

@[simp] theorem firstHitWeight_zero (κ : State → State → R) (A : Finset State)
    (x y : State) :
    firstHitWeight κ A y 0 x = if x ∈ A ∧ x = y then 1 else 0 := by
  rfl

theorem firstHitWeight_succ (κ : State → State → R) (A : Finset State)
    (n : ℕ) (x y : State) :
    firstHitWeight κ A y (n + 1) x =
      if x ∈ A ∧ x ≠ y then
        ∑ z ∈ A, κ x z * firstHitWeight κ A y n z
      else 0 := by
  rfl

@[simp] theorem firstHitWeight_target_succ (κ : State → State → R)
    (A : Finset State) (n : ℕ) (y : State) :
    firstHitWeight κ A y (n + 1) y = 0 := by
  simp [firstHitWeight]

@[simp] theorem firstHitWeight_eq_zero_of_notMem (κ : State → State → R)
    (A : Finset State) {x : State} (hx : x ∉ A) (n : ℕ) (y : State) :
    firstHitWeight κ A y n x = 0 := by
  cases n <;> simp [firstHitWeight, hx]

/-- Renewal at the first visit to `y`, at one fixed time.  This is the
finite, purely algebraic Markov identity underlying the usual last-exit
formula. -/
theorem killedPower_eq_sum_firstHitWeight (κ : State → State → R)
    (A : Finset State) (n : ℕ) (x y : State) :
    killedPower κ A n x y =
      ∑ k ∈ Finset.range (n + 1),
        firstHitWeight κ A y k x * killedPower κ A (n - k) y y := by
  induction n generalizing x with
  | zero =>
      by_cases hxy : x = y
      · subst x
        by_cases hy : y ∈ A <;> simp [killedPower, firstHitWeight, hy]
      · simp [killedPower, firstHitWeight, hxy]
  | succ n ih =>
      by_cases hxy : x = y
      · subst x
        by_cases hy : y ∈ A
        · rw [Finset.sum_range_succ']
          simp [firstHitWeight, hy]
        · simp [hy, killedPower_eq_zero_of_notMem_left]
      · rw [killedPower_succ]
        by_cases hx : x ∈ A
        · rw [if_pos hx]
          simp_rw [ih]
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          conv_rhs => rw [Finset.sum_range_succ']
          simp only [firstHitWeight_succ, if_pos (And.intro hx hxy),
            Nat.succ_sub_succ_eq_sub, firstHitWeight_zero,
            if_neg (not_and_of_not_right _ hxy), zero_mul, add_zero]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro z hz
          ac_rfl
        · simp [hx, firstHitWeight_eq_zero_of_notMem]

/-- Finite first-entrance/last-exit decomposition of the killed Green
function.  The remaining factor is the Green function started afresh from
the hit point. -/
theorem finiteGreen_eq_sum_firstHitWeight (κ : State → State → R)
    (A : Finset State) (N : ℕ) (x y : State) :
    finiteGreen κ A N x y =
      ∑ k ∈ Finset.range (N + 1),
        firstHitWeight κ A y k x * finiteGreen κ A (N - k) y y := by
  induction N with
  | zero =>
      by_cases hxy : x = y
      · subst x
        by_cases hy : y ∈ A <;> simp [finiteGreen, hy]
      · simp [finiteGreen, hxy]
  | succ N ih =>
      rw [finiteGreen_succ, ih, killedPower_eq_sum_firstHitWeight]
      have hpower :
          (∑ k ∈ Finset.range (N + 1 + 1),
              firstHitWeight κ A y k x * killedPower κ A (N + 1 - k) y y) =
            (∑ k ∈ Finset.range (N + 1),
              firstHitWeight κ A y k x * killedPower κ A (N + 1 - k) y y) +
              firstHitWeight κ A y (N + 1) x *
                killedPower κ A (N + 1 - (N + 1)) y y := by
        exact Finset.sum_range_succ _ (N + 1)
      rw [hpower]
      have hout :
          (∑ k ∈ Finset.range (N + 1 + 1),
              firstHitWeight κ A y k x * finiteGreen κ A (N + 1 - k) y y) =
            (∑ k ∈ Finset.range (N + 1),
              firstHitWeight κ A y k x * finiteGreen κ A (N + 1 - k) y y) +
              firstHitWeight κ A y (N + 1) x *
                finiteGreen κ A (N + 1 - (N + 1)) y y := by
        exact Finset.sum_range_succ _ (N + 1)
      rw [hout]
      calc
        (∑ k ∈ Finset.range (N + 1),
              firstHitWeight κ A y k x * finiteGreen κ A (N - k) y y) +
              ((∑ k ∈ Finset.range (N + 1),
                firstHitWeight κ A y k x * killedPower κ A (N + 1 - k) y y) +
                firstHitWeight κ A y (N + 1) x *
                  killedPower κ A (N + 1 - (N + 1)) y y) =
            (∑ k ∈ Finset.range (N + 1),
              (firstHitWeight κ A y k x * finiteGreen κ A (N - k) y y +
                firstHitWeight κ A y k x * killedPower κ A (N + 1 - k) y y)) +
                firstHitWeight κ A y (N + 1) x *
                  killedPower κ A (N + 1 - (N + 1)) y y := by
            rw [Finset.sum_add_distrib]
            ac_rfl
        _ = (∑ k ∈ Finset.range (N + 1),
              firstHitWeight κ A y k x * finiteGreen κ A (N + 1 - k) y y) +
                firstHitWeight κ A y (N + 1) x *
                  finiteGreen κ A (N + 1 - (N + 1)) y y := by
            apply congrArg₂ (· + ·)
            · apply Finset.sum_congr rfl
              intro k hk
              have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
              rw [Nat.succ_sub hkN, finiteGreen_succ, mul_add]
            · simp [finiteGreen]

/-! ## Ordered consequences for nonnegative kernels -/

section ENNReal

variable (κ : State → State → ℝ≥0∞) (A : Finset State)

theorem killedPower_le_finiteGreen (N n : ℕ) (hn : n ≤ N) (x y : State) :
    killedPower κ A n x y ≤ finiteGreen κ A N x y := by
  rw [finiteGreen]
  exact Finset.single_le_sum
    (s := Finset.range (N + 1))
    (f := fun i ↦ killedPower κ A i x y)
    (fun _ _ ↦ by exact bot_le)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn))

theorem finiteGreen_mono {M N : ℕ} (hMN : M ≤ N) (x y : State) :
    finiteGreen κ A M x y ≤ finiteGreen κ A N x y := by
  rw [finiteGreen, finiteGreen]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hMN)) (fun _ _ _ ↦ bot_le)

/-- Total weight of hitting `y` by time `N` before being killed. -/
noncomputable def finiteHitMass (N : ℕ) (x y : State) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (N + 1), firstHitWeight κ A y k x

/-- The first-entrance decomposition bounds the Green function by hitting
mass times the full diagonal Green function.  This is the division-free form
of the standard inequality `G_A(x,y)/G_A(y,y) ≤ P_x(T_y < τ_A)`. -/
theorem finiteGreen_le_finiteHitMass_mul (N : ℕ) (x y : State) :
    finiteGreen κ A N x y ≤
      finiteHitMass κ A N x y * finiteGreen κ A N y y := by
  rw [finiteGreen_eq_sum_firstHitWeight, finiteHitMass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  gcongr
  exact finiteGreen_mono κ A (Nat.sub_le N k) y y

/-- If `y` belongs to the killing set, every post-hit Green factor contains
its time-zero visit.  Thus hitting mass is at most the Green function. -/
theorem finiteHitMass_le_finiteGreen {y : State} (hy : y ∈ A)
    (N : ℕ) (x : State) :
    finiteHitMass κ A N x y ≤ finiteGreen κ A N x y := by
  rw [finiteGreen_eq_sum_firstHitWeight, finiteHitMass]
  apply Finset.sum_le_sum
  intro k hk
  have hone : (1 : ℝ≥0∞) ≤ finiteGreen κ A (N - k) y y := by
    simpa [hy] using killedPower_le_finiteGreen κ A (N - k) 0 (Nat.zero_le _) y y
  calc
    firstHitWeight κ A y k x = firstHitWeight κ A y k x * 1 := (mul_one _).symm
    _ ≤ firstHitWeight κ A y k x * finiteGreen κ A (N - k) y y := by gcongr

end ENNReal

/-! ## Planar simple random walk -/

/-- The one-step matrix of planar simple symmetric random walk. -/
noncomputable def planarKernel (x y : Point) : ℝ≥0∞ :=
  ∑ d : Direction, if y = x + directionVector d then (4 : ℝ≥0∞)⁻¹ else 0

theorem planarKernel_eq_of_direction (x : Point) (d : Direction) :
    planarKernel x (x + directionVector d) = (4 : ℝ≥0∞)⁻¹ := by
  rw [planarKernel]
  have hinj : Function.Injective fun e : Direction ↦ x + directionVector e :=
    fun _ _ h ↦ directionVector_injective (add_left_cancel h)
  rw [Finset.sum_eq_single d]
  · simp
  · intro e _ hed
    rw [if_neg]
    intro h
    apply hed
    exact hinj h.symm
  · simp

theorem planarKernel_eq_zero_of_not_neighbor {x y : Point}
    (hxy : ∀ d : Direction, y ≠ x + directionVector d) :
    planarKernel x y = 0 := by
  simp [planarKernel, hxy]

/-- The four outgoing planar transition weights have total mass one.  This is
the finite row-normalization statement for the planar Markov kernel. -/
theorem sum_planarKernel_neighbors (x : Point) :
    ∑ d : Direction, planarKernel x (x + directionVector d) = 1 := by
  simp_rw [planarKernel_eq_of_direction]
  simpa using ENNReal.mul_inv_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0)
    (ENNReal.ofNat_ne_top : (4 : ℝ≥0∞) ≠ ⊤)

/-- Finite killed Green function for planar simple random walk in a finite
region `A`. -/
noncomputable abbrev planarFiniteGreen (A : Finset Point) (N : ℕ)
    (x y : Point) : ℝ≥0∞ :=
  finiteGreen planarKernel A N x y

/-- Exact finite last-exit bound for planar simple random walk. -/
theorem planarFiniteGreen_le_hit_mul (A : Finset Point) (N : ℕ) (x y : Point) :
    planarFiniteGreen A N x y ≤
      finiteHitMass planarKernel A N x y * planarFiniteGreen A N y y := by
  exact finiteGreen_le_finiteHitMass_mul planarKernel A N x y

end GreenFunction
end Erdos1165
