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

import ErdosProblems.Erdos1165.FourierReturn
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Finite potential-kernel estimates for planar simple random walk

For a lattice point `x`, this file defines the exact finite-word probability
`pₙ(x)` and the even-skeleton potential truncation

`aᴱ_m(x) = ∑_{k=0}^m (p_{2k}(0) - p_{2k}(x))`.

Everything below is finite and combinatorial.  We prove that a word of length
`N` cannot reach a point of `ℓ¹`-norm larger than `N`, identify `p_{2k}(0)`
with the exact central-binomial formula, and prove two uniform estimates:

* `aᴱ_m(x) ≤ 1 + log (m+1)` for every `x`;
* `(1/4) log (m+1) ≤ aᴱ_m(x)` whenever `2m < ‖x‖₁`.

Thus the finite potential already has logarithmic order at every scale lying
strictly below the distance to the target.  Passing from these finite
estimates to the classical infinite potential kernel, and obtaining the
sharp asymptotic `(2/π) log |x| + O(|x|⁻²)`, additionally requires an
off-diagonal local central limit/Fourier estimate and convergence of the
potential series.  Those analytic facts are not postulated here.
-/

open scoped BigOperators

namespace Erdos1165
namespace PotentialKernel

/-! ## Endpoint probabilities and finite propagation -/

/-- The taxicab (`ℓ¹`) norm on the integer lattice. -/
def manhattanNorm (x : Point) : ℕ := x.1.natAbs + x.2.natAbs

@[simp] lemma manhattanNorm_zero : manhattanNorm (0 : Point) = 0 := by
  rfl

@[simp] lemma manhattanNorm_eq_zero_iff (x : Point) :
    manhattanNorm x = 0 ↔ x = 0 := by
  rcases x with ⟨a, b⟩
  simp [manhattanNorm, Prod.ext_iff]

@[simp] lemma manhattanNorm_directionVector (d : Direction) :
    manhattanNorm (directionVector d) = 1 := by
  fin_cases d <;> rfl

/-- A word of `N` nearest-neighbour steps has endpoint of taxicab norm at
most `N`. -/
theorem manhattanNorm_blockDisplacement_le {N : ℕ} (u : Fin N → Direction) :
    manhattanNorm (blockDisplacement u) ≤ N := by
  have hfst := Int.natAbs_sum_le Finset.univ
    (fun i : Fin N ↦ (directionVector (u i)).1)
  have hsnd := Int.natAbs_sum_le Finset.univ
    (fun i : Fin N ↦ (directionVector (u i)).2)
  rw [blockDisplacement]
  unfold manhattanNorm
  rw [Prod.fst_sum, Prod.snd_sum]
  calc
    (∑ i : Fin N, (directionVector (u i)).1).natAbs +
          (∑ i : Fin N, (directionVector (u i)).2).natAbs ≤
        (∑ i : Fin N, (directionVector (u i)).1.natAbs) +
          ∑ i : Fin N, (directionVector (u i)).2.natAbs :=
      Nat.add_le_add hfst hsnd
    _ = ∑ i : Fin N, manhattanNorm (directionVector (u i)) := by
      rw [← Finset.sum_add_distrib]
      rfl
    _ = N := by simp

/-- The finite set of length-`N` increment words ending at `x`. -/
def endpointBlocks (N : ℕ) (x : Point) : Finset (Fin N → Direction) :=
  Finset.univ.filter fun u ↦ blockDisplacement u = x

@[simp] lemma mem_endpointBlocks {N : ℕ} {x : Point} {u : Fin N → Direction} :
    u ∈ endpointBlocks N x ↔ blockDisplacement u = x := by
  simp [endpointBlocks]

/-- Exact real-valued endpoint probability, defined by finite counting. -/
noncomputable def endpointProbability (N : ℕ) (x : Point) : ℝ :=
  (endpointBlocks N x).card / (4 : ℝ) ^ N

lemma endpointProbability_nonneg (N : ℕ) (x : Point) :
    0 ≤ endpointProbability N x := by
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

theorem endpointBlocks_eq_empty_of_lt {N : ℕ} {x : Point}
    (hN : N < manhattanNorm x) : endpointBlocks N x = ∅ := by
  ext u
  constructor
  · intro hu
    have hreach := manhattanNorm_blockDisplacement_le u
    rw [mem_endpointBlocks] at hu
    rw [hu] at hreach
    omega
  · intro hu
    simp at hu

theorem endpointProbability_eq_zero_of_lt {N : ℕ} {x : Point}
    (hN : N < manhattanNorm x) : endpointProbability N x = 0 := by
  rw [endpointProbability, endpointBlocks_eq_empty_of_lt hN]
  simp

/-! ## The return probability on the even skeleton -/

theorem card_endpointBlocks_even_zero (n : ℕ) :
    (endpointBlocks (2 * n) 0).card = Nat.centralBinom n ^ 2 := by
  rw [← card_returning_blocks n]
  let e : ↥(endpointBlocks (2 * n) 0) ≃
      {u : Fin (2 * n) → Direction // blockDisplacement u = 0} :=
    { toFun := fun u ↦ ⟨u.1, (mem_endpointBlocks.mp u.2)⟩
      invFun := fun u ↦ ⟨u.1, mem_endpointBlocks.mpr u.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    (endpointBlocks (2 * n) 0).card =
        Fintype.card ↥(endpointBlocks (2 * n) 0) := (Fintype.card_coe _).symm
    _ = Fintype.card {u : Fin (2 * n) → Direction // blockDisplacement u = 0} :=
      Fintype.card_congr e

theorem endpointProbability_even_zero (n : ℕ) :
    endpointProbability (2 * n) 0 = planarReturnProbability n := by
  rw [endpointProbability, card_endpointBlocks_even_zero]
  simp only [Nat.cast_pow]
  rw [show (4 : ℝ) ^ (2 * n) = 16 ^ n by
    calc
      (4 : ℝ) ^ (2 * n) = ((4 : ℝ) ^ 2) ^ n := by rw [pow_mul]
      _ = 16 ^ n := by norm_num]
  rfl

/-- A matching elementary upper bound for the exact return probability.  The
proof uses only the central-binomial recurrence. -/
theorem planarReturnProbability_upper_bound (n : ℕ) :
    planarReturnProbability n ≤ 1 / (n + 1 : ℝ) := by
  induction n with
  | zero => norm_num [planarReturnProbability, Nat.centralBinom]
  | succ n ih =>
      have hrec := Nat.succ_mul_centralBinom_succ n
      unfold planarReturnProbability at ih ⊢
      have hrecR : ((n + 1 : ℕ) : ℝ) * Nat.centralBinom (n + 1) =
          2 * (2 * n + 1) * Nat.centralBinom n := by
        exact_mod_cast hrec
      have hc : (Nat.centralBinom (n + 1) : ℝ) =
          2 * (2 * n + 1) * Nat.centralBinom n / (n + 1) := by
        apply (eq_div_iff (by positivity : (n + 1 : ℝ) ≠ 0)).2
        norm_num only [Nat.cast_add, Nat.cast_one] at hrecR ⊢
        simpa [mul_comm] using hrecR
      have hprobRec :
          (Nat.centralBinom (n + 1) : ℝ) ^ 2 / 16 ^ (n + 1) =
            ((Nat.centralBinom n : ℝ) ^ 2 / 16 ^ n) *
              ((2 * n + 1 : ℝ) / (2 * (n + 1))) ^ 2 := by
        rw [hc, pow_succ]
        field_simp
        ring
      have hratio :
          (1 / (n + 1 : ℝ)) * ((2 * n + 1 : ℝ) / (2 * (n + 1))) ^ 2 ≤
            1 / (n + 2 : ℝ) := by
        field_simp
        nlinarith
      rw [hprobRec]
      have hfinal := (mul_le_mul_of_nonneg_right ih (sq_nonneg _)).trans hratio
      norm_num only [Nat.cast_add, Nat.cast_one] at hfinal ⊢
      ring_nf at hfinal ⊢
      exact hfinal

/-! ## The finite even-skeleton potential kernel -/

/-- Potential-kernel truncation for the aperiodic two-step skeleton. -/
noncomputable def evenPotentialTrunc (m : ℕ) (x : Point) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (endpointProbability (2 * k) 0 - endpointProbability (2 * k) x)

theorem evenPotentialTrunc_eq_return_sum_of_lt {m : ℕ} {x : Point}
    (hmx : 2 * m < manhattanNorm x) :
    evenPotentialTrunc m x =
      ∑ k ∈ Finset.range (m + 1), planarReturnProbability k := by
  rw [evenPotentialTrunc]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hkx : 2 * k < manhattanNorm x := lt_of_le_of_lt (Nat.mul_le_mul_left 2 hkm) hmx
  rw [endpointProbability_eq_zero_of_lt hkx, sub_zero, endpointProbability_even_zero]

theorem evenPotentialTrunc_upper_bound (m : ℕ) (x : Point) :
    evenPotentialTrunc m x ≤ 1 + Real.log (m + 1 : ℝ) := by
  calc
    evenPotentialTrunc m x ≤
        ∑ k ∈ Finset.range (m + 1), planarReturnProbability k := by
      rw [evenPotentialTrunc]
      apply Finset.sum_le_sum
      intro k hk
      rw [endpointProbability_even_zero]
      linarith [endpointProbability_nonneg (2 * k) x]
    _ ≤ ∑ k ∈ Finset.range (m + 1), (1 / (k + 1 : ℝ)) := by
      exact Finset.sum_le_sum fun k _ ↦ planarReturnProbability_upper_bound k
    _ = (harmonic (m + 1) : ℝ) := by
      simp [harmonic, one_div]
    _ ≤ 1 + Real.log (m + 1 : ℝ) := by
      exact_mod_cast harmonic_le_one_add_log (m + 1)

theorem evenPotentialTrunc_log_lower_bound {m : ℕ} {x : Point}
    (hmx : 2 * m < manhattanNorm x) :
    (1 / 4 : ℝ) * Real.log (m + 1 : ℝ) ≤ evenPotentialTrunc m x := by
  rw [evenPotentialTrunc_eq_return_sum_of_lt hmx]
  calc
    (1 / 4 : ℝ) * Real.log (m + 1 : ℝ) ≤
        (1 / 4 : ℝ) * (harmonic m : ℝ) := by
      gcongr
      exact_mod_cast log_add_one_le_harmonic m
    _ = ∑ k ∈ Finset.Icc 1 m, (1 / (4 * k : ℝ)) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      field_simp
    _ ≤ ∑ k ∈ Finset.Icc 1 m, planarReturnProbability k := by
      apply Finset.sum_le_sum
      intro k hk
      exact planarReturnProbability_lower_bound (Finset.mem_Icc.mp hk).1
    _ ≤ ∑ k ∈ Finset.range (m + 1), planarReturnProbability k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2
      · intro k _ _
        exact (planarReturnProbability_pos k).le

theorem evenPotentialTrunc_two_sided {m : ℕ} {x : Point}
    (hmx : 2 * m < manhattanNorm x) :
    (1 / 4 : ℝ) * Real.log (m + 1 : ℝ) ≤ evenPotentialTrunc m x ∧
      evenPotentialTrunc m x ≤ 1 + Real.log (m + 1 : ℝ) :=
  ⟨evenPotentialTrunc_log_lower_bound hmx, evenPotentialTrunc_upper_bound m x⟩

/-- Radial form of the logarithmic estimate.  The truncation is chosen at the
largest even time strictly below the taxicab distance to `x`. -/
theorem evenPotentialTrunc_radial_two_sided {x : Point} (hx : x ≠ 0) :
    let m := (manhattanNorm x - 1) / 2
    (1 / 4 : ℝ) * Real.log ((manhattanNorm x : ℝ) / 2) ≤
        evenPotentialTrunc m x ∧
      evenPotentialTrunc m x ≤ 1 + Real.log (manhattanNorm x : ℝ) := by
  let d := manhattanNorm x
  let m := (d - 1) / 2
  have hd : 0 < d := Nat.pos_of_ne_zero fun hd0 ↦ hx (manhattanNorm_eq_zero_iff x |>.mp hd0)
  have hmd : 2 * m < d := by
    dsimp [m]
    omega
  have hdm : d ≤ 2 * (m + 1) := by
    dsimp [m]
    omega
  have hmd' : m + 1 ≤ d := by
    dsimp [m]
    omega
  have hscaleLower : (d : ℝ) / 2 ≤ (m + 1 : ℕ) := by
    have hdmR : (d : ℝ) ≤ 2 * (m + 1 : ℕ) := by exact_mod_cast hdm
    linarith
  have hscaleUpper : ((m + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hmd'
  have hlowerLog : Real.log ((d : ℝ) / 2) ≤ Real.log (m + 1 : ℕ) :=
    Real.log_le_log (by positivity) hscaleLower
  have hupperLog : Real.log (m + 1 : ℕ) ≤ Real.log (d : ℝ) :=
    Real.log_le_log (by positivity) hscaleUpper
  dsimp only
  constructor
  · calc
      (1 / 4 : ℝ) * Real.log ((manhattanNorm x : ℝ) / 2) ≤
          (1 / 4 : ℝ) * Real.log (m + 1 : ℕ) := by
        dsimp [d] at hlowerLog
        gcongr
      _ ≤ evenPotentialTrunc m x := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          evenPotentialTrunc_log_lower_bound hmd
  · exact (evenPotentialTrunc_upper_bound m x).trans (by
      dsimp [d] at hupperLog
      norm_num only [Nat.cast_add, Nat.cast_one] at hupperLog
      linarith)

end PotentialKernel
end Erdos1165
