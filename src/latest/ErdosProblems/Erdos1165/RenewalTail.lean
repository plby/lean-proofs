/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.RenewalBound

/-!
# Finite renewal and tail bounds

This file isolates a deterministic estimate used in renewal arguments.  Let
`f k` be the mass of a first return at time `k`, let `u k` be the mass of a
return at time `k`, and put

`q n = ∑ k ∈ Icc 1 n, f k`,  `G n = ∑ k ≤ n, u k`.

For an exact renewal sequence, positivity and a finite reindexing of the
renewal identity give

`q n * G n ≤ G (2 * n) - 1`.

The second part of the file records the purely analytic consequence for any
nonnegative multiplier `q`: a one-step tail recursion
`T (r + 1) n ≤ q n * T r n` iterates to a power bound.  Combining the two
facts yields an explicit Green-ratio estimate without any probability-space
assumptions.
-/

open scoped BigOperators
open Finset

namespace Erdos1165.RenewalTail

/-- First-return mass accumulated through time `n`, excluding time zero. -/
def firstReturnMass (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, f k

/-- The truncated Green function through time `n`, including time zero. -/
def truncatedGreen (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), u k

lemma firstReturnMass_nonneg {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) (n : ℕ) :
    0 ≤ firstReturnMass f n := by
  exact Finset.sum_nonneg fun k _ ↦ hf k

lemma truncatedGreen_nonneg {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) (n : ℕ) :
    0 ≤ truncatedGreen u n := by
  exact Finset.sum_nonneg fun k _ ↦ hu k

lemma one_le_truncatedGreen {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k)
    (hu_zero : u 0 = 1) (n : ℕ) :
    1 ≤ truncatedGreen u n := by
  rw [truncatedGreen, Finset.sum_range_succ']
  rw [hu_zero]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun k _ ↦ hu (k + 1))

lemma sum_Icc_one_eq_truncatedGreen_sub (u : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, u k) = truncatedGreen u N - u 0 := by
  cases N with
  | zero => simp [truncatedGreen]
  | succ N =>
      rw [Erdos1165.sum_Icc_one_succ_eq_sum_range]
      rw [truncatedGreen]
      have hgreen := Finset.sum_range_succ' u (N + 1)
      rw [hgreen]
      ring

/-! ## The finite renewal rectangle -/

private def renewalTriangle (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 N).biUnion Finset.HasAntidiagonal.antidiagonal

private lemma antidiagonal_pairwiseDisjoint (N : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.Icc 1 N) : Set ℕ)
      Finset.HasAntidiagonal.antidiagonal := by
  intro i hi j hj hij
  change Disjoint (Finset.HasAntidiagonal.antidiagonal i)
    (Finset.HasAntidiagonal.antidiagonal j)
  rw [Finset.disjoint_left]
  intro p hpi hpj
  apply hij
  exact (Finset.HasAntidiagonal.mem_antidiagonal.mp hpi).symm.trans
    (Finset.HasAntidiagonal.mem_antidiagonal.mp hpj)

private lemma rectangle_subset_renewalTriangle (n : ℕ) :
    Finset.Icc 1 n ×ˢ Finset.range (n + 1) ⊆ renewalTriangle (2 * n) := by
  intro p hp
  rw [Finset.mem_product] at hp
  rcases hp with ⟨hk, hj⟩
  have hk' := Finset.mem_Icc.mp hk
  have hjlt := Finset.mem_range.mp hj
  have hj' : p.2 ≤ n := by omega
  rw [renewalTriangle, Finset.mem_biUnion]
  refine ⟨p.1 + p.2, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    omega
  · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl

/-- Range-indexed exact renewal identities imply the finite Green bound.

The range formulation includes `k = 0`; this is useful for abstract renewal
sequences in which the convention at zero has already been absorbed into
the recurrence.  `firstReturnMass_mul_truncatedGreen_le` below gives the
customary first-return formulation. -/
theorem firstReturnMass_mul_truncatedGreen_le_of_range
    (f u : ℕ → ℝ)
    (hf_nonneg : ∀ k, 0 ≤ f k)
    (hu_nonneg : ∀ k, 0 ≤ u k)
    (hu_zero : u 0 = 1)
    (hrenew : ∀ m, 0 < m →
      u m = ∑ k ∈ Finset.range (m + 1), f k * u (m - k))
    (n : ℕ) :
    firstReturnMass f n * truncatedGreen u n ≤ truncatedGreen u (2 * n) - 1 := by
  calc
    firstReturnMass f n * truncatedGreen u n =
        ∑ p ∈ Finset.Icc 1 n ×ˢ Finset.range (n + 1), f p.1 * u p.2 := by
      rw [firstReturnMass, truncatedGreen, Finset.sum_mul_sum, Finset.sum_product]
    _ ≤ ∑ p ∈ renewalTriangle (2 * n), f p.1 * u p.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (rectangle_subset_renewalTriangle n)
      intro p hp hnot
      exact mul_nonneg (hf_nonneg p.1) (hu_nonneg p.2)
    _ = ∑ m ∈ Finset.Icc 1 (2 * n), u m := by
      rw [renewalTriangle,
        Finset.sum_biUnion (antidiagonal_pairwiseDisjoint (2 * n))]
      apply Finset.sum_congr rfl
      intro m hm
      calc
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, f p.1 * u p.2) =
            ∑ k ∈ Finset.range (m + 1), f k * u (m - k) :=
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun k j ↦ f k * u j) m
        _ = u m := (hrenew m (Finset.mem_Icc.mp hm).1).symm
    _ = truncatedGreen u (2 * n) - 1 := by
      rw [sum_Icc_one_eq_truncatedGreen_sub, hu_zero]

/-- Exact first-return renewal identities imply
`q n * G n ≤ G (2n) - 1`.

Here `f 0 = 0` is the standard convention for the first-return law, and the
renewal identity is indexed by `Icc 1 m`. -/
theorem firstReturnMass_mul_truncatedGreen_le
    (f u : ℕ → ℝ)
    (hf_nonneg : ∀ k, 0 ≤ f k)
    (hu_nonneg : ∀ k, 0 ≤ u k)
    (hf_zero : f 0 = 0)
    (hu_zero : u 0 = 1)
    (hrenew : ∀ m, 0 < m →
      u m = ∑ k ∈ Finset.Icc 1 m, f k * u (m - k))
    (n : ℕ) :
    firstReturnMass f n * truncatedGreen u n ≤ truncatedGreen u (2 * n) - 1 := by
  apply firstReturnMass_mul_truncatedGreen_le_of_range f u hf_nonneg hu_nonneg hu_zero
  intro m hm
  rw [hrenew m hm]
  have hrange : Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
    ext k
    simp
    omega
  rw [hrange, Finset.sum_insert]
  · simp [hf_zero]
  · simp

/-! ## Iterating a recursive tail inequality -/

/-- A nonnegative one-step multiplier iterates for an arbitrary number of
additional levels. -/
theorem tail_add_le_pow_mul
    (q : ℕ → ℝ) (T : ℕ → ℕ → ℝ)
    (hq_nonneg : ∀ n, 0 ≤ q n)
    (hstep : ∀ r n, T (r + 1) n ≤ q n * T r n)
    (r s n : ℕ) :
    T (r + s) n ≤ (q n) ^ s * T r n := by
  induction s with
  | zero => simp
  | succ s ih =>
      calc
        T (r + (s + 1)) n = T ((r + s) + 1) n := by rw [Nat.add_assoc]
        _ ≤ q n * T (r + s) n := hstep (r + s) n
        _ ≤ q n * ((q n) ^ s * T r n) :=
          mul_le_mul_of_nonneg_left ih (hq_nonneg n)
        _ = (q n) ^ (s + 1) * T r n := by ring

/-- If level zero has mass at most one, the recursive tail is bounded by the
corresponding power of its one-step multiplier. -/
theorem tail_le_pow
    (q : ℕ → ℝ) (T : ℕ → ℕ → ℝ)
    (hq_nonneg : ∀ n, 0 ≤ q n)
    (hzero : ∀ n, T 0 n ≤ 1)
    (hstep : ∀ r n, T (r + 1) n ≤ q n * T r n)
    (r n : ℕ) :
    T r n ≤ (q n) ^ r := by
  calc
    T r n = T (0 + r) n := by simp
    _ ≤ (q n) ^ r * T 0 n := tail_add_le_pow_mul q T hq_nonneg hstep 0 r n
    _ ≤ (q n) ^ r * 1 :=
      mul_le_mul_of_nonneg_left (hzero n) (pow_nonneg (hq_nonneg n) r)
    _ = (q n) ^ r := mul_one _

/-- The finite renewal estimate turns a recursive tail into an explicit
power of a truncated-Green ratio. -/
theorem tail_le_greenRatio_pow
    (f u : ℕ → ℝ) (T : ℕ → ℕ → ℝ)
    (hf_nonneg : ∀ k, 0 ≤ f k)
    (hu_nonneg : ∀ k, 0 ≤ u k)
    (hf_zero : f 0 = 0)
    (hu_zero : u 0 = 1)
    (hrenew : ∀ m, 0 < m →
      u m = ∑ k ∈ Finset.Icc 1 m, f k * u (m - k))
    (hzero : ∀ n, T 0 n ≤ 1)
    (hstep : ∀ r n,
      T (r + 1) n ≤ firstReturnMass f n * T r n)
    (r n : ℕ) :
    T r n ≤
      ((truncatedGreen u (2 * n) - 1) / truncatedGreen u n) ^ r := by
  have hGpos : 0 < truncatedGreen u n :=
    lt_of_lt_of_le zero_lt_one (one_le_truncatedGreen hu_nonneg hu_zero n)
  have hq_nonneg : 0 ≤ firstReturnMass f n :=
    firstReturnMass_nonneg hf_nonneg n
  have hq_le : firstReturnMass f n ≤
      (truncatedGreen u (2 * n) - 1) / truncatedGreen u n := by
    rw [le_div_iff₀ hGpos]
    exact firstReturnMass_mul_truncatedGreen_le f u hf_nonneg hu_nonneg hf_zero
      hu_zero hrenew n
  exact (tail_le_pow (firstReturnMass f) T
    (firstReturnMass_nonneg hf_nonneg) hzero hstep r n).trans
      (pow_le_pow_left₀ hq_nonneg hq_le r)

end Erdos1165.RenewalTail
