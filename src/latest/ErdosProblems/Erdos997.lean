/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 997.
https://www.erdosproblems.com/forum/thread/997

Formalization status:
- Conditional on: maynard_tao_bft

Informal authors:
- an internal model at OpenAI
- Boris Alexeev
- Moe Putterman
- Mehtaab Sawhney
- Mark Sellke
- Gregory Valiant

Formal authors:
- Aristotle
- Pietro Monticone

URLs:
- https://www.erdosproblems.com/forum/thread/997#post-5189
- https://gist.githubusercontent.com/pitmonticone/016f2ed66b4cd1c4c4b9998095170e60/raw/b7dfc05c525ae385b5835f89f1ada721443e4305/Erdos997.lean
-/
/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import ErdosProblems.Axioms

/-!
# Erdős Problem 997: Fractional parts `{α pₙ}` are not well-distributed

The solution follows Section 4 of Alexeev–Putterman–Sawhney–Sellke–Valiant (arXiv:2603.29961),
which combines Dirichlet's approximation theorem with the Maynard–Tao theorem on consecutive primes
in arithmetic progressions (specifically the Banks–Freiberg–Turnage-Butterbaugh corollary).

## Main result

For every `α ∈ ℝ`, the sequence `{α pₙ}` of fractional parts is not well-distributed in the sense of
Hlawka–Petersen.

The Maynard–Tao–BFT theorem (a deep result not in Mathlib) is imported from
`ErdosProblems.Axioms`. Everything else is proved formally.

## References

* B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, G. Valiant,
  "Short proofs in combinatorics and number theory", Section 4,
  [arXiv:2603.29961](https://arxiv.org/abs/2603.29961) (2026).
* [Erdős Problem #997](https://www.erdosproblems.com/997).
-/
open Finset Int Nat Real

namespace Erdos997

/-! ## Core definitions -/

/-- The `n`-th prime (0-indexed). -/
noncomputable abbrev nthPrime (n : ℕ) : ℕ := nth Nat.Prime n

/-- The fractional-part sequence `n ↦ fract(α · pₙ)`. -/
noncomputable def fracSeq (α : ℝ) (n : ℕ) : ℝ := fract (α * (nthPrime n : ℝ))

/-- Number of indices `i ∈ (n, n + k]` with `x i ∈ [a, b]`. -/
noncomputable def countInIcc (x : ℕ → ℝ) (a b : ℝ) (n k : ℕ) : ℕ :=
  ((Ioc n (n + k)).filter fun i ↦ a ≤ x i ∧ x i ≤ b).card

/-- A sequence `x : ℕ → ℝ` is **well-distributed** (Hlawka–Petersen) if the
discrepancy `|count − (b−a)·k|` is `o(k)` uniformly over all starting points
`n` and subintervals `[a, b] ⊆ [0, 1]`. -/
def IsWellDistributed (x : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ n : ℕ,
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      |((countInIcc x a b n k) : ℝ) - (b - a) * (k : ℝ)| < ε * (k : ℝ)

/-- A sequence has the **clustering property** when for every `m ≥ 1` one can
find `n ∈ ℕ` and `[a, b] ⊆ [0, 1]` of width `≤ 1/4` with at least half the
terms `x(n+1), …, x(n+m)` inside `[a, b]`. -/
def HasClustering (x : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 0 < m → ∃ n : ℕ, ∃ a b : ℝ,
    0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ b - a ≤ 1 / 4 ∧
      (m : ℝ) / 2 ≤ (countInIcc x a b n m : ℝ)

/-! ## Step 1: Clustering ⟹ non-well-distribution -/

/-- The clustering property with parameter `1/4` forces discrepancy `≥ k/4`
for arbitrarily large `k`, contradicting well-distribution. -/
theorem not_wellDistributed_of_clustering {x : ℕ → ℝ} (hc : HasClustering x) :
    ¬IsWellDistributed x := by
  intro h
  obtain ⟨K, hK⟩ := h (1 / 4) (by norm_num)
  obtain ⟨n, a, b, ha, hb, hab, h₁, h₂⟩ := hc (K + 1) (succ_pos _)
  specialize hK (K + 1) (by linarith) n a b ha hb hab
  norm_num at *
  nlinarith [abs_lt.mp hK]

/-! ## Step 3: Helper lemmas for the clustering proof -/

/-
Circle-clustering: using `maynardTaoBFT`, for any `α` and `m ≥ 1`, there exist `m` consecutive
primes (starting at index `r+1`) whose fractional parts `{αp}` are pairwise within `1/8` on `ℝ/ℤ`.
-/
theorem circleCluster (α : ℝ) (m : ℕ) (hm : 0 < m) :
    ∃ r, ∀ i j, i < m → j < m → ∃ k : ℤ,
      |fracSeq α (r + 1 + i) - fracSeq α (r + 1 + j) - ↑k| ≤ 1 / 8 := by
  obtain ⟨C, hC₀, hC⟩ := _root_.maynardTaoBFT m hm
  obtain ⟨q, hq⟩ : ∃ q : ℚ, |α - q| ≤ 1 / ((8 * C + 1) * q.den) ∧ q.den ≤ 8 * C := by
    have := exists_rat_abs_sub_le_and_den_le α (show 0 < 8 * C by positivity)
    simp_all only [tsub_le_iff_right, Nat.cast_mul, Nat.cast_ofNat, one_div, mul_inv_rev]
  obtain ⟨r, hr⟩ : ∃ r : ℕ, ∀ i < m, (nth Nat.Prime (r + 1 + i) : ℤ) ≡ q.num [ZMOD q.den] ∧
        nth Nat.Prime (r + m) - nth Nat.Prime (r + 1) ≤ q.den * C := by
    obtain ⟨r, hr₁, hr₂, hr₃⟩ :=
      hC q.den (cast_pos.mpr q.pos) q.num (by simpa [Int.gcd, natAbs_neg] using q.reduced) 1
    refine ⟨r - 1, fun i hi ↦ ⟨?_, ?_⟩⟩ <;>
      rcases r with (_ | r) <;> simp_all +decide [succ_add]
  use r
  intro i j hi hj
  set pi := nth Nat.Prime (r + 1 + i)
  set pj := nth Nat.Prime (r + 1 + j)
  have h_mono := nth_monotone infinite_setOf_prime
  have h_diff : |α * (pi - pj) - (q.num * ((pi - pj) / q.den))| ≤ 1 / 8 := by
    have h1 : |α * (pi - pj) - (q.num * ((pi - pj) / q.den))| ≤
        |α - q| * |(pi - pj : ℝ)| := by
      rw [← abs_mul]
      ring_nf
      rw [Rat.cast_def]
      ring_nf
      norm_num
    have h2 : |(pi - pj : ℝ)| ≤ q.den * C := by
      have := h_mono (show r + 1 + i ≤ r + m by linarith)
      have := h_mono (show r + 1 + j ≤ r + m by linarith)
      have := h_mono (show r + 1 ≤ r + 1 + i by linarith)
      have := h_mono (show r + 1 ≤ r + 1 + j by linarith)
      norm_cast
      grind
    calc _ ≤ |α - q| * |(pi - pj : ℝ)| := h1
      _ ≤ 1 / ((8 * C + 1) * q.den) * (q.den * C) := by
          exact mul_le_mul_of_nonneg_right hq.1 (abs_nonneg _) |>.trans
            (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ ≤ 1 / 8 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀] <;>
            nlinarith [show (q.den : ℝ) ≥ 1 by exact_mod_cast q.pos,
              show (C : ℝ) ≥ 1 by exact_mod_cast hC₀]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, q.num * ((pi - pj) / q.den : ℝ) = k := by
    use q.num * ((pi - pj) / q.den : ℤ)
    have := hr i hi
    have := hr j hj
    simp_all +decide only [Int.ModEq, Int.cast_mul, _root_.mul_eq_mul_left_iff,
      Int.cast_eq_zero, Rat.num_eq_zero]
    exact Or.inl <| by
      rw [Int.cast_div
        (dvd_of_emod_eq_zero <| by
          rw [sub_emod, (hr i hi).1, (hr j hj).1]
          norm_num)
        (by
          norm_cast
          exact q.pos.ne')]
      push_cast
      ring
  use k - ⌊α * pi⌋ + ⌊α * pj⌋
  simp_all +decide only [Int.cast_add, Int.cast_sub, one_div]
  exact abs_le.mpr ⟨by
    linarith! [abs_le.mp h_diff, fract_add_floor (α * pi), fract_add_floor (α * pj)],
    by linarith! [abs_le.mp h_diff, fract_add_floor (α * pi), fract_add_floor (α * pj)]⟩

/-- Pigeonhole: if `m` values in `[0, 1)` are pairwise within `1/8` on `ℝ/ℤ`, then `≥ m/2` lie
in a single interval `[a, b] ⊆ [0, 1]` of width `≤ 1/4`. -/
theorem pigeonholeCluster (x : ℕ → ℝ) (n m : ℕ) (hm : 0 < m)
    (hx01 : ∀ j, j < m → 0 ≤ x (n + 1 + j) ∧ x (n + 1 + j) < 1)
    (hclose : ∀ i j, i < m → j < m → ∃ k : ℤ, |x (n + 1 + i) - x (n + 1 + j) - k| ≤ 1 / 8) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ b - a ≤ 1 / 4 ∧
      (m : ℝ) / 2 ≤ (countInIcc x a b n m : ℝ) := by
  set S_low := (Finset.range m).filter (fun j ↦ x (n + 1 + j) < 1 / 2)
  set S_high := (Finset.range m).filter (fun j ↦ x (n + 1 + j) ≥ 1 / 2)
  obtain ⟨S, hSsub, hScard, hSclose⟩ :
      ∃ S : Finset ℕ, S ⊆ Finset.range m ∧ S.card * 2 ≥ m ∧
        ∀ i ∈ S, ∀ j ∈ S, |x (n + 1 + i) - x (n + 1 + j)| ≤ 1 / 8 := by
    by_cases hS_low : S_low.card * 2 ≥ m
    · refine ⟨S_low, Finset.filter_subset _ _, hS_low, ?_⟩
      intro i hi j hj
      have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      obtain ⟨k, hk⟩ := hclose i j hi' hj'
      rcases k with ⟨_ | _ | k⟩ <;> norm_num at * <;>
        exact abs_le.mpr ⟨by linarith [abs_le.mp hk, hx01 i hi', hx01 j hj',
            (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2],
              by linarith [abs_le.mp hk, hx01 i hi', hx01 j hj',
                (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2]⟩
    · refine ⟨S_high, Finset.filter_subset _ _, ?_, ?_⟩
      · have : S_low.card + S_high.card = m := by
          have := (Finset.range m).card_filter_add_card_filter_not (fun j ↦ x (n + 1 + j) < 1 / 2)
          simp only [Finset.card_range, not_lt] at this
          exact this
        linarith
      · intro i hi j hj
        have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
        have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        obtain ⟨k, hk⟩ := hclose i j hi' hj'
        rcases k with ⟨_ | _ | k⟩ <;> norm_num at * <;>
          linarith [abs_le.mp hk, hx01 i hi', hx01 j hj',
            (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2]
  obtain ⟨a, b, hab, habx, habw⟩ : ∃ a b : ℝ, a ≤ b ∧
      (∀ i ∈ S, a ≤ x (n + 1 + i) ∧ x (n + 1 + i) ≤ b) ∧ b - a ≤ 1 / 4 := by
    by_cases hne : S.Nonempty
    · obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image S (fun i ↦ x (n + 1 + i)) hne
      obtain ⟨i₁, hi₁, hmax⟩ := Finset.exists_max_image S (fun i ↦ x (n + 1 + i)) hne
      exact ⟨x (n+1+i₀), x (n+1+i₁), hmin i₁ hi₁,
        fun i hi ↦ ⟨hmin i hi, hmax i hi⟩, by linarith [abs_le.mp (hSclose i₀ hi₀ i₁ hi₁)]⟩
    · grind
  refine ⟨max a 0, min b 1, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num
  · obtain ⟨i, hi⟩ := Finset.card_pos.mp (by linarith)
    exact ⟨⟨hab, by
      linarith [(habx i hi).1, (habx i hi).2,
        (hx01 i (Finset.mem_range.mp (hSsub hi))).1]⟩,
        by linarith [(habx i hi).1, (habx i hi).2, (hx01 i (Finset.mem_range.mp (hSsub hi))).2]⟩
  · exact Classical.or_iff_not_imp_left.2 fun h ↦ by
      linarith [le_max_left a 0, le_max_right a 0]
  · have : countInIcc x (max a 0) (min b 1) n m ≥ S.card := by
      refine le_trans ?_ (Finset.card_mono <| show S.image (fun i ↦ n + 1 + i) ⊆
          (Finset.Ioc n (n + m)).filter (fun i ↦ max a 0 ≤ x i ∧ x i ≤ min b 1) from ?_)
      · rw [Finset.card_image_of_injective _ fun i j hij ↦ by simpa using hij]
      · grind
    rw [div_le_iff₀] <;> norm_cast
    linarith

/-! ## Step 4: Assembly -/

/-- `fracSeq α` takes values in `[0, 1)`. -/
lemma fracSeq_mem_Ico (α : ℝ) (n : ℕ) : 0 ≤ fracSeq α n ∧ fracSeq α n < 1 :=
  ⟨fract_nonneg _, fract_lt_one _⟩

/-- The sequence `{α pₙ}` has the clustering property, assuming the Maynard–Tao–BFT theorem. -/
theorem fracSeq_hasClustering (α : ℝ) : HasClustering (fracSeq α) := by
  intro m hm
  obtain ⟨r, hr⟩ := circleCluster α m hm
  exact
    ⟨r, pigeonholeCluster (fracSeq α) r m hm (fun j _ ↦ fracSeq_mem_Ico α _)
      (fun i j hi hj ↦ hr i j hi hj)⟩

/-! ## Main theorem -/

/-- **Erdős Problem 997**: for every `α ∈ ℝ`, the sequence `{α pₙ}` is not well-distributed.
Uses the Maynard–Tao–BFT axiom. -/
theorem erdos997 (α : ℝ) : ¬IsWellDistributed (fracSeq α) :=
  not_wellDistributed_of_clustering (fracSeq_hasClustering α)

#print axioms erdos997
-- 'Erdos997.erdos997' depends on axioms: [maynardTaoBFT, propext, Classical.choice,
-- Quot.sound]

end Erdos997
