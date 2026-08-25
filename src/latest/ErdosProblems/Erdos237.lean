/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 237.
https://www.erdosproblems.com/forum/thread/237

Formalization status:
- Unconditional; uses only Lean's standard logical axioms.

Informal authors:
- Yong-Gao Chen
- Yuchen Ding

Formal authors:
- Aristotle
- Pietro Monticone

URLs:
- https://www.erdosproblems.com/forum/thread/237#post-5240
- https://gist.githubusercontent.com/pitmonticone/8ea0d1cdb963b6213ac639b11d33f811/raw/98a5824d16da14313f65d77eeab5563dd874613a/Erdos237.lean
-/
/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Cases
import ErdosProblems.Erdos237.Unconditional
import ErdosProblems.Axioms
import Util.MertensThird

/-!
# Erdős Problem 237

## Problem Statement

Let `A ⊆ ℕ` be an infinite set. Let `f(n)` count the number of representations
`n = p + a` where `p` is prime and `a ∈ A`. Is it true that `limsup f(n) = ∞`?

## Answer

**Yes.** This was proved by Chen and Ding (2022), confirming Erdős's 1950 conjecture.
The assumption that `A` is infinite suffices.

## Proof structure

The final proof uses `qualitativePrimeTuples_unconditional`:
1. Coarse dyadic product weights give an unbounded sieve ratio.
2. Generic S1 limits and an extra-coordinate S2 lower bound apply to arbitrary tuples.
3. The proved Bombieri–Vinogradov theorem and ordinary PNT control the prime sums.
4. Selecting one residue class modulo `k!` and reflecting gives Chen–Ding's finite theorem.
5. An infinite set contains every required finite cardinality.

The quantitative sieve infrastructure below is retained, but the final proof no longer
uses its Mertens estimate or the assumed quantitative `maynard_tao` theorem.

## References

* Chen, Y.-G. and Ding, Y., *On a conjecture of Erdős*,
  [arXiv:2201.10727](https://arxiv.org/abs/2201.10727) (2022).
* Maynard, J., *Small gaps between primes*, Ann. of Math. 181 (2015), 383–413.
* [Erdős Problem #237](https://www.erdosproblems.com/237).
-/

namespace Erdos237

open Nat Set Finset Real

/-! ## Sieve infrastructure -/

/-- **Sieve step.** For any `T : Finset ℤ` and prime `p`, removing the most popular residue class
mod `p` gives `T' ⊆ T` with `|image mod p| < p` and `(p-1)|T| ≤ p|T'|`. -/
lemma sieve_step (T : Finset ℤ) (p : ℕ) (hp : p.Prime) :
    ∃ T' : Finset ℤ, T' ⊆ T ∧
      (Finset.image (· % (p : ℤ)) T').card < p ∧
      (p - 1) * T.card ≤ p * T'.card := by
  by_cases h : (Finset.image (fun x ↦ x % (p : ℤ)) T).card < p
  · exact ⟨T, Finset.Subset.refl _, h,
      mul_le_mul_right _ (pred_le _)⟩
  · obtain ⟨r, hr⟩ : ∃ r ∈ Finset.image (fun x ↦ x % (p : ℤ)) T,
      (filter (fun x ↦ x % (p : ℤ) = r) T).card < T.card / p + 1 := by
      have h_pigeonhole :
          ∑ x ∈ Finset.image (fun x ↦ x % (p : ℤ)) T, (filter (fun y ↦ y % (p : ℤ) = x) T).card =
          T.card := by
        rw [card_eq_sum_ones, sum_image']; aesop
      contrapose! h
      have := Finset.sum_le_sum h
      simp only [Finset.mem_image, Order.add_one_le_iff, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, sum_const, smul_eq_mul, gt_iff_lt] at *
      nlinarith [div_add_mod T.card p,
        mod_lt T.card hp.pos, hp.two_le]
    refine ⟨T.filter (fun x ↦ x % (p : ℤ) ≠ r), filter_subset _ _, ?_, ?_⟩
    · calc (Finset.image (· % (p : ℤ))
              (T.filter (· % (p : ℤ) ≠ r))).card
            < (Finset.image (· % (p : ℤ)) T).card :=
              Finset.card_lt_card <| Finset.ssubset_iff_subset_ne.mpr
                ⟨Finset.image_subset_image (filter_subset _ _), by grind⟩
          _ ≤ p := by
              exact le_trans (Finset.card_le_card <|
                Finset.image_subset_iff.mpr fun x hx ↦ Finset.mem_Ico.mpr
                  ⟨Int.emod_nonneg _ <| cast_ne_zero.mpr hp.ne_zero,
                    Int.emod_lt_of_pos _ <| cast_pos.mpr hp.pos⟩) (by simp)
    · have h_card_filter :
          (filter (fun x ↦ x % (p : ℤ) = r) T).card +
          (filter (fun x ↦ x % (p : ℤ) ≠ r) T).card =
          T.card := by
        rw [card_filter_add_card_filter_not]
      nlinarith [div_mul_le_self (card T) p, Nat.sub_add_cancel hp.pos]

/-- **Iterated sieve.** Processing all primes in `P`. -/
lemma iterated_sieve (S : Finset ℤ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∃ B : Finset ℤ, B ⊆ S ∧ (∀ p ∈ P, (Finset.image (· % (p : ℤ)) B).card < p) ∧
    (∏ p ∈ P, (p - 1)) * S.card ≤ (∏ p ∈ P, p) * B.card := by
  induction P using Finset.induction with
  | empty => exact ⟨S, Finset.Subset.refl _, by simp, by simp⟩
  | insert p P hpP ih =>
    obtain ⟨B₁, hB₁sub, hB₁adm, hB₁prod⟩ :=
      ih (fun q hq ↦ hP q (Finset.mem_insert_of_mem hq))
    obtain ⟨B₂, hB₂sub, hB₂img, hB₂prod⟩ := sieve_step B₁ p (hP p (Finset.mem_insert_self p P))
    refine ⟨B₂, Finset.Subset.trans hB₂sub hB₁sub,
      fun q hq ↦ ?_, ?_⟩
    · rcases Finset.mem_insert.mp hq with rfl | hq'
      · exact hB₂img
      · exact lt_of_le_of_lt
          (Finset.card_le_card <| Finset.image_subset_image hB₂sub)
          (hB₁adm q hq')
    · simp only [Finset.prod_insert hpP, mul_assoc]
      nlinarith [Nat.sub_add_cancel (hP p (Finset.mem_insert_self p P)).pos,
        show 0 ≤ ∏ p ∈ P, (p - 1) from Finset.prod_nonneg fun _ _ ↦ Nat.zero_le _,
        show 0 ≤ ∏ p ∈ P, p from Finset.prod_nonneg fun _ _ ↦ Nat.zero_le _]

/-- Admissibility from image bounds for small primes. -/
lemma admissible_of_small_images (B : Finset ℤ)
    (h : ∀ p : ℕ, p.Prime → p ≤ B.card → (Finset.image (· % (p : ℤ)) B).card < p) :
    Admissible B := by
  intro p hp
  by_cases hB : B.card < p
  · exact lt_of_le_of_lt Finset.card_image_le hB
  · exact h p hp (le_of_not_gt hB)

/-- Product bound conversion from ℕ to ℝ. -/
lemma product_bound_to_real (S B : Finset ℤ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hprod : (∏ p ∈ P, (p - 1)) * S.card ≤ (∏ p ∈ P, p) * B.card) :
    (S.card : ℝ) * ∏ p ∈ P, (1 - 1 / (p : ℝ)) ≤ (B.card : ℝ) := by
  have h_factor : (#S : ℝ) * (∏ p ∈ P, ((p : ℝ) - 1)) ≤ (#B : ℝ) * (∏ p ∈ P, (p : ℝ)) := by
    have h := cast_le (α := ℝ).mpr hprod
    simp only [cast_mul, cast_prod] at h
    rw [Finset.prod_congr rfl fun x hx ↦
      show ((x - 1 : ℕ) : ℝ) = (x : ℝ) - 1 by rw [cast_sub (hP x hx).one_le]; simp] at h
    linarith
  rw [Finset.prod_congr rfl fun x hx ↦ one_sub_div (mod_cast Nat.Prime.ne_zero (hP x hx))]
  rwa [Finset.prod_div_distrib, mul_div,
    div_le_iff₀ (Finset.prod_pos fun p hp ↦ cast_pos.mpr <| Prime.pos <| hP p hp)]

/-! ## Extract admissible subset -/

/-- For `|S| ≥ 3`, there exists `B ⊆ S` that is admissible with
`|B| ≥ |S| / (3 log |S|)`. -/
lemma extract_admissible_subset (S : Finset ℤ) (hS : 3 ≤ S.card) :
    ∃ B : Finset ℤ, B ⊆ S ∧ Admissible B ∧
      (S.card : ℝ) / (3 * Real.log S.card) ≤ (B.card : ℝ) := by
  obtain ⟨B, hB₁, hB₂, hB₃⟩ := iterated_sieve S
    ((Finset.range (S.card + 1)).filter Nat.Prime)
    (fun p hp ↦ (Finset.mem_filter.mp hp).2)
  refine ⟨B, hB₁, ?_, ?_⟩
  · exact admissible_of_small_images B fun p hp hp' ↦
      hB₂ p <| Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr <| by linarith [Finset.card_le_card hB₁], hp⟩
  · convert product_bound_to_real S B
      ((Finset.range (#S + 1)).filter Nat.Prime)
      (fun p hp ↦ (Finset.mem_filter.mp hp).2) _ |> le_trans _ using 1
    · have := mertens_third_theorem (Finset.card S) (by linarith : 3 ≤ Finset.card S)
      convert mul_le_mul_of_nonneg_left this (cast_nonneg (Finset.card S)) using 1; ring
    · convert hB₃ using 1

/-! ## Threshold lemmas -/

/-- `n * log n` is eventually larger than any constant. -/
lemma nat_mul_log_eventually_large (C : ℝ) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      C < ↑n * Real.log ↑n := by
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      n * Real.log n > C := ⟨⌊C⌋₊ + 3, fun n hn ↦ by
      nlinarith [lt_floor_add_one C,
        show (n : ℝ) ≥ ⌊C⌋₊ + 3 by exact_mod_cast hn,
        Real.log_inv n ▸ Real.log_le_sub_one_of_pos
          (inv_pos.2 <| show (n : ℝ) > 0 by norm_cast; linarith),
        mul_inv_cancel₀ (show (n : ℝ) ≠ 0 by norm_cast; linarith)]⟩
  exact ⟨n₀ + 1, succ_pos _, fun n hn ↦ hn₀ n (le_of_succ_le hn)⟩

/-- `n * log n` is monotone for naturals `≥ 1`. -/
lemma nat_mul_log_mono {a b : ℕ} (hab : b ≤ a)
    (hb : 1 ≤ b) :
    (b : ℝ) * Real.log b ≤ ↑a * Real.log ↑a := by
  gcongr

/-- `n / (3 log n)` is eventually larger than any `N`. -/
lemma nat_div_log_eventually_large (N : ℝ) :
    ∃ ℓ₀ : ℕ, 3 ≤ ℓ₀ ∧ ∀ n : ℕ, ℓ₀ ≤ n →
      N ≤ ↑n / (3 * Real.log ↑n) := by
  have h_tend : Filter.Tendsto
      (fun n : ℕ ↦ (n : ℝ) / (3 * Real.log n))
      Filter.atTop Filter.atTop := by
    suffices h_log : Filter.Tendsto (fun u : ℝ ↦ Real.exp u / (3 * u)) Filter.atTop Filter.atTop by
      have := h_log.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      exact this.congr' (by
        filter_upwards [Filter.eventually_gt_atTop 0] with n hn
        simp +decide [Real.exp_log (cast_pos.mpr hn)])
    ring_nf
    exact Filter.Tendsto.atTop_mul_const
      (by norm_num) (by simpa [div_eq_mul_inv] using Real.tendsto_exp_div_pow_atTop 1)
  exact Filter.eventually_atTop.mp
    (h_tend.eventually_ge_atTop N) |>
    fun ⟨ℓ₀, hℓ₀⟩ ↦ ⟨ℓ₀ + 3, by linarith, fun n hn ↦ hℓ₀ n (by linarith)⟩

/-! ## Sieving lemma -/

/-- **Sieving Lemma** (Eratosthenes sieve + Mertens' theorem).
For any `m ≥ 2`, there exists `ℓ₀` such that any `S : Finset ℤ` with
`|S| ≥ ℓ₀` contains an admissible subset `B` satisfying the Maynard–Tao
size threshold `e^{8m+4} < |B| · log|B|`. -/
lemma sieving_lemma (m : ℕ) (_hm : 2 ≤ m) :
    ∃ ℓ₀ : ℕ, ∀ (S : Finset ℤ), ℓ₀ ≤ S.card →
      ∃ B : Finset ℤ, B ⊆ S ∧ Admissible B ∧ Real.exp (8 * m + 4) < B.card * Real.log B.card := by
  obtain ⟨n₀, hn₀pos, hn₀⟩ := nat_mul_log_eventually_large (exp (8 * m + 4))
  obtain ⟨ℓ₀, hℓ₀ge3, hℓ₀⟩ := nat_div_log_eventually_large (↑n₀)
  refine ⟨ℓ₀, fun S hS ↦ ?_⟩
  have hS3 : 3 ≤ S.card := le_trans hℓ₀ge3 hS
  obtain ⟨B, hBS, hBadm, hBsize⟩ := extract_admissible_subset S hS3
  refine ⟨B, hBS, hBadm, ?_⟩
  have hBge_n₀ : n₀ ≤ B.card := by exact_mod_cast le_trans (hℓ₀ S.card hS) hBsize
  calc Real.exp (8 * m + 4)
      < n₀ * Real.log ↑n₀ := hn₀ n₀ le_rfl
    _ ≤ B.card * Real.log ↑B.card := nat_mul_log_mono hBge_n₀ hn₀pos

/-! ## Chen–Ding theorem -/

/-- **Chen–Ding Theorem** (2022), from the unconditional qualitative prime-tuple theorem. -/
theorem chen_ding_theorem (m : ℕ) :
    ∃ ℓ₀ : ℕ, ∀ (S : Finset ℕ), ℓ₀ ≤ S.card → ∃ n : ℕ, m ≤ repCount (S : Set ℕ) n := by
  exact chen_ding_of_qualitative qualitativePrimeTuples_unconditional m

/-! ## Main result -/

/-- **Erdős Problem 237** (Chen–Ding, 2022). For any infinite set `A ⊆ ℕ`, the representation
function `f_A(n) = #{a ∈ A : (n - a) prime}` is unbounded. -/
theorem erdos_237 (A : Set ℕ) (hA : A.Infinite) :
    ∀ C : ℕ, ∃ n : ℕ, C < repCount A n := by
  intro C
  obtain ⟨ℓ₀, hℓ₀⟩ := chen_ding_theorem (C + 1)
  obtain ⟨S, hS₁, hS₂⟩ := hA.exists_subset_card_eq ℓ₀
  obtain ⟨n, hn⟩ := hℓ₀ S hS₂.ge
  exact ⟨n, (lt_of_succ_le hn).trans_le (repCount_mono hS₁ n)⟩

#print axioms erdos_237
-- 'Erdos237.erdos_237' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos237
