/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Licensed under the Apache License, Version 2.0; see LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 884.
Informal proof: Daniel Larsen, building on Terence Tao's construction.
Formal proof: Claude Fable 5, with minor guidance from R. J. Honicky.
Source: https://www.erdosproblems.com/884#post-7362
https://github.com/honicky/erdos884/tree/323e9a01306df1e094b434beaa48c018370fe258
Original Lean/Mathlib version: 4.31.0.
Original Mathlib commit: fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.
The port reuses the repository's existing PNT+ Selberg sieve by Arend Mellendijk.
-/
import ErdosProblems.Erdos884.TauSingular

set_option linter.mathlibStandardSet false

/-!
# Erdős 884 — Lemma A: Chebyshev-type lower bound for primes in `(t, 8t]`

We prove `primesBetween_lower`: there is a threshold `T ≥ 3` such that for all `t ≥ T`
the interval `(⌊t⌋₊, ⌊8t⌋₊]` contains at least `2t / log t` primes.

Route: `Chebyshev.pi_ge'` at `8t` gives a lower bound for `π(⌊8t⌋₊)`, and
`Chebyshev.eventually_primeCounting_le` (with `ε = 1/10`) an upper bound for `π(⌊t⌋₊)`;
the count of primes in the interval is exactly `π(⌊8t⌋₊) - π(⌊t⌋₊)`.
-/

namespace Erdos884

/-- Counting primes in `(a, b]`: `π a + #{primes in (a,b]} = π b`. -/
lemma primeCounting_add_card_Ioc {a b : ℕ} (h : a ≤ b) :
    a.primeCounting + ((Finset.Ioc a b).filter Nat.Prime).card = b.primeCounting := by
  have key : ∀ n : ℕ, n.primeCounting = ((Finset.Iic n).filter Nat.Prime).card := by
    intro n
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range,
      Nat.range_succ_eq_Iic]
  have hdisj : Disjoint ((Finset.Iic a).filter Nat.Prime)
      ((Finset.Ioc a b).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_Iic] at hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx'
    omega
  rw [key a, key b, ← Finset.card_union_of_disjoint hdisj, ← Finset.filter_union,
    Finset.Iic_union_Ioc_eq_Iic h]

/-- The core algebraic inequality behind Lemma A, with `c = log 2`, `L = log t`,
`M = log (8t)`, `E = log (8t+2)` abstracted into real variables. -/
lemma core_ineq {t c L M E : ℝ} (ht : 36 ≤ t) (hc1 : (0.69 : ℝ) ≤ c) (hc2 : c ≤ 0.7)
    (hL0 : 0 < L) (hML : 20 * M ≤ 21 * L) (hE : E ≤ 2 * L) (hLt : 3 * L ≤ t) :
    (2 + (2 * c + 1/10)) * t * M ≤ ((8 * t - 1) * c - E) * L := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have step1 : (2 + (2 * c + 1/10)) * t * M
      ≤ (2 + (2 * c + 1/10)) * t * ((21/20) * L) := by
    have h1 : (0 : ℝ) ≤ (2 + (2 * c + 1/10)) * t := by nlinarith
    have h2 : M ≤ (21/20) * L := by linarith
    exact mul_le_mul_of_nonneg_left h2 h1
  have step2 : ((8 * t - 1) * c - 2 * L) * L ≤ ((8 * t - 1) * c - E) * L := by
    apply mul_le_mul_of_nonneg_right _ hL0.le
    linarith
  refine step1.trans (le_trans ?_ step2)
  have hct : 0.69 * t ≤ c * t := mul_le_mul_of_nonneg_right hc1 ht0
  have key : (2 + (2 * c + 1/10)) * t * (21/20) ≤ (8 * t - 1) * c - 2 * L := by
    nlinarith
  calc (2 + (2 * c + 1/10)) * t * ((21/20) * L)
      = ((2 + (2 * c + 1/10)) * t * (21/20)) * L := by ring
    _ ≤ ((8 * t - 1) * c - 2 * L) * L := mul_le_mul_of_nonneg_right key hL0.le

/-- **Lemma A.** For all sufficiently large `t`, the interval `(⌊t⌋₊, ⌊8t⌋₊]` contains
at least `2t / log t` primes. -/
theorem primesBetween_lower :
    ∃ T : ℝ, 3 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      2 * t / Real.log t ≤ (((Finset.Ioc ⌊t⌋₊ ⌊8*t⌋₊)).filter Nat.Prime).card := by
  obtain ⟨T₄, hT₄⟩ := Filter.eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (show (0:ℝ) < 1/10 by norm_num))
  refine ⟨max (max T₄ ((2:ℝ)^60)) 36, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro t hTt
  have ht36 : (36 : ℝ) ≤ t := le_trans (le_max_right _ _) hTt
  have ht4 : T₄ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTt
  have ht60 : (2:ℝ)^60 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTt
  have ht0 : (0 : ℝ) < t := by linarith
  have hL0 : 0 < Real.log t := Real.log_pos (by linarith)
  have hc1 : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hc2 : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  -- log t ≥ 60 log 2
  have hL60 : 60 * Real.log 2 ≤ Real.log t := by
    have h1 : Real.log ((2:ℝ)^60) ≤ Real.log t := Real.log_le_log (by positivity) ht60
    rwa [Real.log_pow, Nat.cast_ofNat] at h1
  -- 3 log t ≤ t
  have hLt : 3 * Real.log t ≤ t := by
    have hsqrt6 : (6 : ℝ) ≤ Real.sqrt t := by
      rw [show (6:ℝ) = Real.sqrt (6^2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith : (6:ℝ)^2 ≤ t)
    have h1 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt ht0.le
    have h3 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
    have h4 : 6 * Real.sqrt t ≤ Real.sqrt t * Real.sqrt t :=
      mul_le_mul_of_nonneg_right hsqrt6 (Real.sqrt_nonneg t)
    linarith
  -- log (8t) = 3 log 2 + log t
  have hM_eq : Real.log (8*t) = 3 * Real.log 2 + Real.log t := by
    rw [Real.log_mul (by norm_num) (ne_of_gt ht0), show (8:ℝ) = 2^3 by norm_num,
      Real.log_pow]
    norm_num
  have hM0 : 0 < Real.log (8*t) := by rw [hM_eq]; linarith
  have hML : 20 * Real.log (8*t) ≤ 21 * Real.log t := by rw [hM_eq]; linarith
  -- log (8t+2) ≤ 2 log t
  have hE : Real.log (8*t+2) ≤ 2 * Real.log t := by
    have h1 : Real.log (8*t+2) ≤ Real.log (16*t) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (16*t) = 4 * Real.log 2 + Real.log t := by
      rw [Real.log_mul (by norm_num) (ne_of_gt ht0), show (16:ℝ) = 2^4 by norm_num,
        Real.log_pow]
      norm_num
    linarith
  -- the two prime-counting estimates
  have hpi8 : ((8*t - 1) * Real.log 2 - Real.log (8*t + 2)) / Real.log (8*t)
      ≤ (Nat.primeCounting ⌊8*t⌋₊ : ℝ) := Chebyshev.pi_ge' (by linarith)
  have hpit : (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ (Real.log 4 + 1/10) * t / Real.log t := hT₄ t ht4
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog4] at hpit
  -- the counting bridge
  have hbridge : (Nat.primeCounting ⌊t⌋₊ : ℝ)
      + ((((Finset.Ioc ⌊t⌋₊ ⌊8*t⌋₊)).filter Nat.Prime).card : ℝ)
      = (Nat.primeCounting ⌊8*t⌋₊ : ℝ) := by
    exact_mod_cast primeCounting_add_card_Ioc (Nat.floor_le_floor (by linarith : t ≤ 8*t))
  -- the core estimate, in division form
  have hdiv : (2 + (2 * Real.log 2 + 1/10)) * t / Real.log t
      ≤ ((8*t - 1) * Real.log 2 - Real.log (8*t+2)) / Real.log (8*t) := by
    rw [div_le_div_iff₀ hL0 hM0]
    exact core_ineq ht36 hc1 hc2 hL0 hML hE hLt
  have hexpand : (2 + (2 * Real.log 2 + 1/10)) * t / Real.log t
      = 2 * t / Real.log t + (2 * Real.log 2 + 1/10) * t / Real.log t := by ring
  linarith [hdiv, hpi8, hpit, hbridge, hexpand]

end Erdos884
