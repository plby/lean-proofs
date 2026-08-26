/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Copyright 2026 Johan Land.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 1112.
Informal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
Formal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
GPT-5.5 and Gemini 3.1 supplied advice and adversarial review.
Source: https://www.erdosproblems.com/1112#post-7375
https://github.com/beetree/math_erdos_1112/tree/63ed94d3e802782aeb521095c17d6109a2dc57b5
Original Lean version: 4.27.0.
Original Mathlib commit: a3a10db0e9d66acbebf76c5e6a135066525ac900.
-/
/-
Morse–Hedlund, stage 1: the balance calculus and the slope of a balanced word.

Everything here consumes the balance hypothesis in its unfolded Pi form
(`hbal : ∀ i j n, (q(i+n) − q i : ℤ) − (q(j+n) − q j : ℤ) ≤ 1`), so that this
file needs only `Core` and can be imported by `Balanced.lean` without cycles.

Design: the slope is obtained as
`sSup {(q n − 1)/n : n ≥ 1}` directly — no Fekete, no limits.  The two-sided
uniform bound `|q n − n·α| ≤ 1` (n ≥ 1) comes from the multiplicative chain
`t·q n − (t−1) ≤ q(t·n) ≤ t·q n + (t−1)` and the cross bound
`n·q m − n ≤ m·q n + m`, which shows every `(q m − 1)/m` is ≤ every
`(q n + 1)/n`.
-/
import ErdosProblems.Erdos1112.NonEx.TwoLetter.Core

namespace Erdos1112
namespace Proof
namespace MH

theorem qCount_zero (h : ℕ → Bool) : qCount h 0 = 0 := by
  simp [qCount]

theorem qCount_succ (h : ℕ → Bool) (n : ℕ) :
    qCount h (n + 1) = qCount h n + (if h (n + 1) then 1 else 0) := by
  rw [qCount, Finset.sum_range_succ]; rfl

theorem qCount_le (h : ℕ → Bool) (n : ℕ) : qCount h n ≤ n := by
  rw [qCount]
  calc (Finset.range n).sum (fun i => if h (i + 1) then 1 else 0)
      ≤ (Finset.range n).sum (fun _ => 1) :=
        Finset.sum_le_sum (fun i _ => by split <;> omega)
    _ = n := by simp

/-- The unfolded balance hypothesis used throughout this stream. -/
def BalancedHyp (h : ℕ → Bool) : Prop :=
  ∀ i j n : ℕ,
    ((qCount h (i + n) : ℤ) - (qCount h i : ℤ)) -
      ((qCount h (j + n) : ℤ) - (qCount h j : ℤ)) ≤ 1

section Balance

variable {h : ℕ → Bool}

/-- Window subadditivity: `q(m+n) ≤ q m + q n + 1`.
Route: `hbal m 0 n`, `qCount_zero`, `omega`. -/
theorem window_le (hbal : BalancedHyp h) (m n : ℕ) :
    (qCount h (m + n) : ℤ) ≤ qCount h m + qCount h n + 1 := by
  have := hbal m 0 n
  have h0 : qCount h 0 = 0 := qCount_zero h
  rw [Nat.zero_add] at this
  omega

/-- Window superadditivity: `q m + q n ≤ q(m+n) + 1`.
Route: `hbal 0 m n`, `qCount_zero`, `omega`. -/
theorem le_window (hbal : BalancedHyp h) (m n : ℕ) :
    (qCount h m : ℤ) + qCount h n ≤ qCount h (m + n) + 1 := by
  have := hbal 0 m n
  have h0 : qCount h 0 = 0 := qCount_zero h
  rw [Nat.zero_add] at this
  omega

/-- Multiplicative upper chain `q(t·n) ≤ t·q n + (t − 1)` for `t ≥ 1`.
Route: `Nat.le_induction` on `t`; `window_le` at `(t·n, n)`; `push_cast`; `omega`. -/
theorem window_mul_le (hbal : BalancedHyp h) (n : ℕ) : ∀ t : ℕ, 1 ≤ t →
    (qCount h (t * n) : ℤ) ≤ t * qCount h n + (t - 1) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
      have h2 := window_le hbal (t * n) n
      have heq : (t + 1) * n = t * n + n := by ring
      rw [heq]
      push_cast
      linarith

/-- Multiplicative lower chain `t·q n − (t − 1) ≤ q(t·n)` for `t ≥ 1`.
Route: mirror of `window_mul_le` via `le_window`. -/
theorem le_window_mul (hbal : BalancedHyp h) (n : ℕ) : ∀ t : ℕ, 1 ≤ t →
    (t : ℤ) * qCount h n - (t - 1) ≤ qCount h (t * n) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
      have h2 := le_window hbal (t * n) n
      have heq : (t + 1) * n = t * n + n := by ring
      rw [heq]
      push_cast
      linarith

/-- Cross bound `n·q m − n ≤ m·q n + m` (`m, n ≥ 1`): both chains at `m·n`.
Route: `le_window_mul n m` (value `n·m`), `window_mul_le m n` — instances
`q(n·m) ≥ n·q m − (n−1)` and `q(m·n) ≤ m·q n + (m−1)`, `Nat.mul_comm`, `omega`. -/
theorem cross_bound (hbal : BalancedHyp h) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (n : ℤ) * qCount h m - n ≤ m * qCount h n + m := by
  have h1 := le_window_mul hbal m n hn
  have h2 := window_mul_le hbal n m hm
  rw [Nat.mul_comm n m] at h1
  linarith

end Balance

/-- The slope of a binary word: `sSup {(q n − 1)/n : n ≥ 1}` (no limits). -/
noncomputable def slope (h : ℕ → Bool) : ℝ :=
  sSup {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ x = ((qCount h n : ℝ) - 1) / n}

section SlopeBounds

variable {h : ℕ → Bool}

/-- `q n − 1 ≤ n·slope` for `n ≥ 1`.  Route: `le_csSup`; `BddAbove` from
`cross_bound` at `n := 1` (`div_le_div_iff` cross-multiplication). -/
theorem le_slope (n : ℕ) (hn : 1 ≤ n) :
    (qCount h n : ℝ) - 1 ≤ n * slope h := by
  have hbdd : BddAbove {x : ℝ | ∃ m : ℕ, 1 ≤ m ∧ x = ((qCount h m : ℝ) - 1) / m} := by
    refine ⟨1, fun x hx => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hx
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [div_le_one hm0]
    have hq : (qCount h m : ℝ) ≤ m := by exact_mod_cast qCount_le h m
    linarith
  have hle : ((qCount h n : ℝ) - 1) / n ≤ slope h :=
    le_csSup hbdd ⟨n, hn, rfl⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc (qCount h n : ℝ) - 1 = ((qCount h n : ℝ) - 1) / n * n := by field_simp
    _ ≤ slope h * n := mul_le_mul_of_nonneg_right hle hn0.le
    _ = n * slope h := mul_comm _ _

/-- `n·slope ≤ q n + 1` for `n ≥ 1`.  Route: `csSup_le` (nonempty via `n = 1`);
each element `(q m − 1)/m ≤ (q n + 1)/n` by `cross_bound` + `div_le_div_iff`. -/
theorem slope_le (hbal : BalancedHyp h) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * slope h ≤ qCount h n + 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : {x : ℝ | ∃ m : ℕ, 1 ≤ m ∧ x = ((qCount h m : ℝ) - 1) / m}.Nonempty :=
    ⟨((qCount h 1 : ℝ) - 1) / ((1 : ℕ) : ℝ), ⟨1, le_refl 1, rfl⟩⟩
  have hup : slope h ≤ ((qCount h n : ℝ) + 1) / n := by
    apply csSup_le hne
    rintro x ⟨m, hm, rfl⟩
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [div_le_div_iff₀ hm0 hn0]
    have hc : ((n : ℤ) * qCount h m - n : ℝ) ≤ ((m : ℤ) * qCount h n + m : ℝ) := by
      exact_mod_cast cross_bound hbal m n hm hn
    push_cast at hc
    nlinarith
  calc (n : ℝ) * slope h ≤ n * (((qCount h n : ℝ) + 1) / n) :=
        mul_le_mul_of_nonneg_left hup hn0.le
    _ = qCount h n + 1 := by field_simp

/-- `0 ≤ slope h`.  Route: `by_contra`; `exists_nat_gt` picks `n` with
`1/n < −slope`; then `(q n − 1)/n ≤ slope < −1/n` forces `q n < 0`. -/
theorem slope_nonneg : 0 ≤ slope h := by
  by_contra hneg
  push Not at hneg
  have hs : 0 < -slope h := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (-slope h))
  have hn0 : (0 : ℝ) < n := lt_trans (div_pos one_pos hs) hn
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · simp at hn0
    · exact hp
  have h1 := le_slope (h := h) n hn1
  have hq : (0 : ℝ) ≤ qCount h n := Nat.cast_nonneg _
  have h2 : 1 < (n : ℝ) * (-slope h) := by
    have := (div_lt_iff₀ hs).mp hn
    linarith
  nlinarith

/-- `slope h ≤ 1`.  Route: `csSup_le`; `(q m − 1)/m ≤ 1` since `q m ≤ m`
(`qCount` sums `m` indicator terms; `Finset.sum_le_card_nsmul`). -/
theorem slope_le_one : slope h ≤ 1 := by
  have hne : {x : ℝ | ∃ m : ℕ, 1 ≤ m ∧ x = ((qCount h m : ℝ) - 1) / m}.Nonempty :=
    ⟨((qCount h 1 : ℝ) - 1) / ((1 : ℕ) : ℝ), ⟨1, le_refl 1, rfl⟩⟩
  apply csSup_le hne
  rintro x ⟨m, hm, rfl⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_one hm0]
  have hq : (qCount h m : ℝ) ≤ m := by exact_mod_cast qCount_le h m
  linarith

end SlopeBounds

end MH
end Proof
end Erdos1112
