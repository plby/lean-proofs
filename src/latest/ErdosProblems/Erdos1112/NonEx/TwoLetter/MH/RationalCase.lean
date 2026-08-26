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
Morse–Hedlund, stage 2: rational slope ⇒ the word is eventually periodic.

Design (Coven–Hedlund-style but fully integer-domain): with
`α = P/Q` the scaled discrepancy `E n := Q·q n − P·n ∈ ℤ` is bounded
(`|E n| ≤ Q`), and the length-`Q` window sums `w n := q(n+Q) − q n` have
oscillation ≤ 1 (balance), hence take at most two adjacent values.  The block
potential `Φ N := ∑_{r<Q} E(N·Q + r)` is bounded and moves by
`Q·∑_r (w(N·Q+r) − P)` per step; excluding the divergent sign patterns leaves
`w − P ∈ {0,1}` (or `{−1,0}`), so `Φ` is monotone and bounded, hence (integer
valued) eventually constant, forcing `w n = P` for all large `n`; the window
recursion `q(n+1) − q(n) = [h(n+1)]` then yields period `Q`.  No reals, no
density, no compactness.
-/
import ErdosProblems.Erdos1112.NonEx.TwoLetter.MH.Slope

namespace Erdos1112
namespace Proof
namespace MH

/-- A weakly decreasing ℕ-sequence is eventually constant.
Route: `WellFounded.has_min wellFounded_lt (Set.range f)` picks the attained
minimum; `antitone_nat_of_succ_le` gives the other inequality past it. -/
theorem antitone_eventually_constant (f : ℕ → ℕ) (hf : ∀ n, f (n + 1) ≤ f n) :
    ∃ S, ∀ n, S ≤ n → f n = f S := by
  have hanti : Antitone f := antitone_nat_of_succ_le hf
  obtain ⟨m, ⟨S, hSm⟩, hmin⟩ :=
    WellFounded.has_min wellFounded_lt (Set.range f) (Set.range_nonempty f)
  refine ⟨S, fun n hn => ?_⟩
  have h1 : f n ≤ f S := hanti hn
  have h2 : ¬ f n < m := hmin (f n) ⟨n, rfl⟩
  rw [← hSm] at h2
  omega

/-- Generalized telescoping: a shift-`Q` difference sum reindexes to a length-`Q`
window of shift-`N` differences. -/
private theorem sum_shift_diff (f : ℕ → ℤ) (Q N : ℕ) :
    ∑ n ∈ Finset.range N, (f (n + Q) - f n)
      = ∑ j ∈ Finset.range Q, (f (N + j) - f j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep : (∑ j ∈ Finset.range Q, (f (N + 1 + j) - f j))
          - (∑ j ∈ Finset.range Q, (f (N + j) - f j)) = f (N + Q) - f N := by
        rw [← Finset.sum_sub_distrib]
        rw [Finset.sum_congr rfl (fun j _ => by
          change (f (N + 1 + j) - f j) - (f (N + j) - f j) = f (N + j + 1) - f (N + j)
          rw [show N + 1 + j = N + j + 1 from by ring]; ring)]
        exact Finset.sum_range_sub (fun j => f (N + j)) Q
      linarith [hstep]

theorem eventuallyPeriodic_of_rational (h : ℕ → Bool)
    (hbal : BalancedHyp h)
    (P : ℤ) (Q : ℕ) (hQ : 0 < Q)
    (hE : ∀ n : ℕ, |(Q : ℤ) * qCount h n - P * n| ≤ Q) :
    ∃ p, 0 < p ∧ ∃ T, ∀ n, T ≤ n → h (n + p) = h n := by
  have hQ0 : (0 : ℤ) < Q := by exact_mod_cast hQ
  set E : ℕ → ℤ := fun n => (Q : ℤ) * qCount h n - P * n with hE_def
  set w : ℕ → ℤ := fun n => (qCount h (n + Q) : ℤ) - qCount h n with hw_def
  have hQw : ∀ n, (Q : ℤ) * (w n - P) = E (n + Q) - E n := by
    intro n; simp only [hE_def, hw_def]; push_cast; ring
  have hosc : ∀ a b, w a - w b ≤ 1 := by
    intro a b; have := hbal a b Q; simp only [hw_def]; linarith
  set S : ℕ → ℤ := fun N => ∑ n ∈ Finset.range N, (w n - P) with hS_def
  have hQS : ∀ N, (Q : ℤ) * S N = ∑ j ∈ Finset.range Q, (E (N + j) - E j) := by
    intro N
    have h1 : (Q : ℤ) * S N = ∑ n ∈ Finset.range N, (E (n + Q) - E n) := by
      simp only [hS_def, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => hQw n)
    rw [h1, sum_shift_diff]
  have hSbd : ∀ N, |S N| ≤ 2 * Q := by
    intro N
    have hb : |(Q : ℤ) * S N| ≤ 2 * Q * Q := by
      rw [hQS]
      calc |∑ j ∈ Finset.range Q, (E (N + j) - E j)|
            ≤ ∑ j ∈ Finset.range Q, |E (N + j) - E j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Finset.range Q, (2 * Q : ℤ) := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            have h1 := hE (N + j); have h2 := hE j
            simp only [hE_def]
            rw [abs_le] at h1 h2 ⊢; omega
        _ = 2 * Q * Q := by rw [Finset.sum_const, Finset.card_range]; ring
    rw [abs_mul, abs_of_pos hQ0] at hb
    nlinarith [hb, abs_nonneg (S N), hQ0]
  -- monotone dichotomy from oscillation ≤ 1
  have hdich : (∀ n, P ≤ w n) ∨ (∀ n, w n ≤ P) := by
    by_contra hc; push Not at hc
    obtain ⟨⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩ := hc
    have := hosc n₂ n₁; omega
  -- in either case `S` is monotone and bounded, so eventually constant, forcing `w = P`
  have hwP : ∃ T, ∀ n, T ≤ n → w n = P := by
    rcases hdich with hge | hle
    · have hSmono : ∀ N, S N ≤ S (N + 1) := by
        intro N; simp only [hS_def, Finset.sum_range_succ]; linarith [hge N]
      set g : ℕ → ℕ := fun N => (2 * Q - S N).toNat with hg_def
      have hgle : ∀ N, g (N + 1) ≤ g N := by
        intro N; simp only [hg_def]
        have := hSmono N; have := hSbd N; have := hSbd (N + 1)
        rw [abs_le] at *; omega
      obtain ⟨T, hT⟩ := antitone_eventually_constant g hgle
      refine ⟨T, fun n hn => ?_⟩
      have e1 : S n = S (n + 1) := by
        have ha := hT n hn; have hb := hT (n + 1) (by omega)
        simp only [hg_def] at ha hb
        have b1 := hSbd n; have b2 := hSbd (n + 1); have b3 := hSbd T
        rw [abs_le] at b1 b2 b3; omega
      simp only [hS_def, Finset.sum_range_succ] at e1; linarith
    · have hSmono : ∀ N, S (N + 1) ≤ S N := by
        intro N; simp only [hS_def, Finset.sum_range_succ]; linarith [hle N]
      set g : ℕ → ℕ := fun N => (S N + 2 * Q).toNat with hg_def
      have hgle : ∀ N, g (N + 1) ≤ g N := by
        intro N; simp only [hg_def]
        have := hSmono N; have := hSbd N; have := hSbd (N + 1)
        rw [abs_le] at *; omega
      obtain ⟨T, hT⟩ := antitone_eventually_constant g hgle
      refine ⟨T, fun n hn => ?_⟩
      have e1 : S n = S (n + 1) := by
        have ha := hT n hn; have hb := hT (n + 1) (by omega)
        simp only [hg_def] at ha hb
        have b3 := hSbd T; rw [abs_le] at b3
        have b1 := hSbd n; have b2 := hSbd (n + 1)
        rw [abs_le] at b1 b2; omega
      simp only [hS_def, Finset.sum_range_succ] at e1; linarith
  -- `w = P` on a tail ⇒ period `Q`
  obtain ⟨T, hwPT⟩ := hwP
  refine ⟨Q, hQ, T + 1, fun n hn => ?_⟩
  have hw1 := hwPT (n - 1) (by omega)
  have hw2 := hwPT n (by omega)
  simp only [hw_def] at hw1 hw2
  have hq1 := qCount_succ h (n - 1)
  have hq2 := qCount_succ h (n - 1 + Q)
  rw [show n - 1 + 1 = n from by omega] at hq1
  rw [show n - 1 + Q + 1 = n + Q from by omega] at hq2
  have hbit : (if h n then (1 : ℕ) else 0) = (if h (n + Q) then 1 else 0) := by omega
  cases hb1 : h n <;> cases hb2 : h (n + Q) <;> simp_all

end MH
end Proof
end Erdos1112
