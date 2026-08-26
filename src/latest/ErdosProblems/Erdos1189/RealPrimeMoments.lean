/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Prime moments at real cutoffs, including the strict cutoff on p-1.
Informal argument: transfer through the natural ceiling, whose relative error tends to zero.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.PrimePowerAsymptotics

namespace Erdos1189

open Filter Asymptotics
open scoped Asymptotics

noncomputable def realLogPower (r : ℕ) (x : ℝ) : ℝ := x ^ r / Real.log x

lemma realLogPower_eventually_ne_zero (r : ℕ) : ∀ᶠ x in atTop, realLogPower r x ≠ 0 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact div_ne_zero (pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hx))) (Real.log_pos hx).ne'

lemma logPower_ceil_equivalent (r : ℕ) :
    (fun x : ℝ => logPower r (Nat.ceil x)) ~[atTop] realLogPower r := by
  have hc : (fun x : ℝ => (Nat.ceil x : ℝ)) ~[atTop] (fun x : ℝ => x) :=
    isEquivalent_nat_ceil
  have h := (hc.pow r).div (hc.log tendsto_id)
  change (fun x => (Nat.ceil x : ℝ) ^ r / Real.log (Nat.ceil x)) ~[atTop]
    (fun x : ℝ => x ^ r / Real.log x) at h
  exact h

lemma tendsto_moment_at_real_cutoff {f : ℕ → ℝ} {r : ℕ} {a : ℝ}
    (h : Tendsto (fun n => f n / logPower r n) atTop (nhds a)) :
    Tendsto (fun x : ℝ => f (Nat.ceil x) / realLogPower r x) atTop (nhds a) := by
  have hq := (isEquivalent_iff_tendsto_one (realLogPower_eventually_ne_zero r)).mp
    (logPower_ceil_equivalent r)
  have ht := (h.comp tendsto_nat_ceil_atTop).mul hq
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [tendsto_nat_ceil_atTop.eventually (logPower_eventually_ne_zero r)] with x hx
  dsimp only [Function.comp_apply, Pi.div_apply]
  field_simp

lemma mem_primesLE_ceil_iff {p : ℕ} {x : ℝ} :
    p ∈ Nat.primesLE (Nat.ceil x) ↔ p.Prime ∧ (p : ℝ) - 1 < x := by
  rw [Nat.mem_primesLE]
  constructor
  · rintro ⟨hpx, hp⟩
    have hpred : p - 1 < Nat.ceil x := by have := hp.pos; omega
    have h := Nat.lt_ceil.mp hpred
    rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one] at h
    exact ⟨hp, h⟩
  · rintro ⟨hp, hpx⟩
    have h : ((p - 1 : ℕ) : ℝ) < x := by
      simpa only [Nat.cast_sub hp.one_lt.le, Nat.cast_one] using hpx
    have hpred := Nat.lt_ceil.mpr h
    exact ⟨by have := hp.pos; omega, hp⟩

theorem real_prime_weight_sum_ratio :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ Nat.primesLE (Nat.ceil x), ((p : ℝ) - 1)) / realLogPower 2 x)
      atTop (nhds (1 / 2)) :=
  tendsto_moment_at_real_cutoff prime_weight_sum_ratio

theorem real_prime_weight_square_sum_ratio :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ Nat.primesLE (Nat.ceil x), ((p : ℝ) - 1) ^ 2) / realLogPower 3 x)
      atTop (nhds (1 / 3)) :=
  tendsto_moment_at_real_cutoff prime_weight_square_sum_ratio

end Erdos1189
