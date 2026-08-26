import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Omega

/-! # Elementary ratio-limit lemmas for geometric block representations -/

namespace Erdos1123

open Filter
open scoped Topology

theorem increments_upper_bound (a d : ℕ → ℝ) (ε : ℝ) (N : ℕ)
    (h : ∀ n ≥ N, a (n + 1) - a n ≤ ε * (d (n + 1) - d n)) :
    ∀ n ≥ N, a n - a N ≤ ε * (d n - d N) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hstep := h n hn
    linarith

/-- The zero-limit case of the Stolz--Cesàro argument, proved by summing an
eventual bound on increments. -/
theorem ratio_zero_of_increment_ratio_zero (a d : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hd : ∀ n, 0 < d n)
    (hdStep : ∀ n, 0 < d (n + 1) - d n) (hdTop : Tendsto d atTop atTop)
    (hStep : Tendsto (fun n => (a (n + 1) - a n) / (d (n + 1) - d n)) atTop (𝓝 0)) :
    Tendsto (fun n => a n / d n) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    exact Eventually.of_forall (fun n => hl.trans_le (div_nonneg (ha n) (hd n).le))
  · intro ε hε
    have hsmall := hStep.eventually (gt_mem_nhds (half_pos hε))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    have hIncrement (n : ℕ) (hn : N ≤ n) :
        a (n + 1) - a n ≤ (ε / 2) * (d (n + 1) - d n) :=
      ((div_lt_iff₀ (hdStep n)).mp (hN n hn)).le
    have hBound := increments_upper_bound a d (ε / 2) N hIncrement
    have hconst : Tendsto (fun n => a N / d n) atTop (𝓝 0) :=
      hdTop.const_div_atTop (a N)
    filter_upwards [hconst.eventually (gt_mem_nhds (half_pos hε)), eventually_ge_atTop N] with n hn hNn
    have hc := (div_lt_iff₀ (hd n)).mp hn
    have hb := hBound n hNn
    have hprod : 0 ≤ (ε / 2) * d N := mul_nonneg (half_pos hε).le (hd N).le
    apply (div_lt_iff₀ (hd n)).2
    nlinarith

/-- Sampling along a cofinal increasing sequence does not change a zero ratio
limit when adjacent sampled denominators grow by at most a factor of two. -/
theorem ratio_zero_iff_sampled (a d : ℕ → ℝ) (b : ℕ → ℕ)
    (ha : ∀ n, 0 ≤ a n) (hd : ∀ n, 0 ≤ d n)
    (haMono : Monotone a) (hdMono : Monotone d) (hb : StrictMono b)
    (hdPos : ∀ k, 0 < d (b k))
    (hdGrow : ∀ k, d (b (k + 1)) ≤ 2 * d (b k)) :
    Tendsto (fun n => a n / d n) atTop (𝓝 0) ↔
      Tendsto (fun k => a (b k) / d (b k)) atTop (𝓝 0) := by
  constructor
  · intro h
    exact h.comp hb.tendsto_atTop
  · intro h
    apply tendsto_order.2
    constructor
    · intro l hl
      exact Eventually.of_forall (fun n => hl.trans_le (div_nonneg (ha n) (hd n)))
    · intro ε hε
      obtain ⟨K, hK⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds (half_pos hε)))
      apply eventually_atTop.mpr
      refine ⟨b K, fun n hn => ?_⟩
      have hex : ∃ j, n < b j :=
        (hb.tendsto_atTop.eventually (eventually_gt_atTop n)).exists
      let j := Nat.find hex
      have hj : n < b j := Nat.find_spec hex
      have hKj : K < j := by
        by_contra hnot
        have hle := hb.monotone (Nat.le_of_not_gt hnot)
        omega
      have hj₀ : 0 < j := (Nat.zero_le K).trans_lt hKj
      have hjpred : j - 1 < j := Nat.sub_lt hj₀ (by decide)
      have hbpred : b (j - 1) ≤ n := by
        exact Nat.le_of_not_gt (Nat.find_min hex hjpred)
      have hdn : 0 < d n := (hdPos (j - 1)).trans_le (hdMono hbpred)
      have hratio := (div_lt_iff₀ (hdPos j)).mp (hK j hKj.le)
      have hsucc : j - 1 + 1 = j := by omega
      have hgrowth := hdGrow (j - 1)
      rw [hsucc] at hgrowth
      have hdenom : d (b j) ≤ 2 * d n :=
        hgrowth.trans (mul_le_mul_of_nonneg_left (hdMono hbpred) (by norm_num))
      have hscaled := mul_le_mul_of_nonneg_left hdenom (half_pos hε).le
      have han := haMono hj.le
      apply (div_lt_iff₀ hdn).2
      nlinarith

end Erdos1123
