import ErdosProblems.Erdos547.PairDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform large-order bounds for the exposure potential
-/

namespace Erdos547

open Filter
open scoped Topology

theorem exp_neg_nat_le_half_pow (d : ℕ) : Real.exp (-(d : ℝ)) ≤ (1 / 2 : ℝ) ^ d := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hhalf : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) htwo
  have hpow := pow_le_pow_left₀ (Real.exp_nonneg (-1)) hhalf d
  simpa only [← Real.exp_nat_mul, mul_neg_one] using hpow

theorem pair_decay_threshold_of_exp_bound {N k e d : ℕ}
    (hN : 0 < N) (hk : k ≤ N) (a b : ℝ)
    (ha : a ≤ (k : ℝ) ^ 2 / (8 * (N : ℝ) ^ 2))
    (hmargin : (d : ℝ) + b ≤ a * e)
    (hsmall : (N : ℝ) * Real.exp (-b) < 1) :
    pairDecay N k ^ e * N < (1 / 2 : ℝ) ^ d := by
  have hbase : pairDecay N k ≤ Real.exp (-a) := by
    have hle : pairDecay N k ≤ 1 - a := by unfold pairDecay; linarith
    exact hle.trans (Real.one_sub_le_exp_neg a)
  have hpow := pow_le_pow_left₀ (pairDecay_nonneg hN hk) hbase e
  rw [← Real.exp_nat_mul] at hpow
  have hexp : Real.exp ((e : ℝ) * (-a)) ≤ Real.exp (-(d : ℝ)) * Real.exp (-b) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hmargin]
  have hfull := mul_le_mul_of_nonneg_right (hpow.trans hexp) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  calc
    pairDecay N k ^ e * N ≤ Real.exp (-(d : ℝ)) * ((N : ℝ) * Real.exp (-b)) := by
      nlinarith only [hfull]
    _ < Real.exp (-(d : ℝ)) := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left hsmall (Real.exp_pos (-(d : ℝ)))
    _ ≤ _ := exp_neg_nat_le_half_pow d

/-- The decay estimate holds uniformly over all host sizes, integer pair
counts and deficits satisfying fixed linear bounds. -/
theorem eventually_pair_decay_threshold (α β γ : ℝ) (hα : 0 < α)
    (hgap : γ < α ^ 2 * β / 32) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ N k e d : ℕ,
      0 < N → N ≤ 2 * m → k ≤ N → α * m ≤ k → β * m ≤ e → (d : ℝ) ≤ γ * m →
        pairDecay N k ^ e * N < (1 / 2 : ℝ) ^ d := by
  let a := α ^ 2 / 32
  let c := a * β - γ
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c, a]; nlinarith only [hgap]
  have hlim : Tendsto (fun x : ℝ ↦ 2 * x * Real.exp (-c * x)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc).const_mul 2
    simpa only [Real.rpow_one, mul_zero, mul_assoc] using h
  have hlimNat := hlim.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ m : ℕ in atTop, 2 * (m : ℝ) * Real.exp (-c * m) < 1 :=
    (tendsto_order.1 hlimNat).2 1 (by norm_num)
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 hevent
  refine ⟨m₀, ?_⟩
  intro m hm N k e d hN hNm hk hkm hem hdm
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNmr : (N : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hNm
  have hfrac : a ≤ (k : ℝ) ^ 2 / (8 * (N : ℝ) ^ 2) := by
    apply (le_div_iff₀ (show (0 : ℝ) < 8 * (N : ℝ) ^ 2 by positivity)).mpr
    have hNsq : (N : ℝ) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by
      nlinarith only [hNmr, (Nat.cast_nonneg N : (0 : ℝ) ≤ N),
        (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hksq : α ^ 2 * (m : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by
      have hnonneg : 0 ≤ α * (m : ℝ) := by positivity
      nlinarith only [hkm, hnonneg, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hmul := mul_le_mul_of_nonneg_left hNsq (sq_nonneg α)
    dsimp [a]
    nlinarith only [hmul, hksq]
  have hmargin : (d : ℝ) + c * m ≤ a * e := by
    have hmul := mul_le_mul_of_nonneg_left hem ha.le
    dsimp [c]
    nlinarith only [hdm, hmul]
  have hsmall : (N : ℝ) * Real.exp (-(c * m)) < 1 := by
    have hle := mul_le_mul_of_nonneg_right hNmr (Real.exp_nonneg (-c * m))
    have hlt := hm₀ m hm
    simpa only [neg_mul] using hle.trans_lt hlt
  exact pair_decay_threshold_of_exp_bound hN hk a (c * m) hfrac hmargin hsmall

end Erdos547

#print axioms Erdos547.eventually_pair_decay_threshold
