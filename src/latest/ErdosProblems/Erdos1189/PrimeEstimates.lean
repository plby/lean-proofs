/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Prime-counting estimates for the quantitative frame constructions.
The prime number theorem used here is the existing unconditional theorem in
BoundedGaps.PrimeNumberTheorem.Analytic.PrimeCounting, whose axiom audit gives
only propext, Classical.choice, and Quot.sound.
Formal author of the estimates in this file: OpenAI Codex.
-/

import BoundedGaps.PrimeNumberTheorem.Proof.MainTheorem
import ErdosProblems.Erdos1189.PrimeWeights

namespace Erdos1189

open Filter Asymptotics
open scoped Asymptotics

lemma primeCounting_equivalent :
    (fun n : ℕ => (Nat.primeCounting n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) / Real.log n) :=
  BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent

lemma eventually_primeCounting_log_bounds :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ≤ 2 * Nat.primeCounting n * Real.log n ∧
        (Nat.primeCounting n : ℝ) * Real.log n ≤ 2 * n := by
  have ht : Tendsto (fun n : ℕ =>
      (Nat.primeCounting n : ℝ) * Real.log n / n) atTop (nhds 1) :=
    BoundedGaps.unconditional_ordinaryPrimeNumberTheorem
  filter_upwards [(tendsto_order.mp ht).1 (1 / 2) (by norm_num),
    (tendsto_order.mp ht).2 2 (by norm_num), eventually_ge_atTop 1] with n hlo hhi hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [lt_div_iff₀ hnpos] at hlo
  rw [div_lt_iff₀ hnpos] at hhi
  constructor <;> nlinarith

lemma primeCounting_sublinear :
    (fun n : ℕ => (Nat.primeCounting n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  apply primeCounting_equivalent.trans_isLittleO
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · exact Eventually.of_forall fun n hn => by simp [hn]
  · have ht : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    apply ht.inv_tendsto_atTop.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    dsimp
    field_simp

lemma eventually_primeCounting_mul_le (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, (Nat.primeCounting (K * q) : ℝ) ≤ ε * q := by
  by_cases hK : K = 0
  · subst K
    exact Eventually.of_forall fun q => by
      simp only [zero_mul, Nat.primeCounting_zero, Nat.cast_zero]
      positivity
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  have ht : Tendsto (fun q : ℕ => K * q) atTop atTop := by
    apply tendsto_atTop_mono (fun q => Nat.le_mul_of_pos_left q (Nat.pos_of_ne_zero hK)) tendsto_id
  have hb := ht.eventually (primeCounting_sublinear.bound (div_pos hε hKpos))
  filter_upwards [hb] with q hq
  simp only [Real.norm_eq_abs, Nat.cast_nonneg, abs_of_nonneg, Nat.cast_mul] at hq
  rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg K) (Nat.cast_nonneg q))] at hq
  calc
    (Nat.primeCounting (K * q) : ℝ) ≤ ε / K * (K * q) := hq
    _ = ε * q := by field_simp

end Erdos1189
