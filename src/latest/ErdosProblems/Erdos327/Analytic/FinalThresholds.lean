import ErdosProblems.Erdos327.Analytic.ScheduledInitialVanishing
import ErdosProblems.Erdos327.Analytic.CanonicalReduction

/-!
# Elementary final threshold selection

Once the analytic parameters and a finite schedule prefix are fixed, one
natural-number threshold simultaneously enforces the rough modulus, the
roughness cutoff, and inclusion of that prefix in the dyadic range.  A
second elementary lemma absorbs fixed additive constants into `N` times
any fixed positive density.
-/

namespace Erdos327.Analytic

open Real

noncomputable section

/-- One explicit threshold enforces all fixed arithmetic and dyadic
requirements used in the final assembly. -/
def finalArithmeticThreshold (L J : ℕ) : ℕ :=
  max L (max (4 * roughPrimeModulus L) (2 ^ J))

theorem le_finalArithmeticThreshold_left (L J : ℕ) :
    L ≤ finalArithmeticThreshold L J := by
  unfold finalArithmeticThreshold
  exact le_max_left _ _

theorem le_finalArithmeticThreshold_modulus (L J : ℕ) :
    4 * roughPrimeModulus L ≤ finalArithmeticThreshold L J := by
  unfold finalArithmeticThreshold
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem pow_le_finalArithmeticThreshold (L J : ℕ) :
    2 ^ J ≤ finalArithmeticThreshold L J := by
  unfold finalArithmeticThreshold
  exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem finalArithmeticThreshold_spec
    {L J N : ℕ} (hN : finalArithmeticThreshold L J ≤ N) :
    L ≤ N ∧
      4 * roughPrimeModulus L ≤ N ∧
      J ≤ Nat.log 2 N + 1 := by
  refine ⟨(le_finalArithmeticThreshold_left L J).trans hN,
    (le_finalArithmeticThreshold_modulus L J).trans hN, ?_⟩
  have hpow : 2 ^ J ≤ N :=
    (pow_le_finalArithmeticThreshold L J).trans hN
  exact (Nat.le_log_of_pow_le (by norm_num) hpow).trans
    (Nat.le_add_right _ _)

/-- Any fixed nonnegative constant is eventually at most `N` times a
fixed positive density. -/
theorem exists_nat_forall_const_le_nat_mul
    {ρ C : ℝ} (hρ : 0 < ρ) (_hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C ≤ (N : ℝ) * ρ := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (C / ρ)
  refine ⟨N₀, fun N hN ↦ ?_⟩
  have hcast : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hratio : C / ρ ≤ (N : ℝ) := hN₀.trans hcast
  exact (div_le_iff₀ hρ).mp hratio

/-- In particular, the exceptional `+1` in the mixed-edge reduction is
eventually absorbed by any prescribed positive fraction of the rough
density. -/
theorem exists_nat_forall_one_le_nat_mul_roughDensity_div
    {L : ℕ} (hL : 3 ≤ L) {D : ℝ} (hD : 0 < D) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (1 : ℝ) ≤ (N : ℝ) * Erdos327.roughDensity L / D := by
  have hρD : 0 < Erdos327.roughDensity L / D :=
    div_pos (Erdos327.roughDensity_pos hL) hD
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_forall_const_le_nat_mul hρD
      (by norm_num : (0 : ℝ) ≤ 1)
  refine ⟨N₀, fun N hN ↦ ?_⟩
  simpa [div_eq_mul_inv, mul_assoc] using hN₀ N hN

end

end Erdos327.Analytic
