import ErdosProblems.Erdos4.FGKMTGrowingIndexBounds
import ErdosProblems.Erdos4.FGKMTInitialErrorBudget

/-! Dyadic covering rounds and their surviving density at the growing sieve dimension. -/

namespace Erdos4.FGKMT

open Filter

noncomputable def growingRounds (x : ℕ) : ℕ := Nat.log 2 (growingIndex x)

noncomputable def growingCoverDensity (x : ℕ) : ℝ := (1 / 2 : ℝ) ^ growingRounds x

theorem dyadic_log_density_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 / (n : ℝ) ≤ (1 / 2 : ℝ) ^ Nat.log 2 n ∧
      (1 / 2 : ℝ) ^ Nat.log 2 n ≤ 2 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 n := by positivity
  have hlo : (2 : ℝ) ^ Nat.log 2 n ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hup : (n : ℝ) ≤ 2 * (2 : ℝ) ^ Nat.log 2 n := by
    have hh := (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n).le
    rw [pow_succ] at hh
    exact_mod_cast (by simpa only [mul_comm] using hh)
  rw [one_div_pow]
  constructor
  · exact div_le_div_of_nonneg_left (by norm_num) hp hlo
  · apply (div_le_div_iff₀ hp hnpos).mpr
    simpa only [one_mul] using hup

theorem growingRounds_le_index (x : ℕ) : growingRounds x ≤ growingIndex x :=
  Nat.log_le_self _ _

theorem growingIndex_le_dimension (x : ℕ) :
    growingIndex x ≤ sieveDimension (growingIndex x) := by
  exact (Nat.lt_two_pow_self (n := growingIndex x)).le

theorem growingRounds_power_bound {x : ℕ} (hx : 1 ≤ growingIndex x) :
    8 ^ growingRounds x ≤ sieveDimension (growingIndex x) ^ 3 := by
  have hh : 2 ^ growingRounds x ≤ growingIndex x :=
    Nat.pow_log_le_self 2 (by omega : growingIndex x ≠ 0)
  have hpow := Nat.pow_le_pow_left (hh.trans (growingIndex_le_dimension x)) 3
  calc
    8 ^ growingRounds x = (2 ^ growingRounds x) ^ 3 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    _ ≤ _ := hpow

theorem eventually_growing_cover_parameters :
    ∀ᶠ x : ℕ in atTop,
      1 ≤ growingIndex x ∧
      (growingIndex x : ℝ) ≤ Real.log (x : ℝ) ∧
      (growingRounds x : ℝ) ≤ Real.log (x : ℝ) ∧
      1 / Real.log (x : ℝ) ≤ growingCoverDensity x ∧
      1 / (sieveDimension (growingIndex x) : ℝ) ≤ growingCoverDensity x ∧
      growingCoverDensity x ≤ 2 / (growingIndex x : ℝ) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [growingIndex_tendsto.eventually (eventually_ge_atTop 1),
    eventually_growingDimension_bounds, hlog.eventually (eventually_ge_atTop 1)]
    with x hj hdim hL
  change 1 ≤ Real.log (x : ℝ) at hL
  have hjpos : (0 : ℝ) < growingIndex x := by exact_mod_cast hj
  have hjk : (growingIndex x : ℝ) ≤ sieveDimension (growingIndex x) := by
    exact_mod_cast growingIndex_le_dimension x
  have hkL : (sieveDimension (growingIndex x) : ℝ) ≤ Real.log (x : ℝ) := by
    apply hdim.2.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL
      (by norm_num : (1 / 100 : ℝ) ≤ 1)
  have hjL := hjk.trans hkL
  have hmj : (growingRounds x : ℝ) ≤ growingIndex x := by
    exact_mod_cast growingRounds_le_index x
  obtain ⟨hκlow, hκhigh⟩ := dyadic_log_density_bounds hj
  refine ⟨hj, hjL, hmj.trans hjL, ?_, ?_, hκhigh⟩
  · exact (div_le_div_of_nonneg_left (by norm_num) hjpos hjL).trans hκlow
  · exact (div_le_div_of_nonneg_left (by norm_num) hjpos hjk).trans hκlow

end Erdos4.FGKMT
