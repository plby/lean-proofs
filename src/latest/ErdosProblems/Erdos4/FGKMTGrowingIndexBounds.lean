import ErdosProblems.Erdos4.FGKMTGrowingParameters

/-! The dyadic sieve index has the same order as the second logarithm of the endpoint. -/

namespace Erdos4.FGKMT

open Filter

theorem log_growingDimension (x : ℕ) :
    Real.log (sieveDimension (growingIndex x) : ℝ) = (growingIndex x : ℝ) * Real.log 2 := by
  rw [sieveDimension, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem eventually_growingIndex_log_bounds :
    ∀ᶠ x : ℕ in atTop,
      Real.log (Real.log (x : ℝ)) / (200 * Real.log 2) ≤ (growingIndex x : ℝ) ∧
      (growingIndex x : ℝ) ≤ Real.log (Real.log (x : ℝ)) / (100 * Real.log 2) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_growingDimension_bounds,
    hlog.eventually (eventually_ge_atTop 1),
    hloglog.eventually (eventually_ge_atTop (200 * Real.log 4))]
    with x hdim hL hlarge
  let L := Real.log (x : ℝ)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hkpos : (0 : ℝ) < sieveDimension (growingIndex x) := by
    rw [sieveDimension, Nat.cast_pow, Nat.cast_ofNat]
    positivity
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlo := Real.log_le_log (by positivity : 0 < L ^ (1 / 100 : ℝ) / 4) hdim.1
  rw [Real.log_div (Real.rpow_pos_of_pos hLpos _).ne' (by norm_num : (4 : ℝ) ≠ 0),
    Real.log_rpow hLpos, log_growingDimension] at hlo
  have hup := Real.log_le_log hkpos hdim.2
  rw [log_growingDimension, Real.log_rpow hLpos] at hup
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 200 * Real.log 2)).mpr
    change 200 * Real.log 4 ≤ Real.log L at hlarge
    nlinarith
  · apply (le_div_iff₀ (by positivity : 0 < 100 * Real.log 2)).mpr
    nlinarith

end Erdos4.FGKMT
