import ErdosProblems.Erdos321.AdaptiveCutoff

namespace Erdos321

open Filter
open scoped Topology

private theorem adaptiveEndpoint_lower_of_log
    {N : ℕ} (hdata : AdaptiveCutoffData N)
    (hlog : 128 ≤ Real.log N) :
    Real.log N / 128 ≤ (adaptiveEndpoint N : ℝ) := by
  let L := adaptiveLogScale N
  let Q := adaptiveSmoothCutoff N
  let T := adaptiveEndpoint N
  have hLlower : Real.log N / 32 ≤ (L : ℝ) := by
    have hnext := Nat.lt_floor_add_one (Real.log N / 16)
    change Real.log N / 16 < (L : ℝ) + 1 at hnext
    nlinarith
  have hQ1 : 1 ≤ Q := hdata.smooth_ge_one
  have hQtwo : Q + 1 ≤ 2 * Q := by omega
  have hQL : Q * L ≤ N := by
    dsimp [Q, L, adaptiveSmoothCutoff]
    exact Nat.div_mul_le_self N (adaptiveLogScale N)
  have hk : L / 2 ≤ T := by
    dsimp [T, adaptiveEndpoint]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < Q + 1)).2
    calc
      (L / 2) * (Q + 1) ≤ (L / 2) * (2 * Q) :=
        Nat.mul_le_mul_left (L / 2) hQtwo
      _ = (2 * (L / 2)) * Q := by ring
      _ ≤ L * Q := Nat.mul_le_mul_right Q (Nat.mul_div_le L 2)
      _ = Q * L := Nat.mul_comm _ _
      _ ≤ N := hQL
  have hfloorHalf : (L : ℝ) / 2 - 1 < (L / 2 : ℕ) := by
    have hdiv := Nat.lt_mul_div_succ L (by norm_num : 0 < 2)
    have hdivR : (L : ℝ) < 2 * (((L / 2 : ℕ) : ℝ) + 1) := by
      exact_mod_cast hdiv
    linarith
  have hkReal : ((L / 2 : ℕ) : ℝ) ≤ T := by exact_mod_cast hk
  nlinarith

/-- The exact common adaptive endpoint is eventually between two fixed
positive multiples of `log N`. -/
theorem eventually_adaptiveEndpoint_comparable :
    ∀ᶠ N : ℕ in atTop,
      Real.log N / 128 ≤ (adaptiveEndpoint N : ℝ) ∧
        (adaptiveEndpoint N : ℝ) ≤ Real.log N / 16 := by
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog128 : ∀ᶠ N : ℕ in atTop, 128 ≤ Real.log (N : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop 128)
  filter_upwards [eventually_adaptiveCutoffData, hlog128] with N hdata hlog
  constructor
  · exact adaptiveEndpoint_lower_of_log hdata hlog
  · have hTL : (adaptiveEndpoint N : ℝ) ≤ adaptiveLogScale N := by
      exact_mod_cast (Nat.le_of_lt hdata.endpoint_lt_scale)
    have hfloor : ((adaptiveLogScale N : ℕ) : ℝ) ≤ Real.log N / 16 := by
      dsimp [adaptiveLogScale]
      exact Nat.floor_le (by positivity)
    exact hTL.trans hfloor

end Erdos321
