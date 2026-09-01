import ErdosProblems.Erdos321.AdaptiveCutoff

namespace Erdos321

open Filter Asymptotics
open scoped Topology

private noncomputable def badErrorMajorant (N : ℕ) : ℝ :=
  2 * (Real.log N ^ 4 / ((N : ℝ) ^ (1 / 2 : ℝ)))

private theorem tendsto_badErrorMajorant :
    Tendsto badErrorMajorant atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun x : ℝ => 2 * (Real.log x ^ 4 / (x ^ (1 / 2 : ℝ))))
      atTop (𝓝 0) := by
    have h :=
      (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
        (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
    simpa using h.const_mul 2
  change Tendsto
    (fun N : ℕ => 2 * (Real.log (N : ℝ) ^ 4 /
      ((N : ℝ) ^ (1 / 2 : ℝ)))) atTop (𝓝 0)
  convert hreal.comp tendsto_natCast_atTop_atTop using 1
  all_goals rfl

private theorem adaptive_badError_le_majorant {N : ℕ}
    (hdata : AdaptiveCutoffData N) :
    normalizedBadError N (adaptiveEndpoint N) ≤ badErrorMajorant N := by
  let T := adaptiveEndpoint N
  have hN2 : 2 ≤ N := by
    have := hdata.logScale_sq_le
    have hL := hdata.logScale_ge_four
    nlinarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog0 : 0 ≤ Real.log N := (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  have hT0 : (0 : ℝ) ≤ T := by positivity
  have hTlog : (T : ℝ) ≤ Real.log N := hdata.endpoint_le_log
  have hTsmall : (T : ℝ) ≤ Real.log N / 16 := by
    have hTL : (T : ℝ) ≤ adaptiveLogScale N := by
      exact_mod_cast (Nat.le_of_lt hdata.endpoint_lt_scale)
    have hfloor : ((adaptiveLogScale N : ℕ) : ℝ) ≤ Real.log N / 16 := by
      dsimp [adaptiveLogScale]
      exact Nat.floor_le (by positivity)
    exact hTL.trans hfloor
  have hlog3nonneg : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    norm_num at this ⊢
    exact this
  have hexponent : (T : ℝ) * Real.log 3 ≤ Real.log N / 2 := by
    have hmul := mul_le_mul hTsmall hlog3 hlog3nonneg (by positivity)
    nlinarith
  have hpow : (3 : ℝ) ^ T ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      (3 : ℝ) ^ T = Real.exp ((T : ℝ) * Real.log 3) := by
        rw [Real.exp_nat_mul, Real.exp_log (show (0 : ℝ) < 3 by norm_num)]
      _ ≤ Real.exp (Real.log N / 2) := Real.exp_le_exp.mpr hexponent
      _ = (N : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_def_of_pos hNpos]
        congr 1
        ring
  have hTplus : (T : ℝ) + 1 ≤ 2 * Real.log N := by
    nlinarith [hdata.log_ge_one]
  have hpoly : (T : ℝ) ^ 2 * (T + 1) ≤ 2 * Real.log N ^ 3 := by
    calc
      (T : ℝ) ^ 2 * (T + 1) ≤ Real.log N ^ 2 * (2 * Real.log N) := by
        gcongr
      _ = 2 * Real.log N ^ 3 := by ring
  have hspos : 0 < (N : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hNpos _
  have hss :
      (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hprod :
      (3 : ℝ) ^ T * ((T : ℝ) ^ 2 * (T + 1)) ≤
        (N : ℝ) ^ (1 / 2 : ℝ) * (2 * Real.log N ^ 3) := by
    exact mul_le_mul hpow hpoly (by positivity) (by positivity)
  have hrootdiv :
      (N : ℝ) ^ (1 / 2 : ℝ) / N =
        1 / ((N : ℝ) ^ (1 / 2 : ℝ)) := by
    field_simp [ne_of_gt hNpos, ne_of_gt hspos]
    simpa [pow_two] using hss
  dsimp [normalizedBadError, badErrorMajorant]
  calc
    Real.log N / N *
        ((3 : ℝ) ^ T * (T : ℝ) ^ 2 * (T + 1)) ≤
      Real.log N / N *
        ((N : ℝ) ^ (1 / 2 : ℝ) * (2 * Real.log N ^ 3)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa [mul_assoc] using hprod
    _ = 2 * (Real.log N ^ 4 / ((N : ℝ) ^ (1 / 2 : ℝ))) := by
      rw [show Real.log N / N *
          ((N : ℝ) ^ (1 / 2 : ℝ) * (2 * Real.log N ^ 3)) =
          2 * Real.log N ^ 4 * ((N : ℝ) ^ (1 / 2 : ℝ) / N) by ring,
        hrootdiv]
      ring

/-- At the common adaptive endpoint, the normalized global bad-prime loss
vanishes. -/
theorem tendsto_adaptive_normalizedBadError :
    Tendsto (fun N => normalizedBadError N (adaptiveEndpoint N))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_adaptiveCutoffData] with N hdata
    dsimp [normalizedBadError]
    positivity
  · filter_upwards [eventually_adaptiveCutoffData] with N hdata
    exact adaptive_badError_le_majorant hdata
  · exact tendsto_badErrorMajorant

private noncomputable def smoothErrorRemainder (N : ℕ) : ℝ :=
  2 * (Real.log N ^ 2 / (N : ℝ)) +
    6 * (Real.log N ^ 2 / ((N : ℝ) ^ (1 / 2 : ℝ)))

private theorem tendsto_smoothErrorRemainder :
    Tendsto smoothErrorRemainder atTop (𝓝 0) := by
  have hfirstR : Tendsto
      (fun x : ℝ => 2 * (Real.log x ^ 2 / x)) atTop (𝓝 0) := by
    simpa using
      (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero.const_mul 2
  have hsecondR : Tendsto
      (fun x : ℝ => 6 * (Real.log x ^ 2 / (x ^ (1 / 2 : ℝ))))
      atTop (𝓝 0) := by
    have h :=
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
        (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
    simpa using h.const_mul 6
  have hreal : Tendsto
      (fun x : ℝ => 2 * (Real.log x ^ 2 / x) +
        6 * (Real.log x ^ 2 / (x ^ (1 / 2 : ℝ)))) atTop (𝓝 0) := by
    simpa using hfirstR.add hsecondR
  change Tendsto
    (fun N : ℕ => 2 * (Real.log (N : ℝ) ^ 2 / (N : ℝ)) +
      6 * (Real.log (N : ℝ) ^ 2 / ((N : ℝ) ^ (1 / 2 : ℝ))))
      atTop (𝓝 0)
  convert hreal.comp tendsto_natCast_atTop_atTop using 1
  all_goals rfl

private theorem adaptive_smoothError_le {N : ℕ}
    (hdata : AdaptiveCutoffData N) (hlog : 32 ≤ Real.log N) :
    normalizedSmoothError N (adaptiveSmoothCutoff N) ≤
      96 + smoothErrorRemainder N := by
  let L := adaptiveLogScale N
  let Q := adaptiveSmoothCutoff N
  have hN2 : 2 ≤ N := by
    have := hdata.logScale_sq_le
    have hL := hdata.logScale_ge_four
    nlinarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog0 : 0 ≤ Real.log N := by linarith
  have hLlower : Real.log N / 32 ≤ (L : ℝ) := by
    have hnext := Nat.lt_floor_add_one (Real.log N / 16)
    change Real.log N / 16 < (L : ℝ) + 1 at hnext
    nlinarith
  have hQLnat : Q * L ≤ N := by
    dsimp [Q, adaptiveSmoothCutoff]
    exact Nat.div_mul_le_self N L
  have hQL : (Q : ℝ) * L ≤ N := by exact_mod_cast hQLnat
  have hlogLe : Real.log N ≤ 32 * (L : ℝ) := by nlinarith
  have hQlog : (Q : ℝ) * Real.log N ≤ 32 * N := by
    calc
      (Q : ℝ) * Real.log N ≤ Q * (32 * L) :=
        mul_le_mul_of_nonneg_left hlogLe (by positivity)
      _ = 32 * (Q * L) := by ring
      _ ≤ 32 * N := by gcongr
  have hlog4nonneg : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at this ⊢
    exact this
  have hBnum :
      Real.log N * (Real.log 4 * (Q : ℝ)) ≤ 96 * N := by
    calc
      Real.log N * (Real.log 4 * (Q : ℝ)) =
          Real.log 4 * ((Q : ℝ) * Real.log N) := by ring
      _ ≤ Real.log 4 * (32 * N) :=
        mul_le_mul_of_nonneg_left hQlog hlog4nonneg
      _ ≤ 3 * (32 * N) :=
        mul_le_mul_of_nonneg_right hlog4 (by positivity)
      _ = 96 * N := by ring
  have hB : Real.log N / N * (Real.log 4 * (Q : ℝ)) ≤ 96 := by
    calc
      Real.log N / N * (Real.log 4 * (Q : ℝ)) =
          (Real.log N * (Real.log 4 * (Q : ℝ))) / N := by ring
      _ ≤ 96 := (div_le_iff₀ hNpos).2 (by simpa using hBnum)
  have hNN : N + 1 ≤ N * N := by nlinarith
  have hlogNp : Real.log (N + 1) ≤ 2 * Real.log N := by
    have hcast : (N : ℝ) + 1 ≤ (N : ℝ) * N := by exact_mod_cast hNN
    have hmono := Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < N + 1 by positivity)
      (show (0 : ℝ) < (N : ℝ) * N by positivity) hcast
    rw [Real.log_mul (ne_of_gt hNpos) (ne_of_gt hNpos)] at hmono
    nlinarith
  have hA : Real.log N / N * Real.log (N + 1) ≤
      2 * (Real.log N ^ 2 / N) := by
    have hm := mul_le_mul_of_nonneg_left hlogNp (by positivity : 0 ≤ Real.log N / N)
    calc
      Real.log N / N * Real.log (N + 1) ≤
          Real.log N / N * (2 * Real.log N) := hm
      _ = 2 * (Real.log N ^ 2 / N) := by ring
  have hQ1 : 1 ≤ Q := hdata.smooth_ge_one
  have hQN : Q ≤ N := hdata.smooth_le
  have hlogQ0 : 0 ≤ Real.log (Q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hQ1)
  have hlogQ : Real.log (Q : ℝ) ≤ Real.log N := by
    exact Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < Q by exact_mod_cast (show 0 < Q by omega))
      (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega))
      (by exact_mod_cast hQN)
  have hsqrtQ : Real.sqrt Q ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      Real.sqrt Q ≤ Real.sqrt N := Real.sqrt_le_sqrt (by exact_mod_cast hQN)
      _ = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hroot0 : 0 ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (le_of_lt hNpos) _
  have hinside :
      4 * Real.sqrt Q * Real.log Q + 2 * Real.sqrt N * Real.log N ≤
        6 * ((N : ℝ) ^ (1 / 2 : ℝ)) * Real.log N := by
    have hprod : Real.sqrt Q * Real.log Q ≤
        (N : ℝ) ^ (1 / 2 : ℝ) * Real.log N :=
      mul_le_mul hsqrtQ hlogQ hlogQ0 hroot0
    simp only [Real.sqrt_eq_rpow] at hprod ⊢
    nlinarith
  have hspos : 0 < (N : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hNpos _
  have hss :
      (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hrootdiv :
      (N : ℝ) ^ (1 / 2 : ℝ) / N =
        1 / ((N : ℝ) ^ (1 / 2 : ℝ)) := by
    field_simp [ne_of_gt hNpos, ne_of_gt hspos]
    simpa [pow_two] using hss
  have hCD : Real.log N / N *
      (4 * Real.sqrt Q * Real.log Q + 2 * Real.sqrt N * Real.log N) ≤
      6 * (Real.log N ^ 2 / ((N : ℝ) ^ (1 / 2 : ℝ))) := by
    calc
      Real.log N / N *
          (4 * Real.sqrt Q * Real.log Q + 2 * Real.sqrt N * Real.log N) ≤
        Real.log N / N *
          (6 * ((N : ℝ) ^ (1 / 2 : ℝ)) * Real.log N) :=
            mul_le_mul_of_nonneg_left hinside (by positivity)
      _ = 6 * (Real.log N ^ 2 / ((N : ℝ) ^ (1 / 2 : ℝ))) := by
        rw [show Real.log N / N *
            (6 * ((N : ℝ) ^ (1 / 2 : ℝ)) * Real.log N) =
            6 * Real.log N ^ 2 *
              ((N : ℝ) ^ (1 / 2 : ℝ) / N) by ring,
          hrootdiv]
        ring
  dsimp [normalizedSmoothError, smoothErrorRemainder]
  calc
    Real.log N / N *
        (Real.log (N + 1) +
          (Real.log 4 * Q + 4 * Real.sqrt Q * Real.log Q +
            2 * Real.sqrt N * Real.log N)) =
      Real.log N / N * Real.log (N + 1) +
        Real.log N / N * (Real.log 4 * Q) +
        Real.log N / N *
          (4 * Real.sqrt Q * Real.log Q + 2 * Real.sqrt N * Real.log N) := by
            ring
    _ ≤ 2 * (Real.log N ^ 2 / N) + 96 +
        6 * (Real.log N ^ 2 / ((N : ℝ) ^ (1 / 2 : ℝ))) :=
      add_le_add (add_le_add hA hB) hCD
    _ = 96 +
        (2 * (Real.log N ^ 2 / N) +
          6 * (Real.log N ^ 2 / ((N : ℝ) ^ (1 / 2 : ℝ)))) := by ring

/-- The smooth-LCM source in the adaptive normalized upper recurrence is
bounded by an absolute constant. -/
theorem eventually_adaptive_normalizedSmoothError_le :
    ∀ᶠ N : ℕ in atTop,
      normalizedSmoothError N (adaptiveSmoothCutoff N) ≤ 100 := by
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog32 : ∀ᶠ N : ℕ in atTop, 32 ≤ Real.log (N : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop 32)
  have hrem : ∀ᶠ N : ℕ in atTop, smoothErrorRemainder N ≤ 4 :=
    tendsto_smoothErrorRemainder.eventually
      (Iic_mem_nhds (show (0 : ℝ) < 4 by norm_num))
  filter_upwards [eventually_adaptiveCutoffData, hlog32, hrem] with N hdata hlog hrem
  have hmain := adaptive_smoothError_le hdata hlog
  linarith

end Erdos321
