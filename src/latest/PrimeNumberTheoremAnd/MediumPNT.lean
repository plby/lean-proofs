import BoundedGaps.PrimeNumberTheorem.Analytic.StrongChebyshev

open Filter Asymptotics
open scoped Chebyshev Topology

/-!
# A medium-strength prime number theorem

This is the interface supplied by the `PrimeNumberTheoremAnd` development.
The original file was accidentally omitted when the Erdos 321 formalization
was imported.  We derive the same estimate from the stronger Chebyshev bound
available in the pinned `BoundedGaps` dependency.
-/

/-- The Chebyshev psi function has a subexponential error term. -/
theorem MediumPNT : ∃ c > 0,
    (Chebyshev.psi - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
  obtain ⟨C, c, hC, hc, X₀, _hX₀, hpsi⟩ :=
    BoundedGaps.PrimeNumberTheorem.exists_abs_chebyshevPsi_sub_natCast_le_exp_neg_sqrtLog
  let d : ℝ := min (c / 2) (1 / 2)
  have hd : 0 < d := lt_min (half_pos hc) (by norm_num)
  refine ⟨d, hd, ?_⟩
  rw [isBigO_iff]
  refine ⟨C + 1, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ),
      tendsto_nat_floor_atTop.eventually_ge_atTop X₀,
      Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log 2),
      Real.tendsto_log_atTop.eventually_ge_atTop 2] with x hx hnX hlog_two hlog
  let n : ℕ := ⌊x⌋₊
  have hx_pos : 0 < x := by
    apply lt_of_le_of_ne hx
    intro h
    subst x
    norm_num at hlog
  have hx_two : 2 ≤ x := by
    have hexp_two : Real.exp 2 ≤ x :=
      (Real.le_log_iff_exp_le hx_pos).mp hlog
    exact (Real.exp_one_gt_two.le.trans
      (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2))).trans hexp_two
  have hn_le : (n : ℝ) ≤ x := by
    exact Nat.floor_le hx
  have hx_lt : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hx_half_le_n : x / 2 ≤ (n : ℝ) := by linarith
  have hn_pos : (0 : ℝ) < n := (half_pos hx_pos).trans_le hx_half_le_n
  have hlog_half : Real.log x / 2 ≤ Real.log (n : ℝ) := by
    calc
      Real.log x / 2 ≤ Real.log x - Real.log 2 := by linarith
      _ = Real.log (x / 2) := by
        rw [Real.log_div hx_pos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
      _ ≤ Real.log (n : ℝ) := Real.strictMonoOn_log.monotoneOn
        (half_pos hx_pos) hn_pos hx_half_le_n
  have hlog_nonneg : 0 ≤ Real.log x := by linarith
  have hlog_half_one : 1 ≤ Real.log x / 2 := by linarith
  have hroot : (Real.log x) ^ ((1 : ℝ) / 10) / 2 ≤
      Real.sqrt (Real.log (n : ℝ)) := by
    calc
      (Real.log x) ^ ((1 : ℝ) / 10) / 2 ≤
          (Real.log x) ^ ((1 : ℝ) / 10) / 2 ^ ((1 : ℝ) / 10) := by
        gcongr
        exact Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num)
      _ = (Real.log x / 2) ^ ((1 : ℝ) / 10) := by
        rw [Real.div_rpow hlog_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ (Real.log x / 2) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hlog_half_one (by norm_num)
      _ = Real.sqrt (Real.log x / 2) := by
        rw [Real.sqrt_eq_rpow]
      _ ≤ Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_le_sqrt hlog_half
  have hd_le_c_half : d ≤ c / 2 := min_le_left _ _
  have hd_le_one : d ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hexponent :
      d * (Real.log x) ^ ((1 : ℝ) / 10) ≤
        c * Real.sqrt (Real.log (n : ℝ)) := by
    calc
      d * (Real.log x) ^ ((1 : ℝ) / 10) ≤
          (c / 2) * (Real.log x) ^ ((1 : ℝ) / 10) := by
        gcongr
      _ = c * ((Real.log x) ^ ((1 : ℝ) / 10) / 2) := by ring
      _ ≤ c * Real.sqrt (Real.log (n : ℝ)) := by gcongr
  have hscale_one : 1 ≤
      x * Real.exp (-d * (Real.log x) ^ ((1 : ℝ) / 10)) := by
    have hlog_pow_le :
        (Real.log x) ^ ((1 : ℝ) / 10) ≤ Real.log x :=
      Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
    have hdpow_le : d * (Real.log x) ^ ((1 : ℝ) / 10) ≤ Real.log x :=
      calc
        d * (Real.log x) ^ ((1 : ℝ) / 10) ≤
            1 * (Real.log x) ^ ((1 : ℝ) / 10) := by gcongr
        _ ≤ Real.log x := by simpa using hlog_pow_le
    calc
      1 = x * Real.exp (-Real.log x) := by
        rw [Real.exp_neg, Real.exp_log hx_pos]
        field_simp
      _ ≤ x * Real.exp (-d * (Real.log x) ^ ((1 : ℝ) / 10)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith)) hx
  have hpsi_n := hpsi n hnX
  have hpsi_bound :
      |Chebyshev.psi (n : ℝ) - (n : ℝ)| ≤
        C * (x * Real.exp (-d * (Real.log x) ^ ((1 : ℝ) / 10))) := by
    have hexp_bound :
        Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) ≤
          Real.exp (-d * (Real.log x) ^ ((1 : ℝ) / 10)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hnexp_bound :
        (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) ≤
          x * Real.exp (-d * (Real.log x) ^ ((1 : ℝ) / 10)) :=
      mul_le_mul hn_le hexp_bound (Real.exp_nonneg _) hx
    calc
      |Chebyshev.psi (n : ℝ) - (n : ℝ)| ≤
          C * ((n : ℝ) * Real.exp
            (-c * Real.sqrt (Real.log (n : ℝ)))) := hpsi_n
      _ ≤ C * (x * Real.exp
          (-d * (Real.log x) ^ ((1 : ℝ) / 10))) :=
        mul_le_mul_of_nonneg_left hnexp_bound hC.le
  have hfloor_error : |(n : ℝ) - x| ≤ 1 := Nat.abs_floor_sub_le hx
  have hmain : |Chebyshev.psi x - x| ≤
      (C + 1) * (x * Real.exp
        (-d * (Real.log x) ^ ((1 : ℝ) / 10))) := by
    rw [Chebyshev.psi_eq_psi_coe_floor x]
    calc
      |Chebyshev.psi (n : ℝ) - x| ≤
          |Chebyshev.psi (n : ℝ) - (n : ℝ)| + |(n : ℝ) - x| := by
        simpa only [sub_add_sub_cancel] using
          abs_add_le (Chebyshev.psi (n : ℝ) - (n : ℝ)) ((n : ℝ) - x)
      _ ≤ C * (x * Real.exp
            (-d * (Real.log x) ^ ((1 : ℝ) / 10))) + 1 :=
        add_le_add hpsi_bound hfloor_error
      _ ≤ C * (x * Real.exp
            (-d * (Real.log x) ^ ((1 : ℝ) / 10))) +
          1 * (x * Real.exp
            (-d * (Real.log x) ^ ((1 : ℝ) / 10))) := by
        exact add_le_add (le_refl _) (by simpa using hscale_one)
      _ = (C + 1) * (x * Real.exp
          (-d * (Real.log x) ^ ((1 : ℝ) / 10))) := by ring
  simpa [Real.norm_eq_abs, abs_of_pos hx_pos, Function.id_def,
    abs_of_pos (Real.exp_pos _), abs_of_pos hC] using hmain
