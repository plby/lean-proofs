import ErdosProblems.Erdos67.MRGSShiftedTrapezoid

/-!
# A linear-height logarithmic power-sum error

The second-order trapezoidal estimate is split at `ceil |t|`.  The initial
segment is bounded trivially, while the inverse-square error on the remaining
cells is summable with a gain from the split point.  This produces an
`O(1 + |t|)` error rather than the global quadratic-height envelope.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67

noncomputable section

/-- The elementary main term for the logarithmic power sum. -/
def gsLogPowerMain (t : ℝ) (M : ℕ) : ℂ :=
  ((M : ℂ) ^ (1 - Complex.I * (t : ℂ))) /
    (1 - Complex.I * (t : ℂ))

theorem norm_gsLogPowerMain_le (t : ℝ) {M : ℕ} (hM : 0 < M) :
    ‖gsLogPowerMain t M‖ ≤ M := by
  have hden : 1 ≤ ‖(1 : ℂ) - Complex.I * (t : ℂ)‖ := by
    have hsq : ‖(1 : ℂ) - Complex.I * (t : ℂ)‖ ^ 2 = 1 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    nlinarith [sq_nonneg t,
      norm_nonneg ((1 : ℂ) - Complex.I * (t : ℂ))]
  have hdenpos : 0 < ‖(1 : ℂ) - Complex.I * (t : ℂ)‖ :=
    zero_lt_one.trans_le hden
  unfold gsLogPowerMain
  rw [norm_div]
  change ‖(((M : ℝ) : ℂ) ^ (1 - Complex.I * (t : ℂ)))‖ /
      ‖(1 : ℂ) - Complex.I * (t : ℂ)‖ ≤ (M : ℝ)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hM)]
  have hre : (1 - Complex.I * (t : ℂ)).re = 1 := by simp
  rw [hre, Real.rpow_one]
  exact (div_le_iff₀ hdenpos).2 (by
    nlinarith [show (0 : ℝ) ≤ M by positivity])

theorem norm_sum_Ioc_natLogTwist_le (t : ℝ) (M : ℕ) :
    ‖∑ m ∈ Finset.Ioc 0 M, LogPhaseSum.natLogTwist m t‖ ≤ M := by
  calc
    ‖∑ m ∈ Finset.Ioc 0 M, LogPhaseSum.natLogTwist m t‖ ≤
        ∑ m ∈ Finset.Ioc 0 M, ‖LogPhaseSum.natLogTwist m t‖ :=
      norm_sum_le _ _
    _ = ∑ _m ∈ Finset.Ioc 0 M, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [LogPhaseSum.norm_natLogTwist t (Finset.mem_Ioc.mp hm).1]
    _ = M := by simp

/-- The inverse-square mass of the integer cells beginning at a positive
integer `K` is at most `2 / K`. -/
theorem sum_Ico_inv_sq_le_two_div {K M : ℕ} (hK : 0 < K) :
    (∑ n ∈ Finset.Ico K M, (((n : ℝ) ^ 2)⁻¹)) ≤ 2 / (K : ℝ) := by
  have hset : Finset.Ico K M = Finset.Ioo (K - 1) M := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hset]
  have hsucc : K - 1 + 1 = K := by omega
  have hcast : ((K - 1 : ℕ) : ℝ) + 1 = (K : ℝ) := by
    exact_mod_cast hsucc
  simpa only [Nat.cast_pow, Nat.cast_ofNat, hcast] using
    (sum_Ioo_inv_sq_le (α := ℝ) (K - 1) M)

/-- After a split point above the frequency, the tail power sum differs from
its elementary integral by at most `1 + |t|`. -/
theorem norm_sum_Ioc_natLogTwist_tail_sub_main_le
    (t : ℝ) {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M)
    (ht_large : 1 ≤ |t|) (htK : |t| ≤ K) :
    ‖(∑ m ∈ Finset.Ioc K M, LogPhaseSum.natLogTwist m t) -
        (gsLogPowerMain t M - gsLogPowerMain t K)‖ ≤ |t| + 1 := by
  let f : ℝ → ℂ := LogPhaseSum.logPhase t
  let f' : ℝ → ℂ := fun x ↦
    -(Complex.I * (t : ℂ)) *
      (x : ℂ) ^ (-(Complex.I * (t : ℂ)) - 1)
  let f'' : ℝ → ℂ := fun x ↦
    -(Complex.I * (t : ℂ)) * (-(Complex.I * (t : ℂ)) - 1) *
      (x : ℂ) ^ (-(Complex.I * (t : ℂ)) - 1 - 1)
  let H : ℝ := |t| * Real.sqrt (t ^ 2 + 1)
  have hH : 0 ≤ H := mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hcell (n : ℕ) (hn : n ∈ Finset.Ico K M) :
      ‖(f (n : ℝ) + f ((n + 1 : ℕ) : ℝ)) / 2 -
          ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x‖ ≤
        (H / (n : ℝ) ^ 2) / 6 := by
    have hnK : K ≤ n := (Finset.mem_Ico.mp hn).1
    have hnpos : 0 < n := hK.trans_le hnK
    have ha : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hraw := norm_complex_trapezoidal_cell_error_le ha
      (f := f) (f' := f') (f'' := f'')
      (fun x hx ↦
        LogPhaseSum.hasDerivAt_logPhase (ne_of_gt (ha.trans_le hx.1))
          (abs_pos.mp (zero_lt_one.trans_le ht_large)))
      (fun x hx ↦
        LogPhaseSum.hasDerivAt_logPhase_deriv
          (ne_of_gt (ha.trans_le hx.1)))
      (div_nonneg hH (sq_nonneg _))
      (fun x hx ↦ by
        have hxpos : 0 < x := ha.trans_le hx.1
        have hnorm : ‖f'' x‖ = H / x ^ 2 := by
          dsimp [f'', H]
          convert LogPhaseSum.norm_logPhase_secondDeriv (t := t) hxpos using 1
          all_goals ring_nf
        rw [hnorm]
        exact div_le_div_of_nonneg_left hH (sq_pos_of_pos ha)
          ((sq_le_sq₀ ha.le (ha.le.trans hx.1)).2 hx.1))
    convert hraw using 1
    all_goals simp only [Nat.cast_add, Nat.cast_one]
  have hint (n : ℕ) (hn : n ∈ Finset.Ico K M) :
      IntervalIntegrable f volume (n : ℝ) ((n + 1 : ℕ) : ℝ) := by
    have hnK : K ≤ n := (Finset.mem_Ico.mp hn).1
    have hnpos : 0 < n := hK.trans_le hnK
    have ha : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hcont : ContinuousOn f (Set.Icc (n : ℝ) ((n : ℝ) + 1)) :=
      fun x hx ↦
        (LogPhaseSum.hasDerivAt_logPhase
          (ne_of_gt (ha.trans_le hx.1))
          (abs_pos.mp (zero_lt_one.trans_le ht_large))).continuousAt.continuousWithinAt
    simpa only [Nat.cast_add, Nat.cast_one] using
      hcont.intervalIntegrable_of_Icc (by linarith)
  have hid := sum_Ioc_sub_integral_eq_sum_trapezoidal_cell_error f hKM hint
  have hmain :
      (∫ x in (K : ℝ)..(M : ℝ), f x) =
        gsLogPowerMain t M - gsLogPowerMain t K := by
    dsimp only [f, gsLogPowerMain]
    rw [LogPhaseSum.integral_logPhase, sub_div]
    push_cast
    simp
  have hsum :
      (∑ m ∈ Finset.Ioc K M, f (m : ℝ)) =
        ∑ m ∈ Finset.Ioc K M, LogPhaseSum.natLogTwist m t := by
    apply Finset.sum_congr rfl
    intro m hm
    rfl
  rw [hsum, hmain] at hid
  have herrors :
      ‖∑ n ∈ Finset.Ico K M,
          ((f (n : ℝ) + f ((n + 1 : ℕ) : ℝ)) / 2 -
            ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x)‖ ≤ |t| := by
    calc
      ‖∑ n ∈ Finset.Ico K M,
          ((f (n : ℝ) + f ((n + 1 : ℕ) : ℝ)) / 2 -
            ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x)‖ ≤
          ∑ n ∈ Finset.Ico K M,
            ‖(f (n : ℝ) + f ((n + 1 : ℕ) : ℝ)) / 2 -
              ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ico K M, (H / (n : ℝ) ^ 2) / 6 :=
        Finset.sum_le_sum fun n hn ↦ hcell n hn
      _ = (H / 6) *
          ∑ n ∈ Finset.Ico K M, (((n : ℝ) ^ 2)⁻¹) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      _ ≤ (H / 6) * (2 / (K : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (sum_Ico_inv_sq_le_two_div hK)
          (div_nonneg hH (by norm_num))
      _ ≤ |t| := by
        have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
        have htKR : |t| ≤ (K : ℝ) := by exact_mod_cast htK
        have hratio : |t| / (K : ℝ) ≤ 1 :=
          (div_le_one hKR).2 htKR
        have hsqrt : Real.sqrt (t ^ 2 + 1) ≤ 2 * |t| := by
          rw [Real.sqrt_le_iff]
          constructor
          · positivity
          · nlinarith [sq_abs t]
        dsimp only [H]
        calc
          (|t| * Real.sqrt (t ^ 2 + 1) / 6) * (2 / (K : ℝ)) =
              (2 / 6 : ℝ) * (|t| / (K : ℝ)) *
                Real.sqrt (t ^ 2 + 1) := by ring
          _ ≤ (2 / 6 : ℝ) * 1 * (2 * |t|) := by gcongr
          _ ≤ |t| := by nlinarith [abs_nonneg t]
  have hend : ‖(f (M : ℝ) - f (K : ℝ)) / 2‖ ≤ 1 := by
    rw [norm_div]
    norm_num
    calc
      ‖f (M : ℝ) - f (K : ℝ)‖ / 2 ≤
          (‖f (M : ℝ)‖ + ‖f (K : ℝ)‖) / 2 := by
        gcongr
        exact norm_sub_le _ _
      _ = 1 := by
        rw [show ‖f (M : ℝ)‖ = 1 by
          exact LogPhaseSum.norm_logPhase t (by exact_mod_cast hK.trans_le hKM)]
        rw [show ‖f (K : ℝ)‖ = 1 by
          exact LogPhaseSum.norm_logPhase t (by exact_mod_cast hK)]
        norm_num
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add herrors hend)

/-- Uniform source-form power-sum estimate with error linear in the
frequency.  No lower-size condition on the prefix is needed. -/
theorem norm_sum_Ioc_natLogTwist_sub_main_le_linear
    (t : ℝ) {M : ℕ} (hM : 0 < M) (ht : t ≠ 0) :
    ‖(∑ m ∈ Finset.Ioc 0 M, LogPhaseSum.natLogTwist m t) -
        gsLogPowerMain t M‖ ≤ 8 * (1 + |t|) := by
  by_cases ht_small : |t| ≤ 1
  · have hthree := norm_sum_Ioc_natLogTwist_sub_main_le_three
      t hM ht ht_small
    have hnonneg : 0 ≤ |t| := abs_nonneg t
    calc
      ‖(∑ m ∈ Finset.Ioc 0 M, LogPhaseSum.natLogTwist m t) -
          gsLogPowerMain t M‖ ≤ 3 := by
        simpa only [gsLogPowerMain] using hthree
      _ ≤ 8 * (1 + |t|) := by nlinarith
  · have ht_large : 1 ≤ |t| := le_of_not_ge ht_small
    let K : ℕ := Nat.ceil |t|
    have hK : 0 < K := by
      dsimp only [K]
      exact Nat.ceil_pos.mpr (zero_lt_one.trans_le ht_large)
    have htK : |t| ≤ (K : ℝ) := by
      dsimp only [K]
      exact Nat.le_ceil _
    have hKupper : (K : ℝ) < |t| + 1 := by
      dsimp only [K]
      exact Nat.ceil_lt_add_one (abs_nonneg t)
    have hprefix (N : ℕ) (hN : 0 < N) :
        ‖(∑ m ∈ Finset.Ioc 0 N, LogPhaseSum.natLogTwist m t) -
            gsLogPowerMain t N‖ ≤ 2 * N := by
      calc
        ‖(∑ m ∈ Finset.Ioc 0 N, LogPhaseSum.natLogTwist m t) -
            gsLogPowerMain t N‖ ≤
            ‖∑ m ∈ Finset.Ioc 0 N, LogPhaseSum.natLogTwist m t‖ +
              ‖gsLogPowerMain t N‖ := norm_sub_le _ _
        _ ≤ (N : ℝ) + N :=
          add_le_add (norm_sum_Ioc_natLogTwist_le t N)
            (norm_gsLogPowerMain_le t hN)
        _ = 2 * N := by ring
    by_cases hMK : M ≤ K
    · have hrough := hprefix M hM
      have hcast : (M : ℝ) ≤ K := by exact_mod_cast hMK
      calc
        ‖(∑ m ∈ Finset.Ioc 0 M, LogPhaseSum.natLogTwist m t) -
            gsLogPowerMain t M‖ ≤ 2 * M := hrough
        _ ≤ 2 * K := by gcongr
        _ ≤ 8 * (1 + |t|) := by nlinarith
    · have hKM : K ≤ M := (Nat.lt_of_not_ge hMK).le
      have htail := norm_sum_Ioc_natLogTwist_tail_sub_main_le
        t hK hKM ht_large htK
      have hdisj : Disjoint (Finset.Ioc 0 K) (Finset.Ioc K M) := by
        rw [Finset.disjoint_left]
        intro n hn₀ hn₁
        have hn₀' := Finset.mem_Ioc.mp hn₀
        have hn₁' := Finset.mem_Ioc.mp hn₁
        omega
      have hunion : Finset.Ioc 0 K ∪ Finset.Ioc K M = Finset.Ioc 0 M :=
        Finset.Ioc_union_Ioc_eq_Ioc (by omega) hKM
      have hsumSplit :
          (∑ m ∈ Finset.Ioc 0 M, LogPhaseSum.natLogTwist m t) =
            (∑ m ∈ Finset.Ioc 0 K, LogPhaseSum.natLogTwist m t) +
              ∑ m ∈ Finset.Ioc K M, LogPhaseSum.natLogTwist m t := by
        rw [← hunion, Finset.sum_union hdisj]
      have hKprefix := hprefix K hK
      calc
        ‖(∑ m ∈ Finset.Ioc 0 M, LogPhaseSum.natLogTwist m t) -
            gsLogPowerMain t M‖ =
            ‖((∑ m ∈ Finset.Ioc 0 K, LogPhaseSum.natLogTwist m t) -
                gsLogPowerMain t K) +
              ((∑ m ∈ Finset.Ioc K M, LogPhaseSum.natLogTwist m t) -
                (gsLogPowerMain t M - gsLogPowerMain t K))‖ := by
          rw [hsumSplit]
          congr 1
          ring
        _ ≤
            ‖(∑ m ∈ Finset.Ioc 0 K, LogPhaseSum.natLogTwist m t) -
                gsLogPowerMain t K‖ +
              ‖(∑ m ∈ Finset.Ioc K M, LogPhaseSum.natLogTwist m t) -
                (gsLogPowerMain t M - gsLogPowerMain t K)‖ := norm_add_le _ _
        _ ≤ 2 * K + (|t| + 1) := add_le_add hKprefix htail
        _ ≤ 8 * (1 + |t|) := by nlinarith [abs_nonneg t]

/-- Divisor-convolution form of the linear-height estimate.  Replacing the
floor `N / d` by the real quotient costs at most one. -/
theorem norm_sum_Ioc_natLogTwist_sub_realQuotient_main_le_linear
    (t : ℝ) {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) (ht : t ≠ 0) :
    ‖(∑ m ∈ Finset.Ioc 0 (N / d), LogPhaseSum.natLogTwist m t) -
        ((((N : ℝ) / (d : ℝ) : ℝ) : ℂ) ^
            (1 - Complex.I * (t : ℂ))) /
          (1 - Complex.I * (t : ℂ))‖ ≤
      9 * (1 + |t|) := by
  have hM : 0 < N / d := Nat.div_pos hdN hd
  let M : ℝ := (N / d : ℕ)
  let z : ℝ := (N : ℝ) / (d : ℝ)
  let main : ℝ → ℂ := fun y ↦
    ((y : ℂ) ^ (1 - Complex.I * (t : ℂ))) /
      (1 - Complex.I * (t : ℂ))
  have hfloor : M ≤ z := by
    dsimp only [M, z]
    exact Nat.cast_div_le
  have hfloorUpper : z < M + 1 := by
    dsimp only [M, z]
    have hnat : N < (N / d + 1) * d :=
      (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self _)
    have hreal : (N : ℝ) < (((N / d + 1) * d : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    rw [div_lt_iff₀ hdR]
    push_cast at hreal ⊢
    exact hreal
  have hmain : ‖main M - main z‖ ≤ 1 := by
    have hint : (∫ x in M..z, LogPhaseSum.logPhase t x) =
        main z - main M := by
      dsimp only [main]
      rw [LogPhaseSum.integral_logPhase]
      ring
    have hnormIntegral :
        ‖∫ x in M..z, LogPhaseSum.logPhase t x‖ ≤ |z - M| := by
      have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun x ↦ LogPhaseSum.logPhase t x) (C := (1 : ℝ))
        (a := M) (b := z) (fun x hx ↦ by
          have hxIcc : x ∈ Set.Icc M z := by
            rw [← Set.uIcc_of_le hfloor]
            exact Set.uIoc_subset_uIcc hx
          have hMpos : 0 < M := by
            dsimp only [M]
            exact_mod_cast hM
          exact (LogPhaseSum.norm_logPhase t
            (hMpos.trans_le hxIcc.1)).le)
      simpa using hraw
    rw [hint, norm_sub_rev] at hnormIntegral
    exact hnormIntegral.trans (by
      rw [abs_of_nonneg (sub_nonneg.mpr hfloor)]
      linarith)
  have hpower := norm_sum_Ioc_natLogTwist_sub_main_le_linear t hM ht
  have hmainM : main M = gsLogPowerMain t (N / d) := by
    dsimp only [main, M, gsLogPowerMain]
    push_cast
    simp
  change ‖(∑ m ∈ Finset.Ioc 0 (N / d),
      LogPhaseSum.natLogTwist m t) - main z‖ ≤ 9 * (1 + |t|)
  calc
    ‖(∑ m ∈ Finset.Ioc 0 (N / d),
        LogPhaseSum.natLogTwist m t) - main z‖ =
        ‖((∑ m ∈ Finset.Ioc 0 (N / d),
          LogPhaseSum.natLogTwist m t) - main M) +
            (main M - main z)‖ := by ring_nf
    _ ≤ ‖(∑ m ∈ Finset.Ioc 0 (N / d),
          LogPhaseSum.natLogTwist m t) - main M‖ +
        ‖main M - main z‖ := norm_add_le _ _
    _ ≤ 8 * (1 + |t|) + 1 := by
      apply add_le_add _ hmain
      rw [hmainM]
      exact hpower
    _ ≤ 9 * (1 + |t|) := by nlinarith [abs_nonneg t]

end

end Erdos67
