import ErdosProblems.Erdos696.SiegelWalfisz

/-! # Real endpoints and the bounded initial interval in Siegel–Walfisz -/

namespace Erdos696

open Filter MeasureTheory BoundedGaps.Maynard

lemma li_sub_le {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    |li v - li u| ≤ (v - u) / Real.log 2 := by
  have hv : 2 ≤ v := hu.trans huv
  have hint : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume u v := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht2 : 2 ≤ t := hu.trans (Set.uIcc_of_le huv ▸ ht).1
    have ht0 : t ≠ 0 := by linarith only [ht2]
    have hlog0 : Real.log t ≠ 0 := (Real.log_pos (by linarith only [ht2])).ne'
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (inv_log_intervalIntegrable hu) hint
  have heq : li v - li u = ∫ t in u..v, (Real.log t)⁻¹ := by
    simp only [li, one_div]
    linarith only [hsum]
  rw [heq, ← Real.norm_eq_abs]
  have hbound : ‖∫ t in u..v, (Real.log t)⁻¹‖ ≤ (Real.log 2)⁻¹ * |v - u| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have ht2 : 2 ≤ t := hu.trans (Set.uIoc_of_le huv ▸ ht).1.le
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hlog2.trans_le hlog))]
    exact (inv_le_inv₀ (hlog2.trans_le hlog) hlog2).mpr hlog
  simpa only [abs_of_nonneg (sub_nonneg.mpr huv), div_eq_mul_inv, mul_comm] using hbound

lemma piMod_eq_count (t : ℝ) (q a : ℕ) :
    piMod t q a = Nat.count (fun p => p.Prime ∧ p % q = a % q) (⌊t⌋₊ + 1) := by
  classical
  have heq : piMod t q a = piMod (⌊t⌋₊ : ℝ) q a := by
    simp only [piMod, Nat.floor_natCast]
  rw [heq, piMod_natCast_eq, primeCountUpTo, Nat.count_eq_card_filter_range]

lemma piMod_ceil_sub_le (t : ℝ) (q a : ℕ) :
    |(piMod (⌈t⌉₊ : ℝ) q a : ℝ) - (piMod t q a : ℝ)| ≤ 1 := by
  classical
  let P : ℕ → Prop := fun p => p.Prime ∧ p % q = a % q
  have hlo := Nat.count_monotone P (Nat.add_le_add_right (Nat.floor_le_ceil t) 1)
  have hhi := Nat.count_monotone P
    (Nat.add_le_add_right (Nat.ceil_le_floor_add_one t) 1)
  have hsucc := Nat.count_succ P (⌊t⌋₊ + 1)
  have hdiff : Nat.count P (⌈t⌉₊ + 1) ≤ Nat.count P (⌊t⌋₊ + 1) + 1 := by
    split_ifs at hsucc <;> omega
  rw [piMod_eq_count, piMod_eq_count, Nat.floor_natCast]
  change |(Nat.count P (⌈t⌉₊ + 1) : ℝ) - (Nat.count P (⌊t⌋₊ + 1) : ℝ)| ≤ 1
  rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlo))]
  have hdiffR : (Nat.count P (⌈t⌉₊ + 1) : ℝ) ≤ (Nat.count P (⌊t⌋₊ + 1) : ℝ) + 1 := by
    exact_mod_cast hdiff
  linarith only [hdiffR]

theorem exists_eventually_piMod_sw_real (A : ℝ) (hA : 0 < A) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ᶠ t : ℝ in atTop, ∀ q : ℕ, 1 ≤ q →
        (q : ℝ) ≤ Real.log t ^ A → ∀ a : ℕ, a.Coprime q →
          |(piMod t q a : ℝ) - li t / q.totient| ≤ C * swError c t := by
  obtain ⟨C, c, hC, hc, hc1, hnat⟩ := exists_eventually_piMod_sw_nat A hA
  obtain ⟨N, hnat⟩ := eventually_atTop.mp hnat
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * C + 1 + (Real.log 2)⁻¹, c, by positivity, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (N : ℝ), eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 4] with t htN ht2 htlog
  intro q hq hqLog a ha
  let n : ℕ := ⌈t⌉₊
  have ht0 : 0 < t := by linarith only [ht2]
  have htn : t ≤ n := Nat.le_ceil t
  have hn0 : (0 : ℝ) < n := ht0.trans_le htn
  have hn2 : (2 : ℝ) ≤ n := ht2.trans htn
  have hnN : N ≤ n := by exact_mod_cast htN.trans htn
  have hnGap : (n : ℝ) ≤ t + 1 := (Nat.ceil_lt_add_one ht0.le).le
  have hnLog : Real.log t ≤ Real.log (n : ℝ) := Real.log_le_log ht0 htn
  have hqLogN : (q : ℝ) ≤ Real.log (n : ℝ) ^ A :=
    hqLog.trans (Real.rpow_le_rpow (by linarith only [htlog]) hnLog hA.le)
  have hnBound := hnat n hnN q hq hqLogN a ha
  have hscale : swError c n ≤ 2 * swError c t := by
    calc
      _ ≤ (2 * t) * Real.exp (-c * Real.sqrt (Real.log t)) := by
        apply mul_le_mul (by linarith only [hnGap, ht2])
          (Real.exp_monotone ?_) (Real.exp_pos _).le (by positivity)
        nlinarith only [mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnLog) hc.le]
      _ = _ := by unfold swError; ring
  have hE1 : 1 ≤ swError c t := by
    apply le_trans _ (sqrt_le_swError hc1 ht0 htlog)
    apply (Real.le_sqrt zero_le_one ht0.le).mpr
    nlinarith only [ht2]
  have hphi : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hpi : |(piMod t q a : ℝ) - (piMod n q a : ℝ)| ≤ 1 := by
    simpa only [abs_sub_comm, n] using piMod_ceil_sub_le t q a
  have hli : |li n / q.totient - li t / q.totient| ≤ (Real.log 2)⁻¹ := by
    rw [← sub_div, abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hphi)]
    calc
      _ ≤ |li n - li t| := div_le_self (abs_nonneg _) hphi
      _ ≤ ((n : ℝ) - t) / Real.log 2 := li_sub_le ht2 htn
      _ ≤ (Real.log 2)⁻¹ := by
        rw [← one_div]
        apply div_le_div_of_nonneg_right _ hlog2.le
        linarith only [hnGap]
  have hmid : |(piMod n q a : ℝ) - li n / q.totient| ≤ (2 * C) * swError c t := by
    calc
      _ ≤ C * swError c n := hnBound
      _ ≤ C * (2 * swError c t) := mul_le_mul_of_nonneg_left hscale hC.le
      _ = _ := by ring
  have htri := (abs_sub_le (piMod t q a : ℝ) (piMod n q a : ℝ)
    (li t / q.totient)).trans
      (add_le_add le_rfl (abs_sub_le (piMod n q a : ℝ) (li n / q.totient)
        (li t / q.totient)))
  have hEInv := mul_le_mul_of_nonneg_left hE1 (inv_nonneg.mpr hlog2.le)
  nlinarith only [hpi, hli, hmid, htri, hE1, hEInv]

lemma piMod_crude_bound {t : ℝ} (ht : 2 ≤ t) (q a : ℕ) (hq : 1 ≤ q) :
    |(piMod t q a : ℝ) - li t / q.totient| ≤ (2 + (Real.log 2)⁻¹) * t := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hphi : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hcount : piMod t q a ≤ ⌊t⌋₊ + 1 := by
    rw [piMod_eq_count]
    exact Nat.count_le _
  have hpi : (piMod t q a : ℝ) ≤ 2 * t := by
    have hcountR : (piMod t q a : ℝ) ≤ (⌊t⌋₊ : ℝ) + 1 := by exact_mod_cast hcount
    have hfloor := Nat.floor_le (by linarith only [ht] : 0 ≤ t)
    linarith only [hcountR, hfloor, ht]
  have hli : |li t| ≤ t / Real.log 2 := by
    have h := li_sub_le (u := 2) le_rfl ht
    simp only [li, intervalIntegral.integral_same, sub_zero] at h
    exact h.trans (div_le_div_of_nonneg_right (by linarith) hlog2.le)
  have hliDiv : |li t / q.totient| ≤ t / Real.log 2 := by
    rw [abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hphi)]
    exact (div_le_self (abs_nonneg _) hphi).trans hli
  have htri := abs_sub (piMod t q a : ℝ) (li t / q.totient)
  rw [abs_of_nonneg (Nat.cast_nonneg (piMod t q a) : (0 : ℝ) ≤ piMod t q a)] at htri
  calc
    _ ≤ 2 * t + t / Real.log 2 := htri.trans (add_le_add hpi hliDiv)
    _ = _ := by ring

/-- The exact Siegel–Walfisz statement assumed in the linked formalization,
now proved from the existing unconditional character estimates. -/
theorem siegelWalfisz_unconditional : SiegelWalfisz := by
  constructor
  intro A hA
  obtain ⟨C₀, c, hC₀, hc, hbound⟩ := exists_eventually_piMod_sw_real A hA
  obtain ⟨T₀, hbound⟩ := eventually_atTop.mp hbound
  let T := max T₀ 2
  let D := 2 + (Real.log 2)⁻¹
  let C := C₀ + D * Real.exp (c * Real.sqrt (Real.log T))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hC₀C : C₀ ≤ C := le_add_of_nonneg_right (mul_nonneg hD.le (Real.exp_pos _).le)
  have hsmallC : D * Real.exp (c * Real.sqrt (Real.log T)) ≤ C := by
    dsimp [C]
    linarith only [hC₀]
  refine ⟨c, hc, C, hC, ?_⟩
  intro t ht q hq hqLog a ha
  have ht0 : 0 < t := by linarith only [ht]
  have hE : 0 ≤ swError c t := swError_nonneg ht0.le c
  change |(piMod t q a : ℝ) - li t / q.totient| ≤ C * t * Real.exp (-c * Real.sqrt (Real.log t))
  have hgoal : |(piMod t q a : ℝ) - li t / q.totient| ≤ C * swError c t := by
    by_cases hlarge : T ≤ t
    · exact (hbound t ((le_max_left _ _).trans hlarge) q hq hqLog a ha).trans
        (mul_le_mul_of_nonneg_right hC₀C hE)
    · have htT : t ≤ T := (lt_of_not_ge hlarge).le
      have hlog : Real.sqrt (Real.log t) ≤ Real.sqrt (Real.log T) :=
        Real.sqrt_le_sqrt (Real.log_le_log ht0 htT)
      have hprod : 1 ≤ Real.exp (c * Real.sqrt (Real.log T)) *
          Real.exp (-c * Real.sqrt (Real.log t)) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        nlinarith only [mul_le_mul_of_nonneg_left hlog hc.le]
      calc
        _ ≤ D * t := piMod_crude_bound ht q a hq
        _ ≤ (D * Real.exp (c * Real.sqrt (Real.log T))) * swError c t := by
          have h := mul_le_mul_of_nonneg_left hprod (mul_nonneg hD.le ht0.le)
          dsimp [swError]
          nlinarith only [h]
        _ ≤ C * swError c t := mul_le_mul_of_nonneg_right hsmallC hE
  simpa only [swError, mul_assoc] using hgoal

end Erdos696
