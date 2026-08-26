import ErdosProblems.Erdos796.BaselineAsymptotic
import ErdosProblems.Erdos49.PNT.IEANTN.Mertens

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The Meissel--Mertens constant

This module transports the prime reciprocal-sum theorem from the
`PrimeNumberTheoremAnd` development to the natural-variable formulation used
by this project.
-/

namespace Erdos796

open Filter Topology Asymptotics
open Real Finset Interval MeasureTheory
open scoped BigOperators

theorem primesLE_eq_filter_Ioc (n : ℕ) :
    Nat.primesLE n = (Finset.Ioc 0 n).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hpn, hp⟩
    exact ⟨⟨hp.pos, hpn⟩, hp⟩
  · rintro ⟨⟨_, hpn⟩, hp⟩
    exact ⟨hpn, hp⟩

/- The imported development proves the first Mertens estimates without any
unfinished dependencies.  Its proof of the second estimate, however, routes
through an unrelated explicit numerical bound that is unfinished upstream.
The next lemmas repeat the short Abel-summation argument using only the clean
two-sided estimates `Mertens.E₁p.le` and `Mertens.E₁p.ge`. -/

private theorem sum_div_log_eq_clean {x : ℝ} (hx : 2 ≤ x)
    (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊x⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊x⌋₊, f n) / log x +
        ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, f n) / (t * log t ^ 2) := by
  let g : ℕ → ℝ := fun n => if n < 2 then 0 else f n
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * g n
  · rw [← Mertens.sum_Ioc_one_eq_sum_Icc_zero
      (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn => ?_
    have hn1 : ¬n ≤ 1 := by simp_all
    simp [g, hn1]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := fun n => (log n)⁻¹)
      (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv,
      ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← Mertens.sum_Ioc_one_eq_sum_Icc_zero
        (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn => ?_
      simp only [mem_Ioc] at hn
      have hn1 : ¬n ≤ 1 := by linarith
      simp [g, hn1]
    · rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht => ?_
      simp only [Set.mem_Ioc] at ht
      rw [← Mertens.sum_Ioc_one_eq_sum_Icc_zero
        (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn => ?_
      simp only [mem_Ioc] at hn
      have hn1 : ¬n ≤ 1 := by linarith
      simp [g, hn1]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have hlog : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext y; rw [deriv_inv_log]
    have hlog : log t ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

theorem integrable_const_div_mul_log_sq_clean {x : ℝ}
    (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun t => c / (t * log t ^ 2))
      (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_
    tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have hlog : log t ≠ 0 := by simp; grind
    have hdiff : DifferentiableAt ℝ (fun y => -(log y)⁻¹) t := by
      fun_prop (disch := grind)
    convert! hdiff.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

private theorem E₁p_bounded_clean :
    ∃ c > 0, ∀ x ≥ 1, |Mertens.E₁p x| ≤ c := by
  refine ⟨log 4 + 6 + Mertens.E₁, ?_, ?_⟩
  · have hlog : 0 < log 4 := log_pos (by norm_num)
    have hE := Mertens.E₁.nonneg
    linarith
  · intro x hx
    rw [abs_le']
    constructor
    · have hle := Mertens.E₁p.le hx
      have hE := Mertens.E₁.nonneg
      linarith
    · have hge := Mertens.E₁p.ge hx
      have hlog : 0 ≤ log 4 := (log_pos (by norm_num)).le
      linarith

theorem integrable_E₁p_div_mul_log_sq_clean {x : ℝ}
    (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn
      (fun t => Mertens.E₁p t / (t * log t ^ 2))
      (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hcpos, hc⟩ := E₁p_bounded_clean
  apply MeasureTheory.Integrable.mono
    (integrable_const_div_mul_log_sq_clean c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs,
      abs_of_pos hcpos]
    gcongr
    exact hc t (by linarith)

theorem integ_div_mul_log_sq_clean {x : ℝ} (c : ℝ)
    (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t ^ 2) = c / log x := by
  convert! MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (m := 0) (f := fun y => -c / log y) ?_
      (integrable_const_div_mul_log_sq_clean c hx) ?_ using 1
  · grind
  · intro t ht
    simp at ht
    convert! HasDerivAt.fun_div (hasDerivAt_const _ (-c))
      (hasDerivAt_log (by linarith)) ?_ using 1
    · grind
    simp
    grind
  · convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp

theorem E₂p_eq_clean {x : ℝ} (hx : 2 ≤ x) :
    Mertens.E₂p x = Mertens.E₁p x / log x -
      ∫ t in Set.Ioi x, Mertens.E₁p t / (t * log t ^ 2) := by
  unfold Mertens.E₂p
  rw [sum_filter, ← Mertens.sum_Ioc_one_eq_sum_Ioc_zero
    (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have hterm (n : ℕ) :
      (if Nat.Prime n then (1 : ℝ) / n else 0) =
        (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with hn
    · have hlog : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · simp
  simp_rw [hterm]
  rw [sum_div_log_eq_clean hx,
    Mertens.sum_Ioc_one_eq_sum_Ioc_zero
      (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [Mertens.sum_log_prime_div_eq]
  have hint :
      ∫ t in 2..x,
          (∑ n ∈ Ioc 1 ⌊t⌋₊,
            if Nat.Prime n then log (n : ℝ) / (n : ℝ) else 0) /
              (t * log t ^ 2) =
        ∫ t in 2..x,
          (1 / (t * log t) +
            Mertens.E₁p t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [Mertens.sum_Ioc_one_eq_sum_Ioc_zero
      (Nat.le_floor (by grind)) (by simp), ← sum_filter,
      Mertens.sum_log_prime_div_eq]
    field
  rw [hint, intervalIntegral.integral_add]
  · rw [Mertens.integral_one_div_mul_log hx, add_div,
      div_self (by simp; grind)]
    unfold Mertens.M
    calc
      _ = Mertens.E₁p x / log x +
          (∫ t in 2..x, Mertens.E₁p t / (t * log t ^ 2)) -
            (∫ t in Set.Ioi 2,
              Mertens.E₁p t / (t * log t ^ 2)) := by ring
      _ = _ := by
        rw [← intervalIntegral.integral_interval_add_Ioi
          (integrable_E₁p_div_mul_log_sq_clean (by rfl))
          (integrable_E₁p_div_mul_log_sq_clean hx)]
        ring
  · exact Mertens.intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact (integrable_E₁p_div_mul_log_sq_clean (x := 2) (by rfl)).mono
      (by grind) (by rfl)

private theorem E₂p_abs_le_clean {x : ℝ} (hx : 2 ≤ x) :
    |Mertens.E₂p x| ≤ (log 4 + 6 + Mertens.E₁) / log x := by
  have hlog : 0 < log x := by apply log_pos; linarith
  rw [E₂p_eq_clean hx, abs_le']
  constructor
  · grw [Mertens.E₁p.le (by linarith)]
    have hint :
        ∫ t in Set.Ioi x, Mertens.E₁p t / (t * log t ^ 2) ≥
          (-2 - Mertens.E₁) / log x := calc
      _ ≥ ∫ t in Set.Ioi x,
          (-2 - Mertens.E₁) / (t * log t ^ 2) := by
        apply MeasureTheory.setIntegral_mono_on
          (integrable_const_div_mul_log_sq_clean (-2 - Mertens.E₁) hx)
          (integrable_E₁p_div_mul_log_sq_clean hx) (by measurability)
        intro y hy
        simp at hy
        have hy1 : 1 < y := by linarith
        have hylog : 0 < log y := log_pos hy1
        gcongr
        exact Mertens.E₁p.ge (by linarith)
      _ = _ := integ_div_mul_log_sq_clean (-2 - Mertens.E₁) hx
    grw [hint]
    grind
  · grw [Mertens.E₁p.ge (by linarith)]
    have hint :
        ∫ t in Set.Ioi x, Mertens.E₁p t / (t * log t ^ 2) ≤
          (log 4 + 4) / log x := calc
      _ ≤ ∫ t in Set.Ioi x,
          (log 4 + 4) / (t * log t ^ 2) := by
        apply MeasureTheory.setIntegral_mono_on
          (integrable_E₁p_div_mul_log_sq_clean hx)
          (integrable_const_div_mul_log_sq_clean (log 4 + 4) hx)
          (by measurability)
        intro y hy
        simp at hy
        have hy1 : 1 < y := by linarith
        have hylog : 0 < log y := log_pos hy1
        gcongr
        exact Mertens.E₁p.le (by linarith)
      _ = _ := integ_div_mul_log_sq_clean (log 4 + 4) hx
    grw [hint]
    grind

private theorem E₂p_bound_clean :
    Mertens.E₂p =O[atTop] (fun x => 1 / log x) := by
  simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop,
    ge_iff_le]
  use log 4 + 6 + Mertens.E₁, 2
  intro x hx
  convert! E₂p_abs_le_clean hx using 1
  have hlog : 0 < log x := by apply log_pos; linarith
  grind [abs_of_pos hlog]

/-- The prime-form second Mertens error tends to zero, proved without the
unfinished explicit numerical estimate in the imported development. -/
theorem mertensE₂p_tendsto_zero :
    Tendsto Mertens.E₂p atTop (nhds 0) :=
  (isLittleO_one_iff ℝ).mp
    (E₂p_bound_clean.trans_isLittleO Real.inv_log_eq_o_one)

/-- The constant constructed in the imported Mertens development satisfies
the defining natural-variable limit. -/
theorem meisselMertensConstant :
    IsMeisselMertensConstant Mertens.M := by
  have herrorNat : Tendsto (fun n : ℕ => Mertens.E₂p (n : ℝ))
      atTop (nhds 0) :=
    mertensE₂p_tendsto_zero.comp tendsto_natCast_atTop_atTop
  have heq :
      (fun n : ℕ => primeHarmonic n - Real.log (Real.log (n : ℝ))) =
        (fun n : ℕ => Mertens.M + Mertens.E₂p (n : ℝ)) := by
    funext n
    have hsum := Mertens.sum_prime_div_eq (n : ℝ)
    rw [Nat.floor_natCast] at hsum
    have hfin := primesLE_eq_filter_Ioc n
    unfold primeHarmonic
    rw [hfin]
    simp only [Finset.sum_filter] at hsum ⊢
    have hsum' :
        (∑ p ∈ Finset.Ioc 0 n,
          if p.Prime then (p : ℝ)⁻¹ else 0) =
          Real.log (Real.log (n : ℝ)) + Mertens.M +
            Mertens.E₂p (n : ℝ) := by
      simpa [one_div] using! hsum
    rw [hsum']
    ring
  rw [IsMeisselMertensConstant]
  have ht : Tendsto
      (fun n : ℕ => Mertens.M + Mertens.E₂p (n : ℝ))
      atTop (nhds Mertens.M) := by
    have hconst : Tendsto (fun _n : ℕ => Mertens.M)
        atTop (nhds Mertens.M) := tendsto_const_nhds
    simpa only [add_zero] using! hconst.add herrorNat
  exact ht.congr' (Eventually.of_forall fun n => (congrFun heq n).symm)

end Erdos796
