import ErdosProblems.Erdos67b.MRLemma14ContinuousHigh
import ErdosProblems.Erdos67b.MRFatouNormSq
import BoundedGaps.BombieriVinogradov.Analytic.DirichletSineRemainder

/-!
# Continuous Perron-limit adapter for MR Lemma 14

This file passes from the finite continuous-endpoint Perron estimates to the
actual step-function short sum.  The first ingredient is Perron inversion at
an arbitrary positive real endpoint away from its jump set.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Erdos67b

noncomputable section

open BoundedGaps.Maynard

/-- The limiting scalar Perron weight at a positive real cutoff.  It is zero
below the jump, one above it, and one half at the jump. -/
def lemma14RealPerronWeight (y : ℝ) : ℂ :=
  (((1 / 2 + Real.sign (Real.log y) / 2 : ℝ)) : ℂ)

theorem lemma14RealPerronWeight_eq_zero
    {y : ℝ} (hy : 0 < y) (hy1 : y < 1) :
    lemma14RealPerronWeight y = 0 := by
  have hlog : Real.log y < 0 := Real.log_neg hy hy1
  rw [lemma14RealPerronWeight, Real.sign_of_neg hlog]
  norm_num

theorem lemma14RealPerronWeight_eq_one
    {y : ℝ} (hy1 : 1 < y) :
    lemma14RealPerronWeight y = 1 := by
  have hlog : 0 < Real.log y := Real.log_pos hy1
  rw [lemma14RealPerronWeight, Real.sign_of_pos hlog]
  norm_num

/-- Scalar Perron inversion at every non-jump positive real endpoint. -/
theorem tendsto_dirichletPerronKernel_atTop_of_ne_one
    {y alpha : ℝ} (hy : 0 < y) (hy1 : y ≠ 1)
    (halpha : 0 < alpha) (halphaUpper : alpha ≤ 2) :
    Filter.Tendsto (fun U : ℝ ↦ dirichletPerronKernel y alpha U)
      Filter.atTop (nhds (lemma14RealPerronWeight y)) := by
  rcases lt_or_gt_of_ne hy1 with hylt | hygt
  · rw [lemma14RealPerronWeight_eq_zero hy hylt]
    by_cases hhalf : y ≤ 1 / 2
    · refine squeeze_zero_norm' (a := fun U : ℝ ↦ y ^ alpha / U) ?_ ?_
      · filter_upwards [Filter.eventually_gt_atTop 0] with U hU
        exact norm_dirichletPerronKernel_lowBase_le hy hhalf halpha hU
      · exact tendsto_const_nhds.div_atTop Filter.tendsto_id
    · have hyLower : 1 / 2 ≤ y := le_of_not_ge hhalf
      have hyUpper : y ≤ 2 := hylt.le.trans (by norm_num)
      let A : ℝ → ℂ := fun U ↦
        (((1 / 2 +
          (∫ u in (0 : ℝ)..(U * Real.log y), Real.sinc u) /
            Real.pi : ℝ)) : ℂ)
      let R : ℝ → ℝ := fun U ↦
        (20 / Real.pi) * U⁻¹ +
          (1 / (|Real.log y| * Real.pi)) * U⁻¹
      refine squeeze_zero_norm' (a := R) ?_ ?_
      · filter_upwards [Filter.eventually_gt_atTop 0] with U hU
        have hcentral :=
          norm_dirichletPerronKernel_sub_half_add_sinc_le
            hyLower hyUpper halpha halphaUpper hU
        have hlog : Real.log y < 0 := Real.log_neg hy hylt
        have hULog : U * Real.log y ≠ 0 := mul_ne_zero hU.ne' hlog.ne
        have hsinc :=
          abs_integral_sinc_sub_sign_pi_div_two_le_inv_abs hULog
        have hsign : Real.sign (U * Real.log y) = -1 :=
          Real.sign_of_neg (mul_neg_of_pos_of_neg hU hlog)
        rw [hsign] at hsinc
        have hA : ‖A U‖ ≤ (U * |Real.log y|)⁻¹ / Real.pi := by
          dsimp only [A]
          rw [Complex.norm_real, Real.norm_eq_abs]
          have habsProd : |U * Real.log y| = U * |Real.log y| := by
            rw [abs_mul, abs_of_pos hU]
          rw [habsProd] at hsinc
          have hpi : 0 < Real.pi := Real.pi_pos
          rw [show 1 / 2 +
              (∫ u in (0 : ℝ)..U * Real.log y, Real.sinc u) / Real.pi =
              ((∫ u in (0 : ℝ)..U * Real.log y, Real.sinc u) +
                Real.pi / 2) / Real.pi by field_simp [Real.pi_ne_zero]; ring,
            abs_div]
          simpa only [abs_of_pos hpi] using
            (div_le_div_of_nonneg_right (by simpa [zpow_neg] using hsinc) hpi.le)
        have htriangle := norm_le_norm_add_norm_sub'
          (dirichletPerronKernel y alpha U) (A U)
        change ‖dirichletPerronKernel y alpha U‖ ≤ R U
        calc
          ‖dirichletPerronKernel y alpha U‖ ≤
              ‖A U‖ + ‖dirichletPerronKernel y alpha U - A U‖ := by
            simpa [norm_sub_rev] using htriangle
          _ ≤ (U * |Real.log y|)⁻¹ / Real.pi +
              20 / (Real.pi * U) := add_le_add hA (by simpa [A] using hcentral)
          _ = R U := by
            dsimp [R]
            rw [mul_inv_rev]
            field_simp [Real.pi_ne_zero, (abs_pos.mpr
              (Real.log_ne_zero_of_pos_of_ne_one hy hy1)).ne']
            ring
      · have hlogAbs : 0 < |Real.log y| := abs_pos.mpr
          (Real.log_ne_zero_of_pos_of_ne_one hy hy1)
        simpa only [R, mul_zero, add_zero] using
          (tendsto_inv_atTop_zero.const_mul (20 / Real.pi)).add
            (tendsto_inv_atTop_zero.const_mul
              (1 / (|Real.log y| * Real.pi)))
  · rw [lemma14RealPerronWeight_eq_one hygt]
    by_cases htwo : 2 ≤ y
    · have hzero : Filter.Tendsto
          (fun U : ℝ ↦ dirichletPerronKernel y alpha U - 1)
          Filter.atTop (nhds 0) := by
        refine squeeze_zero_norm' (a := fun U : ℝ ↦ y ^ alpha / U) ?_ ?_
        · filter_upwards [Filter.eventually_gt_atTop 0] with U hU
          exact norm_dirichletPerronKernel_sub_one_highBase_le
            htwo halpha hU
        · exact tendsto_const_nhds.div_atTop Filter.tendsto_id
      simpa only [sub_add_cancel, zero_add] using hzero.add_const (1 : ℂ)
    · have hyLower : 1 / 2 ≤ y := by linarith
      have hyUpper : y ≤ 2 := le_of_not_ge htwo
      let A : ℝ → ℂ := fun U ↦
        (((1 / 2 +
          (∫ u in (0 : ℝ)..(U * Real.log y), Real.sinc u) /
            Real.pi : ℝ)) : ℂ)
      let R : ℝ → ℝ := fun U ↦
        (20 / Real.pi) * U⁻¹ +
          (1 / (|Real.log y| * Real.pi)) * U⁻¹
      have hzero : Filter.Tendsto
          (fun U : ℝ ↦ dirichletPerronKernel y alpha U - 1)
          Filter.atTop (nhds 0) := by
        refine squeeze_zero_norm' (a := R) ?_ ?_
        · filter_upwards [Filter.eventually_gt_atTop 0] with U hU
          have hcentral :=
            norm_dirichletPerronKernel_sub_half_add_sinc_le
              hyLower hyUpper halpha halphaUpper hU
          have hlog : 0 < Real.log y := Real.log_pos hygt
          have hULog : U * Real.log y ≠ 0 := mul_ne_zero hU.ne' hlog.ne'
          have hsinc :=
            abs_integral_sinc_sub_sign_pi_div_two_le_inv_abs hULog
          have hsign : Real.sign (U * Real.log y) = 1 :=
            Real.sign_of_pos (mul_pos hU hlog)
          rw [hsign] at hsinc
          simp only [one_mul, zpow_neg] at hsinc
          have hA : ‖A U - 1‖ ≤ (U * |Real.log y|)⁻¹ / Real.pi := by
            dsimp only [A]
            rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_eq_abs]
            have habsProd : |U * Real.log y| = U * |Real.log y| := by
              rw [abs_mul, abs_of_pos hU]
            rw [habsProd] at hsinc
            have hpi : 0 < Real.pi := Real.pi_pos
            rw [show (1 / 2 +
                (∫ u in (0 : ℝ)..U * Real.log y, Real.sinc u) /
                  Real.pi) - 1 =
                ((∫ u in (0 : ℝ)..U * Real.log y, Real.sinc u) -
                  Real.pi / 2) / Real.pi by field_simp [Real.pi_ne_zero]; ring,
              abs_div]
            simpa [abs_of_pos hpi, zpow_neg] using
              (div_le_div_of_nonneg_right hsinc hpi.le)
          change ‖dirichletPerronKernel y alpha U - 1‖ ≤ R U
          calc
            ‖dirichletPerronKernel y alpha U - 1‖ =
                ‖(dirichletPerronKernel y alpha U - A U) + (A U - 1)‖ := by
              congr 1
              ring
            _ ≤ ‖dirichletPerronKernel y alpha U - A U‖ + ‖A U - 1‖ :=
              norm_add_le _ _
            _ ≤ 20 / (Real.pi * U) +
                (U * |Real.log y|)⁻¹ / Real.pi :=
              add_le_add (by simpa [A] using hcentral) hA
            _ = R U := by
              dsimp [R]
              rw [mul_inv_rev]
              field_simp [Real.pi_ne_zero, (abs_pos.mpr
                (Real.log_ne_zero_of_pos_of_ne_one hy hy1)).ne']
        · have hlogAbs : 0 < |Real.log y| := abs_pos.mpr
            (Real.log_ne_zero_of_pos_of_ne_one hy hy1)
          simpa only [R, mul_zero, add_zero] using
            (tendsto_inv_atTop_zero.const_mul (20 / Real.pi)).add
              (tendsto_inv_atTop_zero.const_mul
                (1 / (|Real.log y| * Real.pi)))
      simpa only [sub_add_cancel, zero_add] using hzero.add_const (1 : ℂ)

private theorem lemma14_cpow_div_of_pos
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    ((x / y : ℝ) : ℂ) ^ s = (x : ℂ) ^ s / (y : ℂ) ^ s := by
  rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (div_ne_zero hx.ne' hy.ne')),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
    ← Complex.exp_sub]
  congr 1
  rw [← sub_mul]
  congr 1
  rw [← Complex.ofReal_log (div_nonneg hx.le hy.le),
    Real.log_div hx.ne' hy.ne', Complex.ofReal_sub,
    Complex.ofReal_log hx.le, Complex.ofReal_log hy.le]

private theorem LSeries_dyadicRestrictedCoefficient_eq_finsetSum
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ) (s : ℂ) :
    LSeries (dyadicRestrictedCoefficient S f Y) s =
      ∑ n ∈ dyadicRestrictedSupport S Y,
        LSeries.term (dyadicRestrictedCoefficient S f Y) s n := by
  classical
  unfold LSeries
  rw [tsum_eq_sum (s := dyadicRestrictedSupport S Y)]
  intro n hn
  unfold LSeries.term dyadicRestrictedCoefficient
  simp [hn]

/-- For the finite dyadic coefficient, the Perron integral is literally the
finite sum of scalar Perron kernels, at every positive real cutoff. -/
theorem dirichletPerronIntegral_dyadicRestricted_eq_sum_kernel
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ)
    {y : ℝ} (hy : 0 < y) (U : ℝ) :
    dirichletPerronIntegral (dyadicRestrictedCoefficient S f Y) y 1 U =
      ∑ n ∈ dyadicRestrictedSupport S Y,
        f n * dirichletPerronKernel (y / n) 1 U := by
  classical
  have hnpos (n : ℕ) (hn : n ∈ dyadicRestrictedSupport S Y) : 0 < n := by
    rw [dyadicRestrictedSupport, Finset.mem_inter, Finset.mem_Ioc] at hn
    omega
  unfold dirichletPerronIntegral
  simp_rw [LSeries_dyadicRestrictedCoefficient_eq_finsetSum]
  have hdist : (fun t : ℝ ↦
      (∑ n ∈ dyadicRestrictedSupport S Y,
          LSeries.term (dyadicRestrictedCoefficient S f Y)
            (((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n) *
          (y : ℂ) ^ (((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
            (((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      fun t : ℝ ↦ ∑ n ∈ dyadicRestrictedSupport S Y,
        LSeries.term (dyadicRestrictedCoefficient S f Y)
            (((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n *
          (y : ℂ) ^ (((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
            (((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    funext t
    rw [Finset.sum_mul, Finset.sum_div]
  rw [hdist, intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 := hnpos n hn
    rw [dirichletPerronKernel, ← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    simp only
    rw [show LSeries.term (dyadicRestrictedCoefficient S f Y)
          (((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n =
        f n / (n : ℂ) ^ (((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) by
          unfold LSeries.term dyadicRestrictedCoefficient
          simp [hn, hn0.ne']]
    rw [lemma14_cpow_div_of_pos hy hnR]
    norm_num only [Complex.ofReal_natCast]
    ring
  · intro n hn
    have hn0 := hnpos n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hs : Continuous fun t : ℝ ↦ (1 : ℂ) + (t : ℂ) * Complex.I := by fun_prop
    have hsne : ∀ t : ℝ, (1 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
      intro t ht
      have hre := congrArg Complex.re ht
      norm_num at hre
    have hnpow : Continuous fun t : ℝ ↦
        (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
      exact continuous_const.cpow hs fun _ ↦ by
        simpa only [← Complex.ofReal_natCast] using
          Complex.ofReal_mem_slitPlane.mpr hnR
    have hnpowne : ∀ t : ℝ,
        (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro t
      exact Complex.cpow_ne_zero_iff.mpr <| Or.inl <|
        Nat.cast_ne_zero.mpr hn0.ne'
    have hypow : Continuous fun t : ℝ ↦
        (y : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
      exact continuous_const.cpow hs fun _ ↦
        Complex.ofReal_mem_slitPlane.mpr hy
    have hterm : Continuous fun t : ℝ ↦
        LSeries.term (dyadicRestrictedCoefficient S f Y)
            ((1 : ℂ) + (t : ℂ) * Complex.I) n := by
      simp only [LSeries.term_of_ne_zero hn0.ne']
      exact continuous_const.div hnpow hnpowne
    exact ((hterm.mul hypow).div hs hsne).intervalIntegrable _ _

/-- The real-endpoint finite prefix selected by Perron inversion. -/
def dyadicRestrictedRealPerronPrefix
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ dyadicRestrictedSupport S Y,
    f n * lemma14RealPerronWeight (y / n)

theorem tendsto_dirichletPerronIntegral_dyadicRestricted_atTop
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ)
    {y : ℝ} (hy : 0 < y)
    (hyn : ∀ n ∈ dyadicRestrictedSupport S Y, y ≠ n) :
    Filter.Tendsto
      (fun U : ℝ ↦
        dirichletPerronIntegral (dyadicRestrictedCoefficient S f Y) y 1 U)
      Filter.atTop (nhds (dyadicRestrictedRealPerronPrefix S f Y y)) := by
  rw [show (fun U : ℝ ↦
      dirichletPerronIntegral (dyadicRestrictedCoefficient S f Y) y 1 U) =
    fun U ↦ ∑ n ∈ dyadicRestrictedSupport S Y,
      f n * dirichletPerronKernel (y / n) 1 U by
        funext U
        exact dirichletPerronIntegral_dyadicRestricted_eq_sum_kernel
          S f Y hy U]
  unfold dyadicRestrictedRealPerronPrefix
  apply tendsto_finsetSum
  intro n hn
  have hnpos : 0 < n := by
    rw [dyadicRestrictedSupport, Finset.mem_inter, Finset.mem_Ioc] at hn
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hyratio : 0 < y / (n : ℝ) := div_pos hy hnR
  have hratio1 : y / (n : ℝ) ≠ 1 := by
    intro heq
    rw [div_eq_one_iff_eq hnR.ne'] at heq
    exact hyn n hn heq
  exact (tendsto_dirichletPerronKernel_atTop_of_ne_one
    hyratio hratio1 (by norm_num) (by norm_num)).const_mul (f n)

private theorem sum_Ioc_dyadicRestrictedCoefficient_eq_support
    (S : Finset ℕ) (f : ℕ → ℂ) (Y n H : ℕ) :
    (∑ m ∈ Finset.Ioc n (n + H), dyadicRestrictedCoefficient S f Y m) =
      ∑ m ∈ dyadicRestrictedSupport S Y,
        if m ∈ Finset.Ioc n (n + H) then f m else 0 := by
  classical
  calc
    (∑ m ∈ Finset.Ioc n (n + H), dyadicRestrictedCoefficient S f Y m) =
        ∑ m ∈ Finset.Ioc n (n + H),
          if m ∈ dyadicRestrictedSupport S Y then f m else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rfl
    _ = ∑ m ∈ (Finset.Ioc n (n + H)).filter
          (fun m ↦ m ∈ dyadicRestrictedSupport S Y), f m := by
      rw [Finset.sum_filter]
    _ = ∑ m ∈ (dyadicRestrictedSupport S Y).filter
          (fun m ↦ m ∈ Finset.Ioc n (n + H)), f m := by
      congr 1
      ext m
      simp only [Finset.mem_filter]
      tauto
    _ = ∑ m ∈ dyadicRestrictedSupport S Y,
          if m ∈ Finset.Ioc n (n + H) then f m else 0 := by
      rw [Finset.sum_filter]

theorem dyadicRestrictedRealPerronPrefix_sub_eq_shortAverage_on_cell
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ)
    {n H : ℕ} {x : ℝ} (hx : x ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1))
    (hH : 0 < H) :
    (dyadicRestrictedRealPerronPrefix S f Y (x + H) -
        dyadicRestrictedRealPerronPrefix S f Y x) / (H : ℂ) =
      dyadicRestrictedShortAverage S f Y n H := by
  classical
  have hterm (m : ℕ) (hm : m ∈ dyadicRestrictedSupport S Y) :
      f m * lemma14RealPerronWeight ((x + H) / m) -
          f m * lemma14RealPerronWeight (x / m) =
        if m ∈ Finset.Ioc n (n + H) then f m else 0 := by
    have hmpos : 0 < m := by
      rw [dyadicRestrictedSupport, Finset.mem_inter, Finset.mem_Ioc] at hm
      omega
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    by_cases hmi : m ∈ Finset.Ioc n (n + H)
    · have hmI := Finset.mem_Ioc.mp hmi
      have hxm : x < (m : ℝ) := by
        have hnm : n + 1 ≤ m := by omega
        exact hx.2.trans_le (by exact_mod_cast hnm)
      have hmxH : (m : ℝ) < x + H := by
        have hmle : m ≤ n + H := hmI.2
        have hmcast : (m : ℝ) ≤ n + H := by exact_mod_cast hmle
        linarith [hx.1]
      have hlower : x / (m : ℝ) < 1 := (div_lt_one hmR).mpr hxm
      have hupper : 1 < (x + H) / (m : ℝ) := (one_lt_div hmR).mpr hmxH
      rw [lemma14RealPerronWeight_eq_zero
          (div_pos ((Nat.cast_nonneg n).trans_lt hx.1) hmR)
          hlower,
        lemma14RealPerronWeight_eq_one hupper]
      simp [hmi]
    · rw [Finset.mem_Ioc, not_and_or] at hmi
      rcases hmi with hmn | hmupper
      · have hmx : (m : ℝ) < x := by
          have hmcast : (m : ℝ) ≤ n := by exact_mod_cast le_of_not_gt hmn
          exact hmcast.trans_lt hx.1
        have hmxH : (m : ℝ) < x + H := hmx.trans (lt_add_of_pos_right _ (by positivity))
        have hlower : 1 < x / (m : ℝ) := (one_lt_div hmR).mpr hmx
        have hupper : 1 < (x + H) / (m : ℝ) := (one_lt_div hmR).mpr hmxH
        rw [lemma14RealPerronWeight_eq_one hlower,
          lemma14RealPerronWeight_eq_one hupper]
        simp [Finset.mem_Ioc, hmn]
      · have hxHm : x + H < (m : ℝ) := by
          have hnat : n + H + 1 ≤ m := by omega
          have hcast : (n : ℝ) + H + 1 ≤ m := by exact_mod_cast hnat
          linarith [hx.2]
        have hxm : x < (m : ℝ) :=
          (lt_add_of_pos_right x (by positivity)).trans hxHm
        have hlower : x / (m : ℝ) < 1 := (div_lt_one hmR).mpr hxm
        have hupper : (x + H) / (m : ℝ) < 1 := (div_lt_one hmR).mpr hxHm
        rw [lemma14RealPerronWeight_eq_zero
            (div_pos ((Nat.cast_nonneg n).trans_lt hx.1) hmR) hlower,
          lemma14RealPerronWeight_eq_zero
            (div_pos (add_pos ((Nat.cast_nonneg n).trans_lt hx.1) (by positivity)) hmR)
            hupper]
        simp [Finset.mem_Ioc, hmupper]
  unfold dyadicRestrictedRealPerronPrefix dyadicRestrictedShortAverage
  rw [sum_Ioc_dyadicRestrictedCoefficient_eq_support]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  exact hterm m hm

/-- On every open unit cell, the continuous real-endpoint Perron short
average tends to the exact discrete normalized short average. -/
theorem tendsto_perronKernelSegmentOn_dyadic_on_cell
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ)
    {n H : ℕ} {x : ℝ} (hx : x ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1))
    (hH : 0 < H) :
    Filter.Tendsto
      (fun U : ℝ ↦ perronKernelSegmentOn
        (dyadicVerticalDirichletPolynomial S f Y) x H (-U) U)
      Filter.atTop (nhds (dyadicRestrictedShortAverage S f Y n H)) := by
  have hxpos : 0 < x := (Nat.cast_nonneg n).trans_lt hx.1
  have hxHpos : 0 < x + H := add_pos hxpos (by positivity)
  have hxNot (m : ℕ) (_hm : m ∈ dyadicRestrictedSupport S Y) : x ≠ m := by
    intro heq
    have hnm : n < m := by exact_mod_cast (hx.1.trans_eq heq)
    have hmn1 : m < n + 1 := by
      exact_mod_cast (heq ▸ hx.2)
    omega
  have hxHNot (m : ℕ) (_hm : m ∈ dyadicRestrictedSupport S Y) : x + H ≠ m := by
    intro heq
    have hnm : n + H < m := by
      exact_mod_cast (by linarith [hx.1] : (n : ℝ) + H < m)
    have hmn1 : m < n + H + 1 := by
      exact_mod_cast (by linarith [hx.2] : (m : ℝ) < n + H + 1)
    omega
  have hlimPlus := tendsto_dirichletPerronIntegral_dyadicRestricted_atTop
    S f Y hxHpos hxHNot
  have hlimBase := tendsto_dirichletPerronIntegral_dyadicRestricted_atTop
    S f Y hxpos hxNot
  have hlim := (hlimPlus.sub hlimBase).div_const (H : ℂ)
  have hmodel (U : ℝ) :
      (dirichletPerronIntegral (dyadicRestrictedCoefficient S f Y)
            (x + H) 1 U -
          dirichletPerronIntegral (dyadicRestrictedCoefficient S f Y)
            x 1 U) / (H : ℂ) =
        perronKernelSegmentOn
          (dyadicVerticalDirichletPolynomial S f Y) x H (-U) U := by
    have hsource := dyadicRestrictedPerron_shortDifference_eq S f Y hxpos
      (show (0 : ℝ) < H by exact_mod_cast hH) U
    unfold perronKernelSegmentOn
    convert hsource using 1 <;> norm_num
  rw [show (fun U : ℝ ↦ perronKernelSegmentOn
      (dyadicVerticalDirichletPolynomial S f Y) x H (-U) U) =
    fun U ↦
      (dirichletPerronIntegral (dyadicRestrictedCoefficient S f Y)
            (x + H) 1 U -
          dirichletPerronIntegral (dyadicRestrictedCoefficient S f Y)
            x 1 U) / (H : ℂ) by funext U; exact (hmodel U).symm]
  simpa only [dyadicRestrictedRealPerronPrefix_sub_eq_shortAverage_on_cell
    S f Y hx hH] using hlim

/-- The normalized real-endpoint step function.  Its squared integral is
the discrete uncentered mean square divided by `H^2`. -/
def realEndpointStepShortAverage
    (a : ℕ → ℂ) (X H : ℕ) (x : ℝ) : ℂ :=
  realEndpointStepShortSum a X H x / (H : ℂ)

theorem integrable_normSq_realEndpointStepShortAverage
    (a : ℕ → ℂ) (X H : ℕ) :
    Integrable (fun x : ℝ ↦
      Complex.normSq (realEndpointStepShortAverage a X H x)) := by
  have hsum : Integrable (fun x : ℝ ↦
      ∑ n ∈ Finset.Ioc X (2 * X),
        (Set.Ico (n : ℝ) ((n : ℝ) + 1)).indicator
          (fun _ ↦ Complex.normSq (integerShortSum a n H)) x) := by
    apply MeasureTheory.integrable_finset_sum
    intro n hn
    have hconst : IntegrableOn
        (fun _x : ℝ ↦ Complex.normSq (integerShortSum a n H))
        (Set.Ico (n : ℝ) ((n : ℝ) + 1)) := by
      apply MeasureTheory.integrableOn_const
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top
      exact enorm_ne_top
    exact hconst.integrable_indicator measurableSet_Ico
  have hstep : Integrable (fun x : ℝ ↦
      Complex.normSq (realEndpointStepShortSum a X H x)) :=
    hsum.congr (Filter.Eventually.of_forall fun x ↦
      (normSq_realEndpointStepShortSum a X H x).symm)
  have hdiv := hstep.div_const ((H : ℝ) ^ 2)
  apply hdiv.congr
  filter_upwards [] with x
  unfold realEndpointStepShortAverage
  rw [Complex.normSq_div, Complex.normSq_natCast, pow_two]

theorem integral_normSq_realEndpointStepShortAverage_window_eq
    (a : ℕ → ℂ) (X : ℕ) {H : ℕ} (hH : 0 < H) :
    (∫ x in Set.Ioc ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1),
        Complex.normSq (realEndpointStepShortAverage a X H x)) =
      uncenteredShortIntervalMeanSquare a X H / (H : ℝ) ^ 2 := by
  have hset := integral_normSq_realEndpointStepShortSum_window_eq a X H
  rw [MeasureTheory.restrict_Ico_eq_restrict_Ioc] at hset
  unfold realEndpointStepShortAverage
  simp_rw [Complex.normSq_div, Complex.normSq_natCast]
  simp_rw [div_eq_mul_inv]
  rw [MeasureTheory.integral_mul_const, hset]
  ring

theorem realEndpointStepShortAverage_eq_dyadic_on_unitCell
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ)
    {X H n : ℕ} (hn : n ∈ Finset.Ioc X (2 * X))
    {x : ℝ} (hx : x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)) :
    realEndpointStepShortAverage
        (dyadicRestrictedCoefficient S f Y) X H x =
      dyadicRestrictedShortAverage S f Y n H := by
  rw [realEndpointStepShortAverage,
    realEndpointStepShortSum_eq_on_unitCell _ hn hx]
  unfold integerShortSum dyadicRestrictedShortAverage
  rw [sum_Icc_add_eq_sum_Ioc]

/-- Apart from the integer cell boundaries (a null set), every point in the
shifted real window belongs to the open unit cell of a unique base
`n ∈ (X,2X]`. -/
theorem ae_exists_open_unitCell_on_realEndpoint_window (X : ℕ) :
    ∀ᵐ x ∂volume.restrict
        (Set.Ioc ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1)),
      ∃ n ∈ Finset.Ioc X (2 * X),
        x ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1) := by
  let W : Set ℝ := Set.Ioc ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1)
  have hboundaries :
      ∀ᵐ x ∂volume.restrict W, x ∉ Set.range (fun n : ℕ ↦ (n : ℝ)) :=
    (Set.countable_range (fun n : ℕ ↦ (n : ℝ))).ae_notMem _
  filter_upwards [hboundaries, ae_restrict_mem measurableSet_Ioc] with x hxnot hxW
  let n : ℕ := ⌊x⌋₊
  have hxnonneg : 0 ≤ x := by
    have hXnonneg : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    linarith [hxW.1]
  have hnle : (n : ℝ) ≤ x := Nat.floor_le hxnonneg
  have hxlt : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hxne : x ≠ (n : ℝ) := by
    intro heq
    exact hxnot ⟨n, heq.symm⟩
  have hnlt : (n : ℝ) < x := lt_of_le_of_ne hnle (Ne.symm hxne)
  have hXn : X < n := by
    have hle : X + 1 ≤ n := Nat.le_floor (by
      norm_num only [Nat.cast_add, Nat.cast_one]
      exact hxW.1.le)
    omega
  have hn2X : n ≤ 2 * X := by
    have hxneUpper : x ≠ (((2 * X : ℕ) : ℝ) + 1) := by
      intro heq
      exact hxnot ⟨2 * X + 1, by
        simpa only [Nat.cast_add, Nat.cast_one] using heq.symm⟩
    have hxltUpper : x < (((2 * X : ℕ) : ℝ) + 1) :=
      lt_of_le_of_ne hxW.2 hxneUpper
    have hlt : n < 2 * X + 1 :=
      (Nat.floor_lt hxnonneg).2 (by
        simpa only [Nat.cast_add, Nat.cast_one] using hxltUpper)
    omega
  exact ⟨n, Finset.mem_Ioc.mpr ⟨hXn, hn2X⟩, hnlt, hxlt⟩

/-- Almost-everywhere convergence on the correctly shifted real endpoint
window.  The normalization agrees exactly with the finite Perron segment,
so no endpoint correction survives after integration. -/
theorem ae_tendsto_dyadicContinuousPerron_to_stepAverage
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X : ℕ)
    {H : ℕ} (hH : 0 < H) :
    ∀ᵐ x ∂volume.restrict
        (Set.Ioc ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1)),
      Filter.Tendsto
        (fun k : ℕ ↦ perronKernelSegmentOn
          (dyadicVerticalDirichletPolynomial S f Y) x H
          (-(k : ℝ)) (k : ℝ))
        Filter.atTop
        (nhds (realEndpointStepShortAverage
          (dyadicRestrictedCoefficient S f Y) X H x)) := by
  filter_upwards [ae_exists_open_unitCell_on_realEndpoint_window X]
    with x hxcell
  rcases hxcell with ⟨n, hn, hx⟩
  have hreal := tendsto_perronKernelSegmentOn_dyadic_on_cell
    S f Y hx hH
  have hnat : Filter.Tendsto (fun k : ℕ ↦ (k : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hlim := hreal.comp hnat
  rw [realEndpointStepShortAverage_eq_dyadic_on_unitCell
    S f Y hn ⟨hx.1.le, hx.2⟩]
  exact hlim

/-- Fatou transfer from uniform finite-height continuous Perron estimates to
the exact discrete normalized mean square.  This is the point where the
outer Perron height is sent to infinity; there is no squared truncation
error. -/
theorem normalized_uncenteredShortIntervalMeanSquare_le_of_uniform_continuousPerron
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ)
    {X H : ℕ} (hH : 0 < H) {T E : ℝ} (hT : 0 ≤ T) (hE : 0 ≤ E)
    (huniform : ∀ U : ℝ, T ≤ U →
      (∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
        Complex.normSq (perronKernelSegmentOn
          (dyadicVerticalDirichletPolynomial S f Y) x H (-U) U)) ≤ E) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f Y) X H / (H : ℝ) ^ 2 ≤ E := by
  let P : ℝ := (X : ℝ) + 1
  let Q : ℝ := ((2 * X : ℕ) : ℝ) + 1
  let W : Set ℝ := Set.Ioc P Q
  let U : ℕ → ℕ := fun k ↦ Nat.ceil T + k
  let G : ℕ → ℝ → ℝ := fun k x ↦
    Complex.normSq (perronKernelSegmentOn
      (dyadicVerticalDirichletPolynomial S f Y) x H
        (-(U k : ℝ)) (U k : ℝ))
  let g : ℝ → ℝ := fun x ↦
    Complex.normSq (realEndpointStepShortAverage
      (dyadicRestrictedCoefficient S f Y) X H x)
  have hP : 0 < P := by
    dsimp only [P]
    positivity
  have hPQ : P ≤ Q := by
    dsimp only [P, Q]
    have hXR : (X : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by
      exact_mod_cast (show X ≤ 2 * X by omega)
    linarith
  have hlim0 : ∀ᵐ x ∂volume.restrict W,
      Filter.Tendsto
        (fun k : ℕ ↦ perronKernelSegmentOn
          (dyadicVerticalDirichletPolynomial S f Y) x H
          (-(k : ℝ)) (k : ℝ))
        Filter.atTop
        (nhds (realEndpointStepShortAverage
          (dyadicRestrictedCoefficient S f Y) X H x)) := by
    simpa only [W, P, Q] using
      ae_tendsto_dyadicContinuousPerron_to_stepAverage S f Y X hH
  have hGg : ∀ᵐ x ∂volume.restrict W,
      Filter.Tendsto (fun k : ℕ ↦ G k x) Filter.atTop (nhds (g x)) := by
    filter_upwards [hlim0] with x hx
    have hshift : Filter.Tendsto (fun k : ℕ ↦ k + Nat.ceil T)
        Filter.atTop Filter.atTop := Filter.tendsto_add_atTop_nat (Nat.ceil T)
    have hmodel : Filter.Tendsto
        (fun k : ℕ ↦ perronKernelSegmentOn
          (dyadicVerticalDirichletPolynomial S f Y) x H
          (-(U k : ℝ)) (U k : ℝ)) Filter.atTop
        (nhds (realEndpointStepShortAverage
          (dyadicRestrictedCoefficient S f Y) X H x)) := by
      refine Filter.Tendsto.congr' ?_ (hx.comp hshift)
      filter_upwards [] with k
      simp only [U, Nat.add_comm, Function.comp_apply]
    exact (Complex.continuous_normSq.tendsto _).comp hmodel
  have hGc (k : ℕ) : ContinuousOn (G k) (Set.Icc P Q) := by
    dsimp only [G]
    exact Complex.continuous_normSq.comp_continuousOn
      ((continuousOn_perronKernelSegmentOn
        (dyadicVerticalDirichletPolynomial S f Y)
        (continuous_dyadicVerticalDirichletPolynomial S f Y)
        hP (by exact_mod_cast hH) (-(U k : ℝ)) (U k : ℝ)).mono
          Set.Icc_subset_Ici_self)
  have hGi (k : ℕ) : Integrable (G k) (volume.restrict W) := by
    exact (hGc k).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hGaem (k : ℕ) : AEMeasurable (fun x ↦ ‖G k x‖ₑ)
      (volume.restrict W) := by
    exact ((hGc k).mono Set.Ioc_subset_Icc_self).aemeasurable
      measurableSet_Ioc |>.enorm
  have hfatou := lintegral_enorm_le_liminf_of_tendsto hGg hGaem
  have hGnonneg (k : ℕ) (x : ℝ) : 0 ≤ G k x :=
    Complex.normSq_nonneg _
  have hgnonneg (x : ℝ) : 0 ≤ g x := Complex.normSq_nonneg _
  have hlin (k : ℕ) :
      (∫⁻ x, ‖G k x‖ₑ ∂volume.restrict W) =
        ENNReal.ofReal (∫ x in P..Q, G k x) := by
    rw [show (∫⁻ x, ‖G k x‖ₑ ∂volume.restrict W) =
        ∫⁻ x, ENNReal.ofReal (G k x) ∂volume.restrict W by
          apply lintegral_congr
          intro x
          exact Real.enorm_eq_ofReal (hGnonneg k x)]
    rw [← ofReal_integral_eq_lintegral_ofReal (hGi k)
      (Filter.Eventually.of_forall (hGnonneg k))]
    congr 1
    rw [intervalIntegral.integral_of_le hPQ]
  have hliminf :
      Filter.liminf
          (fun k : ℕ ↦ ∫⁻ x, ‖G k x‖ₑ ∂volume.restrict W)
          Filter.atTop ≤ ENNReal.ofReal E := by
    apply Filter.liminf_le_of_frequently_le'
    apply Filter.Frequently.of_forall
    intro k
    rw [hlin k]
    apply ENNReal.ofReal_le_ofReal
    apply huniform
    calc
      T ≤ (Nat.ceil T : ℝ) := Nat.le_ceil T
      _ ≤ (Nat.ceil T + k : ℕ) := by
        exact_mod_cast Nat.le_add_right (Nat.ceil T) k
  have hgle : (∫⁻ x, ‖g x‖ₑ ∂volume.restrict W) ≤
      ENNReal.ofReal E := hfatou.trans hliminf
  have hgi : Integrable g (volume.restrict W) :=
    (integrable_normSq_realEndpointStepShortAverage
      (dyadicRestrictedCoefficient S f Y) X H).restrict
  have hgint : (∫⁻ x, ‖g x‖ₑ ∂volume.restrict W) =
      ENNReal.ofReal (∫ x in W, g x) := by
    rw [show (∫⁻ x, ‖g x‖ₑ ∂volume.restrict W) =
        ∫⁻ x, ENNReal.ofReal (g x) ∂volume.restrict W by
          apply lintegral_congr
          intro x
          exact Real.enorm_eq_ofReal (hgnonneg x)]
    exact (ofReal_integral_eq_lintegral_ofReal hgi
      (Filter.Eventually.of_forall hgnonneg)).symm
  rw [hgint, integral_normSq_realEndpointStepShortAverage_window_eq
    _ X hH] at hgle
  exact (ENNReal.ofReal_le_ofReal_iff hE).mp hgle

private theorem continuous_mul_perronIncrementKernel_real
    (F : ℝ → ℂ) (hF : Continuous F) {x h : ℝ}
    (hx : 0 < x) (hh : 0 < h) :
    Continuous (fun t ↦ F t * perronIncrementKernel x h t) := by
  unfold perronIncrementKernel
  apply hF.mul
  apply Continuous.div
  · have he : Continuous (fun t : ℝ ↦ (1 : ℂ) + (t : ℂ) * Complex.I) := by
      fun_prop
    have hxHc : ((x + h : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (add_pos hx hh).ne'
    have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    exact (he.const_cpow (Or.inl hxHc)).sub
      (he.const_cpow (Or.inl hxc))
  · fun_prop
  · intro t ht
    rcases mul_eq_zero.mp ht with hcast | hline
    · exact (Complex.ofReal_ne_zero.mpr hh.ne') hcast
    · have hre := congrArg Complex.re hline
      norm_num at hre

/-- Exact central/high decomposition of a symmetric real-endpoint Perron
segment. -/
theorem perronKernelSegmentOn_eq_central_add_symmetricHigh
    (F : ℝ → ℂ) (hF : Continuous F)
    {x h T U : ℝ} (hx : 0 < x) (hh : 0 < h) :
    perronKernelSegmentOn F x h (-U) U =
      perronKernelSegmentOn F x h (-T) T +
        lemma14SymmetricPerronHighSegmentOn F x h T U := by
  let G : ℝ → ℂ := fun t ↦ F t * perronIncrementKernel x h t
  have hG : Continuous G :=
    continuous_mul_perronIncrementKernel_real F hF hx hh
  have hleft := intervalIntegral.integral_add_adjacent_intervals
    (hG.intervalIntegrable (μ := volume) (-U) (-T))
    (hG.intervalIntegrable (μ := volume) (-T) T)
  have hright := intervalIntegral.integral_add_adjacent_intervals
    (hG.intervalIntegrable (μ := volume) (-U) T)
    (hG.intervalIntegrable (μ := volume) T U)
  have hsplit :
      (∫ t in -U..U, G t) =
        (∫ t in -T..T, G t) +
          (∫ t in -U..-T, G t) + ∫ t in T..U, G t := by
    calc
      (∫ t in -U..U, G t) =
          (∫ t in -U..T, G t) + ∫ t in T..U, G t := hright.symm
      _ = ((∫ t in -U..-T, G t) + ∫ t in -T..T, G t) +
          ∫ t in T..U, G t := by rw [hleft]
      _ = _ := by ring
  unfold perronKernelSegmentOn lemma14SymmetricPerronHighSegmentOn
  change (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in -U..U, G t)) = _
  rw [hsplit]
  simp only [perronKernelSegmentOn]
  dsimp only [G]
  ring

/-- Source-form continuous Lemma-14 transfer.  The actual discrete normalized
short-interval mean square is bounded by the central Perron band plus a
uniform reciprocal-square weighted far-frequency energy.  The spatial
window is exactly `[X+1,2X+1]`, matching the unit-cell embedding. -/
theorem normalized_uncenteredShortIntervalMeanSquare_le_central_add_weightedHigh
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ)
    {X H : ℕ} (hH : 0 < H) {T Efar : ℝ}
    (hT : 0 < T) (hEfar : 0 ≤ Efar)
    (hfar : ∀ U : ℝ, T ≤ U →
      (∫ t in -U..-T,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)) +
        ∫ t in T..U,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t) ≤ Efar) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f Y) X H / (H : ℝ) ^ 2 ≤
      2 * (∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
        Complex.normSq (perronKernelSegmentOn
          (dyadicVerticalDirichletPolynomial S f Y) x H (-T) T)) +
      4 * lemma14UniversalPerronSegmentSafeWeightedCoefficient
          ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H * Efar := by
  let F : ℝ → ℂ := dyadicVerticalDirichletPolynomial S f Y
  let P : ℝ := (X : ℝ) + 1
  let Q : ℝ := ((2 * X : ℕ) : ℝ) + 1
  let C : ℝ := lemma14UniversalPerronSegmentSafeWeightedCoefficient P Q H
  let Ecentral : ℝ := ∫ x in P..Q,
    Complex.normSq (perronKernelSegmentOn F x H (-T) T)
  have hF : Continuous F := continuous_dyadicVerticalDirichletPolynomial S f Y
  have hP : 0 < P := by dsimp only [P]; positivity
  have hPQ : P ≤ Q := by
    dsimp only [P, Q]
    have hXR : (X : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by
      exact_mod_cast (show X ≤ 2 * X by omega)
    linarith
  have hQ3P : Q ≤ 3 * P := by
    dsimp only [P, Q]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    nlinarith
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hC : 0 ≤ C :=
    lemma14UniversalPerronSegmentSafeWeightedCoefficient_nonneg
      hP hPQ hHR
  have hcentralCont : ContinuousOn
      (fun x ↦ perronKernelSegmentOn F x H (-T) T) (Set.uIcc P Q) :=
    (continuousOn_perronKernelSegmentOn F hF hP hHR (-T) T).mono (by
      rw [Set.uIcc_of_le hPQ]
      exact Set.Icc_subset_Ici_self)
  have hEcentral : 0 ≤ Ecentral := by
    dsimp only [Ecentral]
    apply intervalIntegral.integral_nonneg hPQ
    intro x hx
    exact Complex.normSq_nonneg _
  apply normalized_uncenteredShortIntervalMeanSquare_le_of_uniform_continuousPerron
    S f Y hH hT.le
      (add_nonneg (mul_nonneg (by norm_num) hEcentral)
        (mul_nonneg
          (mul_nonneg (by norm_num) hC) hEfar))
  intro U hTU
  let L : ℝ → ℂ := fun x ↦ perronKernelSegmentOn F x H (-T) T
  let R : ℝ → ℂ := fun x ↦
    lemma14SymmetricPerronHighSegmentOn F x H T U
  have hleftCont : ContinuousOn L (Set.uIcc P Q) := hcentralCont
  have hrightCont : ContinuousOn R (Set.uIcc P Q) := by
    apply (ContinuousOn.add
      ((continuousOn_perronKernelSegmentOn F hF hP hHR (-U) (-T)).mono ?_)
      ((continuousOn_perronKernelSegmentOn F hF hP hHR T U).mono ?_))
    · rw [Set.uIcc_of_le hPQ]
      exact Set.Icc_subset_Ici_self
    · rw [Set.uIcc_of_le hPQ]
      exact Set.Icc_subset_Ici_self
  have hcombine := intervalIntegral_normSq_add_le_two_add
    L R hPQ hleftCont hrightCont
  have hhigh :=
    integral_normSq_lemma14SymmetricPerronHighSegmentOn_le_safeWeighted_universal
      F hF hP hPQ hQ3P hHR hT hTU
  have hfull :
      (∫ x in P..Q,
        Complex.normSq (perronKernelSegmentOn F x H (-U) U)) ≤
        2 * (Ecentral + ∫ x in P..Q, Complex.normSq (R x)) := by
    calc
      (∫ x in P..Q,
          Complex.normSq (perronKernelSegmentOn F x H (-U) U)) =
          ∫ x in P..Q, Complex.normSq (L x + R x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hxIcc : x ∈ Set.Icc P Q := by
          rwa [Set.uIcc_of_le hPQ] at hx
        dsimp only [L, R]
        rw [perronKernelSegmentOn_eq_central_add_symmetricHigh
          F hF (hP.trans_le hxIcc.1) hHR]
      _ ≤ 2 * ((∫ x in P..Q, Complex.normSq (L x)) +
          ∫ x in P..Q, Complex.normSq (R x)) := hcombine
      _ = 2 * (Ecentral +
          ∫ x in P..Q, Complex.normSq (R x)) := by rfl
  change (∫ x in P..Q,
      Complex.normSq (perronKernelSegmentOn F x H (-U) U)) ≤
    2 * Ecentral + 4 * C * Efar
  calc
    (∫ x in P..Q,
        Complex.normSq (perronKernelSegmentOn F x H (-U) U)) ≤
        2 * (Ecentral + ∫ x in P..Q, Complex.normSq (R x)) := hfull
    _ ≤ 2 * (Ecentral + 2 * C * Efar) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add (le_refl Ecentral)
      calc
        (∫ x in P..Q, Complex.normSq (R x)) ≤
            2 * C *
              ((∫ t in -U..-T,
                  lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
                ∫ t in T..U,
                  lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) := by
          simpa only [R, C] using hhigh
        _ ≤ 2 * C * Efar :=
          mul_le_mul_of_nonneg_left (hfar U hTU)
            (mul_nonneg (by norm_num) hC)
    _ = 2 * Ecentral + 4 * C * Efar := by ring

/-- Unnormalized form of the source transfer.  This is the direct endpoint
for `uncenteredShortIntervalMeanSquare`: the `H^2` normalization is restored
only after the low/high cancellation argument has been completed. -/
theorem uncenteredShortIntervalMeanSquare_le_central_add_weightedHigh
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ)
    {X H : ℕ} (hH : 0 < H) {T Efar : ℝ}
    (hT : 0 < T) (hEfar : 0 ≤ Efar)
    (hfar : ∀ U : ℝ, T ≤ U →
      (∫ t in -U..-T,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)) +
        ∫ t in T..U,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t) ≤ Efar) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f Y) X H ≤
      2 * (H : ℝ) ^ 2 *
        (∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
          Complex.normSq (perronKernelSegmentOn
            (dyadicVerticalDirichletPolynomial S f Y) x H (-T) T)) +
      4 * (H : ℝ) ^ 2 *
        lemma14UniversalPerronSegmentSafeWeightedCoefficient
          ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H * Efar := by
  have hnorm :=
    normalized_uncenteredShortIntervalMeanSquare_le_central_add_weightedHigh
      S f Y (X := X) hH hT hEfar hfar
  have hHsq : (0 : ℝ) < (H : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hH)
  have hscaled := (div_le_iff₀ hHsq).mp hnorm
  calc
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f Y) X H ≤
        (2 * (∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
          Complex.normSq (perronKernelSegmentOn
            (dyadicVerticalDirichletPolynomial S f Y) x H (-T) T)) +
          4 * lemma14UniversalPerronSegmentSafeWeightedCoefficient
            ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H * Efar) *
          (H : ℝ) ^ 2 := hscaled
    _ = _ := by ring

/-- One-bounded specialization: the complete far tail has total safe
reciprocal-square mass at most `2/T`, independently of the outer height. -/
theorem normalized_uncenteredShortIntervalMeanSquare_le_central_add_invHigh
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (Y : ℕ)
    {X H : ℕ} (hH : 0 < H) {T : ℝ} (hT : 0 < T) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f Y) X H / (H : ℝ) ^ 2 ≤
      2 * (∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
        Complex.normSq (perronKernelSegmentOn
          (dyadicVerticalDirichletPolynomial S f Y) x H (-T) T)) +
      8 * lemma14UniversalPerronSegmentSafeWeightedCoefficient
          ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H * T⁻¹ := by
  have hF := continuous_dyadicVerticalDirichletPolynomial S f Y
  have hFnorm := norm_dyadicVerticalDirichletPolynomial_le_one S hf Y
  have hfar (U : ℝ) (hTU : T ≤ U) :
      (∫ t in -U..-T,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)) +
        ∫ t in T..U,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t) ≤
      2 * T⁻¹ := by
    have hneg := intervalIntegral_safeReciprocalSqWeight_mul_normSq_neg_le_inv
      (dyadicVerticalDirichletPolynomial S f Y) hF hFnorm hT hTU
    have hpos := intervalIntegral_safeReciprocalSqWeight_mul_normSq_le_inv
      (dyadicVerticalDirichletPolynomial S f Y) hF hFnorm hT hTU
    linarith
  have hbase :=
    normalized_uncenteredShortIntervalMeanSquare_le_central_add_weightedHigh
      S f Y (X := X) hH hT
        (mul_nonneg (by norm_num) (inv_nonneg.mpr hT.le)) hfar
  convert hbase using 1 <;> ring

/-- Step-function embedding of the difference of two normalized dyadic
short averages. -/
def dyadicTwoLengthStepAverage
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H₁ H₂ : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc X (2 * X),
    (Set.Ico (n : ℝ) ((n : ℝ) + 1)).indicator
      (fun _ ↦ dyadicRestrictedShortAverage S f Y n H₁ -
        dyadicRestrictedShortAverage S f Y n H₂) x

private theorem dyadicTwoLengthStepAverage_eq_on_unitCell
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ)
    {X H₁ H₂ n : ℕ} (hn : n ∈ Finset.Ioc X (2 * X))
    {x : ℝ} (hx : x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)) :
    dyadicTwoLengthStepAverage S f Y X H₁ H₂ x =
      dyadicRestrictedShortAverage S f Y n H₁ -
        dyadicRestrictedShortAverage S f Y n H₂ := by
  classical
  unfold dyadicTwoLengthStepAverage
  rw [Finset.sum_eq_single n]
  · exact Set.indicator_of_mem hx _
  · intro m hm hmn
    apply Set.indicator_of_notMem
    intro hxm
    have hmnlt : m < n + 1 := by
      exact_mod_cast hxm.1.trans_lt hx.2
    have hnm_lt : n < m + 1 := by
      exact_mod_cast hx.1.trans_lt hxm.2
    omega
  · intro hnot
    exact (hnot hn).elim

private theorem normSq_dyadicTwoLengthStepAverage
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H₁ H₂ : ℕ) (x : ℝ) :
    Complex.normSq (dyadicTwoLengthStepAverage S f Y X H₁ H₂ x) =
      ∑ n ∈ Finset.Ioc X (2 * X),
        (Set.Ico (n : ℝ) ((n : ℝ) + 1)).indicator
          (fun _ ↦ Complex.normSq
            (dyadicRestrictedShortAverage S f Y n H₁ -
              dyadicRestrictedShortAverage S f Y n H₂)) x := by
  classical
  unfold dyadicTwoLengthStepAverage
  rw [normSq_sum_eq_sum_normSq_of_pairwise_disjoint]
  · apply Finset.sum_congr rfl
    intro n hn
    by_cases hx : x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  · intro m hm n hn hmn
    by_cases hxm : x ∈ Set.Ico (m : ℝ) ((m : ℝ) + 1)
    · by_cases hxn : x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)
      · exfalso
        apply hmn
        have hmnlt : m < n + 1 := by exact_mod_cast hxm.1.trans_lt hxn.2
        have hnm_lt : n < m + 1 := by exact_mod_cast hxn.1.trans_lt hxm.2
        omega
      · exact Or.inr (Set.indicator_of_notMem hxn _)
    · exact Or.inl (Set.indicator_of_notMem hxm _)

theorem integrable_normSq_dyadicTwoLengthStepAverage
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H₁ H₂ : ℕ) :
    Integrable (fun x : ℝ ↦
      Complex.normSq (dyadicTwoLengthStepAverage S f Y X H₁ H₂ x)) := by
  have hsum : Integrable (fun x : ℝ ↦
      ∑ n ∈ Finset.Ioc X (2 * X),
        (Set.Ico (n : ℝ) ((n : ℝ) + 1)).indicator
          (fun _ ↦ Complex.normSq
            (dyadicRestrictedShortAverage S f Y n H₁ -
              dyadicRestrictedShortAverage S f Y n H₂)) x) := by
    apply MeasureTheory.integrable_finsetSum
    intro n hn
    have hconst : IntegrableOn (fun _x : ℝ ↦ Complex.normSq
        (dyadicRestrictedShortAverage S f Y n H₁ -
          dyadicRestrictedShortAverage S f Y n H₂))
        (Set.Ico (n : ℝ) ((n : ℝ) + 1)) := by
      apply MeasureTheory.integrableOn_const
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top
      exact enorm_ne_top
    exact hconst.integrable_indicator measurableSet_Ico
  exact hsum.congr (Filter.Eventually.of_forall fun x ↦
    (normSq_dyadicTwoLengthStepAverage S f Y X H₁ H₂ x).symm)

theorem integral_normSq_dyadicTwoLengthStepAverage_window_eq
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H₁ H₂ : ℕ) :
    (∫ x in Set.Ioc ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1),
      Complex.normSq (dyadicTwoLengthStepAverage S f Y X H₁ H₂ x)) =
      ∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq
        (dyadicRestrictedShortAverage S f Y n H₁ -
          dyadicRestrictedShortAverage S f Y n H₂) := by
  let W : Set ℝ := Set.Ico ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1)
  let q : ℝ → ℝ := fun x ↦
    Complex.normSq (dyadicTwoLengthStepAverage S f Y X H₁ H₂ x)
  have hglobal : (∫ x : ℝ, q x) =
      ∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq
        (dyadicRestrictedShortAverage S f Y n H₁ -
          dyadicRestrictedShortAverage S f Y n H₂) := by
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x ↦
        normSq_dyadicTwoLengthStepAverage S f Y X H₁ H₂ x)]
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [MeasureTheory.integral_indicator measurableSet_Ico]
      rw [setIntegral_const, measureReal_def, Real.volume_Ico]
      norm_num
    · intro n hn
      have hconst : IntegrableOn (fun _x : ℝ ↦ Complex.normSq
          (dyadicRestrictedShortAverage S f Y n H₁ -
            dyadicRestrictedShortAverage S f Y n H₂))
          (Set.Ico (n : ℝ) ((n : ℝ) + 1)) := by
        apply MeasureTheory.integrableOn_const
        rw [Real.volume_Ico]
        exact ENNReal.ofReal_ne_top
        exact enorm_ne_top
      exact hconst.integrable_indicator measurableSet_Ico
  have hzero : ∀ x ∉ W, q x = 0 := by
    intro x hx
    have hstep : dyadicTwoLengthStepAverage S f Y X H₁ H₂ x = 0 := by
      classical
      unfold dyadicTwoLengthStepAverage
      apply Finset.sum_eq_zero
      intro n hn
      apply Set.indicator_of_notMem
      intro hxn
      apply hx
      have hnb := Finset.mem_Ioc.mp hn
      constructor
      · have hnat : X + 1 ≤ n := by omega
        exact (by exact_mod_cast hnat : (X : ℝ) + 1 ≤ n) |>.trans hxn.1
      · have hnat : n + 1 ≤ 2 * X + 1 := by omega
        exact hxn.2.trans_le (by exact_mod_cast hnat)
    dsimp only [q]
    rw [hstep, Complex.normSq_zero]
  have hwindow : (∫ x in W, q x) = ∫ x : ℝ, q x := by
    calc
      (∫ x in W, q x) = ∫ x : ℝ, W.indicator q x :=
        (MeasureTheory.integral_indicator measurableSet_Ico).symm
      _ = ∫ x : ℝ, q x := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ W
        · exact Set.indicator_of_mem hx q
        · rw [Set.indicator_of_notMem hx, hzero x hx]
  rw [← hglobal, ← hwindow]
  change (∫ x in Set.Ioc ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1), q x) = _
  rw [← MeasureTheory.restrict_Ico_eq_restrict_Ioc]

/-- Pointwise low-frequency cancellation at a real starting point in the
shifted unit-cell window. -/
theorem norm_dyadicTwoLengthPerronCentral_real_le
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (Y : ℕ)
    {X H₁ H₂ : ℕ} (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T x : ℝ} (hT : 0 ≤ T) (hx : (X : ℝ) + 1 ≤ x) :
    ‖perronKernelSegmentOn
          (dyadicVerticalDirichletPolynomial S f Y) x H₁ (-T) T -
        perronKernelSegmentOn
          (dyadicVerticalDirichletPolynomial S f Y) x H₂ (-T) T‖ ≤
      ‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ *
        (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / ((X : ℝ) + 1)) := by
  let F : ℝ → ℂ := dyadicVerticalDirichletPolynomial S f Y
  let K : ℝ → ℂ := fun t ↦
    perronIncrementKernel x H₁ t - perronIncrementKernel x H₂ t
  have hP : (0 : ℝ) < (X : ℝ) + 1 := by positivity
  have hxpos : 0 < x := hP.trans_le hx
  have hH₁R : (0 : ℝ) < H₁ := by exact_mod_cast hH₁
  have hH₂R : (0 : ℝ) < H₂ := by exact_mod_cast hH₂
  have hF : Continuous F := continuous_dyadicVerticalDirichletPolynomial S f Y
  have hrewrite :
      perronKernelSegmentOn F x H₁ (-T) T -
          perronKernelSegmentOn F x H₂ (-T) T =
        (((2 * Real.pi : ℝ) : ℂ)⁻¹) * ∫ t in -T..T, F t * K t := by
    unfold perronKernelSegmentOn
    rw [← mul_sub]
    rw [← intervalIntegral.integral_sub
      ((continuous_mul_perronIncrementKernel_real F hF hxpos hH₁R).intervalIntegrable
        (-T) T)
      ((continuous_mul_perronIncrementKernel_real F hF hxpos hH₂R).intervalIntegrable
        (-T) T)]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only [K]
    ring
  change ‖perronKernelSegmentOn F x H₁ (-T) T -
      perronKernelSegmentOn F x H₂ (-T) T‖ ≤ _
  rw [hrewrite, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hpoint (t : ℝ) (ht : t ∈ Set.uIoc (-T) T) :
      ‖F t * K t‖ ≤
        T * (((H₁ : ℝ) + H₂) / ((X : ℝ) + 1)) := by
    rw [Set.uIoc_of_le (by linarith)] at ht
    have habst : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have hkernel := norm_perronIncrementKernel_sub_le_relative
      hxpos hH₁R hH₂R t
    have hsum : (0 : ℝ) ≤ (H₁ : ℝ) + H₂ := by positivity
    have hratio : |t| * ((H₁ : ℝ) + H₂) / x ≤
        T * ((H₁ : ℝ) + H₂) / ((X : ℝ) + 1) := by
      calc
        |t| * ((H₁ : ℝ) + H₂) / x ≤
            T * ((H₁ : ℝ) + H₂) / x := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right habst hsum) hxpos.le
        _ ≤ T * ((H₁ : ℝ) + H₂) / ((X : ℝ) + 1) := by
          exact div_le_div_of_nonneg_left (mul_nonneg hT hsum) hP hx
    calc
      ‖F t * K t‖ = ‖F t‖ * ‖K t‖ := norm_mul _ _
      _ ≤ 1 * (|t| * ((H₁ : ℝ) + H₂) / x) := by
        gcongr
        exact norm_dyadicVerticalDirichletPolynomial_le_one S hf Y t
      _ = |t| * ((H₁ : ℝ) + H₂) / x := by ring
      _ ≤ T * ((H₁ : ℝ) + H₂) / ((X : ℝ) + 1) := hratio
      _ = T * (((H₁ : ℝ) + H₂) / ((X : ℝ) + 1)) := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ ↦ F t * K t)
    (C := T * (((H₁ : ℝ) + H₂) / ((X : ℝ) + 1)))
    (a := -T) (b := T) hpoint
  calc
    ‖∫ t in -T..T, F t * K t‖ ≤
        T * (((H₁ : ℝ) + H₂) / ((X : ℝ) + 1)) * |T - -T| := hint
    _ = 2 * T ^ 2 * ((H₁ : ℝ) + H₂) / ((X : ℝ) + 1) := by
      rw [show T - -T = 2 * T by ring, abs_of_nonneg (by positivity)]
      ring

/-- Integrated continuous-x low-frequency cancellation on the exact shifted
window. -/
theorem integral_normSq_dyadicTwoLengthPerronCentral_le
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (Y : ℕ)
    {X H₁ H₂ : ℕ} (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
      Complex.normSq
        (perronKernelSegmentOn
            (dyadicVerticalDirichletPolynomial S f Y) x H₁ (-T) T -
          perronKernelSegmentOn
            (dyadicVerticalDirichletPolynomial S f Y) x H₂ (-T) T)) ≤
      (X : ℝ) *
        (‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ *
          (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / ((X : ℝ) + 1))) ^ 2 := by
  let P : ℝ := (X : ℝ) + 1
  let Q : ℝ := ((2 * X : ℕ) : ℝ) + 1
  let G : ℝ → ℂ := fun x ↦
    perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
        x H₁ (-T) T -
      perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
        x H₂ (-T) T
  let C : ℝ := ‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ *
    (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / P)
  have hP : 0 < P := by dsimp only [P]; positivity
  have hPQ : P ≤ Q := by
    dsimp only [P, Q]
    have hXR : (X : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by
      exact_mod_cast (show X ≤ 2 * X by omega)
    linarith
  have hH₁R : (0 : ℝ) < H₁ := by exact_mod_cast hH₁
  have hH₂R : (0 : ℝ) < H₂ := by exact_mod_cast hH₂
  have hF := continuous_dyadicVerticalDirichletPolynomial S f Y
  have hGcont : ContinuousOn G (Set.uIcc P Q) := by
    apply ContinuousOn.sub
    · exact (continuousOn_perronKernelSegmentOn _ hF hP hH₁R (-T) T).mono
        (by rw [Set.uIcc_of_le hPQ]; exact Set.Icc_subset_Ici_self)
    · exact (continuousOn_perronKernelSegmentOn _ hF hP hH₂R (-T) T).mono
        (by rw [Set.uIcc_of_le hPQ]; exact Set.Icc_subset_Ici_self)
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc P Q) : Complex.normSq (G x) ≤ C ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    have hn := norm_dyadicTwoLengthPerronCentral_real_le
      S hf Y hH₁ hH₂ hT hx.1
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    exact (sq_le_sq₀ (norm_nonneg _) hC).2 (by simpa only [G, C, P] using hn)
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hPQ
    (Complex.continuous_normSq.comp_continuousOn hGcont).intervalIntegrable
    ((continuousOn_const : ContinuousOn
      (fun _x : ℝ ↦ C ^ 2) (Set.uIcc P Q)).intervalIntegrable) hpoint
  rw [intervalIntegral.integral_const] at hmono
  have hlength : Q - P = (X : ℝ) := by
    dsimp only [P, Q]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hlength] at hmono
  simpa only [G, C, P, Q, smul_eq_mul, Function.comp_apply] using hmono

/-- Low-band estimate retaining the original Dirichlet polynomial's vertical
`L²` energy.  This is the directly consumable near/medium-frequency form of
the source cancellation argument. -/
theorem integral_normSq_dyadicTwoLengthPerronCentral_le_verticalEnergy
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ)
    {X H₁ H₂ : ℕ} (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
      Complex.normSq
        (perronKernelSegmentOn
            (dyadicVerticalDirichletPolynomial S f Y) x H₁ (-T) T -
          perronKernelSegmentOn
            (dyadicVerticalDirichletPolynomial S f Y) x H₂ (-T) T)) ≤
      (X : ℝ) *
        Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
        (2 * T) *
        (T * ((H₁ : ℝ) + H₂) / ((X : ℝ) + 1)) ^ 2 *
        (∫ t in -T..T,
          Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)) := by
  let F : ℝ → ℂ := dyadicVerticalDirichletPolynomial S f Y
  let P : ℝ := (X : ℝ) + 1
  let Q : ℝ := ((2 * X : ℕ) : ℝ) + 1
  let D : ℝ := T * ((H₁ : ℝ) + H₂) / P
  let E : ℝ := ∫ t in -T..T, Complex.normSq (F t)
  let G : ℝ → ℂ := fun x ↦
    perronKernelSegmentOn F x H₁ (-T) T -
      perronKernelSegmentOn F x H₂ (-T) T
  let C : ℝ := Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
    (2 * T) * D ^ 2 * E
  have hF : Continuous F := continuous_dyadicVerticalDirichletPolynomial S f Y
  have hP : 0 < P := by dsimp only [P]; positivity
  have hPQ : P ≤ Q := by
    dsimp only [P, Q]
    have hXR : (X : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by
      exact_mod_cast (show X ≤ 2 * X by omega)
    linarith
  have hH₁R : (0 : ℝ) < H₁ := by exact_mod_cast hH₁
  have hH₂R : (0 : ℝ) < H₂ := by exact_mod_cast hH₂
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hE : 0 ≤ E := by
    dsimp only [E]
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact Complex.normSq_nonneg _
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Complex.normSq_nonneg _)
          (mul_nonneg (by norm_num) hT))
        (sq_nonneg D))
      hE
  have hGcont : ContinuousOn G (Set.uIcc P Q) := by
    apply ContinuousOn.sub
    · exact (continuousOn_perronKernelSegmentOn F hF hP hH₁R (-T) T).mono
        (by rw [Set.uIcc_of_le hPQ]; exact Set.Icc_subset_Ici_self)
    · exact (continuousOn_perronKernelSegmentOn F hF hP hH₂R (-T) T).mono
        (by rw [Set.uIcc_of_le hPQ]; exact Set.Icc_subset_Ici_self)
  have hmodel (x : ℝ) (hx : x ∈ Set.Icc P Q) :
      Complex.normSq (G x) ≤ C := by
    let K : ℝ → ℂ := fun t ↦
      perronIncrementKernel x H₁ t - perronIncrementKernel x H₂ t
    have hxpos : 0 < x := hP.trans_le hx.1
    have hFK : Continuous (fun t ↦ F t * K t) := by
      have h₁ := continuous_mul_perronIncrementKernel_real F hF hxpos hH₁R
      have h₂ := continuous_mul_perronIncrementKernel_real F hF hxpos hH₂R
      convert h₁.sub h₂ using 1 <;>
        ext t <;> simp only [K, Pi.sub_apply] <;> ring
    have hkernel (t : ℝ) (ht : t ∈ Set.Icc (-T) T) : ‖K t‖ ≤ D := by
      have habst : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      have hk := norm_perronIncrementKernel_sub_le_relative
        hxpos hH₁R hH₂R t
      have hsum : (0 : ℝ) ≤ (H₁ : ℝ) + H₂ := by positivity
      calc
        ‖K t‖ ≤ |t| * ((H₁ : ℝ) + H₂) / x := hk
        _ ≤ T * ((H₁ : ℝ) + H₂) / x := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right habst hsum) hxpos.le
        _ ≤ T * ((H₁ : ℝ) + H₂) / P := by
          exact div_le_div_of_nonneg_left (mul_nonneg hT hsum) hP hx.1
        _ = D := by rfl
    have hmul : (∫ t in -T..T, Complex.normSq (F t * K t)) ≤ D ^ 2 * E := by
      have hFKsq : ContinuousOn (fun t ↦ Complex.normSq (F t * K t))
          (Set.uIcc (-T) T) :=
        Complex.continuous_normSq.comp_continuousOn hFK.continuousOn
      have hmajor : ContinuousOn (fun t ↦ D ^ 2 * Complex.normSq (F t))
          (Set.uIcc (-T) T) :=
        continuousOn_const.mul (Complex.continuous_normSq.comp hF).continuousOn
      have hpt (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
          Complex.normSq (F t * K t) ≤ D ^ 2 * Complex.normSq (F t) := by
        rw [Complex.normSq_mul]
        have hksq := (sq_le_sq₀ (norm_nonneg (K t)) hD).2 (hkernel t ht)
        simpa only [Complex.normSq_eq_norm_sq, mul_comm] using
          (mul_le_mul_of_nonneg_left hksq (sq_nonneg ‖F t‖))
      calc
        (∫ t in -T..T, Complex.normSq (F t * K t)) ≤
            ∫ t in -T..T, D ^ 2 * Complex.normSq (F t) := by
          exact intervalIntegral.integral_mono_on (by linarith)
            hFKsq.intervalIntegrable hmajor.intervalIntegrable hpt
        _ = D ^ 2 * E := by
          rw [intervalIntegral.integral_const_mul]
    have hcs := normSq_intervalIntegral_le_length_mul_integral_normSq
      hFK (by linarith : -T ≤ T)
    have hrewrite : G x = ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
        ∫ t in -T..T, F t * K t := by
      dsimp only [G]
      unfold perronKernelSegmentOn
      rw [← mul_sub]
      rw [← intervalIntegral.integral_sub
        ((continuous_mul_perronIncrementKernel_real F hF hxpos hH₁R).intervalIntegrable
          (-T) T)
        ((continuous_mul_perronIncrementKernel_real F hF hxpos hH₂R).intervalIntegrable
          (-T) T)]
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only [K]
      ring
    rw [hrewrite, Complex.normSq_mul]
    calc
      Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
          Complex.normSq (∫ t in -T..T, F t * K t) ≤
        Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
          ((T - -T) * ∫ t in -T..T, Complex.normSq (F t * K t)) := by
        exact mul_le_mul_of_nonneg_left hcs (Complex.normSq_nonneg _)
      _ ≤ Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
          ((2 * T) * (D ^ 2 * E)) := by
        rw [show T - -T = 2 * T by ring]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmul (mul_nonneg (by norm_num) hT))
          (Complex.normSq_nonneg _)
      _ = C := by dsimp only [C]; ring
  have hCint : IntervalIntegrable (fun _x : ℝ ↦ C) volume P Q :=
    continuous_const.intervalIntegrable P Q
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hPQ
    (Complex.continuous_normSq.comp_continuousOn hGcont).intervalIntegrable
    hCint hmodel
  rw [intervalIntegral.integral_const] at hmono
  have hlength : Q - P = (X : ℝ) := by
    dsimp only [P, Q]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hlength] at hmono
  convert hmono using 1 <;>
    simp only [G, C, D, E, P, Q, smul_eq_mul, Function.comp_apply] <;>
    ring

/-- Genuine two-length source endpoint.  The central term is the square of
the *difference* of the two normalized Perron kernels, so its frequency-zero
main term cancels before estimation.  The far tails retain their full safe
reciprocal-square energies. -/
theorem dyadicTwoLengthShortMeanSquare_le_central_add_weightedHigh_continuous
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ)
    {X H₁ H₂ : ℕ} (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T Efar : ℝ} (hT : 0 < T) (hEfar : 0 ≤ Efar)
    (hfar : ∀ U : ℝ, T ≤ U →
      (∫ t in -U..-T,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)) +
        ∫ t in T..U,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t) ≤ Efar) :
    (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq
        (dyadicRestrictedShortAverage S f Y n H₁ -
          dyadicRestrictedShortAverage S f Y n H₂)) ≤
      2 * (∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
        Complex.normSq
          (perronKernelSegmentOn
              (dyadicVerticalDirichletPolynomial S f Y) x H₁ (-T) T -
            perronKernelSegmentOn
              (dyadicVerticalDirichletPolynomial S f Y) x H₂ (-T) T)) +
      8 * (lemma14UniversalPerronSegmentSafeWeightedCoefficient
              ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₁ +
            lemma14UniversalPerronSegmentSafeWeightedCoefficient
              ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₂) * Efar := by
  let F : ℝ → ℂ := dyadicVerticalDirichletPolynomial S f Y
  let P : ℝ := (X : ℝ) + 1
  let Q : ℝ := ((2 * X : ℕ) : ℝ) + 1
  let W : Set ℝ := Set.Ioc P Q
  let C₁ : ℝ := lemma14UniversalPerronSegmentSafeWeightedCoefficient P Q H₁
  let C₂ : ℝ := lemma14UniversalPerronSegmentSafeWeightedCoefficient P Q H₂
  let Ecentral : ℝ := ∫ x in P..Q, Complex.normSq
    (perronKernelSegmentOn F x H₁ (-T) T -
      perronKernelSegmentOn F x H₂ (-T) T)
  let U : ℕ → ℕ := fun k ↦ Nat.ceil T + k
  let A : ℕ → ℝ → ℂ := fun k x ↦
    perronKernelSegmentOn F x H₁ (-(U k : ℝ)) (U k : ℝ) -
      perronKernelSegmentOn F x H₂ (-(U k : ℝ)) (U k : ℝ)
  let B : ℝ → ℂ := dyadicTwoLengthStepAverage S f Y X H₁ H₂
  have hFcont : Continuous F := continuous_dyadicVerticalDirichletPolynomial S f Y
  have hP : 0 < P := by dsimp only [P]; positivity
  have hPQ : P ≤ Q := by
    dsimp only [P, Q]
    have hXR : (X : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by
      exact_mod_cast (show X ≤ 2 * X by omega)
    linarith
  have hQ3P : Q ≤ 3 * P := by
    dsimp only [P, Q]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    nlinarith
  have hH₁R : (0 : ℝ) < H₁ := by exact_mod_cast hH₁
  have hH₂R : (0 : ℝ) < H₂ := by exact_mod_cast hH₂
  have hC₁ : 0 ≤ C₁ :=
    lemma14UniversalPerronSegmentSafeWeightedCoefficient_nonneg
      hP hPQ hH₁R
  have hC₂ : 0 ≤ C₂ :=
    lemma14UniversalPerronSegmentSafeWeightedCoefficient_nonneg
      hP hPQ hH₂R
  have hEcentral : 0 ≤ Ecentral := by
    dsimp only [Ecentral]
    apply intervalIntegral.integral_nonneg hPQ
    intro x hx
    exact Complex.normSq_nonneg _
  have hAint (k : ℕ) : IntegrableOn
      (fun x ↦ Complex.normSq (A k x)) W := by
    have h₁ : ContinuousOn
        (fun x ↦ perronKernelSegmentOn F x H₁
          (-(U k : ℝ)) (U k : ℝ)) (Set.Icc P Q) :=
      (continuousOn_perronKernelSegmentOn F hFcont hP hH₁R
        (-(U k : ℝ)) (U k : ℝ)).mono Set.Icc_subset_Ici_self
    have h₂ : ContinuousOn
        (fun x ↦ perronKernelSegmentOn F x H₂
          (-(U k : ℝ)) (U k : ℝ)) (Set.Icc P Q) :=
      (continuousOn_perronKernelSegmentOn F hFcont hP hH₂R
        (-(U k : ℝ)) (U k : ℝ)).mono Set.Icc_subset_Ici_self
    exact (Complex.continuous_normSq.comp_continuousOn (h₁.sub h₂))
      |>.integrableOn_Icc |>.mono_set Set.Ioc_subset_Icc_self
  have hBint : IntegrableOn (fun x ↦ Complex.normSq (B x)) W :=
    (integrable_normSq_dyadicTwoLengthStepAverage
      S f Y X H₁ H₂).integrableOn
  have hlim : ∀ᵐ x ∂volume.restrict W,
      Filter.Tendsto (fun k ↦ A k x) Filter.atTop (nhds (B x)) := by
    filter_upwards [ae_exists_open_unitCell_on_realEndpoint_window X]
      with x hxcell
    rcases hxcell with ⟨n, hn, hx⟩
    have h₁ := tendsto_perronKernelSegmentOn_dyadic_on_cell
      S f Y hx hH₁
    have h₂ := tendsto_perronKernelSegmentOn_dyadic_on_cell
      S f Y hx hH₂
    have hshift : Filter.Tendsto (fun k : ℕ ↦ k + Nat.ceil T)
        Filter.atTop Filter.atTop := Filter.tendsto_add_atTop_nat (Nat.ceil T)
    have hshiftR : Filter.Tendsto
        (fun k : ℕ ↦ ((k + Nat.ceil T : ℕ) : ℝ))
        Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp hshift
    have h₁shift : Filter.Tendsto
        (fun k : ℕ ↦ perronKernelSegmentOn F x H₁
          (-((k + Nat.ceil T : ℕ) : ℝ)) ((k + Nat.ceil T : ℕ) : ℝ))
        Filter.atTop (nhds (dyadicRestrictedShortAverage S f Y n H₁)) := by
      refine Filter.Tendsto.congr' ?_ (h₁.comp hshiftR)
      filter_upwards [] with k
      rfl
    have h₂shift : Filter.Tendsto
        (fun k : ℕ ↦ perronKernelSegmentOn F x H₂
          (-((k + Nat.ceil T : ℕ) : ℝ)) ((k + Nat.ceil T : ℕ) : ℝ))
        Filter.atTop (nhds (dyadicRestrictedShortAverage S f Y n H₂)) := by
      refine Filter.Tendsto.congr' ?_ (h₂.comp hshiftR)
      filter_upwards [] with k
      rfl
    have hsub := h₁shift.sub h₂shift
    dsimp only [B]
    rw [dyadicTwoLengthStepAverage_eq_on_unitCell
      S f Y hn ⟨hx.1.le, hx.2⟩]
    refine Filter.Tendsto.congr' ?_ hsub
    filter_upwards [] with k
    simp only [A, U, Nat.add_comm, Function.comp_apply]
  have hbound (k : ℕ) :
      (∫ x in W, Complex.normSq (A k x)) ≤
        2 * Ecentral + 8 * (C₁ + C₂) * Efar := by
    rw [← intervalIntegral.integral_of_le hPQ]
    have hTU : T ≤ (U k : ℝ) := by
      calc
        T ≤ (Nat.ceil T : ℝ) := Nat.le_ceil T
        _ ≤ (U k : ℝ) := by
          dsimp only [U]
          exact_mod_cast Nat.le_add_right (Nat.ceil T) k
    let L : ℝ → ℂ := fun x ↦
      perronKernelSegmentOn F x H₁ (-T) T -
        perronKernelSegmentOn F x H₂ (-T) T
    let R₁ : ℝ → ℂ := fun x ↦
      lemma14SymmetricPerronHighSegmentOn F x H₁ T (U k)
    let R₂ : ℝ → ℂ := fun x ↦
      lemma14SymmetricPerronHighSegmentOn F x H₂ T (U k)
    let R : ℝ → ℂ := fun x ↦ R₁ x - R₂ x
    have hLcont : ContinuousOn L (Set.uIcc P Q) := by
      apply ContinuousOn.sub
      · exact (continuousOn_perronKernelSegmentOn F hFcont hP hH₁R (-T) T).mono
          (by rw [Set.uIcc_of_le hPQ]; exact Set.Icc_subset_Ici_self)
      · exact (continuousOn_perronKernelSegmentOn F hFcont hP hH₂R (-T) T).mono
          (by rw [Set.uIcc_of_le hPQ]; exact Set.Icc_subset_Ici_self)
    have hR₁cont : ContinuousOn R₁ (Set.uIcc P Q) := by
      apply ContinuousOn.add
      · exact (continuousOn_perronKernelSegmentOn F hFcont hP hH₁R
          (-(U k : ℝ)) (-T)).mono
          (by rw [Set.uIcc_of_le hPQ]; exact Set.Icc_subset_Ici_self)
      · exact (continuousOn_perronKernelSegmentOn F hFcont hP hH₁R
          T (U k : ℝ)).mono
          (by rw [Set.uIcc_of_le hPQ]; exact Set.Icc_subset_Ici_self)
    have hR₂cont : ContinuousOn R₂ (Set.uIcc P Q) := by
      apply ContinuousOn.add
      · exact (continuousOn_perronKernelSegmentOn F hFcont hP hH₂R
          (-(U k : ℝ)) (-T)).mono
          (by rw [Set.uIcc_of_le hPQ]; exact Set.Icc_subset_Ici_self)
      · exact (continuousOn_perronKernelSegmentOn F hFcont hP hH₂R
          T (U k : ℝ)).mono
          (by rw [Set.uIcc_of_le hPQ]; exact Set.Icc_subset_Ici_self)
    have hRcont : ContinuousOn R (Set.uIcc P Q) := hR₁cont.sub hR₂cont
    have hcombine := intervalIntegral_normSq_add_le_two_add
      L R hPQ hLcont hRcont
    have hRcombine0 := intervalIntegral_normSq_add_le_two_add
      R₁ (fun x ↦ -R₂ x) hPQ hR₁cont hR₂cont.neg
    have hRcombine : (∫ x in P..Q, Complex.normSq (R x)) ≤
        2 * ((∫ x in P..Q, Complex.normSq (R₁ x)) +
          ∫ x in P..Q, Complex.normSq (R₂ x)) := by
      simpa only [R, sub_eq_add_neg, Complex.normSq_neg] using hRcombine0
    have hhigh₁ :=
      integral_normSq_lemma14SymmetricPerronHighSegmentOn_le_safeWeighted_universal
        F hFcont hP hPQ hQ3P hH₁R hT hTU
    have hhigh₂ :=
      integral_normSq_lemma14SymmetricPerronHighSegmentOn_le_safeWeighted_universal
        F hFcont hP hPQ hQ3P hH₂R hT hTU
    have hsplit (x : ℝ) (hx : x ∈ Set.Icc P Q) : A k x = L x + R x := by
      dsimp only [A, L, R, R₁, R₂]
      rw [perronKernelSegmentOn_eq_central_add_symmetricHigh
          F hFcont (T := T) (U := (U k : ℝ))
          (hP.trans_le hx.1) hH₁R,
        perronKernelSegmentOn_eq_central_add_symmetricHigh
          F hFcont (T := T) (U := (U k : ℝ))
          (hP.trans_le hx.1) hH₂R]
      ring
    have hfull : (∫ x in P..Q, Complex.normSq (A k x)) ≤
        2 * (Ecentral + ∫ x in P..Q, Complex.normSq (R x)) := by
      calc
        (∫ x in P..Q, Complex.normSq (A k x)) =
            ∫ x in P..Q, Complex.normSq (L x + R x) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [Set.uIcc_of_le hPQ] at hx
          change Complex.normSq (A k x) = Complex.normSq (L x + R x)
          rw [hsplit x hx]
        _ ≤ 2 * ((∫ x in P..Q, Complex.normSq (L x)) +
            ∫ x in P..Q, Complex.normSq (R x)) := hcombine
        _ = 2 * (Ecentral + ∫ x in P..Q, Complex.normSq (R x)) := by rfl
    have hRbound : (∫ x in P..Q, Complex.normSq (R x)) ≤
        4 * (C₁ + C₂) * Efar := by
      calc
        (∫ x in P..Q, Complex.normSq (R x)) ≤
            2 * ((∫ x in P..Q, Complex.normSq (R₁ x)) +
              ∫ x in P..Q, Complex.normSq (R₂ x)) := hRcombine
        _ ≤ 2 * (2 * C₁ * Efar + 2 * C₂ * Efar) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply add_le_add
          · exact hhigh₁.trans (mul_le_mul_of_nonneg_left
              (hfar (U k) hTU) (mul_nonneg (by norm_num) hC₁))
          · exact hhigh₂.trans (mul_le_mul_of_nonneg_left
              (hfar (U k) hTU) (mul_nonneg (by norm_num) hC₂))
        _ = 4 * (C₁ + C₂) * Efar := by ring
    calc
      (∫ x in P..Q, Complex.normSq (A k x)) ≤
          2 * (Ecentral + ∫ x in P..Q, Complex.normSq (R x)) := hfull
      _ ≤ 2 * (Ecentral + 4 * (C₁ + C₂) * Efar) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (le_refl Ecentral) hRbound) (by norm_num)
      _ = 2 * Ecentral + 8 * (C₁ + C₂) * Efar := by ring
  have hfatou := integral_normSq_le_of_ae_tendsto_of_uniform
    hAint hBint hlim
    (add_nonneg (mul_nonneg (by norm_num) hEcentral)
      (mul_nonneg
        (mul_nonneg (by norm_num) (add_nonneg hC₁ hC₂)) hEfar)) hbound
  rw [integral_normSq_dyadicTwoLengthStepAverage_window_eq
    S f Y X H₁ H₂] at hfatou
  exact hfatou

/-- One-bounded two-length specialization with an outer-height-independent
far tail. -/
theorem dyadicTwoLengthShortMeanSquare_le_central_add_invHigh_continuous
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (Y : ℕ)
    {X H₁ H₂ : ℕ} (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T : ℝ} (hT : 0 < T) :
    (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq
        (dyadicRestrictedShortAverage S f Y n H₁ -
          dyadicRestrictedShortAverage S f Y n H₂)) ≤
      2 * (∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
        Complex.normSq
          (perronKernelSegmentOn
              (dyadicVerticalDirichletPolynomial S f Y) x H₁ (-T) T -
            perronKernelSegmentOn
              (dyadicVerticalDirichletPolynomial S f Y) x H₂ (-T) T)) +
      16 * (lemma14UniversalPerronSegmentSafeWeightedCoefficient
              ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₁ +
            lemma14UniversalPerronSegmentSafeWeightedCoefficient
              ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₂) * T⁻¹ := by
  have hF := continuous_dyadicVerticalDirichletPolynomial S f Y
  have hFnorm := norm_dyadicVerticalDirichletPolynomial_le_one S hf Y
  have hfar (U : ℝ) (hTU : T ≤ U) :
      (∫ t in -U..-T,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)) +
        ∫ t in T..U,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t) ≤
      2 * T⁻¹ := by
    have hneg := intervalIntegral_safeReciprocalSqWeight_mul_normSq_neg_le_inv
      (dyadicVerticalDirichletPolynomial S f Y) hF hFnorm hT hTU
    have hpos := intervalIntegral_safeReciprocalSqWeight_mul_normSq_le_inv
      (dyadicVerticalDirichletPolynomial S f Y) hF hFnorm hT hTU
    linarith
  have hbase :=
    dyadicTwoLengthShortMeanSquare_le_central_add_weightedHigh_continuous
      S f Y (X := X) hH₁ hH₂ hT
        (mul_nonneg (by norm_num) (inv_nonneg.mpr hT.le)) hfar
  convert hbase using 1 <;> ring

end

end Erdos67b
