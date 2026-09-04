import ErdosProblems.Erdos1081.Erdos1081Core
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

namespace Erdos1081

open Filter Finset Set
open scoped Topology ComplexConjugate

noncomputable section

theorem cauchySeq_exp_mul_I_div_nat_add_one
    {theta : ℝ} (hz : Complex.exp (theta * Complex.I) ≠ 1) :
    CauchySeq (fun n : ℕ ↦
      ∑ i ∈ Finset.range n,
        (1 / ((i + 1 : ℕ) : ℝ)) •
          (Complex.exp (theta * Complex.I) : ℂ) ^ (i + 1)) := by
  let z : ℂ := Complex.exp (theta * Complex.I)
  let b : ℝ := 2 / ‖1 - z‖
  have hz' : z ≠ 1 := by simpa [z] using hz
  have hden : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz'.symm)
  have hbound : ∀ n : ℕ,
      ‖∑ i ∈ Finset.range n, z ^ (i + 1)‖ ≤ b := by
    intro n
    have hgeom : (∑ i ∈ Finset.range n, z ^ (i + 1)) =
        z * ((1 - z ^ n) / (1 - z)) := by
      calc
        (∑ i ∈ Finset.range n, z ^ (i + 1)) =
            z * ∑ i ∈ Finset.range n, z ^ i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_succ]
          exact mul_comm _ _
        _ = z * ((1 - z ^ n) / (1 - z)) := by
          congr 1
          rw [geom_sum_eq hz']
          field_simp [hz']
          ring
    rw [hgeom, norm_mul, norm_div]
    have hzNorm : ‖z‖ = 1 := by simp [z]
    rw [hzNorm, one_mul]
    calc
      ‖1 - z ^ n‖ / ‖1 - z‖ ≤ 2 / ‖1 - z‖ := by
        gcongr
        calc
          ‖1 - z ^ n‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ n‖ := norm_sub_le _ _
          _ = 2 := by norm_num [hzNorm]
      _ = b := rfl
  have hanti : Antitone (fun i : ℕ ↦ 1 / ((i + 1 : ℕ) : ℝ)) := by
    intro i j hij
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have htend : Tendsto (fun i : ℕ ↦ 1 / ((i + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded htend hbound

theorem one_sub_exp_mul_I_factor {theta : ℝ} :
    (1 : ℂ) - Complex.exp (theta * Complex.I) =
      (2 * Real.sin (theta / 2) : ℝ) *
        Complex.exp ((↑(theta / 2 - Real.pi / 2) : ℂ) * Complex.I) := by
  change (1 : ℂ) - Complex.exp ((theta : ℂ) * Complex.I) =
    (2 * Real.sin (theta / 2) : ℝ) *
      Complex.exp (((theta / 2 - Real.pi / 2 : ℝ) : ℂ) * Complex.I)
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos theta, ← Complex.ofReal_sin theta,
    ← Complex.ofReal_cos (theta / 2 - Real.pi / 2),
    ← Complex.ofReal_sin (theta / 2 - Real.pi / 2)]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, mul_one, sub_zero, add_zero]
    rw [Real.cos_sub_pi_div_two]
    rw [show theta = 2 * (theta / 2) by ring, Real.cos_two_mul]
    rw [← Real.sin_sq_add_cos_sq (theta / 2)]
    ring_nf
  · simp only [Complex.sub_im, Complex.one_im, zero_sub, Complex.add_im,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, zero_mul, add_zero]
    rw [Real.sin_sub_pi_div_two]
    rw [show theta = 2 * (theta / 2) by ring, Real.sin_two_mul]
    ring_nf

theorem one_sub_exp_mul_I_mem_slitPlane
    {theta : ℝ} (htheta0 : 0 < theta) (htheta2pi : theta < 2 * Real.pi) :
    (1 : ℂ) - Complex.exp (theta * Complex.I) ∈ Complex.slitPlane := by
  rw [one_sub_exp_mul_I_factor]
  rw [Complex.mem_slitPlane_iff]
  left
  change 0 < ((2 * Real.sin (theta / 2) : ℝ) *
    Complex.exp (((theta / 2 - Real.pi / 2 : ℝ) : ℂ) * Complex.I)).re
  rw [Complex.re_ofReal_mul, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos (theta / 2 - Real.pi / 2),
    ← Complex.ofReal_sin (theta / 2 - Real.pi / 2)]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero]
  have hsin : 0 < Real.sin (theta / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcos : 0 < Real.cos (theta / 2 - Real.pi / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  exact mul_pos (mul_pos two_pos hsin) hcos

theorem log_one_sub_exp_mul_I
    {theta : ℝ} (htheta0 : 0 < theta) (htheta2pi : theta < 2 * Real.pi) :
    Complex.log ((1 : ℂ) - Complex.exp (theta * Complex.I)) =
      Real.log (2 * Real.sin (theta / 2)) +
        (↑(theta / 2 - Real.pi / 2) : ℂ) * Complex.I := by
  rw [one_sub_exp_mul_I_factor]
  have hsin : 0 < 2 * Real.sin (theta / 2) := by
    have := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith : theta / 2 < Real.pi)
    positivity
  rw [Complex.log_ofReal_mul hsin (Complex.exp_ne_zero _)]
  rw [Complex.log_exp]
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, sub_zero]
    linarith [Real.pi_pos]
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, sub_zero]
    linarith [Real.pi_pos]

theorem exists_tendsto_exp_mul_I_div_nat_add_one
    {theta : ℝ} (hz : Complex.exp (theta * Complex.I) ≠ 1) :
    ∃ l : ℂ, Tendsto (fun n : ℕ ↦
      ∑ i ∈ Finset.range n,
        (Complex.exp (theta * Complex.I) : ℂ) ^ (i + 1) / ((i + 1 : ℕ) : ℂ))
      atTop (nhds l) := by
  apply cauchySeq_tendsto_of_complete
  convert cauchySeq_exp_mul_I_div_nat_add_one hz using 1
  ext n
  apply Finset.sum_congr rfl
  intro i hi
  simp only [one_div, Complex.real_smul, div_eq_mul_inv]
  push_cast
  ring

theorem tsum_exp_mul_I_powerSeries_eq_neg_log_div
    {theta r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∑' n : ℕ, (Complex.exp (theta * Complex.I) : ℂ) ^ (n + 1) /
        ((n + 1 : ℕ) : ℂ) * (r : ℂ) ^ n) =
      -Complex.log (1 - (r : ℂ) * Complex.exp (theta * Complex.I)) / (r : ℂ) := by
  let z : ℂ := Complex.exp (theta * Complex.I)
  have hzNorm : ‖z‖ = 1 := by simp [z]
  have hrNorm : ‖(r : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hzNorm, mul_one]
    exact hr1
  have hs := (Complex.hasSum_taylorSeries_neg_log' hrNorm).mul_left ((r : ℂ)⁻¹)
  calc
    (∑' n : ℕ, (Complex.exp (theta * Complex.I) : ℂ) ^ (n + 1) /
        ((n + 1 : ℕ) : ℂ) * (r : ℂ) ^ n) =
        ∑' n : ℕ, (r : ℂ)⁻¹ * (((r : ℂ) * z) ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) := by
      apply tsum_congr
      intro n
      simp only [z, mul_pow]
      rw [pow_succ (r : ℂ)]
      field_simp [ne_of_gt hr0]
    _ = (r : ℂ)⁻¹ * -Complex.log (1 - (r : ℂ) * z) := by
      convert hs.tsum_eq using 1 <;> simp [Nat.cast_add]
    _ = -Complex.log (1 - (r : ℂ) * Complex.exp (theta * Complex.I)) / (r : ℂ) := by
      simp only [z, div_eq_mul_inv]
      ring

theorem tendsto_neg_log_one_sub_real_mul_exp_div
    {theta : ℝ} (htheta0 : 0 < theta) (htheta2pi : theta < 2 * Real.pi) :
    Tendsto
      (fun r : ℝ ↦ -Complex.log (1 - (r : ℂ) * Complex.exp (theta * Complex.I)) / (r : ℂ))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (-Complex.log (1 - Complex.exp (theta * Complex.I)))) := by
  have hcoe : Tendsto (fun r : ℝ ↦ (r : ℂ))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have harg : Tendsto
      (fun r : ℝ ↦ (1 : ℂ) - (r : ℂ) * Complex.exp (theta * Complex.I))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds ((1 : ℂ) - Complex.exp (theta * Complex.I))) := by
    convert tendsto_const_nhds.sub (hcoe.mul_const (Complex.exp (theta * Complex.I))) using 1 <;>
      ring_nf
  have hlog := harg.clog (one_sub_exp_mul_I_mem_slitPlane htheta0 htheta2pi)
  have hdiv := hlog.neg.div hcoe (by norm_num : (1 : ℂ) ≠ 0)
  convert hdiv using 1
  · ext r
    rfl
  · norm_num

theorem tendsto_partialSum_exp_mul_I_div
    {theta : ℝ} (htheta0 : 0 < theta) (htheta2pi : theta < 2 * Real.pi) :
    Tendsto (fun n : ℕ ↦
      ∑ i ∈ Finset.range n,
        (Complex.exp (theta * Complex.I) : ℂ) ^ (i + 1) / ((i + 1 : ℕ) : ℂ))
      atTop (nhds (-Complex.log (1 - Complex.exp (theta * Complex.I)))) := by
  have hz : Complex.exp (theta * Complex.I) ≠ 1 := by
    intro hz
    have hnorm : ‖(1 : ℂ) - Complex.exp (theta * Complex.I)‖ = 0 := by simp [hz]
    have hmem := one_sub_exp_mul_I_mem_slitPlane htheta0 htheta2pi
    exact (Complex.slitPlane_ne_zero hmem) (norm_eq_zero.mp hnorm)
  obtain ⟨l, hl⟩ := exists_tendsto_exp_mul_I_div_nat_add_one hz
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  rw [tendsto_map'_iff] at habel
  have heq : Filter.EventuallyEq (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (fun r : ℝ ↦ ∑' n : ℕ,
        (Complex.exp (theta * Complex.I) : ℂ) ^ (n + 1) / ((n + 1 : ℕ) : ℂ) *
          (r : ℂ) ^ n)
      (fun r : ℝ ↦
        -Complex.log (1 - (r : ℂ) * Complex.exp (theta * Complex.I)) / (r : ℂ)) := by
    filter_upwards [(eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hr0 hr1
    exact tsum_exp_mul_I_powerSeries_eq_neg_log_div hr0 hr1
  have htarget := tendsto_neg_log_one_sub_real_mul_exp_div htheta0 htheta2pi
  have habelTarget := htarget.congr' heq.symm
  have hlEq : l = -Complex.log (1 - Complex.exp (theta * Complex.I)) :=
    tendsto_nhds_unique habel habelTarget
  simpa [hlEq] using hl

theorem sum_Ico_sub_succ (f : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, (f i - f (i + 1)) = f m - f n := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rw [Finset.sum_Ico_succ_top hmn, ih]
      ring

theorem norm_sum_Ico_antitone_smul_le
    {f : ℕ → ℝ} {z : ℕ → ℂ} {b : ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hfanti : Antitone f)
    (hzbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ b)
    {m n : ℕ} (hmn : m < n) :
    ‖∑ i ∈ Finset.Ico m n, f i • z i‖ ≤ 2 * b * f m := by
  let G : ℕ → ℂ := fun k ↦ ∑ i ∈ Finset.range k, z i
  have hb0 : 0 ≤ b := by
    have := hzbound 0
    simpa using this
  have hmn' : m ≤ n - 1 := Nat.le_sub_one_of_lt hmn
  rw [Finset.sum_Ico_by_parts f z hmn]
  calc
    ‖f (n - 1) • G n - f m • G m -
        ∑ i ∈ Finset.Ico m (n - 1), (f (i + 1) - f i) • G (i + 1)‖ ≤
        ‖f (n - 1) • G n‖ + ‖f m • G m‖ +
          ‖∑ i ∈ Finset.Ico m (n - 1), (f (i + 1) - f i) • G (i + 1)‖ := by
      calc
        _ ≤ ‖f (n - 1) • G n - f m • G m‖ +
            ‖∑ i ∈ Finset.Ico m (n - 1), (f (i + 1) - f i) • G (i + 1)‖ :=
          norm_sub_le _ _
        _ ≤ (‖f (n - 1) • G n‖ + ‖f m • G m‖) +
            ‖∑ i ∈ Finset.Ico m (n - 1), (f (i + 1) - f i) • G (i + 1)‖ := by
          gcongr
          exact norm_sub_le _ _
        _ = _ := by ring
    _ ≤ f (n - 1) * b + f m * b +
        ∑ i ∈ Finset.Ico m (n - 1), (f i - f (i + 1)) * b := by
      gcongr
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
        exact mul_le_mul_of_nonneg_left (hzbound n) (hf0 _)
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
        exact mul_le_mul_of_nonneg_left (hzbound m) (hf0 _)
      · calc
          ‖∑ i ∈ Finset.Ico m (n - 1), (f (i + 1) - f i) • G (i + 1)‖ ≤
              ∑ i ∈ Finset.Ico m (n - 1), ‖(f (i + 1) - f i) • G (i + 1)‖ :=
            norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.Ico m (n - 1), (f i - f (i + 1)) * b := by
            gcongr with i hi
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_nonpos (sub_nonpos.mpr (hfanti (Nat.le_succ i))), neg_sub]
            exact mul_le_mul_of_nonneg_left (hzbound (i + 1))
              (sub_nonneg.mpr (hfanti (Nat.le_succ i)))
    _ = 2 * b * f m := by
      rw [← Finset.sum_mul]
      rw [sum_Ico_sub_succ f hmn']
      ring

theorem norm_sub_partialSum_le_of_tendsto_antitone
    {f : ℕ → ℝ} {z : ℕ → ℂ} {b : ℝ} {L : ℂ}
    (hf0 : ∀ i, 0 ≤ f i) (hfanti : Antitone f)
    (hzbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ b)
    (hsum : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, f i • z i) atTop (nhds L))
    (m : ℕ) :
    ‖L - ∑ i ∈ Finset.range m, f i • z i‖ ≤ 2 * b * f m := by
  rw [norm_sub_rev]
  apply le_of_tendsto (tendsto_const_nhds.sub hsum).norm
  filter_upwards [eventually_gt_atTop m] with n hmn
  rw [norm_sub_rev]
  rw [← Finset.sum_Ico_eq_sub _ hmn.le]
  exact norm_sum_Ico_antitone_smul_le hf0 hfanti hzbound hmn

noncomputable def dirichletWeight (s : ℝ) (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ) ^ s)⁻¹

theorem dirichletWeight_nonneg (s : ℝ) (n : ℕ) :
    0 ≤ dirichletWeight s n :=
  inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)

theorem dirichletWeight_antitone {s : ℝ} (hs : 0 ≤ s) :
    Antitone (dirichletWeight s) := by
  intro i j hij
  unfold dirichletWeight
  apply (inv_le_inv₀ (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_pos_of_pos (by positivity) _)).2
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1) hs

theorem dirichletWeight_le_one_div {s : ℝ} (hs : 1 ≤ s) (n : ℕ) :
    dirichletWeight s n ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
  rw [dirichletWeight, one_div]
  apply (inv_le_inv₀ (Real.rpow_pos_of_pos (by positivity) _)
    (by positivity : 0 < (((n + 1 : ℕ) : ℝ)))).2
  simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ (((n + 1 : ℕ) : ℝ)) by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) hs)

theorem dirichletWeight_smul_exp_eq
    (theta s : ℝ) (n : ℕ) :
    dirichletWeight s n • (Complex.exp (theta * Complex.I) : ℂ) ^ (n + 1) =
      (Complex.exp (theta * Complex.I) : ℂ) ^ (n + 1) /
        ((n + 1 : ℕ) : ℂ) ^ (s : ℂ) := by
  simp only [dirichletWeight, Complex.real_smul, div_eq_mul_inv]
  rw [Complex.ofReal_inv,
    Complex.ofReal_cpow (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ)))]
  norm_cast
  ring

theorem tendsto_partial_dirichletWeight_exp_eq_expZeta
    (x s : ℝ) (hs : 1 < s) :
    Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n,
        dirichletWeight s i •
          (Complex.exp ((2 * Real.pi * x) * Complex.I) : ℂ) ^ (i + 1))
      atTop (nhds (HurwitzZeta.expZeta x (s : ℂ))) := by
  have hsRe : 1 < ((s : ℂ)).re := by simpa
  have hfull := HurwitzZeta.hasSum_expZeta_of_one_lt_re x hsRe
  have hshift := (hasSum_nat_add_iff' (f := fun n : ℕ ↦
    Complex.exp (2 * Real.pi * Complex.I * x * n) / (n : ℂ) ^ (s : ℂ)) 1).mpr hfull
  have hshift0 : HasSum (fun n : ℕ ↦
      Complex.exp (2 * Real.pi * Complex.I * x * (n + 1)) /
        ((n + 1 : ℕ) : ℂ) ^ (s : ℂ))
      (HurwitzZeta.expZeta x (s : ℂ)) := by
    have hs0 : (s : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hs))
    simpa [hs0] using hshift
  have hshift' : HasSum (fun n : ℕ ↦
      dirichletWeight s n •
        (Complex.exp ((2 * Real.pi * x) * Complex.I) : ℂ) ^ (n + 1))
      (HurwitzZeta.expZeta x (s : ℂ)) := by
    exact hshift0.congr_fun (fun n ↦ by
      rw [show (2 : ℂ) * Real.pi * x * Complex.I =
          (↑(2 * Real.pi * x) : ℂ) * Complex.I by push_cast; ring]
      rw [dirichletWeight_smul_exp_eq]
      congr 2
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring)
  exact hshift'.tendsto_sum_nat

theorem norm_sum_range_exp_pow_le
    {theta : ℝ} (hz : Complex.exp (theta * Complex.I) ≠ 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n,
        (Complex.exp (theta * Complex.I) : ℂ) ^ (i + 1)‖ ≤
      2 / ‖1 - Complex.exp (theta * Complex.I)‖ := by
  let z : ℂ := Complex.exp (theta * Complex.I)
  have hz' : z ≠ 1 := by simpa [z] using hz
  have hgeom : (∑ i ∈ Finset.range n, z ^ (i + 1)) =
      z * ((1 - z ^ n) / (1 - z)) := by
    calc
      (∑ i ∈ Finset.range n, z ^ (i + 1)) =
          z * ∑ i ∈ Finset.range n, z ^ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [pow_succ]
        exact mul_comm _ _
      _ = z * ((1 - z ^ n) / (1 - z)) := by
        congr 1
        rw [geom_sum_eq hz']
        field_simp [hz']
        ring
  rw [hgeom, norm_mul, norm_div]
  have hzNorm : ‖z‖ = 1 := by simp [z]
  rw [hzNorm, one_mul]
  gcongr
  calc
    ‖1 - z ^ n‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ n‖ := norm_sub_le _ _
    _ = 2 := by norm_num [hzNorm]

theorem tendsto_partial_dirichletWeight_one_exp
    {theta : ℝ} (htheta0 : 0 < theta) (htheta2pi : theta < 2 * Real.pi) :
    Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n,
        dirichletWeight 1 i • (Complex.exp (theta * Complex.I) : ℂ) ^ (i + 1))
      atTop (nhds (-Complex.log (1 - Complex.exp (theta * Complex.I)))) := by
  convert tendsto_partialSum_exp_mul_I_div htheta0 htheta2pi using 1
  ext n
  apply Finset.sum_congr rfl
  intro i hi
  rw [dirichletWeight_smul_exp_eq]
  simp

theorem expZeta_apply_one_eq_neg_log
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HurwitzZeta.expZeta x 1 =
      -Complex.log (1 - Complex.exp ((2 * Real.pi * x) * Complex.I)) := by
  let theta : ℝ := 2 * Real.pi * x
  let z : ℂ := Complex.exp (theta * Complex.I)
  let b : ℝ := 2 / ‖1 - z‖
  let q : ℕ → ℝ := fun k ↦ 1 + 1 / ((k : ℝ) + 1)
  have htheta0 : 0 < theta := by dsimp [theta]; positivity
  have htheta2pi : theta < 2 * Real.pi := by
    dsimp [theta]
    nlinarith [Real.pi_pos]
  have hz : z ≠ 1 := by
    intro hz1
    have hmem := one_sub_exp_mul_I_mem_slitPlane htheta0 htheta2pi
    exact Complex.slitPlane_ne_zero hmem (by simp [z, hz1])
  have hb0 : 0 ≤ b := by
    dsimp [b]
    positivity
  have hzbound : ∀ n, ‖∑ i ∈ Finset.range n, z ^ (i + 1)‖ ≤ b := by
    intro n
    simpa [z, b] using norm_sum_range_exp_pow_le (theta := theta) (by simpa [z] using hz) n
  have hq : Tendsto q atTop (nhds 1) := by
    have hsmall : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [q] using tendsto_const_nhds.add hsmall
  have hqgt (k : ℕ) : 1 < q k := by
    dsimp [q]
    have hk : 0 < 1 / ((k : ℝ) + 1) := one_div_pos.mpr (by positivity)
    linarith
  have hbase : Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n,
      dirichletWeight 1 i • z ^ (i + 1)) atTop
      (nhds (-Complex.log (1 - z))) := by
    simpa [z] using tendsto_partial_dirichletWeight_one_exp htheta0 htheta2pi
  have hhead (m : ℕ) : Tendsto
      (fun k : ℕ ↦ ∑ i ∈ Finset.range m, dirichletWeight (q k) i • z ^ (i + 1))
      atTop (nhds (∑ i ∈ Finset.range m, dirichletWeight 1 i • z ^ (i + 1))) := by
    apply tendsto_finsetSum
    intro i hi
    have hpow : Tendsto (fun k : ℕ ↦ (((i + 1 : ℕ) : ℝ) ^ q k)) atTop
        (nhds ((((i + 1 : ℕ) : ℝ) ^ (1 : ℝ)))) :=
      (Real.continuousAt_const_rpow (by positivity : (((i + 1 : ℕ) : ℝ)) ≠ 0)).tendsto.comp hq
    have hinv : Tendsto (fun k : ℕ ↦ dirichletWeight (q k) i) atTop
        (nhds (dirichletWeight 1 i)) := by
      exact hpow.inv₀ (by positivity)
    exact hinv.smul_const (z ^ (i + 1))
  have hseq : Tendsto (fun k : ℕ ↦ HurwitzZeta.expZeta x (q k : ℂ)) atTop
      (nhds (-Complex.log (1 - z))) := by
    rw [Metric.tendsto_atTop]
    intro eps heps
    have honeDiv : Tendsto (fun m : ℕ ↦ 1 / ((m : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hsmall : Tendsto (fun m : ℕ ↦ 4 * b * (1 / ((m : ℝ) + 1))) atTop
        (nhds 0) := by
      convert tendsto_const_nhds.mul honeDiv using 1 <;> norm_num
    have hev := hsmall.eventually (eventually_lt_nhds (half_pos heps))
    rw [eventually_atTop] at hev
    obtain ⟨m, hm⟩ := hev
    have hh := Metric.tendsto_atTop.mp (hhead m) (eps / 2) (half_pos heps)
    obtain ⟨K, hK⟩ := hh
    refine ⟨K, fun k hk ↦ ?_⟩
    let Hk : ℂ := ∑ i ∈ Finset.range m, dirichletWeight (q k) i • z ^ (i + 1)
    let H1 : ℂ := ∑ i ∈ Finset.range m, dirichletWeight 1 i • z ^ (i + 1)
    have htailk := norm_sub_partialSum_le_of_tendsto_antitone
      (f := dirichletWeight (q k)) (z := fun i ↦ z ^ (i + 1)) (b := b)
      (dirichletWeight_nonneg _) (dirichletWeight_antitone (le_trans zero_le_one (hqgt k).le))
      hzbound (by simpa [theta, z] using
        tendsto_partial_dirichletWeight_exp_eq_expZeta x (q k) (hqgt k)) m
    have htailk' : ‖HurwitzZeta.expZeta x (q k : ℂ) - Hk‖ ≤
        2 * b * (1 / ((m : ℝ) + 1)) := by
      exact htailk.trans (mul_le_mul_of_nonneg_left
        (by simpa [Nat.cast_add, Nat.cast_one] using
          dirichletWeight_le_one_div (hqgt k).le m)
        (mul_nonneg (by positivity) hb0))
    have htail1 := norm_sub_partialSum_le_of_tendsto_antitone
      (f := dirichletWeight 1) (z := fun i ↦ z ^ (i + 1)) (b := b)
      (dirichletWeight_nonneg _) (dirichletWeight_antitone zero_le_one)
      hzbound hbase m
    have htail1' : ‖H1 - -Complex.log (1 - z)‖ ≤
        2 * b * (1 / ((m : ℝ) + 1)) := by
      rw [norm_sub_rev]
      exact htail1.trans (mul_le_mul_of_nonneg_left
        (by simpa [Nat.cast_add, Nat.cast_one] using
          dirichletWeight_le_one_div le_rfl m)
        (mul_nonneg (by positivity) hb0))
    have hheadk : ‖Hk - H1‖ < eps / 2 := by
      simpa only [dist_eq_norm, Hk, H1] using hK k hk
    rw [dist_eq_norm]
    calc
      ‖HurwitzZeta.expZeta x (q k : ℂ) - -Complex.log (1 - z)‖ =
          ‖(HurwitzZeta.expZeta x (q k : ℂ) - Hk) + (Hk - H1) +
            (H1 - -Complex.log (1 - z))‖ := by congr 1 <;> ring
      _ ≤ ‖HurwitzZeta.expZeta x (q k : ℂ) - Hk‖ + ‖Hk - H1‖ +
          ‖H1 - -Complex.log (1 - z)‖ := by
        calc
          _ ≤ ‖(HurwitzZeta.expZeta x (q k : ℂ) - Hk) + (Hk - H1)‖ +
              ‖H1 - -Complex.log (1 - z)‖ := norm_add_le _ _
          _ ≤ (‖HurwitzZeta.expZeta x (q k : ℂ) - Hk‖ + ‖Hk - H1‖) +
              ‖H1 - -Complex.log (1 - z)‖ := by
            gcongr
            exact norm_add_le _ _
      _ < eps := by
        have hm' := hm m le_rfl
        nlinarith
  have hxUnit : (x : UnitAddCircle) ≠ 0 := by
    intro hx
    have hxEq : x = 0 :=
      (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1 : ℝ)) ⟨hx0.le, hx1⟩).mp hx
    linarith
  have hcont : Tendsto (fun k : ℕ ↦ HurwitzZeta.expZeta x (q k : ℂ)) atTop
      (nhds (HurwitzZeta.expZeta x 1)) := by
    have hqComplex : Tendsto (fun k : ℕ ↦ (q k : ℂ)) atTop (nhds (1 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).comp hq
    exact (HurwitzZeta.differentiableAt_expZeta (x : UnitAddCircle) 1 (Or.inr hxUnit)).continuousAt.tendsto.comp
      hqComplex
  simpa [theta, z] using tendsto_nhds_unique hcont hseq

theorem sinZeta_apply_one
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HurwitzZeta.sinZeta x 1 = (Real.pi * (1 / 2 - x) : ℝ) := by
  let theta : ℝ := 2 * Real.pi * x
  let theta' : ℝ := 2 * Real.pi - theta
  have htheta0 : 0 < theta := by dsimp [theta]; positivity
  have htheta2pi : theta < 2 * Real.pi := by
    dsimp [theta]
    nlinarith [Real.pi_pos]
  have htheta'0 : 0 < theta' := by dsimp [theta']; linarith
  have htheta'2pi : theta' < 2 * Real.pi := by dsimp [theta']; linarith
  have hcircle : ((-x : ℝ) : UnitAddCircle) = ((1 - x : ℝ) : UnitAddCircle) := by
    rw [show (1 - x : ℝ) = -x + 1 by ring, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  have hcircle' : -(x : UnitAddCircle) = ((1 - x : ℝ) : UnitAddCircle) := by
    simpa only [AddCircle.coe_neg] using hcircle
  have hexp1 := expZeta_apply_one_eq_neg_log hx0 hx1
  have hexp2 := expZeta_apply_one_eq_neg_log (sub_pos.mpr hx1) (by linarith [hx0] : 1 - x < 1)
  have hlog1 := log_one_sub_exp_mul_I htheta0 htheta2pi
  have hlog2 := log_one_sub_exp_mul_I htheta'0 htheta'2pi
  have hthetaEq : 2 * Real.pi * (1 - x) = theta' := by simp [theta, theta']; ring
  have hthetaEqC1 : (2 : ℂ) * Real.pi * (x : ℂ) * Complex.I =
      (theta : ℂ) * Complex.I := by
    calc
      (2 : ℂ) * Real.pi * (x : ℂ) * Complex.I =
          ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
      _ = (theta : ℂ) * Complex.I := by rfl
  have hthetaEqC : (2 : ℂ) * Real.pi * ((1 - x : ℝ) : ℂ) * Complex.I =
      (theta' : ℂ) * Complex.I := by
    calc
      (2 : ℂ) * Real.pi * ((1 - x : ℝ) : ℂ) * Complex.I =
          ((2 * Real.pi * (1 - x) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      _ = (theta' : ℂ) * Complex.I := by rw [hthetaEq]
  have hsin : Real.sin (theta' / 2) = Real.sin (theta / 2) := by
    rw [show theta' / 2 = Real.pi - theta / 2 by simp [theta']; ring, Real.sin_pi_sub]
  rw [HurwitzZeta.sinZeta_eq]
  rw [hcircle']
  rw [hthetaEqC1] at hexp1
  rw [hexp1]
  rw [hthetaEqC] at hexp2
  rw [hexp2]
  rw [hlog1, hlog2]
  rw [hsin]
  push_cast
  field_simp [Complex.I_ne_zero]
  simp [theta, theta']
  ring

/-- The odd part of the Hurwitz zeta function at zero, for the standard
representative of a nonzero point of the circle. -/
theorem hurwitzZetaOdd_apply_zero
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HurwitzZeta.hurwitzZetaOdd x 0 = (1 / 2 - x : ℝ) := by
  have hs : ∀ n : ℕ, (1 : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have hre := congr_arg Complex.re h
    norm_num at hre
    have hn : 0 ≤ (n : ℝ) := by positivity
    linarith
  have h := HurwitzZeta.hurwitzZetaOdd_one_sub
    (x : UnitAddCircle) (s := (1 : ℂ)) hs
  rw [show (1 : ℂ) - 1 = 0 by ring] at h
  rw [sinZeta_apply_one hx0 hx1] at h
  simp only [Complex.cpow_neg_one, Complex.Gamma_one,
    Complex.sin_pi_div_two, mul_one] at h
  rw [h]
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The first generalized Bernoulli formula for an odd periodic function,
obtained here directly from the boundary value of the odd Hurwitz zeta
function. -/
theorem ZMod.LFunction_apply_zero_of_odd
    {N : ℕ} [NeZero N] {Φ : ZMod N → ℂ} (hΦ : Φ.Odd) :
    ZMod.LFunction Φ 0 =
      -(1 / (N : ℂ)) * ∑ j : ZMod N, (j.val : ℂ) * Φ j := by
  have hzeta : ∀ j : ZMod N,
      Φ j * HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle j) 0 =
        Φ j * ((1 / 2 : ℝ) - (j.val / N : ℝ) : ℝ) := by
    intro j
    by_cases hj : j = 0
    · subst j
      simp [hΦ.map_zero]
    · have hjval : 0 < j.val := Nat.pos_of_ne_zero (j.val_ne_zero.mpr hj)
      have hN : 0 < N := NeZero.pos N
      rw [ZMod.toAddCircle_apply]
      rw [hurwitzZetaOdd_apply_zero
          (div_pos (Nat.cast_pos.mpr hjval) (Nat.cast_pos.mpr hN))
          ((div_lt_one (Nat.cast_pos.mpr hN)).mpr (Nat.cast_lt.mpr j.val_lt))]
  rw [ZMod.LFunction_def_odd hΦ]
  simp only [neg_zero, Complex.cpow_zero, one_mul]
  rw [Finset.sum_congr rfl (fun j _ ↦ hzeta j)]
  have hsum : ∑ j : ZMod N, Φ j = 0 := hΦ.sum_eq_zero
  calc
    ∑ j : ZMod N, Φ j * (((1 / 2 : ℝ) - (j.val / N : ℝ) : ℝ) : ℂ) =
        (1 / 2 : ℂ) * ∑ j : ZMod N, Φ j -
          (1 / (N : ℂ)) * ∑ j : ZMod N, (j.val : ℂ) * Φ j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      field_simp [Nat.cast_ne_zero.mpr (NeZero.ne N)]
    _ = -(1 / (N : ℂ)) * ∑ j : ZMod N, (j.val : ℂ) * Φ j := by
      rw [hsum, mul_zero, zero_sub]
      ring

/-- The complex-valued quadratic character modulo an odd prime. -/
noncomputable def complexQuadraticChar (p : ℕ) [Fact p.Prime] :
    DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

@[simp]
theorem complexQuadraticChar_apply (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    complexQuadraticChar p a = (quadraticChar (ZMod p) a : ℂ) := rfl

theorem complexQuadraticChar_ne_one
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    complexQuadraticChar p ≠ 1 := by
  have hp2 : p ≠ 2 := by omega
  rw [complexQuadraticChar, MulChar.ringHomComp_ne_one_iff]
  · exact quadraticChar_ne_one ((ZMod.ringChar_zmod_n p).substr hp2)
  · exact Int.cast_injective

theorem complexQuadraticChar_odd
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    (complexQuadraticChar p : ZMod p → ℂ).Odd := by
  have hp2 : p ≠ 2 := by omega
  have hnegZ : quadraticChar (ZMod p) (-1) = -1 := by
    rw [quadraticChar_neg_one ((ZMod.ringChar_zmod_n p).substr hp2)]
    rw [ZMod.card]
    exact ZMod.χ₄_nat_three_mod_four hp4
  have hneg : complexQuadraticChar p (-1) = -1 := by
    simp only [complexQuadraticChar_apply, hnegZ, Int.cast_neg, Int.cast_one]
  intro a
  rw [show -a = (-1) * a by ring, map_mul, hneg, neg_one_mul]

theorem complexQuadraticChar_isPrimitive
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    DirichletCharacter.IsPrimitive (complexQuadraticChar p) := by
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Nat.dvd_prime Fact.out).mp
      (DirichletCharacter.conductor_dvd_level (complexQuadraticChar p)) with h | h
  · exfalso
    apply complexQuadraticChar_ne_one hp4
    exact (DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h
  · exact h

theorem complexQuadraticChar_isQuadratic
    (p : ℕ) [Fact p.Prime] :
    (complexQuadraticChar p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

theorem Gammaℝ_two : Complex.Gammaℝ (2 : ℂ) = (Real.pi : ℂ)⁻¹ := by
  rw [Complex.Gammaℝ_def]
  norm_num [Complex.cpow_neg_one, Complex.Gamma_one]

/-- The exact functional-equation relation between the values at zero and
one of the odd quadratic character. -/
theorem complexQuadraticChar_LFunction_one_mul_gaussSum
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    DirichletCharacter.LFunction (complexQuadraticChar p) 1 *
        gaussSum (complexQuadraticChar p) ZMod.stdAddChar =
      (Real.pi : ℂ) * Complex.I *
        DirichletCharacter.LFunction (complexQuadraticChar p) 0 := by
  let χ := complexQuadraticChar p
  let τ := gaussSum χ ZMod.stdAddChar
  have hodd : (χ : ZMod p → ℂ).Odd := complexQuadraticChar_odd hp4
  have hprim : DirichletCharacter.IsPrimitive χ :=
    complexQuadraticChar_isPrimitive hp4
  have hquad : χ.IsQuadratic := complexQuadraticChar_isQuadratic p
  have hdft : ZMod.dft χ = fun j ↦ (-τ) * χ j := by
    funext j
    rw [hprim.fourierTransform_eq_inv_mul_gaussSum]
    rw [hquad.inv]
    rw [hodd j]
    dsimp [τ]
    ring
  have hFE := ZMod.completedLFunction_one_sub_odd hodd (1 : ℂ)
  simp only [sub_self, Complex.cpow_zero, one_mul] at hFE
  rw [hdft, ZMod.completedLFunction_const_mul] at hFE
  have hL0 := ZMod.LFunction_eq_completed_div_gammaFactor_odd hodd (0 : ℂ)
  have hL1 := ZMod.LFunction_eq_completed_div_gammaFactor_odd hodd (1 : ℂ)
  simp only [zero_add, Complex.Gammaℝ_one, div_one] at hL0
  rw [one_add_one_eq_two, Gammaℝ_two] at hL1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  dsimp [DirichletCharacter.LFunction]
  dsimp [χ, τ] at hFE hL0 hL1 ⊢
  rw [hL0, hL1, hFE, div_inv_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

noncomputable def quadraticWeightedSum (p : ℕ) [Fact p.Prime] : ℤ :=
  ∑ j : ZMod p, (j.val : ℤ) * quadraticChar (ZMod p) j

theorem complexQuadraticChar_LFunction_zero_eq_weightedSum
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    DirichletCharacter.LFunction (complexQuadraticChar p) 0 =
      -(1 / (p : ℂ)) * (quadraticWeightedSum p : ℂ) := by
  have h := ZMod.LFunction_apply_zero_of_odd
    (complexQuadraticChar_odd hp4)
  change ZMod.LFunction (complexQuadraticChar p : ZMod p → ℂ) 0 =
    -(1 / (p : ℂ)) * (quadraticWeightedSum p : ℂ)
  rw [h]
  congr 1
  rw [quadraticWeightedSum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Int.cast_mul, Int.cast_natCast, complexQuadraticChar_apply]

theorem complexQuadraticChar_gaussSum_ne_zero
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    gaussSum (complexQuadraticChar p) ZMod.stdAddChar ≠ 0 := by
  apply gaussSum_ne_zero_of_nontrivial
  · rw [ZMod.card]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  · exact complexQuadraticChar_ne_one hp4
  · exact ZMod.isPrimitive_stdAddChar p

theorem quadraticWeightedSum_ne_zero
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    quadraticWeightedSum p ≠ 0 := by
  intro hsum
  have hL0 : DirichletCharacter.LFunction (complexQuadraticChar p) 0 = 0 := by
    rw [complexQuadraticChar_LFunction_zero_eq_weightedSum hp4, hsum]
    norm_num
  have hrel := complexQuadraticChar_LFunction_one_mul_gaussSum hp4
  rw [hL0, mul_zero] at hrel
  exact mul_ne_zero
    (DirichletCharacter.LFunction_apply_one_ne_zero
      (complexQuadraticChar_ne_one hp4))
    (complexQuadraticChar_gaussSum_ne_zero hp4) hrel

theorem norm_complexQuadraticChar_gaussSum
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ‖gaussSum (complexQuadraticChar p) ZMod.stdAddChar‖ =
      Real.sqrt p := by
  let τ := gaussSum (complexQuadraticChar p) ZMod.stdAddChar
  have hsq := gaussSum_sq (χ := complexQuadraticChar p)
    (ψ := ZMod.stdAddChar)
    (complexQuadraticChar_ne_one hp4)
    (complexQuadraticChar_isQuadratic p)
    (ZMod.isPrimitive_stdAddChar p)
  have hneg := complexQuadraticChar_odd hp4 (-1)
  have hneg' : complexQuadraticChar p (-1) = -1 := by
    have hneg0 : (1 : ℂ) = -complexQuadraticChar p (-1) := by
      simpa only [neg_neg, map_one] using hneg
    simpa using (congrArg Neg.neg hneg0).symm
  have hsq' : τ ^ 2 = -(p : ℂ) := by
    have hsq0 : τ ^ 2 = complexQuadraticChar p (-1) * (p : ℂ) := by
      simpa only [τ, complexQuadraticChar, ZMod.card] using hsq
    rw [hneg'] at hsq0
    simpa using hsq0
  have hnormsq : ‖τ‖ ^ 2 = (p : ℝ) := by
    rw [← norm_pow, hsq']
    simp
  have hpnonneg : (0 : ℝ) ≤ p := by positivity
  nlinarith [Real.sq_sqrt hpnonneg, norm_nonneg τ, Real.sqrt_nonneg (p : ℝ)]

/-- A completely uniform (deliberately weak) lower bound for the quadratic
Dirichlet L-value at one. -/
theorem complexQuadraticChar_LFunction_one_norm_lower
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    Real.pi / ((p : ℝ) * Real.sqrt p) ≤
      ‖DirichletCharacter.LFunction (complexQuadraticChar p) 1‖ := by
  let S := quadraticWeightedSum p
  have hS0 : S ≠ 0 := quadraticWeightedSum_ne_zero hp4
  have hSabs : (1 : ℤ) ≤ |S| := Int.one_le_abs hS0
  have hSabsR : (1 : ℝ) ≤ (|S| : ℝ) := by
    exact_mod_cast hSabs
  have hSnorm : (1 : ℝ) ≤ ‖(S : ℂ)‖ := by
    simpa only [Complex.norm_intCast, Int.cast_one] using
      hSabsR
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hL0eq := complexQuadraticChar_LFunction_zero_eq_weightedSum hp4
  have hL0norm :
      ‖DirichletCharacter.LFunction (complexQuadraticChar p) 0‖ =
        (p : ℝ)⁻¹ * ‖(S : ℂ)‖ := by
    rw [hL0eq]
    simp only [norm_mul, norm_neg, norm_inv, norm_natCast, norm_one, one_div,
      S]
  have hL0lower : (p : ℝ)⁻¹ ≤
      ‖DirichletCharacter.LFunction (complexQuadraticChar p) 0‖ := by
    rw [hL0norm]
    exact le_mul_of_one_le_right (inv_nonneg.mpr hpR.le) hSnorm
  have hrel := complexQuadraticChar_LFunction_one_mul_gaussSum hp4
  have hnormrel := congr_arg norm hrel
  simp only [norm_mul, norm_complexQuadraticChar_gaussSum hp4,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_I] at hnormrel
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.2 hpR
  rw [show Real.pi / ((p : ℝ) * Real.sqrt p) =
      (Real.pi * (p : ℝ)⁻¹) / Real.sqrt p by
    field_simp]
  apply (div_le_iff₀ hsqrt).2
  rw [hnormrel]
  calc
    Real.pi * (p : ℝ)⁻¹ ≤
        Real.pi * ‖DirichletCharacter.LFunction (complexQuadraticChar p) 0‖ :=
      mul_le_mul_of_nonneg_left hL0lower Real.pi_pos.le
    _ = Real.pi * 1 *
        ‖DirichletCharacter.LFunction (complexQuadraticChar p) 0‖ := by ring

end

end Erdos1081
