import ErdosProblems.Erdos67.MRLemma14Smoothing
import ErdosProblems.Erdos67.MRLemma14TwoLengthLow
import ErdosProblems.Erdos67.MRRamarePerronProjectionL2

/-!
# Source high-frequency smoothing for MR Lemma 14

This file records the two exact changes of variables in the source proof
and the logarithmic Plancherel estimate for the resulting fixed smoothing
parameter.  The important point is that the normalized increment is kept
intact until after the moving-endpoint average; no two large Perron
endpoints are estimated separately.
-/

open scoped BigOperators ComplexConjugate
open Finset MeasureTheory

namespace Erdos67

noncomputable section

open MRLemma14Smoothing

/-- The scale-free increment that remains after factoring `x^s` and making
the substitution `w=xu` in the smoothed Perron kernel. -/
def perronRatioIncrement (u t : ℝ) : ℂ :=
  ((((1 + u : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) - 1) /
    ((1 : ℂ) + (t : ℂ) * Complex.I)

/-- The scale-free increment is `u` times the normalized Perron kernel
based at one. -/
theorem perronRatioIncrement_eq_mul_kernel (u t : ℝ) :
    perronRatioIncrement u t = (u : ℂ) * perronIncrementKernel 1 u t := by
  unfold perronRatioIncrement perronIncrementKernel
  norm_num
  by_cases hu : u = 0
  · simp [hu]
  · field_simp [hu]

/-- On a positive relative interval the scale-free increment is at most
its relative length. -/
theorem norm_perronRatioIncrement_le_self {u : ℝ} (hu : 0 < u) (t : ℝ) :
    ‖perronRatioIncrement u t‖ ≤ u := by
  rw [perronRatioIncrement_eq_mul_kernel, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hu]
  calc
    u * ‖perronIncrementKernel 1 u t‖ ≤ u * 1 :=
      mul_le_mul_of_nonneg_left
        (norm_perronIncrementKernel_le_one (by norm_num) hu t) hu.le
    _ = u := mul_one u

/-- Away from zero the same increment has the reciprocal-frequency bound
used after the source smoothing step. -/
theorem norm_perronRatioIncrement_le_div_abs
    {u t : ℝ} (hu : 0 < u) (ht : t ≠ 0) :
    ‖perronRatioIncrement u t‖ ≤ (2 + u) / |t| := by
  rw [perronRatioIncrement_eq_mul_kernel, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hu]
  have hk := norm_perronIncrementKernel_le_div_abs
    (x := (1 : ℝ)) (h := u) (t := t) (by norm_num) hu ht
  calc
    u * ‖perronIncrementKernel 1 u t‖ ≤
        u * ((2 * 1 + u) / (u * |t|)) :=
      mul_le_mul_of_nonneg_left hk hu.le
    _ = (2 + u) / |t| := by
      field_simp [hu.ne', abs_ne_zero.mpr ht]

/-- The source `min{u,1/|t|}` multiplier bound, with its explicit harmless
`2+u` numerator. -/
theorem norm_perronRatioIncrement_le_min
    {u t : ℝ} (hu : 0 < u) (ht : t ≠ 0) :
    ‖perronRatioIncrement u t‖ ≤ min u ((2 + u) / |t|) := by
  exact le_min (norm_perronRatioIncrement_le_self hu t)
    (norm_perronRatioIncrement_le_div_abs hu ht)

/-- Continuity in the vertical parameter on every positive relative
interval. -/
theorem continuous_perronRatioIncrement_of_pos {u : ℝ} (hu : 0 < u) :
    Continuous (fun t : ℝ ↦ perronRatioIncrement u t) := by
  unfold perronRatioIncrement
  apply Continuous.div
  · have hexp : Continuous (fun t : ℝ ↦
        (((1 + u : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))) := by
      apply (by fun_prop : Continuous fun t : ℝ ↦
        ((1 : ℂ) + (t : ℂ) * Complex.I)).const_cpow
      exact Or.inl (Complex.ofReal_ne_zero.mpr (by linarith : 1 + u ≠ 0))
    exact hexp.sub continuous_const
  · fun_prop
  · intro t ht
    have hre := congrArg Complex.re ht
    norm_num at hre

/-- Low-side multiplier energy after smoothing. -/
theorem integral_normSq_mul_perronRatioIncrement_le_self
    (F : ℝ → ℂ) (hF : Continuous F) {u A B : ℝ}
    (hu : 0 < u) (hAB : A ≤ B) :
    (∫ t in A..B, Complex.normSq (F t * perronRatioIncrement u t)) ≤
      u ^ 2 * ∫ t in A..B, Complex.normSq (F t) := by
  have hr := continuous_perronRatioIncrement_of_pos hu
  have hleft : Continuous (fun t ↦
      Complex.normSq (F t * perronRatioIncrement u t)) := by fun_prop
  have hright : Continuous (fun t ↦ u ^ 2 * Complex.normSq (F t)) := by fun_prop
  calc
    _ ≤ ∫ t in A..B, u ^ 2 * Complex.normSq (F t) := by
      apply intervalIntegral.integral_mono_on hAB
        (hleft.intervalIntegrable A B) (hright.intervalIntegrable A B)
      intro t ht
      rw [Complex.normSq_mul]
      have hsquare : Complex.normSq (perronRatioIncrement u t) ≤ u ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
        exact (sq_le_sq₀ (norm_nonneg _) hu.le).2
          (norm_perronRatioIncrement_le_self hu t)
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left hsquare (Complex.normSq_nonneg (F t)))
    _ = _ := by rw [intervalIntegral.integral_const_mul]

/-- Reciprocal-frequency multiplier energy on an interval separated from
zero. -/
theorem integral_normSq_mul_perronRatioIncrement_le_div
    (F : ℝ → ℂ) (hF : Continuous F) {u A B T : ℝ}
    (hu : 0 < u) (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ t in A..B, Complex.normSq (F t * perronRatioIncrement u t)) ≤
      ((2 + u) / T) ^ 2 * ∫ t in A..B, Complex.normSq (F t) := by
  have hr := continuous_perronRatioIncrement_of_pos hu
  have hleft : Continuous (fun t ↦
      Complex.normSq (F t * perronRatioIncrement u t)) := by fun_prop
  have hright : Continuous (fun t ↦
      ((2 + u) / T) ^ 2 * Complex.normSq (F t)) := by fun_prop
  calc
    _ ≤ ∫ t in A..B,
        ((2 + u) / T) ^ 2 * Complex.normSq (F t) := by
      apply intervalIntegral.integral_mono_on hAB
        (hleft.intervalIntegrable A B) (hright.intervalIntegrable A B)
      intro t ht
      rw [Complex.normSq_mul]
      have htne : t ≠ 0 := by
        intro hzero
        subst t
        have hzeroAway := haway 0 ht
        norm_num at hzeroAway
        exact (not_le_of_gt hT) hzeroAway
      have hnum : 0 ≤ 2 + u := by linarith
      have hratio : (2 + u) / |t| ≤ (2 + u) / T :=
        div_le_div_of_nonneg_left hnum hT (haway t ht)
      have hnorm := (norm_perronRatioIncrement_le_div_abs hu htne).trans hratio
      have hsquare : Complex.normSq (perronRatioIncrement u t) ≤
          ((2 + u) / T) ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
        exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg hnum hT.le)).2 hnorm
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left hsquare (Complex.normSq_nonneg (F t)))
    _ = _ := by rw [intervalIntegral.integral_const_mul]

/-- First source change of variables, `w=xu`, after the moving-endpoint
average. -/
theorem integral_perronIncrement_changeVariables_left
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (t : ℝ) :
    (∫ w in h..3 * h,
        ((((x + w : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) -
            (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) /
          ((1 : ℂ) + (t : ℂ) * Complex.I))) =
      (x : ℂ) * ∫ u in h / x..3 * h / x,
        (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
          perronRatioIncrement u t := by
  let q : ℝ → ℂ := fun w ↦
    ((((x + w : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) -
        (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) /
      ((1 : ℂ) + (t : ℂ) * Complex.I))
  have hcv := intervalIntegral.smul_integral_comp_mul_left
    (f := q) (a := h / x) (b := 3 * h / x) x
  have hleft : x * (h / x) = h := by field_simp [hx.ne']
  have hright : x * (3 * h / x) = 3 * h := by field_simp [hx.ne']
  rw [hleft, hright] at hcv
  rw [← hcv]
  simp only [Complex.real_smul]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp [q]
  unfold perronRatioIncrement
  have hxu : ((x + x * u : ℝ) : ℂ) = (x : ℂ) * ((1 + u : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hxu, Complex.mul_cpow_ofReal_nonneg hx.le (by
    have hu' : h / x ≤ u := by
      have hbounds : h / x ≤ 3 * h / x := by
        have := div_pos hh hx
        rw [show 3 * h / x = 3 * (h / x) by ring]
        linarith
      rw [Set.uIcc_of_le hbounds] at hu
      exact hu.1
    have : 0 < 1 + u := by
      have : 0 < h / x := div_pos hh hx
      linarith
    exact_mod_cast this.le)]
  ring

/-- Second source change of variables, `w=h+(x+h)u`. -/
theorem integral_perronIncrement_changeVariables_right
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (t : ℝ) :
    (∫ w in h..3 * h,
        ((((x + w : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) -
            ((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) /
          ((1 : ℂ) + (t : ℂ) * Complex.I))) =
      ((x + h : ℝ) : ℂ) * ∫ u in 0..2 * h / (x + h),
        ((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
          perronRatioIncrement u t := by
  let q : ℝ → ℂ := fun w ↦
    ((((x + w : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) -
        ((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) /
      ((1 : ℂ) + (t : ℂ) * Complex.I))
  have hxh : 0 < x + h := by linarith
  have hcv := intervalIntegral.smul_integral_comp_mul_add
    (f := q) (a := 0) (b := 2 * h / (x + h)) (x + h) h
  have hright : (x + h) * (2 * h / (x + h)) + h = 3 * h := by
    field_simp [hxh.ne']
    norm_num
  rw [hright] at hcv
  simp only [mul_zero, zero_add] at hcv
  calc
    (∫ w in h..3 * h, q w) =
        (x + h) • ∫ u in 0..2 * h / (x + h), q ((x + h) * u + h) := hcv.symm
    _ = ((x + h : ℝ) : ℂ) * ∫ u in 0..2 * h / (x + h),
        ((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
          perronRatioIncrement u t := by
      simp only [Complex.real_smul]
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp [q]
      unfold perronRatioIncrement
      have hxu : ((x + ((x + h) * u + h) : ℝ) : ℂ) =
          ((x + h : ℝ) : ℂ) * ((1 + u : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hxu, Complex.mul_cpow_ofReal_nonneg hxh.le (by
        rw [Set.uIcc_of_le (by positivity)] at hu
        have : 0 ≤ u := hu.1
        exact_mod_cast (by linarith : (0 : ℝ) ≤ 1 + u))]
      ring

/-- The fixed-`u` logarithmic transform that occurs after smoothing and
factoring the `x^s` term. -/
def smoothedLogTransformOn
    (F : ℝ → ℂ) (u : ℝ) (x : ℕ) (A B : ℝ) : ℂ :=
  ∫ t in A..B, F t *
    (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
      perronRatioIncrement u t

/-- Discrete logarithmic Plancherel for a fixed source smoothing
parameter.  This is the exact finite counterpart of expanding the square,
integrating in `x`, and using decay of the Fourier transform of the smooth
cutoff. -/
theorem sum_normSq_smoothedLogTransformOn_le
    (F : ℝ → ℂ) (hF : Continuous F) {X : ℕ} (hX : 0 < X)
    {u A B : ℝ} (hu : 0 < u) (hAB : A ≤ B) :
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (smoothedLogTransformOn F u x A B)) ≤
      (2 * X : ℝ) ^ 2 *
        (B - A + 2 * Real.pi * (2 * X : ℕ)) *
          ∫ t in A..B,
            Complex.normSq (F t * perronRatioIncrement u t) := by
  classical
  let D : Finset ℕ := Finset.Ioc X (2 * X)
  let g : ℝ → ℂ := fun t ↦ F t * perronRatioIncrement u t
  let freq : ↑D → ℝ := fun x ↦ -Real.log x.1
  have hratio : Continuous (fun t : ℝ ↦ perronRatioIncrement u t) :=
    continuous_perronRatioIncrement_of_pos hu
  have hg : Continuous g := hF.mul hratio
  have hN : 0 < 2 * X := by omega
  have hpos : ∀ x : ↑D, 0 < x.1 := by
    intro x
    have hxmem := Finset.mem_Ioc.mp x.2
    omega
  have hle : ∀ x : ↑D, x.1 ≤ 2 * X := fun x ↦ (Finset.mem_Ioc.mp x.2).2
  have hsep : ∀ r s : ↑D, r ≠ s →
      ((2 * X : ℕ) : ℝ)⁻¹ ≤ |freq r - freq s| := by
    intro r s hrs
    have hbase := inv_nat_le_abs_log_sub_log
      (hpos r) (hpos s) (hle r) (hle s) (by
        intro h
        exact hrs (Subtype.ext h))
    dsimp [freq]
    simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using hbase
  have hplan := sum_normSq_finiteFrequencyAnalysisCoefficientOn_le
    freq g hg hAB (inv_pos.mpr (by exact_mod_cast hN)) hsep
  have hplan' :
      (∑ r, Complex.normSq
        (finiteFrequencyAnalysisCoefficientOn freq g A B r)) ≤
        (B - A + 2 * Real.pi * (2 * X : ℕ)) *
          ∫ t in A..B, Complex.normSq (g t) := by
    simpa only [inv_inv] using hplan
  have hpoint (x : ↑D) :
      smoothedLogTransformOn F u x.1 A B =
        (x.1 : ℂ) * finiteFrequencyAnalysisCoefficientOn freq g A B x := by
    unfold smoothedLogTransformOn finiteFrequencyAnalysisCoefficientOn
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have hpow := nat_cpow_one_add_mul_I_eq_phase (hpos x) t
    dsimp [g, freq]
    rw [hpow]
    have hphase : conj (realExponentialPhase (t * -Real.log x.1)) =
        realExponentialPhase (t * Real.log x.1) := by
      rw [show t * -Real.log x.1 = -(t * Real.log x.1) by ring,
        conj_realExponentialPhase]
      congr 1
      ring
    rw [hphase]
    ring
  have hcast (x : ↑D) : ((x.1 : ℝ) ^ 2) ≤ (2 * X : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 (by exact_mod_cast hle x)
  rw [← Finset.sum_attach]
  change (∑ x : ↑D,
      Complex.normSq (smoothedLogTransformOn F u x.1 A B)) ≤ _
  calc
    (∑ x : ↑D,
        Complex.normSq (smoothedLogTransformOn F u x.1 A B)) =
        ∑ x : ↑D,
          (x.1 : ℝ) ^ 2 *
            Complex.normSq (finiteFrequencyAnalysisCoefficientOn freq g A B x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hpoint, Complex.normSq_mul, Complex.normSq_natCast]
      ring
    _ ≤ ∑ x : ↑D,
        (2 * X : ℝ) ^ 2 *
          Complex.normSq (finiteFrequencyAnalysisCoefficientOn freq g A B x) := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_right (hcast x) (Complex.normSq_nonneg _)
    _ = (2 * X : ℝ) ^ 2 *
        ∑ x : ↑D,
          Complex.normSq (finiteFrequencyAnalysisCoefficientOn freq g A B x) := by
      rw [Finset.mul_sum]
    _ ≤ (2 * X : ℝ) ^ 2 *
        (B - A + 2 * Real.pi * (2 * X : ℕ)) *
          ∫ t in A..B, Complex.normSq (g t) := by
      have hfac : 0 ≤ (2 * X : ℝ) ^ 2 := sq_nonneg _
      exact (mul_le_mul_of_nonneg_left hplan' hfac).trans_eq (by ring)
    _ = _ := by rfl

/-- The fixed-`u` logarithmic Plancherel estimate on an arbitrary finite
set of positive endpoints bounded by `N`.  This form is what the moving
endpoint average needs: after the order of the finite sum and the
`u`-integral is exchanged, the active endpoints form a `u`-dependent
subset. -/
theorem sum_normSq_smoothedLogTransformOn_finset_le
    (F : ℝ → ℂ) (hF : Continuous F) (D : Finset ℕ) {N : ℕ} (hN : 0 < N)
    (hpos : ∀ x ∈ D, 0 < x) (hle : ∀ x ∈ D, x ≤ N)
    {u A B : ℝ} (hu : 0 < u) (hAB : A ≤ B) :
    (∑ x ∈ D, Complex.normSq (smoothedLogTransformOn F u x A B)) ≤
      (N : ℝ) ^ 2 *
        (B - A + 2 * Real.pi * N) *
          ∫ t in A..B,
            Complex.normSq (F t * perronRatioIncrement u t) := by
  classical
  let freq : ↑D → ℝ := fun x ↦ -Real.log x.1
  let g : ℝ → ℂ := fun t ↦ F t * perronRatioIncrement u t
  have hratio : Continuous (fun t : ℝ ↦ perronRatioIncrement u t) :=
    continuous_perronRatioIncrement_of_pos hu
  have hg : Continuous g := hF.mul hratio
  have hpos' : ∀ x : ↑D, 0 < x.1 := fun x ↦ hpos x.1 x.2
  have hle' : ∀ x : ↑D, x.1 ≤ N := fun x ↦ hle x.1 x.2
  have hsep : ∀ r s : ↑D, r ≠ s →
      ((N : ℕ) : ℝ)⁻¹ ≤ |freq r - freq s| := by
    intro r s hrs
    have hbase := inv_nat_le_abs_log_sub_log
      (hpos' r) (hpos' s) (hle' r) (hle' s) (by
        intro h
        exact hrs (Subtype.ext h))
    dsimp [freq]
    simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using hbase
  have hplan := sum_normSq_finiteFrequencyAnalysisCoefficientOn_le
    freq g hg hAB (inv_pos.mpr (by exact_mod_cast hN)) hsep
  have hplan' :
      (∑ r, Complex.normSq
        (finiteFrequencyAnalysisCoefficientOn freq g A B r)) ≤
        (B - A + 2 * Real.pi * N) *
          ∫ t in A..B, Complex.normSq (g t) := by
    simpa only [inv_inv] using hplan
  have hpoint (x : ↑D) :
      smoothedLogTransformOn F u x.1 A B =
        (x.1 : ℂ) * finiteFrequencyAnalysisCoefficientOn freq g A B x := by
    unfold smoothedLogTransformOn finiteFrequencyAnalysisCoefficientOn
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have hpow := nat_cpow_one_add_mul_I_eq_phase (hpos' x) t
    dsimp [g, freq]
    rw [hpow]
    have hphase : conj (realExponentialPhase (t * -Real.log x.1)) =
        realExponentialPhase (t * Real.log x.1) := by
      rw [show t * -Real.log x.1 = -(t * Real.log x.1) by ring,
        conj_realExponentialPhase]
      congr 1
      ring
    rw [hphase]
    ring
  have hcast (x : ↑D) : ((x.1 : ℝ) ^ 2) ≤ (N : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 (by exact_mod_cast hle' x)
  rw [← Finset.sum_attach]
  change (∑ x : ↑D,
      Complex.normSq (smoothedLogTransformOn F u x.1 A B)) ≤ _
  calc
    (∑ x : ↑D,
        Complex.normSq (smoothedLogTransformOn F u x.1 A B)) =
        ∑ x : ↑D,
          (x.1 : ℝ) ^ 2 *
            Complex.normSq (finiteFrequencyAnalysisCoefficientOn freq g A B x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hpoint, Complex.normSq_mul, Complex.normSq_natCast]
      ring
    _ ≤ ∑ x : ↑D,
        (N : ℝ) ^ 2 *
          Complex.normSq (finiteFrequencyAnalysisCoefficientOn freq g A B x) := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_right (hcast x) (Complex.normSq_nonneg _)
    _ = (N : ℝ) ^ 2 *
        ∑ x : ↑D,
          Complex.normSq (finiteFrequencyAnalysisCoefficientOn freq g A B x) := by
      rw [Finset.mul_sum]
    _ ≤ (N : ℝ) ^ 2 *
        (B - A + 2 * Real.pi * N) *
          ∫ t in A..B, Complex.normSq (g t) := by
      have hfac : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
      exact (mul_le_mul_of_nonneg_left hplan' hfac).trans_eq (by ring)
    _ = _ := by rfl

/-- A subset form of fixed-`u` logarithmic Plancherel. -/
theorem sum_normSq_smoothedLogTransformOn_subset_le
    (F : ℝ → ℂ) (hF : Continuous F) {X : ℕ} (hX : 0 < X)
    (D : Finset ℕ) (hD : D ⊆ Finset.Ioc X (2 * X))
    {u A B : ℝ} (hu : 0 < u) (hAB : A ≤ B) :
    (∑ x ∈ D, Complex.normSq (smoothedLogTransformOn F u x A B)) ≤
      (2 * X : ℝ) ^ 2 *
        (B - A + 2 * Real.pi * (2 * X : ℕ)) *
          ∫ t in A..B,
            Complex.normSq (F t * perronRatioIncrement u t) := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    sum_normSq_smoothedLogTransformOn_finset_le F hF D (N := 2 * X)
      (by omega)
      (fun x hx ↦ by
        have hx' := (Finset.mem_Ioc.mp (hD hx)).1
        omega)
      (fun x hx ↦ (Finset.mem_Ioc.mp (hD hx)).2) hu hAB

/-- A globally continuous extension in the smoothing parameter, obtained
by replacing a negative parameter by zero.  All source intervals use
nonnegative parameters, so this extension changes no value that occurs in
the argument. -/
def safePerronRatioIncrement (u t : ℝ) : ℂ :=
  perronRatioIncrement (max u 0) t

theorem safePerronRatioIncrement_eq_of_nonneg
    {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    safePerronRatioIncrement u t = perronRatioIncrement u t := by
  simp [safePerronRatioIncrement, max_eq_left hu]

/-- Joint continuity of the harmless global extension. -/
theorem continuous_uncurry_safePerronRatioIncrement :
    Continuous (Function.uncurry safePerronRatioIncrement) := by
  unfold safePerronRatioIncrement perronRatioIncrement Function.uncurry
  have hbase : Continuous (fun p : ℝ × ℝ ↦
      (((1 + max p.1 0 : ℝ) : ℂ))) := by fun_prop
  have hexp : Continuous (fun p : ℝ × ℝ ↦
      (((1 + max p.1 0 : ℝ) : ℂ) ^
        ((1 : ℂ) + (p.2 : ℂ) * Complex.I))) := by
    apply hbase.cpow (by fun_prop)
    intro p
    rw [Complex.ofReal_mem_slitPlane]
    have : 0 ≤ max p.1 0 := le_max_right _ _
    linarith
  apply (hexp.sub continuous_const).div (by fun_prop)
  intro p hp
  have hre := congrArg Complex.re hp
  norm_num at hre

/-- Globally continuous version of the fixed-parameter logarithmic
transform. -/
def safeSmoothedLogTransformOn
    (F : ℝ → ℂ) (u : ℝ) (x : ℕ) (A B : ℝ) : ℂ :=
  ∫ t in A..B, F t *
    (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
      safePerronRatioIncrement u t

theorem safeSmoothedLogTransformOn_eq_of_nonneg
    (F : ℝ → ℂ) {u : ℝ} (hu : 0 ≤ u) (x : ℕ) (A B : ℝ) :
    safeSmoothedLogTransformOn F u x A B =
      smoothedLogTransformOn F u x A B := by
  unfold safeSmoothedLogTransformOn smoothedLogTransformOn
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp
  rw [safePerronRatioIncrement_eq_of_nonneg hu]

theorem continuous_safeSmoothedLogTransformOn
    (F : ℝ → ℂ) (hF : Continuous F) (x : ℕ) (hx : 0 < x) (A B : ℝ) :
    Continuous (fun u ↦ safeSmoothedLogTransformOn F u x A B) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  letI : NeZero (x : ℂ) := ⟨hxC⟩
  unfold safeSmoothedLogTransformOn
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hexp : Continuous (fun p : ℝ × ℝ ↦
      (1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  have hpow : Continuous (fun p : ℝ × ℝ ↦
      ((x : ℕ) : ℂ) ^ ((1 : ℂ) + (p.2 : ℂ) * Complex.I)) :=
    (continuous_const_cpow ((x : ℕ) : ℂ)).comp hexp
  exact ((hF.comp continuous_snd).mul hpow).mul
    continuous_uncurry_safePerronRatioIncrement

/-- Fubini for the source smoothing transform on a nonnegative
`u`-interval.  The continuous extension above handles the endpoint
`u = 0`; on the whole interval its values agree with the original ratio
kernel. -/
theorem intervalIntegral_smoothedLogTransformOn_eq_swap
    (F : ℝ → ℂ) (hF : Continuous F) (x : ℕ) (hx : 0 < x)
    {a b A B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ u in a..b, smoothedLogTransformOn F u x A B) =
      ∫ t in A..B, F t *
        (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
          ∫ u in a..b, perronRatioIncrement u t := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  letI : NeZero (x : ℂ) := ⟨hxC⟩
  let H : ℝ → ℝ → ℂ := fun t u ↦ F t *
    (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
      safePerronRatioIncrement u t
  have hexp : Continuous (fun p : ℝ × ℝ ↦
      (1 : ℂ) + (p.1 : ℂ) * Complex.I) := by fun_prop
  have hpow : Continuous (fun p : ℝ × ℝ ↦
      (x : ℂ) ^ ((1 : ℂ) + (p.1 : ℂ) * Complex.I)) :=
    (continuous_const_cpow (x : ℂ)).comp hexp
  have hH : Continuous (Function.uncurry H) := by
    exact ((hF.comp continuous_fst).mul hpow).mul
      (continuous_uncurry_safePerronRatioIncrement.comp continuous_swap)
  have hrect : IntegrableOn (Function.uncurry H)
      (Set.uIoc A B ×ˢ Set.uIoc a b) :=
    (hH.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set
        (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hswap :
      (∫ t in A..B, ∫ u in a..b, H t u) =
        ∫ u in a..b, ∫ t in A..B, H t u :=
    MeasureTheory.intervalIntegral_intervalIntegral_swap hrect
  have hsafe (u : ℝ) (hu : u ∈ Set.uIcc a b) : 0 ≤ u := by
    rw [Set.uIcc_of_le hab] at hu
    exact ha.trans hu.1
  calc
    (∫ u in a..b, smoothedLogTransformOn F u x A B) =
        ∫ u in a..b, ∫ t in A..B, H t u := by
      apply intervalIntegral.integral_congr
      intro u hu
      unfold smoothedLogTransformOn
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp [H]
      rw [safePerronRatioIncrement_eq_of_nonneg (hsafe u hu)]
    _ = ∫ t in A..B, ∫ u in a..b, H t u := hswap.symm
    _ = ∫ t in A..B, F t *
        (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
          ∫ u in a..b, perronRatioIncrement u t := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp [H]
      rw [safePerronRatioIncrement_eq_of_nonneg (hsafe u hu)]

/-- Continuity in the vertical variable of the integrated ratio kernel
on a nonnegative source-smoothing interval. -/
theorem continuous_intervalIntegral_perronRatioIncrement
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Continuous (fun t ↦ ∫ u in a..b, perronRatioIncrement u t) := by
  have hsafe (u : ℝ) (hu : u ∈ Set.uIcc a b) : 0 ≤ u := by
    rw [Set.uIcc_of_le hab] at hu
    exact ha.trans hu.1
  have heq : (fun t ↦ ∫ u in a..b, perronRatioIncrement u t) =
      fun t ↦ ∫ u in a..b, safePerronRatioIncrement u t := by
    funext t
    apply intervalIntegral.integral_congr
    intro u hu
    exact (safePerronRatioIncrement_eq_of_nonneg (hsafe u hu) t).symm
  rw [heq]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact continuous_uncurry_safePerronRatioIncrement.comp continuous_swap

/-- A vertical Perron segment for one normalized interval length. -/
def perronKernelSegmentOn
    (F : ℝ → ℂ) (x h : ℝ) (A B : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in A..B, F t * perronIncrementKernel x h t)

/-- The first, base-`x`, source smoothing piece before the common
`(2π)⁻¹` factor. -/
def sourceSmoothedLeftOn
    (F : ℝ → ℂ) (x h : ℕ) (A B : ℝ) : ℂ :=
  (h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ * (x : ℂ) *
    ∫ u in (h : ℝ) / x..3 * h / x,
      smoothedLogTransformOn F u x A B

/-- The second, base-`x+h`, source smoothing piece before the common
`(2π)⁻¹` factor. -/
def sourceSmoothedRightOn
    (F : ℝ → ℂ) (x h : ℕ) (A B : ℝ) : ℂ :=
  (h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ * ((x + h : ℕ) : ℂ) *
    ∫ u in 0..(2 * h : ℝ) / (x + h),
      smoothedLogTransformOn F u (x + h) A B

/-- Pointwise source smoothing identity for the normalized Perron
increment.  This keeps the two moving-endpoint integrals together until
their common endpoint has canceled. -/
theorem perronIncrementKernel_eq_sourceSmoothed_real
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (t : ℝ) :
    perronIncrementKernel x h t =
      (h : ℂ)⁻¹ * (((2 * h : ℝ) : ℂ))⁻¹ *
        ((x : ℂ) * (∫ u in h / x..3 * h / x,
            (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
              perronRatioIncrement u t) -
          ((x + h : ℝ) : ℂ) * (∫ u in 0..2 * h / (x + h),
            ((x + h : ℝ) : ℂ) ^
                ((1 : ℂ) + (t : ℂ) * Complex.I) *
              perronRatioIncrement u t)) := by
  let s : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I
  let G : ℝ → ℂ := fun w ↦ ((x + w : ℝ) : ℂ) ^ s / s
  have hsre : 0 < s.re := by simp [s]
  have hG : Continuous G := by
    exact (Complex.continuous_ofReal_cpow_const hsre |>.comp (by fun_prop)).div_const s
  have hsmooth := MRLemma14Smoothing.sub_average_movingEndpoint_eq
    G hG ((x : ℂ) ^ s / s) (((x + h : ℝ) : ℂ) ^ s / s) hh
  have hleft := integral_perronIncrement_changeVariables_left
    (x := x) (h := h) hx hh t
  have hright := integral_perronIncrement_changeVariables_right
    (x := x) (h := h) hx hh t
  dsimp [G, s] at hsmooth
  simp_rw [← sub_div] at hsmooth
  rw [hleft, hright] at hsmooth
  have hhC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hsC : ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    norm_num at hre
  unfold perronIncrementKernel
  calc
    _ = (h : ℂ)⁻¹ *
        ((((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) -
            (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) /
          ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
      field_simp [hhC, hsC]
    _ = _ := by
      rw [hsmooth]
      ring

/-- Natural-endpoint form of the pointwise source smoothing identity. -/
theorem perronIncrementKernel_eq_sourceSmoothed
    {x h : ℕ} (hx : 0 < x) (hh : 0 < h) (t : ℝ) :
    perronIncrementKernel x h t =
      (h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ *
        ((x : ℂ) * (∫ u in (h : ℝ) / x..3 * h / x,
            (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
              perronRatioIncrement u t) -
          ((x + h : ℕ) : ℂ) * (∫ u in 0..(2 * h : ℝ) / (x + h),
            ((x + h : ℕ) : ℂ) ^
                ((1 : ℂ) + (t : ℂ) * Complex.I) *
              perronRatioIncrement u t)) := by
  convert perronIncrementKernel_eq_sourceSmoothed_real
      (x := (x : ℝ)) (h := (h : ℝ))
      (by exact_mod_cast hx) (by exact_mod_cast hh) t using 1 <;>
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Complex.ofReal_natCast, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_ofNat]

/-- Exact source smoothing formula after swapping the finite vertical and
relative-endpoint integrals. -/
theorem perronKernelSegmentOn_eq_sourceSmoothed
    (F : ℝ → ℂ) (hF : Continuous F) {x h : ℕ}
    (hx : 0 < x) (hh : 0 < h) (A B : ℝ) :
    perronKernelSegmentOn F x h A B =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (sourceSmoothedLeftOn F x h A B -
          sourceSmoothedRightOn F x h A B)) := by
  have hxh : 0 < x + h := by omega
  have hleftSwap := intervalIntegral_smoothedLogTransformOn_eq_swap
    F hF x hx
      (a := (h : ℝ) / x) (b := 3 * h / x) (A := A) (B := B)
      (by positivity) (by
        have : 0 < (h : ℝ) / x := by positivity
        rw [show (3 * h : ℝ) / x = 3 * ((h : ℝ) / x) by ring]
        linarith)
  have hrightSwap := intervalIntegral_smoothedLogTransformOn_eq_swap
    F hF (x + h) hxh
      (a := 0) (b := (2 * h : ℝ) / (x + h)) (A := A) (B := B)
      (by norm_num) (by positivity)
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hxhC : ((x + h : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hxh.ne'
  letI : NeZero (x : ℂ) := ⟨hxC⟩
  letI : NeZero ((x + h : ℕ) : ℂ) := ⟨hxhC⟩
  let L : ℝ → ℂ := fun t ↦ F t *
    (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
      ∫ u in (h : ℝ) / x..3 * h / x, perronRatioIncrement u t
  let R : ℝ → ℂ := fun t ↦ F t *
    ((x + h : ℕ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
      ∫ u in 0..(2 * h : ℝ) / (x + h), perronRatioIncrement u t
  have hL : Continuous L := by
    dsimp [L]
    exact (hF.mul ((continuous_const_cpow (x : ℂ)).comp (by fun_prop))).mul
      (continuous_intervalIntegral_perronRatioIncrement
        (a := (h : ℝ) / x) (b := 3 * h / x)
        (by positivity) (by
          have : 0 < (h : ℝ) / x := by positivity
          rw [show (3 * h : ℝ) / x = 3 * ((h : ℝ) / x) by ring]
          linarith))
  have hR : Continuous R := by
    dsimp [R]
    exact (hF.mul ((continuous_const_cpow ((x + h : ℕ) : ℂ)).comp
      (by fun_prop))).mul
        (continuous_intervalIntegral_perronRatioIncrement
          (a := 0) (b := (2 * h : ℝ) / (x + h)) (by norm_num) (by positivity))
  unfold perronKernelSegmentOn sourceSmoothedLeftOn sourceSmoothedRightOn
  rw [hleftSwap, hrightSwap]
  apply congrArg (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ·)
  change (∫ t in A..B, F t * perronIncrementKernel x h t) =
    (h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ * (x : ℂ) * (∫ t in A..B, L t) -
      (h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ * ((x + h : ℕ) : ℂ) *
        (∫ t in A..B, R t)
  calc
    (∫ t in A..B, F t * perronIncrementKernel x h t) =
        ∫ t in A..B,
          (h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ *
            ((x : ℂ) * L t - ((x + h : ℕ) : ℂ) * R t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp
      rw [perronIncrementKernel_eq_sourceSmoothed hx hh t]
      have hLi :
          (∫ u in (h : ℝ) / x..3 * h / x,
              (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
                perronRatioIncrement u t) =
            (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) *
              ∫ u in (h : ℝ) / x..3 * h / x,
                perronRatioIncrement u t := by
        rw [intervalIntegral.integral_const_mul]
      have hRi :
          (∫ u in 0..(2 * h : ℝ) / (x + h),
              ((x + h : ℕ) : ℂ) ^
                  ((1 : ℂ) + (t : ℂ) * Complex.I) *
                perronRatioIncrement u t) =
            ((x + h : ℕ) : ℂ) ^
                ((1 : ℂ) + (t : ℂ) * Complex.I) *
              ∫ u in 0..(2 * h : ℝ) / (x + h),
                perronRatioIncrement u t := by
        rw [intervalIntegral.integral_const_mul]
      have hmain := congrArg₂ (· - ·)
        (congrArg ((x : ℂ) * ·) hLi)
        (congrArg (((x + h : ℕ) : ℂ) * ·) hRi)
      rw [hmain]
      dsimp [L, R]
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          ((hL.const_mul (x : ℂ)).intervalIntegrable A B)
          ((hR.const_mul ((x + h : ℕ) : ℂ)).intervalIntegrable A B),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      ring

/-- Cauchy--Schwarz and enlargement to one common relative-endpoint
interval for the base-`x` smoothing piece.  This is the first quantitative
step in the source high-frequency argument; importantly, its prefactor is
`X / h^3`, so the subsequent `u^2` multiplier exactly cancels the powers
of the interval length. -/
theorem sum_normSq_sourceSmoothedLeftOn_le_uniform
    (F : ℝ → ℂ) (hF : Continuous F) {X h : ℕ}
    (hX : 0 < X) (hh : 0 < h) :
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (sourceSmoothedLeftOn F x h A B)) ≤
      (X : ℝ) / (h : ℝ) ^ 3 *
        ∫ u in (h : ℝ) / (2 * X)..3 * h / X,
          ∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq (safeSmoothedLogTransformOn F u x A B) := by
  classical
  let D : Finset ℕ := Finset.Ioc X (2 * X)
  let a₀ : ℝ := (h : ℝ) / (2 * X)
  let b₀ : ℝ := 3 * h / X
  have hfac : 0 ≤ (X : ℝ) / (h : ℝ) ^ 3 := by positivity
  have hpoint (x : ℕ) (hxmem : x ∈ D) :
      Complex.normSq (sourceSmoothedLeftOn F x h A B) ≤
        (X : ℝ) / (h : ℝ) ^ 3 *
          ∫ u in a₀..b₀,
            Complex.normSq (safeSmoothedLogTransformOn F u x A B) := by
    have hxbounds := Finset.mem_Ioc.mp hxmem
    have hx : 0 < x := by omega
    have hxX : (x : ℝ) ≤ 2 * X := by exact_mod_cast hxbounds.2
    have hXx : (X : ℝ) ≤ x := by exact_mod_cast hxbounds.1.le
    have hax : a₀ ≤ (h : ℝ) / x := by
      dsimp [a₀]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hxX
    have hbx : 3 * (h : ℝ) / x ≤ b₀ := by
      dsimp [b₀]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hXx
    have habx : (h : ℝ) / x ≤ 3 * h / x := by
      have hp : 0 < (h : ℝ) / x := by positivity
      rw [show (3 * h : ℝ) / x = 3 * ((h : ℝ) / x) by ring]
      linarith
    have ha₀b₀ : a₀ ≤ b₀ := hax.trans (habx.trans hbx)
    have hsafeInt :
        (∫ u in (h : ℝ) / x..3 * h / x,
            smoothedLogTransformOn F u x A B) =
          ∫ u in (h : ℝ) / x..3 * h / x,
            safeSmoothedLogTransformOn F u x A B := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le habx] at hu
      exact (safeSmoothedLogTransformOn_eq_of_nonneg F
        (show 0 ≤ u by exact (by positivity : 0 ≤ (h : ℝ) / x) |>.trans hu.1)
        x A B).symm
    have hcont := continuous_safeSmoothedLogTransformOn F hF x hx A B
    have hcs := normSq_intervalIntegral_le_length_mul_integral_normSq
      hcont habx
    have henlarge :
        (∫ u in (h : ℝ) / x..3 * h / x,
            Complex.normSq (safeSmoothedLogTransformOn F u x A B)) ≤
          ∫ u in a₀..b₀,
            Complex.normSq (safeSmoothedLogTransformOn F u x A B) := by
      exact intervalIntegral.integral_mono_interval hax habx hbx
        (MeasureTheory.ae_of_all _ (fun u ↦ Complex.normSq_nonneg _))
        ((Complex.continuous_normSq.comp hcont).intervalIntegrable a₀ b₀)
    have hlen : 3 * (h : ℝ) / x - (h : ℝ) / x = 2 * h / x := by ring
    have hcoef :
        Complex.normSq
            ((h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ * (x : ℂ)) *
              (2 * (h : ℝ) / x) ≤
          (X : ℝ) / (h : ℝ) ^ 3 := by
      simp only [Complex.normSq_mul, Complex.normSq_inv,
        Complex.normSq_natCast, Nat.cast_mul, Nat.cast_ofNat]
      norm_num [Complex.normSq]
      field_simp [show (h : ℝ) ≠ 0 by positivity,
        show (x : ℝ) ≠ 0 by positivity]
      nlinarith [hxX]
    unfold sourceSmoothedLeftOn
    rw [hsafeInt, Complex.normSq_mul]
    calc
      Complex.normSq
            ((h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ * (x : ℂ)) *
          Complex.normSq
            (∫ u in (h : ℝ) / x..3 * h / x,
              safeSmoothedLogTransformOn F u x A B) ≤
        Complex.normSq
            ((h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ * (x : ℂ)) *
          ((2 * (h : ℝ) / x) *
            ∫ u in (h : ℝ) / x..3 * h / x,
              Complex.normSq (safeSmoothedLogTransformOn F u x A B)) := by
          apply mul_le_mul_of_nonneg_left
          simpa only [hlen] using hcs
          exact Complex.normSq_nonneg _
      _ ≤ ((X : ℝ) / (h : ℝ) ^ 3) *
          ∫ u in (h : ℝ) / x..3 * h / x,
            Complex.normSq (safeSmoothedLogTransformOn F u x A B) := by
        have hI : 0 ≤ ∫ u in (h : ℝ) / x..3 * h / x,
            Complex.normSq (safeSmoothedLogTransformOn F u x A B) :=
          intervalIntegral.integral_nonneg_of_forall habx
            (fun u ↦ Complex.normSq_nonneg _)
        calc
          Complex.normSq
                ((h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ * (x : ℂ)) *
              ((2 * (h : ℝ) / x) *
                ∫ u in (h : ℝ) / x..3 * h / x,
                  Complex.normSq (safeSmoothedLogTransformOn F u x A B)) =
              (Complex.normSq
                  ((h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ * (x : ℂ)) *
                (2 * (h : ℝ) / x)) *
                  ∫ u in (h : ℝ) / x..3 * h / x,
                    Complex.normSq (safeSmoothedLogTransformOn F u x A B) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hI
      _ ≤ ((X : ℝ) / (h : ℝ) ^ 3) *
          ∫ u in a₀..b₀,
            Complex.normSq (safeSmoothedLogTransformOn F u x A B) :=
        mul_le_mul_of_nonneg_left henlarge hfac
  calc
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (sourceSmoothedLeftOn F x h A B)) ≤
      ∑ x ∈ D, (X : ℝ) / (h : ℝ) ^ 3 *
        ∫ u in a₀..b₀,
          Complex.normSq (safeSmoothedLogTransformOn F u x A B) := by
      exact Finset.sum_le_sum hpoint
    _ = (X : ℝ) / (h : ℝ) ^ 3 *
        ∫ u in a₀..b₀,
          ∑ x ∈ D,
            Complex.normSq (safeSmoothedLogTransformOn F u x A B) := by
      rw [intervalIntegral.integral_finset_sum, Finset.mul_sum]
      intro x hxmem
      exact (Complex.continuous_normSq.comp
        (continuous_safeSmoothedLogTransformOn F hF x
          (by have := Finset.mem_Ioc.mp hxmem; omega) A B)).intervalIntegrable a₀ b₀
    _ = _ := by
      dsimp [D, a₀, b₀]

/-- The base-`x` smoothing piece on one vertical band, in the exact
source-normalized form.  The interval integral in `u^2` is explicit; its
length is `O(h/X)` and its endpoint is `O(h/X)`, so the displayed
`X/h^3` prefactor cancels completely. -/
theorem sum_normSq_sourceSmoothedLeftOn_le_verticalEnergy
    (F : ℝ → ℂ) (hF : Continuous F) {X h : ℕ}
    (hX : 0 < X) (hh : 0 < h) {A B : ℝ} (hAB : A ≤ B) :
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (sourceSmoothedLeftOn F x h A B)) ≤
      ((X : ℝ) / (h : ℝ) ^ 3) *
        ((2 * X : ℝ) ^ 2 *
          (B - A + 2 * Real.pi * (2 * X : ℕ))) *
        (∫ u in (h : ℝ) / (2 * X)..3 * h / X, u ^ 2) *
        ∫ t in A..B, Complex.normSq (F t) := by
  classical
  let a₀ : ℝ := (h : ℝ) / (2 * X)
  let b₀ : ℝ := 3 * h / X
  let C : ℝ := (2 * X : ℝ) ^ 2 *
    (B - A + 2 * Real.pi * (2 * X : ℕ))
  let E : ℝ := ∫ t in A..B, Complex.normSq (F t)
  have ha₀ : 0 < a₀ := by dsimp [a₀]; positivity
  have hab₀ : a₀ ≤ b₀ := by
    dsimp [a₀, b₀]
    have hp : 0 < (h : ℝ) / X := by positivity
    rw [show (h : ℝ) / (2 * X) = (1 / 2) * ((h : ℝ) / X) by field_simp,
      show 3 * (h : ℝ) / X = 3 * ((h : ℝ) / X) by ring]
    linarith
  have hQ : 0 ≤ B - A + 2 * Real.pi * (2 * X : ℕ) := by positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    exact intervalIntegral.integral_nonneg_of_forall hAB
      (fun t ↦ Complex.normSq_nonneg _)
  have hsum (u : ℝ) (hu : u ∈ Set.Icc a₀ b₀) :
      (∑ x ∈ Finset.Ioc X (2 * X),
          Complex.normSq (safeSmoothedLogTransformOn F u x A B)) ≤
        C * u ^ 2 * E := by
    have hu0 : 0 < u := ha₀.trans_le hu.1
    have heq :
        (∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq (safeSmoothedLogTransformOn F u x A B)) =
          ∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq (smoothedLogTransformOn F u x A B) := by
      apply Finset.sum_congr rfl
      intro x hxmem
      rw [safeSmoothedLogTransformOn_eq_of_nonneg F hu0.le]
    rw [heq]
    have hplan := sum_normSq_smoothedLogTransformOn_le
      F hF hX hu0 hAB
    have hmul := integral_normSq_mul_perronRatioIncrement_le_self
      F hF hu0 hAB
    calc
      (∑ x ∈ Finset.Ioc X (2 * X),
          Complex.normSq (smoothedLogTransformOn F u x A B)) ≤
        C * ∫ t in A..B,
          Complex.normSq (F t * perronRatioIncrement u t) := by
        simpa only [C]
      _ ≤ C * (u ^ 2 * E) := mul_le_mul_of_nonneg_left hmul hC
      _ = C * u ^ 2 * E := by ring
  have hsumCont : Continuous (fun u ↦
      ∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (safeSmoothedLogTransformOn F u x A B)) := by
    apply continuous_finsetSum
    intro x hxmem
    exact Complex.continuous_normSq.comp
      (continuous_safeSmoothedLogTransformOn F hF x
        (by have := Finset.mem_Ioc.mp hxmem; omega) A B)
  have hrightCont : Continuous (fun u ↦ C * u ^ 2 * E) := by fun_prop
  have hmono :
      (∫ u in a₀..b₀,
          ∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq (safeSmoothedLogTransformOn F u x A B)) ≤
        ∫ u in a₀..b₀, C * u ^ 2 * E := by
    exact intervalIntegral.integral_mono_on hab₀
      (hsumCont.intervalIntegrable a₀ b₀)
      (hrightCont.intervalIntegrable a₀ b₀) hsum
  have huniform := sum_normSq_sourceSmoothedLeftOn_le_uniform
    F hF hX hh (A := A) (B := B)
  calc
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (sourceSmoothedLeftOn F x h A B)) ≤
      ((X : ℝ) / (h : ℝ) ^ 3) *
        ∫ u in a₀..b₀,
          ∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq (safeSmoothedLogTransformOn F u x A B) := by
      simpa only [a₀, b₀] using huniform
    _ ≤ ((X : ℝ) / (h : ℝ) ^ 3) *
        ∫ u in a₀..b₀, C * u ^ 2 * E :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ((X : ℝ) / (h : ℝ) ^ 3) * C *
        (∫ u in a₀..b₀, u ^ 2) * E := by
      have hint : (∫ u in a₀..b₀, C * u ^ 2 * E) =
          C * (∫ u in a₀..b₀, u ^ 2) * E := by
        rw [intervalIntegral.integral_mul_const,
          intervalIntegral.integral_const_mul]
      rw [hint]
      ring
    _ = _ := by rfl

/-- Reciprocal-frequency version of the source-normalized estimate.  On a
dyadic band separated from zero by `T`, this exposes exactly the square of
the smoothed Perron multiplier `(2+u)/T`; after the short `u` integration
it yields the summable high-shell weight. -/
theorem sum_normSq_sourceSmoothedLeftOn_le_shellEnergy
    (F : ℝ → ℂ) (hF : Continuous F) {X h : ℕ}
    (hX : 0 < X) (hh : 0 < h) {A B T : ℝ}
    (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (sourceSmoothedLeftOn F x h A B)) ≤
      ((X : ℝ) / (h : ℝ) ^ 3) *
        ((2 * X : ℝ) ^ 2 *
          (B - A + 2 * Real.pi * (2 * X : ℕ))) *
        (∫ u in (h : ℝ) / (2 * X)..3 * h / X,
          ((2 + u) / T) ^ 2) *
        ∫ t in A..B, Complex.normSq (F t) := by
  classical
  let a₀ : ℝ := (h : ℝ) / (2 * X)
  let b₀ : ℝ := 3 * h / X
  let C : ℝ := (2 * X : ℝ) ^ 2 *
    (B - A + 2 * Real.pi * (2 * X : ℕ))
  let E : ℝ := ∫ t in A..B, Complex.normSq (F t)
  have ha₀ : 0 < a₀ := by dsimp [a₀]; positivity
  have hab₀ : a₀ ≤ b₀ := by
    dsimp [a₀, b₀]
    have hp : 0 < (h : ℝ) / X := by positivity
    rw [show (h : ℝ) / (2 * X) = (1 / 2) * ((h : ℝ) / X) by field_simp,
      show 3 * (h : ℝ) / X = 3 * ((h : ℝ) / X) by ring]
    linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    have : 0 ≤ B - A + 2 * Real.pi * (2 * X : ℕ) := by positivity
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    exact intervalIntegral.integral_nonneg_of_forall hAB
      (fun t ↦ Complex.normSq_nonneg _)
  have hsum (u : ℝ) (hu : u ∈ Set.Icc a₀ b₀) :
      (∑ x ∈ Finset.Ioc X (2 * X),
          Complex.normSq (safeSmoothedLogTransformOn F u x A B)) ≤
        C * ((2 + u) / T) ^ 2 * E := by
    have hu0 : 0 < u := ha₀.trans_le hu.1
    have heq :
        (∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq (safeSmoothedLogTransformOn F u x A B)) =
          ∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq (smoothedLogTransformOn F u x A B) := by
      apply Finset.sum_congr rfl
      intro x hxmem
      rw [safeSmoothedLogTransformOn_eq_of_nonneg F hu0.le]
    rw [heq]
    have hplan := sum_normSq_smoothedLogTransformOn_le
      F hF hX hu0 hAB
    have hmul := integral_normSq_mul_perronRatioIncrement_le_div
      F hF hu0 hAB hT haway
    calc
      (∑ x ∈ Finset.Ioc X (2 * X),
          Complex.normSq (smoothedLogTransformOn F u x A B)) ≤
        C * ∫ t in A..B,
          Complex.normSq (F t * perronRatioIncrement u t) := by
        simpa only [C]
      _ ≤ C * (((2 + u) / T) ^ 2 * E) :=
        mul_le_mul_of_nonneg_left hmul hC
      _ = C * ((2 + u) / T) ^ 2 * E := by ring
  have hsumCont : Continuous (fun u ↦
      ∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (safeSmoothedLogTransformOn F u x A B)) := by
    apply continuous_finsetSum
    intro x hxmem
    exact Complex.continuous_normSq.comp
      (continuous_safeSmoothedLogTransformOn F hF x
        (by have := Finset.mem_Ioc.mp hxmem; omega) A B)
  have hrightCont : Continuous
      (fun u ↦ C * ((2 + u) / T) ^ 2 * E) := by fun_prop
  have hmono :
      (∫ u in a₀..b₀,
          ∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq (safeSmoothedLogTransformOn F u x A B)) ≤
        ∫ u in a₀..b₀, C * ((2 + u) / T) ^ 2 * E := by
    exact intervalIntegral.integral_mono_on hab₀
      (hsumCont.intervalIntegrable a₀ b₀)
      (hrightCont.intervalIntegrable a₀ b₀) hsum
  have huniform := sum_normSq_sourceSmoothedLeftOn_le_uniform
    F hF hX hh (A := A) (B := B)
  calc
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (sourceSmoothedLeftOn F x h A B)) ≤
      ((X : ℝ) / (h : ℝ) ^ 3) *
        ∫ u in a₀..b₀,
          ∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq (safeSmoothedLogTransformOn F u x A B) := by
      simpa only [a₀, b₀] using huniform
    _ ≤ ((X : ℝ) / (h : ℝ) ^ 3) *
        ∫ u in a₀..b₀, C * ((2 + u) / T) ^ 2 * E :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ((X : ℝ) / (h : ℝ) ^ 3) * C *
        (∫ u in a₀..b₀, ((2 + u) / T) ^ 2) * E := by
      have hint : (∫ u in a₀..b₀, C * ((2 + u) / T) ^ 2 * E) =
          C * (∫ u in a₀..b₀, ((2 + u) / T) ^ 2) * E := by
        rw [intervalIntegral.integral_mul_const,
          intervalIntegral.integral_const_mul]
      rw [hint]
      ring
    _ = _ := by rfl

/-- Fixed-`u` logarithmic Plancherel after shifting every endpoint from
`x` to `x+h`.  The shifted endpoints are distinct and bounded by `3X`
when `h ≤ X`; this is the input needed for the second source smoothing
piece. -/
theorem sum_normSq_safeSmoothedLogTransformOn_shift_le
    (F : ℝ → ℂ) (hF : Continuous F) {X h : ℕ}
    (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X)
    {u A B : ℝ} (hu : 0 < u) (hAB : A ≤ B) :
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (safeSmoothedLogTransformOn F u (x + h) A B)) ≤
      (3 * X : ℝ) ^ 2 *
        (B - A + 2 * Real.pi * (3 * X : ℕ)) *
          ∫ t in A..B,
            Complex.normSq (F t * perronRatioIncrement u t) := by
  classical
  let D₀ : Finset ℕ := Finset.Ioc X (2 * X)
  let D : Finset ℕ := D₀.image (fun x ↦ x + h)
  have hinj : ∀ a ∈ D₀, ∀ b ∈ D₀, a + h = b + h → a = b := by
    intro a ha b hb hab
    omega
  have hsumEq (q : ℕ → ℝ) :
      (∑ x ∈ D₀, q (x + h)) = ∑ y ∈ D, q y := by
    dsimp [D]
    rw [Finset.sum_image]
    exact hinj
  have hpos : ∀ y ∈ D, 0 < y := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    omega
  have hle : ∀ y ∈ D, y ≤ 3 * X := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxb := (Finset.mem_Ioc.mp hx).2
    omega
  have hgeneric := sum_normSq_smoothedLogTransformOn_finset_le
    F hF D (N := 3 * X) (by omega) hpos hle hu hAB
  have hsafeEq (y : ℕ) :
      safeSmoothedLogTransformOn F u y A B =
        smoothedLogTransformOn F u y A B :=
    safeSmoothedLogTransformOn_eq_of_nonneg F hu.le y A B
  rw [show (∑ x ∈ Finset.Ioc X (2 * X),
      Complex.normSq (safeSmoothedLogTransformOn F u (x + h) A B)) =
      ∑ x ∈ D₀,
        Complex.normSq (smoothedLogTransformOn F u (x + h) A B) by
    dsimp [D₀]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hsafeEq]]
  rw [hsumEq (fun y ↦ Complex.normSq
    (smoothedLogTransformOn F u y A B))]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hgeneric

/-- Cauchy--Schwarz and common-interval enlargement for the shifted
`x+h` smoothing piece.  Its prefactor has the same source scale as the
left piece (up to the harmless factor two caused by `x+h ≤ 3X`). -/
theorem sum_normSq_sourceSmoothedRightOn_le_uniform
    (F : ℝ → ℂ) (hF : Continuous F) {X h : ℕ}
    (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X) :
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (sourceSmoothedRightOn F x h A B)) ≤
      (2 * X : ℝ) / (h : ℝ) ^ 3 *
        ∫ u in 0..(2 * h : ℝ) / X,
          ∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq
              (safeSmoothedLogTransformOn F u (x + h) A B) := by
  classical
  let D : Finset ℕ := Finset.Ioc X (2 * X)
  let b₀ : ℝ := (2 * h : ℝ) / X
  have hfac : 0 ≤ (2 * X : ℝ) / (h : ℝ) ^ 3 := by positivity
  have hpoint (x : ℕ) (hxmem : x ∈ D) :
      Complex.normSq (sourceSmoothedRightOn F x h A B) ≤
        (2 * X : ℝ) / (h : ℝ) ^ 3 *
          ∫ u in 0..b₀,
            Complex.normSq
              (safeSmoothedLogTransformOn F u (x + h) A B) := by
    have hxbounds := Finset.mem_Ioc.mp hxmem
    have hx : 0 < x := by omega
    have hxh : 0 < x + h := by omega
    have hXxh : (X : ℝ) ≤ x + h := by exact_mod_cast hxbounds.1.le.trans (Nat.le_add_right x h)
    have hxhX : ((x + h : ℕ) : ℝ) ≤ 3 * X := by
      exact_mod_cast (by omega : x + h ≤ 3 * X)
    norm_num only [Nat.cast_add] at hxhX
    have habx : (0 : ℝ) ≤ (2 * h : ℝ) / (x + h) := by positivity
    have hbx : (2 * h : ℝ) / (x + h) ≤ b₀ := by
      dsimp [b₀]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hXxh
    have hb₀ : 0 ≤ b₀ := habx.trans hbx
    have hsafeInt :
        (∫ u in 0..(2 * h : ℝ) / (x + h),
            smoothedLogTransformOn F u (x + h) A B) =
          ∫ u in 0..(2 * h : ℝ) / (x + h),
            safeSmoothedLogTransformOn F u (x + h) A B := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le habx] at hu
      exact (safeSmoothedLogTransformOn_eq_of_nonneg F hu.1
        (x + h) A B).symm
    have hcont := continuous_safeSmoothedLogTransformOn F hF
      (x + h) hxh A B
    have hcs := normSq_intervalIntegral_le_length_mul_integral_normSq
      hcont habx
    have henlarge :
        (∫ u in 0..(2 * h : ℝ) / (x + h),
            Complex.normSq
              (safeSmoothedLogTransformOn F u (x + h) A B)) ≤
          ∫ u in 0..b₀,
            Complex.normSq
              (safeSmoothedLogTransformOn F u (x + h) A B) := by
      exact intervalIntegral.integral_mono_interval (le_refl 0) habx hbx
        (MeasureTheory.ae_of_all _ (fun u ↦ Complex.normSq_nonneg _))
        ((Complex.continuous_normSq.comp hcont).intervalIntegrable 0 b₀)
    have hcoef :
        Complex.normSq
            ((h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ *
              ((x + h : ℕ) : ℂ)) *
              ((2 * h : ℝ) / (x + h)) ≤
          (2 * X : ℝ) / (h : ℝ) ^ 3 := by
      simp only [Complex.normSq_mul, Complex.normSq_inv,
        Complex.normSq_natCast, Nat.cast_mul, Nat.cast_ofNat]
      norm_num [Complex.normSq]
      field_simp [show (h : ℝ) ≠ 0 by positivity,
        show ((x + h : ℕ) : ℝ) ≠ 0 by positivity]
      nlinarith [hxhX, (show (0 : ℝ) < X by exact_mod_cast hX)]
    unfold sourceSmoothedRightOn
    rw [hsafeInt, Complex.normSq_mul]
    calc
      Complex.normSq
            ((h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ *
              ((x + h : ℕ) : ℂ)) *
          Complex.normSq
            (∫ u in 0..(2 * h : ℝ) / (x + h),
              safeSmoothedLogTransformOn F u (x + h) A B) ≤
        Complex.normSq
            ((h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ *
              ((x + h : ℕ) : ℂ)) *
          (((2 * h : ℝ) / (x + h)) *
            ∫ u in 0..(2 * h : ℝ) / (x + h),
              Complex.normSq
                (safeSmoothedLogTransformOn F u (x + h) A B)) := by
          exact mul_le_mul_of_nonneg_left (by simpa only [sub_zero] using hcs)
            (Complex.normSq_nonneg _)
      _ ≤ ((2 * X : ℝ) / (h : ℝ) ^ 3) *
          ∫ u in 0..(2 * h : ℝ) / (x + h),
            Complex.normSq
              (safeSmoothedLogTransformOn F u (x + h) A B) := by
        have hI : 0 ≤ ∫ u in 0..(2 * h : ℝ) / (x + h),
            Complex.normSq
              (safeSmoothedLogTransformOn F u (x + h) A B) :=
          intervalIntegral.integral_nonneg_of_forall habx
            (fun u ↦ Complex.normSq_nonneg _)
        calc
          Complex.normSq
                ((h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ *
                  ((x + h : ℕ) : ℂ)) *
              (((2 * h : ℝ) / (x + h)) *
                ∫ u in 0..(2 * h : ℝ) / (x + h),
                  Complex.normSq
                    (safeSmoothedLogTransformOn F u (x + h) A B)) =
              (Complex.normSq
                  ((h : ℂ)⁻¹ * (((2 * h : ℕ) : ℂ))⁻¹ *
                    ((x + h : ℕ) : ℂ)) *
                ((2 * h : ℝ) / (x + h))) *
                  ∫ u in 0..(2 * h : ℝ) / (x + h),
                    Complex.normSq
                      (safeSmoothedLogTransformOn F u (x + h) A B) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hI
      _ ≤ ((2 * X : ℝ) / (h : ℝ) ^ 3) *
          ∫ u in 0..b₀,
            Complex.normSq
              (safeSmoothedLogTransformOn F u (x + h) A B) :=
        mul_le_mul_of_nonneg_left henlarge hfac
  calc
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (sourceSmoothedRightOn F x h A B)) ≤
      ∑ x ∈ D, (2 * X : ℝ) / (h : ℝ) ^ 3 *
        ∫ u in 0..b₀,
          Complex.normSq
            (safeSmoothedLogTransformOn F u (x + h) A B) := by
      exact Finset.sum_le_sum hpoint
    _ = (2 * X : ℝ) / (h : ℝ) ^ 3 *
        ∫ u in 0..b₀,
          ∑ x ∈ D,
            Complex.normSq
              (safeSmoothedLogTransformOn F u (x + h) A B) := by
      rw [intervalIntegral.integral_finset_sum, Finset.mul_sum]
      intro x hxmem
      exact (Complex.continuous_normSq.comp
        (continuous_safeSmoothedLogTransformOn F hF (x + h)
          (by have := Finset.mem_Ioc.mp hxmem; omega) A B)).intervalIntegrable 0 b₀
    _ = _ := by dsimp [D, b₀]

@[simp] theorem perronRatioIncrement_zero_left (t : ℝ) :
    perronRatioIncrement 0 t = 0 := by
  simp [perronRatioIncrement]

@[simp] theorem safeSmoothedLogTransformOn_zero
    (F : ℝ → ℂ) (x : ℕ) (A B : ℝ) :
    safeSmoothedLogTransformOn F 0 x A B = 0 := by
  unfold safeSmoothedLogTransformOn safePerronRatioIncrement
  simp

/-- Original-polynomial vertical-energy bound for the shifted source
smoothing piece. -/
theorem sum_normSq_sourceSmoothedRightOn_le_verticalEnergy
    (F : ℝ → ℂ) (hF : Continuous F) {X h : ℕ}
    (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X)
    {A B : ℝ} (hAB : A ≤ B) :
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (sourceSmoothedRightOn F x h A B)) ≤
      ((2 * X : ℝ) / (h : ℝ) ^ 3) *
        ((3 * X : ℝ) ^ 2 *
          (B - A + 2 * Real.pi * (3 * X : ℕ))) *
        (∫ u in 0..(2 * h : ℝ) / X, u ^ 2) *
        ∫ t in A..B, Complex.normSq (F t) := by
  classical
  let b₀ : ℝ := (2 * h : ℝ) / X
  let C : ℝ := (3 * X : ℝ) ^ 2 *
    (B - A + 2 * Real.pi * (3 * X : ℕ))
  let E : ℝ := ∫ t in A..B, Complex.normSq (F t)
  have hb₀ : 0 ≤ b₀ := by dsimp [b₀]; positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    have : 0 ≤ B - A + 2 * Real.pi * (3 * X : ℕ) := by positivity
    positivity
  have hsum (u : ℝ) (hu : u ∈ Set.Icc 0 b₀) :
      (∑ x ∈ Finset.Ioc X (2 * X),
          Complex.normSq
            (safeSmoothedLogTransformOn F u (x + h) A B)) ≤
        C * u ^ 2 * E := by
    by_cases hu0 : u = 0
    · subst u
      simp
    · have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have hplan := sum_normSq_safeSmoothedLogTransformOn_shift_le
        F hF hX hh hhX hupos hAB
      have hmul := integral_normSq_mul_perronRatioIncrement_le_self
        F hF hupos hAB
      calc
        (∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq
              (safeSmoothedLogTransformOn F u (x + h) A B)) ≤
          C * ∫ t in A..B,
            Complex.normSq (F t * perronRatioIncrement u t) := by
          simpa only [C]
        _ ≤ C * (u ^ 2 * E) := mul_le_mul_of_nonneg_left hmul hC
        _ = C * u ^ 2 * E := by ring
  have hsumCont : Continuous (fun u ↦
      ∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq
          (safeSmoothedLogTransformOn F u (x + h) A B)) := by
    apply continuous_finsetSum
    intro x hxmem
    exact Complex.continuous_normSq.comp
      (continuous_safeSmoothedLogTransformOn F hF (x + h)
        (by have := Finset.mem_Ioc.mp hxmem; omega) A B)
  have hrightCont : Continuous (fun u ↦ C * u ^ 2 * E) := by fun_prop
  have hmono :
      (∫ u in 0..b₀,
          ∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq
              (safeSmoothedLogTransformOn F u (x + h) A B)) ≤
        ∫ u in 0..b₀, C * u ^ 2 * E := by
    exact intervalIntegral.integral_mono_on hb₀
      (hsumCont.intervalIntegrable 0 b₀)
      (hrightCont.intervalIntegrable 0 b₀) hsum
  have huniform := sum_normSq_sourceSmoothedRightOn_le_uniform
    F hF hX hh hhX (A := A) (B := B)
  calc
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (sourceSmoothedRightOn F x h A B)) ≤
      ((2 * X : ℝ) / (h : ℝ) ^ 3) *
        ∫ u in 0..b₀,
          ∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq
              (safeSmoothedLogTransformOn F u (x + h) A B) := by
      simpa only [b₀] using huniform
    _ ≤ ((2 * X : ℝ) / (h : ℝ) ^ 3) *
        ∫ u in 0..b₀, C * u ^ 2 * E :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ((2 * X : ℝ) / (h : ℝ) ^ 3) * C *
        (∫ u in 0..b₀, u ^ 2) * E := by
      have hint : (∫ u in 0..b₀, C * u ^ 2 * E) =
          C * (∫ u in 0..b₀, u ^ 2) * E := by
        rw [intervalIntegral.integral_mul_const,
          intervalIntegral.integral_const_mul]
      rw [hint]
      ring
    _ = _ := by rfl

/-- Reciprocal-frequency shell bound for the shifted source smoothing
piece. -/
theorem sum_normSq_sourceSmoothedRightOn_le_shellEnergy
    (F : ℝ → ℂ) (hF : Continuous F) {X h : ℕ}
    (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X)
    {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (sourceSmoothedRightOn F x h A B)) ≤
      ((2 * X : ℝ) / (h : ℝ) ^ 3) *
        ((3 * X : ℝ) ^ 2 *
          (B - A + 2 * Real.pi * (3 * X : ℕ))) *
        (∫ u in 0..(2 * h : ℝ) / X, ((2 + u) / T) ^ 2) *
        ∫ t in A..B, Complex.normSq (F t) := by
  classical
  let b₀ : ℝ := (2 * h : ℝ) / X
  let C : ℝ := (3 * X : ℝ) ^ 2 *
    (B - A + 2 * Real.pi * (3 * X : ℕ))
  let E : ℝ := ∫ t in A..B, Complex.normSq (F t)
  have hb₀ : 0 ≤ b₀ := by dsimp [b₀]; positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    have : 0 ≤ B - A + 2 * Real.pi * (3 * X : ℕ) := by positivity
    positivity
  have hsum (u : ℝ) (hu : u ∈ Set.Icc 0 b₀) :
      (∑ x ∈ Finset.Ioc X (2 * X),
          Complex.normSq
            (safeSmoothedLogTransformOn F u (x + h) A B)) ≤
        C * ((2 + u) / T) ^ 2 * E := by
    by_cases hu0 : u = 0
    · subst u
      simp
      have hE : 0 ≤ E := by
        dsimp [E]
        exact intervalIntegral.integral_nonneg_of_forall hAB
          (fun t ↦ Complex.normSq_nonneg _)
      positivity
    · have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have hplan := sum_normSq_safeSmoothedLogTransformOn_shift_le
        F hF hX hh hhX hupos hAB
      have hmul := integral_normSq_mul_perronRatioIncrement_le_div
        F hF hupos hAB hT haway
      calc
        (∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq
              (safeSmoothedLogTransformOn F u (x + h) A B)) ≤
          C * ∫ t in A..B,
            Complex.normSq (F t * perronRatioIncrement u t) := by
          simpa only [C]
        _ ≤ C * (((2 + u) / T) ^ 2 * E) :=
          mul_le_mul_of_nonneg_left hmul hC
        _ = C * ((2 + u) / T) ^ 2 * E := by ring
  have hsumCont : Continuous (fun u ↦
      ∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq
          (safeSmoothedLogTransformOn F u (x + h) A B)) := by
    apply continuous_finsetSum
    intro x hxmem
    exact Complex.continuous_normSq.comp
      (continuous_safeSmoothedLogTransformOn F hF (x + h)
        (by have := Finset.mem_Ioc.mp hxmem; omega) A B)
  have hrightCont : Continuous
      (fun u ↦ C * ((2 + u) / T) ^ 2 * E) := by fun_prop
  have hmono :
      (∫ u in 0..b₀,
          ∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq
              (safeSmoothedLogTransformOn F u (x + h) A B)) ≤
        ∫ u in 0..b₀, C * ((2 + u) / T) ^ 2 * E := by
    exact intervalIntegral.integral_mono_on hb₀
      (hsumCont.intervalIntegrable 0 b₀)
      (hrightCont.intervalIntegrable 0 b₀) hsum
  have huniform := sum_normSq_sourceSmoothedRightOn_le_uniform
    F hF hX hh hhX (A := A) (B := B)
  calc
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (sourceSmoothedRightOn F x h A B)) ≤
      ((2 * X : ℝ) / (h : ℝ) ^ 3) *
        ∫ u in 0..b₀,
          ∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq
              (safeSmoothedLogTransformOn F u (x + h) A B) := by
      simpa only [b₀] using huniform
    _ ≤ ((2 * X : ℝ) / (h : ℝ) ^ 3) *
        ∫ u in 0..b₀, C * ((2 + u) / T) ^ 2 * E :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ((2 * X : ℝ) / (h : ℝ) ^ 3) * C *
        (∫ u in 0..b₀, ((2 + u) / T) ^ 2) * E := by
      have hint : (∫ u in 0..b₀, C * ((2 + u) / T) ^ 2 * E) =
          C * (∫ u in 0..b₀, ((2 + u) / T) ^ 2) * E := by
        rw [intervalIntegral.integral_mul_const,
          intervalIntegral.integral_const_mul]
      rw [hint]
      ring
    _ = _ := by rfl

/-- Combine bounds for the two source smoothing pieces into a bound for
one normalized Perron segment. -/
theorem sum_normSq_perronKernelSegmentOn_le_of_sourceBounds
    (F : ℝ → ℂ) (hF : Continuous F) {X h : ℕ}
    (hX : 0 < X) (hh : 0 < h) (A B Eₗ Eᵣ : ℝ)
    (hleft : (∑ x ∈ Finset.Ioc X (2 * X),
      Complex.normSq (sourceSmoothedLeftOn F x h A B)) ≤ Eₗ)
    (hright : (∑ x ∈ Finset.Ioc X (2 * X),
      Complex.normSq (sourceSmoothedRightOn F x h A B)) ≤ Eᵣ) :
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (perronKernelSegmentOn F x h A B)) ≤
      2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) * (Eₗ + Eᵣ) := by
  classical
  let c : ℂ := (((2 * Real.pi : ℝ) : ℂ))⁻¹
  have hpoint (x : ℕ) (hxmem : x ∈ Finset.Ioc X (2 * X)) :
      Complex.normSq (perronKernelSegmentOn F x h A B) ≤
        2 * Complex.normSq c *
          (Complex.normSq (sourceSmoothedLeftOn F x h A B) +
            Complex.normSq (sourceSmoothedRightOn F x h A B)) := by
    have hx : 0 < x := by have := Finset.mem_Ioc.mp hxmem; omega
    rw [perronKernelSegmentOn_eq_sourceSmoothed F hF hx hh A B,
      Complex.normSq_mul]
    have hsub := normSq_sub_le_two_mul_add
      (sourceSmoothedLeftOn F x h A B)
      (sourceSmoothedRightOn F x h A B)
    dsimp [c]
    exact (mul_le_mul_of_nonneg_left hsub (Complex.normSq_nonneg _)).trans_eq
      (by ring)
  calc
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (perronKernelSegmentOn F x h A B)) ≤
      ∑ x ∈ Finset.Ioc X (2 * X),
        2 * Complex.normSq c *
          (Complex.normSq (sourceSmoothedLeftOn F x h A B) +
            Complex.normSq (sourceSmoothedRightOn F x h A B)) :=
      Finset.sum_le_sum hpoint
    _ = 2 * Complex.normSq c *
        ((∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq (sourceSmoothedLeftOn F x h A B)) +
          ∑ x ∈ Finset.Ioc X (2 * X),
            Complex.normSq (sourceSmoothedRightOn F x h A B)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 * Complex.normSq c * (Eₗ + Eᵣ) := by
      apply mul_le_mul_of_nonneg_left
      · linarith
      · exact mul_nonneg (by norm_num) (Complex.normSq_nonneg c)
    _ = _ := by rfl

/-- Explicit central/original-polynomial source bound for a single
normalized Perron segment. -/
theorem sum_normSq_perronKernelSegmentOn_le_verticalEnergy
    (F : ℝ → ℂ) (hF : Continuous F) {X h : ℕ}
    (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X)
    {A B : ℝ} (hAB : A ≤ B) :
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (perronKernelSegmentOn F x h A B)) ≤
      2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
        (((X : ℝ) / (h : ℝ) ^ 3) *
          ((2 * X : ℝ) ^ 2 *
            (B - A + 2 * Real.pi * (2 * X : ℕ))) *
          (∫ u in (h : ℝ) / (2 * X)..3 * h / X, u ^ 2) *
          (∫ t in A..B, Complex.normSq (F t)) +
        ((2 * X : ℝ) / (h : ℝ) ^ 3) *
          ((3 * X : ℝ) ^ 2 *
            (B - A + 2 * Real.pi * (3 * X : ℕ))) *
          (∫ u in 0..(2 * h : ℝ) / X, u ^ 2) *
          (∫ t in A..B, Complex.normSq (F t))) := by
  exact sum_normSq_perronKernelSegmentOn_le_of_sourceBounds
    F hF hX hh A B _ _
      (sum_normSq_sourceSmoothedLeftOn_le_verticalEnergy F hF hX hh hAB)
      (sum_normSq_sourceSmoothedRightOn_le_verticalEnergy F hF hX hh hhX hAB)

/-- Explicit far-shell source bound for a single normalized Perron
segment. -/
theorem sum_normSq_perronKernelSegmentOn_le_shellEnergy
    (F : ℝ → ℂ) (hF : Continuous F) {X h : ℕ}
    (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X)
    {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (perronKernelSegmentOn F x h A B)) ≤
      2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
        (((X : ℝ) / (h : ℝ) ^ 3) *
          ((2 * X : ℝ) ^ 2 *
            (B - A + 2 * Real.pi * (2 * X : ℕ))) *
          (∫ u in (h : ℝ) / (2 * X)..3 * h / X,
            ((2 + u) / T) ^ 2) *
          (∫ t in A..B, Complex.normSq (F t)) +
        ((2 * X : ℝ) / (h : ℝ) ^ 3) *
          ((3 * X : ℝ) ^ 2 *
            (B - A + 2 * Real.pi * (3 * X : ℕ))) *
          (∫ u in 0..(2 * h : ℝ) / X, ((2 + u) / T) ^ 2) *
          (∫ t in A..B, Complex.normSq (F t))) := by
  exact sum_normSq_perronKernelSegmentOn_le_of_sourceBounds
    F hF hX hh A B _ _
      (sum_normSq_sourceSmoothedLeftOn_le_shellEnergy
        F hF hX hh hAB hT haway)
      (sum_normSq_sourceSmoothedRightOn_le_shellEnergy
        F hF hX hh hhX hAB hT haway)

/-- Named central-band bound, for concise use in the two-length assembly. -/
def sourceSingleVerticalEnergyBound
    (F : ℝ → ℂ) (X h : ℕ) (A B : ℝ) : ℝ :=
  2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
    (((X : ℝ) / (h : ℝ) ^ 3) *
      ((2 * X : ℝ) ^ 2 *
        (B - A + 2 * Real.pi * (2 * X : ℕ))) *
      (∫ u in (h : ℝ) / (2 * X)..3 * h / X, u ^ 2) *
      (∫ t in A..B, Complex.normSq (F t)) +
    ((2 * X : ℝ) / (h : ℝ) ^ 3) *
      ((3 * X : ℝ) ^ 2 *
        (B - A + 2 * Real.pi * (3 * X : ℕ))) *
      (∫ u in 0..(2 * h : ℝ) / X, u ^ 2) *
      (∫ t in A..B, Complex.normSq (F t)))

/-- Named reciprocal-frequency shell bound. -/
def sourceSingleShellEnergyBound
    (F : ℝ → ℂ) (X h : ℕ) (A B T : ℝ) : ℝ :=
  2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
    (((X : ℝ) / (h : ℝ) ^ 3) *
      ((2 * X : ℝ) ^ 2 *
        (B - A + 2 * Real.pi * (2 * X : ℕ))) *
      (∫ u in (h : ℝ) / (2 * X)..3 * h / X,
        ((2 + u) / T) ^ 2) *
      (∫ t in A..B, Complex.normSq (F t)) +
    ((2 * X : ℝ) / (h : ℝ) ^ 3) *
      ((3 * X : ℝ) ^ 2 *
        (B - A + 2 * Real.pi * (3 * X : ℕ))) *
      (∫ u in 0..(2 * h : ℝ) / X, ((2 + u) / T) ^ 2) *
      (∫ t in A..B, Complex.normSq (F t)))

theorem sum_normSq_perronKernelSegmentOn_le_sourceSingleVerticalEnergyBound
    (F : ℝ → ℂ) (hF : Continuous F) {X h : ℕ}
    (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X)
    {A B : ℝ} (hAB : A ≤ B) :
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (perronKernelSegmentOn F x h A B)) ≤
      sourceSingleVerticalEnergyBound F X h A B := by
  simpa only [sourceSingleVerticalEnergyBound] using
    sum_normSq_perronKernelSegmentOn_le_verticalEnergy
      F hF hX hh hhX hAB

theorem sum_normSq_perronKernelSegmentOn_le_sourceSingleShellEnergyBound
    (F : ℝ → ℂ) (hF : Continuous F) {X h : ℕ}
    (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X)
    {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq (perronKernelSegmentOn F x h A B)) ≤
      sourceSingleShellEnergyBound F X h A B T := by
  simpa only [sourceSingleShellEnergyBound] using
    sum_normSq_perronKernelSegmentOn_le_shellEnergy
      F hF hX hh hhX hAB hT haway

end

end Erdos67
