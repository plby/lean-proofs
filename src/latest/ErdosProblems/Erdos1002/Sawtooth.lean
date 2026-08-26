import ErdosProblems.Erdos1002.Statement
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The sawtooth and Bernoulli mark in Erdős Problem 1002

This file establishes the elementary real-analytic facts used by the
Fourier--Ramanujan reconstruction.  In particular, the endpoint jump of the
sawtooth is retained: its range is the half-open interval `(-1 / 2, 1 / 2]`.

The Fourier coefficients below use mathlib's `fourierCoeffOn` convention,
whose `n`-th coefficient on `[0, 1]` integrates against `exp (-2 * π * I * n * x)`.
Thus the sign in `sawtooth_fourierCoeff_nonzero` is the sign used in the paper.
No pointwise Fourier-series identity is asserted here.
-/

open MeasureTheory Set
open scoped ComplexConjugate Real

namespace Erdos1002

noncomputable section

/-! ## Pointwise and periodicity facts -/

/-- The sawtooth is unchanged by every integral translation. -/
theorem sawtooth_add_intCast (x : ℝ) (m : ℤ) :
    sawtooth (x + (m : ℝ)) = sawtooth x := by
  simp [sawtooth, Int.fract_add_intCast]

/-- The sawtooth has period one. -/
theorem sawtooth_periodic : Function.Periodic sawtooth 1 := by
  intro x
  simpa using! sawtooth_add_intCast x 1

@[simp]
theorem sawtooth_intCast (m : ℤ) : sawtooth (m : ℝ) = 1 / 2 := by
  simp [sawtooth]

/-- On the fundamental half-open cell `[0, 1)`, the sawtooth is linear. -/
theorem sawtooth_eq_half_sub {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    sawtooth x = 1 / 2 - x := by
  rw [sawtooth, Int.fract_eq_self.2 hx]

/-- The sharp half-open range of the centered sawtooth. -/
theorem sawtooth_mem_Ioc (x : ℝ) : sawtooth x ∈ Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
  constructor
  · dsimp [sawtooth]
    have h := Int.fract_lt_one x
    linarith
  · dsimp [sawtooth]
    have h := Int.fract_nonneg x
    linarith

/-- The uniform sharp absolute-value bound for the sawtooth. -/
theorem abs_sawtooth_le_half (x : ℝ) : |sawtooth x| ≤ (1 / 2 : ℝ) := by
  rw [abs_le]
  exact ⟨(sawtooth_mem_Ioc x).1.le, (sawtooth_mem_Ioc x).2⟩

/-- The periodic Bernoulli mark `V(x) = {x}(1 - {x}) / 2` from the paper. -/
def bernoulliMark (x : ℝ) : ℝ :=
  Int.fract x * (1 - Int.fract x) / 2

/-- The Bernoulli mark is unchanged by every integral translation. -/
theorem bernoulliMark_add_intCast (x : ℝ) (m : ℤ) :
    bernoulliMark (x + (m : ℝ)) = bernoulliMark x := by
  simp [bernoulliMark, Int.fract_add_intCast]

/-- The Bernoulli mark has period one. -/
theorem bernoulliMark_periodic : Function.Periodic bernoulliMark 1 := by
  intro x
  simpa using! bernoulliMark_add_intCast x 1

@[simp]
theorem bernoulliMark_intCast (m : ℤ) : bernoulliMark (m : ℝ) = 0 := by
  simp [bernoulliMark]

/-- On `[0, 1)`, the Bernoulli mark is its defining quadratic polynomial. -/
theorem bernoulliMark_eq_quadratic {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    bernoulliMark x = x * (1 - x) / 2 := by
  rw [bernoulliMark, Int.fract_eq_self.2 hx]

/-- The upper bound for the Bernoulli mark is attained at `1 / 2`. -/
theorem bernoulliMark_half : bernoulliMark (1 / 2 : ℝ) = 1 / 8 := by
  rw [bernoulliMark_eq_quadratic (by constructor <;> norm_num)]
  norm_num

theorem bernoulliMark_nonneg (x : ℝ) : 0 ≤ bernoulliMark x := by
  dsimp [bernoulliMark]
  exact div_nonneg
    (mul_nonneg (Int.fract_nonneg x) (sub_nonneg.mpr (Int.fract_lt_one x).le)) (by norm_num)

/-- The sharp pointwise upper bound `V ≤ 1 / 8`. -/
theorem bernoulliMark_le_one_eighth (x : ℝ) : bernoulliMark x ≤ (1 / 8 : ℝ) := by
  dsimp [bernoulliMark]
  have h0 := Int.fract_nonneg x
  have h1 := (Int.fract_lt_one x).le
  nlinarith [sq_nonneg (Int.fract x - 1 / 2)]

theorem abs_bernoulliMark_le_one_eighth (x : ℝ) :
    |bernoulliMark x| ≤ (1 / 8 : ℝ) := by
  rw [abs_of_nonneg (bernoulliMark_nonneg x)]
  exact bernoulliMark_le_one_eighth x

/-- Although `Int.fract` jumps at the integers, the two endpoint values of
`u(1-u)/2` agree.  Hence the periodic Bernoulli mark is globally continuous. -/
theorem continuous_bernoulliMark : Continuous bernoulliMark := by
  let q : ℝ → ℝ := fun u ↦ u * (1 - u) / 2
  have hq : Continuous q := by
    dsimp [q]
    fun_prop
  have hend : q 0 = q 1 := by
    dsimp [q]
    norm_num
  simpa only [bernoulliMark, q, Function.comp_apply] using!
    hq.continuousOn.comp_fract'' hend

/-! ## Measurability and local integrability -/

theorem sawtooth_measurable : Measurable sawtooth := by
  exact measurable_const.sub measurable_id.fract

theorem bernoulliMark_measurable : Measurable bernoulliMark := by
  exact (measurable_id.fract.mul (measurable_const.sub measurable_id.fract)).div_const 2

theorem integrableOn_sawtooth_uIcc (a b : ℝ) :
    IntegrableOn sawtooth (uIcc a b) volume := by
  apply Measure.integrableOn_of_bounded (by
    rw [uIcc]
    exact measure_Icc_lt_top.ne)
    sawtooth_measurable.aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs] using! abs_sawtooth_le_half x

theorem intervalIntegrable_sawtooth (a b : ℝ) :
    IntervalIntegrable sawtooth volume a b :=
  (integrableOn_sawtooth_uIcc a b).intervalIntegrable

theorem integrableOn_bernoulliMark_uIcc (a b : ℝ) :
    IntegrableOn bernoulliMark (uIcc a b) volume := by
  apply Measure.integrableOn_of_bounded (by
    rw [uIcc]
    exact measure_Icc_lt_top.ne)
    bernoulliMark_measurable.aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs] using! abs_bernoulliMark_le_one_eighth x

theorem intervalIntegrable_bernoulliMark (a b : ℝ) :
    IntervalIntegrable bernoulliMark volume a b :=
  (integrableOn_bernoulliMark_uIcc a b).intervalIntegrable

/-! ## One-period integrals -/

theorem bernoulliMark_ae_eq_quadratic :
    bernoulliMark =ᵐ[volume.restrict (uIoc (0 : ℝ) 1)]
      (fun x : ℝ => x * (1 - x) / 2) := by
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  rw [uIoc_of_le (by norm_num)] at hx
  rcases hx.2.eq_or_lt with rfl | hlt
  · simp [bernoulliMark]
  · exact bernoulliMark_eq_quadratic ⟨hx.1.le, hlt⟩

/-- The exact one-period mean of the Bernoulli mark. -/
theorem integral_bernoulliMark : ∫ x in (0 : ℝ)..1, bernoulliMark x = 1 / 12 := by
  rw [intervalIntegral.integral_congr_ae_restrict bernoulliMark_ae_eq_quadratic]
  have hpoly : (fun x : ℝ => x * (1 - x) / 2) =
      (fun x : ℝ => x / 2 - x ^ 2 / 2) := by
    funext x
    ring
  rw [hpoly]
  calc
    (∫ x in (0 : ℝ)..1, x / 2 - x ^ 2 / 2) =
        (∫ x in (0 : ℝ)..1, x / 2) - ∫ x in (0 : ℝ)..1, x ^ 2 / 2 := by
      exact intervalIntegral.integral_sub
        ((continuous_id.div_const 2).intervalIntegrable 0 1)
        (((continuous_id.pow 2).div_const 2).intervalIntegrable 0 1)
    _ = 1 / 12 := by norm_num [intervalIntegral.integral_div, integral_pow]

/-- The centered sawtooth has zero mean on one period. -/
theorem integral_sawtooth_zero : ∫ x in (0 : ℝ)..1, sawtooth x = 0 := by
  rw [intervalIntegral.integral_congr_ae_restrict
    (show sawtooth =ᵐ[volume.restrict (uIoc (0 : ℝ) 1)]
      (fun x : ℝ => 1 / 2 - x) by
      filter_upwards [ae_restrict_mem measurableSet_uIoc,
        (volume.restrict (uIoc (0 : ℝ) 1)).ae_ne 1] with x hx hne
      rw [uIoc_of_le (by norm_num)] at hx
      have hlt : x < 1 := lt_of_le_of_ne hx.2 hne
      rw [sawtooth, Int.fract_eq_self.2 ⟨hx.1.le, hlt⟩])]
  calc
    (∫ x in (0 : ℝ)..1, 1 / 2 - x) =
        (∫ _x in (0 : ℝ)..1, (1 / 2 : ℝ)) - ∫ x in (0 : ℝ)..1, x := by
      exact intervalIntegral.integral_sub intervalIntegrable_const
        (continuous_id.intervalIntegrable 0 1)
    _ = 0 := by norm_num [integral_id]

/-! ## Fourier coefficients on one period -/

private def linearSaw (x : ℝ) : ℂ := ((1 / 2 - x : ℝ) : ℂ)

private def quadraticMark (x : ℝ) : ℂ := ((x * (1 - x) / 2 : ℝ) : ℂ)

private theorem sawtooth_ae_eq_linearSaw :
    (fun x : ℝ => (sawtooth x : ℂ)) =ᵐ[volume.restrict (Ioc 0 1)] linearSaw := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    (volume.restrict (Ioc (0 : ℝ) 1)).ae_ne 1] with x hx hne
  have hlt : x < 1 := lt_of_le_of_ne hx.2 hne
  rw [sawtooth, Int.fract_eq_self.2 ⟨hx.1.le, hlt⟩]
  rfl

private theorem coeff_const (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun _ : ℝ => (-1 : ℂ)) n = 0 := by
  rw [fourierCoeffOn_of_hasDerivAt (by norm_num) hn
    (f' := fun _ : ℝ => (0 : ℂ))]
  · have hz : fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
        (fun _ : ℝ => (0 : ℂ)) n = 0 := by
      simp [fourierCoeffOn, fourierCoeff, AddCircle.liftIoc, Set.restrict_def]
    rw [hz]
    ring
  · intro x hx
    exact hasDerivAt_const x (-1 : ℂ)
  · exact intervalIntegrable_const

private theorem coeff_linear (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) linearSaw n =
      1 / (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
  rw [fourierCoeffOn_of_hasDerivAt (by norm_num) hn
    (f' := fun _ : ℝ => (-1 : ℂ))]
  · rw [coeff_const n hn]
    simp [linearSaw]
  · intro x hx
    have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using! (Complex.ofRealCLM.hasFDerivAt (x := x)).hasDerivAt
    convert! (hasDerivAt_const x ((1 / 2 : ℝ) : ℂ)).sub hid using 1
    · ext y
      simp [linearSaw]
    · norm_num
  · exact intervalIntegrable_const

/-- For nonzero `n`, the sawtooth coefficient against `exp (-2πinx)` is `1 / (2πin)`. -/
theorem sawtooth_fourierCoeff_nonzero (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
        (fun x : ℝ => (sawtooth x : ℂ)) n =
      1 / (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
  have hcongr := fourierCoeffOn_congr_ae (show (0 : ℝ) < 1 by norm_num)
    sawtooth_ae_eq_linearSaw
  rw [congrFun hcongr n, coeff_linear n hn]

/-- The zeroth Fourier coefficient of the centered sawtooth vanishes. -/
theorem sawtooth_fourierCoeff_zero :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
        (fun x : ℝ => (sawtooth x : ℂ)) 0 = 0 := by
  rw [fourierCoeffOn_eq_integral]
  simp
  rw [intervalIntegral.integral_ofReal, integral_sawtooth_zero]
  norm_num

private theorem coeff_quadraticMark (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) quadraticMark n =
      -1 / (4 * (Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 2) := by
  rw [fourierCoeffOn_of_hasDerivAt (by norm_num) hn (f' := linearSaw)]
  · rw [coeff_linear n hn]
    simp [quadraticMark]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    field_simp [hnC, Real.pi_ne_zero]
    simp [Complex.I_sq]
    norm_num
  · intro x hx
    unfold quadraticMark linearSaw
    have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using! (Complex.ofRealCLM.hasFDerivAt (x := x)).hasDerivAt
    convert! (hid.mul ((hasDerivAt_const x (1 : ℂ)).sub hid)).div_const 2 using 1
    · ext y
      simp only [Pi.mul_apply, Pi.sub_apply]
      push_cast
      ring
    · push_cast
      simp only [Pi.sub_apply]
      ring
  · apply Continuous.intervalIntegrable
    unfold linearSaw
    fun_prop

private theorem bernoulliMark_ae_eq_quadraticMark :
    (fun x : ℝ => (bernoulliMark x : ℂ)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      quadraticMark := by
  have h := bernoulliMark_ae_eq_quadratic
  rw [uIoc_of_le (by norm_num)] at h
  filter_upwards [h] with x hx
  simp [quadraticMark, hx]

/-- The nonzero Fourier coefficients of `V` agree with the paper's formula. -/
theorem bernoulliMark_fourierCoeff_nonzero (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
        (fun x : ℝ => (bernoulliMark x : ℂ)) n =
      -1 / (4 * (Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 2) := by
  have hcongr := fourierCoeffOn_congr_ae (show (0 : ℝ) < 1 by norm_num)
    bernoulliMark_ae_eq_quadraticMark
  rw [congrFun hcongr n, coeff_quadraticMark n hn]

/-- The zeroth Fourier coefficient of `V` is its mean `1 / 12`. -/
theorem bernoulliMark_fourierCoeff_zero :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
        (fun x : ℝ => (bernoulliMark x : ℂ)) 0 = (1 / 12 : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  simp
  rw [intervalIntegral.integral_ofReal, integral_bernoulliMark]
  norm_num

end

end Erdos1002
