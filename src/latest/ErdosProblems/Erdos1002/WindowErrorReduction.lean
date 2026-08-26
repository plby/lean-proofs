import ErdosProblems.Erdos1002.PVPeriodization
import ErdosProblems.Erdos1002.ReconstructionCoefficients
import ErdosProblems.Erdos1002.RamanujanIncompleteOrthogonality
import ErdosProblems.Erdos1002.Shots
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite reductions for the nearest-cell window error

This file isolates the fully finite part of Proposition 2.2 of the
manuscript.  There are two complementary reductions.

* `pvWindowErrorTruncation` is the literal difference between the nearest
  primitive-cell sum and the residue-wise symmetric finite cutoff used to
  define the principal-value periodization.  We prove its exact
  denominator decomposition, measurability, and interval integrability.
  Thus no principal-value sum is interchanged with an integral here.

* `windowModeCoefficient` is the finite arithmetic coefficient
  `C_ℓ(n)` from the proof of the window estimate.  Finite Fourier
  polynomials made from these coefficients satisfy exact Parseval
  identities.  A weighted finite Cauchy--Schwarz argument then reduces
  their squared `L²` norm to an explicit finite nonnegative arithmetic
  sum, retaining every divisor, endpoint, carrier, and weight.

The remaining analytic frontier is deliberately not encoded as an
assumption: one must still identify the Fourier coefficients of the
cotangent window with `windowKernelCoefficient`, prove their uniform decay,
and pass from the finite cutoffs below to the actual principal-value and
full Fourier limits.
-/

open Filter MeasureTheory Set
open scoped ArithmeticFunction.sigma BigOperators ComplexConjugate ENNReal Real

namespace Erdos1002

noncomputable section

/-! ## The literal finite nearest-cell/PV-cutoff difference -/

/-- The contribution of one denominator to the difference between the
nearest primitive cell and the residue-wise symmetric periodization
cutoff. -/
def pvWindowErrorDenominatorTerm (N R p : ℕ) (α : ℝ) : ℂ :=
  (primitiveShot N p α : ℂ) -
    ∑ a ∈ reducedResidues p, residuePeriodizationTruncation N p a R α

/-- The literal finite approximation to `Y_{N,P} - Z_{N,P}`. -/
def pvWindowErrorTruncation (N P R : ℕ) (α : ℝ) : ℂ :=
  (primitiveShotSum N P α : ℂ) - pvPeriodizationTruncation N P R α

/-- Exact denominator-by-denominator decomposition of the finite window
error.  Both sides are finite sums. -/
theorem pvWindowErrorTruncation_eq_sum_denominators
    (N P R : ℕ) (α : ℝ) :
    pvWindowErrorTruncation N P R α =
      ∑ p ∈ Finset.Icc 1 P, pvWindowErrorDenominatorTerm N R p α := by
  simp only [pvWindowErrorTruncation, primitiveShotSum,
    pvPeriodizationTruncation, pvWindowErrorDenominatorTerm,
    Complex.ofReal_sum]
  rw [Finset.sum_sub_distrib]

private theorem measurable_transformKernel_window (N : ℕ) :
    Measurable (transformKernel N) := by
  unfold transformKernel
  exact Measurable.ite
    (by simpa only [Set.setOf_eq_eq_singleton] using!
      (measurableSet_singleton (0 : ℝ)))
    measurable_const
    ((bernoulliMark_measurable.comp
      (measurable_const.mul measurable_id)).div measurable_id)

/-- Every single finite periodization cell is measurable. -/
theorem measurable_periodizationCell_window (N p : ℕ) (q : ℤ) :
    Measurable (periodizationCell N p q) := by
  unfold periodizationCell
  exact (measurable_transformKernel_window N).complex_ofReal.const_mul _ |>.comp
    (measurable_const.mul measurable_id |>.sub measurable_const)

/-- A residue-wise finite cutoff is measurable. -/
theorem measurable_residuePeriodizationTruncation_window
    (N p a R : ℕ) :
    Measurable (residuePeriodizationTruncation N p a R) := by
  unfold residuePeriodizationTruncation
  exact Finset.measurable_fun_sum (Finset.range (2 * R + 1)) fun r _ ↦
    measurable_periodizationCell_window N p (residueCutoffQ p a R r)

/-- The full finite `p`, residue, and symmetric-cutoff periodization is
measurable. -/
theorem measurable_pvPeriodizationTruncation_window (N P R : ℕ) :
    Measurable (pvPeriodizationTruncation N P R) := by
  unfold pvPeriodizationTruncation
  apply Finset.measurable_fun_sum
  intro p _hp
  exact Finset.measurable_fun_sum (reducedResidues p) fun a _ ↦
    measurable_residuePeriodizationTruncation_window N p a R

theorem measurable_pvWindowErrorDenominatorTerm (N R p : ℕ) :
    Measurable (pvWindowErrorDenominatorTerm N R p) := by
  unfold pvWindowErrorDenominatorTerm
  exact (measurable_primitiveShot N p).complex_ofReal.sub
    (Finset.measurable_fun_sum (reducedResidues p) fun a _ ↦
      measurable_residuePeriodizationTruncation_window N p a R)

/-- The literal finite window error is measurable. -/
theorem measurable_pvWindowErrorTruncation (N P R : ℕ) :
    Measurable (pvWindowErrorTruncation N P R) := by
  unfold pvWindowErrorTruncation
  exact (measurable_primitiveShotSum N P).complex_ofReal.sub
    (measurable_pvPeriodizationTruncation_window N P R)

/-- The cancellation in `V(Nx)/x` gives a uniform local bound, including
the totalized value at `x = 0`. -/
theorem norm_transformKernel_le_half_N_window (N : ℕ) (x : ℝ) :
    ‖transformKernel N x‖ ≤ (N : ℝ) / 2 := by
  by_cases hx : x = 0
  · simp [transformKernel, hx, div_nonneg]
  · rw [transformKernel, if_neg hx, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (bernoulliMark_nonneg _)]
    have hxabs : 0 < |x| := abs_pos.mpr hx
    apply (div_le_iff₀ hxabs).2
    have hmark : bernoulliMark ((N : ℝ) * x) ≤ |(N : ℝ) * x| / 2 := by
      rcases le_total 0 ((N : ℝ) * x) with hy | hy
      · have hfloor : (0 : ℝ) ≤ (⌊(N : ℝ) * x⌋ : ℤ) := by
          exact_mod_cast Int.floor_nonneg.mpr hy
        have hfract_le : Int.fract ((N : ℝ) * x) ≤ (N : ℝ) * x := by
          rw [Int.fract]
          linarith
        rw [abs_of_nonneg hy]
        dsimp [bernoulliMark]
        nlinarith [Int.fract_nonneg ((N : ℝ) * x),
          (Int.fract_lt_one ((N : ℝ) * x)).le]
      · have hny : 0 ≤ -((N : ℝ) * x) := neg_nonneg.mpr hy
        rw [← bernoulliMark_neg ((N : ℝ) * x),
          ← abs_neg ((N : ℝ) * x), abs_of_nonneg hny]
        have hfloor : (0 : ℝ) ≤ (⌊-((N : ℝ) * x)⌋ : ℤ) := by
          exact_mod_cast Int.floor_nonneg.mpr hny
        have hfract_le :
            Int.fract (-((N : ℝ) * x)) ≤ -((N : ℝ) * x) := by
          rw [Int.fract]
          linarith
        dsimp [bernoulliMark]
        nlinarith [Int.fract_nonneg (-((N : ℝ) * x)),
          (Int.fract_lt_one (-((N : ℝ) * x))).le]
    calc
      bernoulliMark ((N : ℝ) * x) ≤ |(N : ℝ) * x| / 2 := hmark
      _ = ((N : ℝ) / 2) * |x| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
        ring

private theorem primitiveShot_eq_transformKernel
    (N p : ℕ) (α : ℝ) (hp : 0 < p) :
    (primitiveShot N p α : ℂ) =
      if IsPrimitiveResonance p α then
        (((1 / (p : ℝ) : ℝ) *
          transformKernel N (resonanceDelta p α) : ℝ) : ℂ)
      else 0 := by
  by_cases hprimitive : IsPrimitiveResonance p α
  · rw [if_pos hprimitive, primitiveShot_of_primitive N p α hprimitive]
    by_cases hδ : resonanceDelta p α = 0
    · simp [hδ, transformKernel]
    · rw [transformKernel, if_neg hδ]
      push_cast
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      field_simp [hpR, hδ]
  · rw [if_neg hprimitive, primitiveShot_of_not_primitive N p α hprimitive]
    norm_num

/-- A primitive nearest-cell shot has the same uniform local bound as one
periodization cell. -/
theorem norm_primitiveShot_le (N p : ℕ) (α : ℝ) (hp : 0 < p) :
    ‖(primitiveShot N p α : ℂ)‖ ≤ (N : ℝ) / (2 * (p : ℝ)) := by
  rw [primitiveShot_eq_transformKernel N p α hp]
  split_ifs with hprimitive
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ))]
    calc
      (1 / (p : ℝ)) * |transformKernel N (resonanceDelta p α)| ≤
          (1 / (p : ℝ)) * ((N : ℝ) / 2) := by
        gcongr
        simpa only [Real.norm_eq_abs] using!
          norm_transformKernel_le_half_N_window N (resonanceDelta p α)
      _ = (N : ℝ) / (2 * (p : ℝ)) := by ring
  · simp [div_nonneg]

/-- One periodization cell has the same explicit bound as one nearest
primitive shot. -/
theorem norm_periodizationCell_le
    (N p : ℕ) (q : ℤ) (α : ℝ) (hp : 0 < p) :
    ‖periodizationCell N p q α‖ ≤ (N : ℝ) / (2 * (p : ℝ)) := by
  rw [periodizationCell, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ))]
  calc
    (1 / (p : ℝ)) *
        |transformKernel N ((p : ℝ) * α - (q : ℝ))| ≤
      (1 / (p : ℝ)) * ((N : ℝ) / 2) := by
        gcongr
        simpa only [Real.norm_eq_abs] using!
          norm_transformKernel_le_half_N_window N
            ((p : ℝ) * α - (q : ℝ))
    _ = (N : ℝ) / (2 * (p : ℝ)) := by ring

/-- A completely explicit nonnegative majorant for the finite cutoff
error.  It is intentionally left as a finite sum, so no estimate for
Euler's totient or a harmonic sum is hidden. -/
def pvWindowErrorMajorant (N P R : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 P,
    ((N : ℝ) / (2 * (p : ℝ)) +
      ∑ _a ∈ reducedResidues p,
        ∑ _r ∈ Finset.range (2 * R + 1),
          (N : ℝ) / (2 * (p : ℝ)))

theorem pvWindowErrorMajorant_nonneg (N P R : ℕ) :
    0 ≤ pvWindowErrorMajorant N P R := by
  unfold pvWindowErrorMajorant
  positivity

/-- Pointwise domination of the literal finite cutoff error. -/
theorem norm_pvWindowErrorTruncation_le
    (N P R : ℕ) (α : ℝ) :
    ‖pvWindowErrorTruncation N P R α‖ ≤ pvWindowErrorMajorant N P R := by
  rw [pvWindowErrorTruncation_eq_sum_denominators]
  calc
    ‖∑ p ∈ Finset.Icc 1 P, pvWindowErrorDenominatorTerm N R p α‖ ≤
        ∑ p ∈ Finset.Icc 1 P,
          ‖pvWindowErrorDenominatorTerm N R p α‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.Icc 1 P,
        ((N : ℝ) / (2 * (p : ℝ)) +
          ∑ a ∈ reducedResidues p,
            ∑ _r ∈ Finset.range (2 * R + 1),
              (N : ℝ) / (2 * (p : ℝ))) := by
      gcongr with p hpMem
      have hp : 0 < p := (Finset.mem_Icc.mp hpMem).1
      unfold pvWindowErrorDenominatorTerm
      calc
        ‖(primitiveShot N p α : ℂ) -
            ∑ a ∈ reducedResidues p,
              residuePeriodizationTruncation N p a R α‖ ≤
          ‖(primitiveShot N p α : ℂ)‖ +
            ‖∑ a ∈ reducedResidues p,
              residuePeriodizationTruncation N p a R α‖ := norm_sub_le _ _
        _ ≤ (N : ℝ) / (2 * (p : ℝ)) +
            ∑ a ∈ reducedResidues p,
              ‖residuePeriodizationTruncation N p a R α‖ := by
          gcongr
          · exact norm_primitiveShot_le N p α hp
          · exact norm_sum_le _ _
        _ ≤ (N : ℝ) / (2 * (p : ℝ)) +
            ∑ a ∈ reducedResidues p,
              ∑ _r ∈ Finset.range (2 * R + 1),
                (N : ℝ) / (2 * (p : ℝ)) := by
          gcongr with a ha
          unfold residuePeriodizationTruncation
          calc
            ‖∑ r ∈ Finset.range (2 * R + 1),
                periodizationCell N p (residueCutoffQ p a R r) α‖ ≤
              ∑ r ∈ Finset.range (2 * R + 1),
                ‖periodizationCell N p (residueCutoffQ p a R r) α‖ :=
                norm_sum_le _ _
            _ ≤ ∑ _r ∈ Finset.range (2 * R + 1),
                (N : ℝ) / (2 * (p : ℝ)) := by
              gcongr with r hr
              exact norm_periodizationCell_le N p
                (residueCutoffQ p a R r) α hp
    _ = pvWindowErrorMajorant N P R := rfl

/-- The literal finite window error is interval-integrable on every bounded
interval. -/
theorem intervalIntegrable_pvWindowErrorTruncation
    (N P R : ℕ) (a b : ℝ) :
    IntervalIntegrable (pvWindowErrorTruncation N P R) volume a b := by
  apply (intervalIntegrable_const
    (c := pvWindowErrorMajorant N P R)).mono_fun
  · exact (measurable_pvWindowErrorTruncation N P R).aestronglyMeasurable
  · filter_upwards with α
    rw [Real.norm_eq_abs, abs_of_nonneg
      (pvWindowErrorMajorant_nonneg N P R)]
    exact norm_pvWindowErrorTruncation_le N P R α

/-- Squared `L²` energy of the literal finite cutoff error on the unit
interval. -/
def pvWindowErrorTruncationEnergy (N P R : ℕ) : ℝ :=
  ∫ α in (0 : ℝ)..1, ‖pvWindowErrorTruncation N P R α‖ ^ 2

private theorem intervalIntegrable_sq_norm_pvWindowErrorTruncation
    (N P R : ℕ) (a b : ℝ) :
    IntervalIntegrable
      (fun α ↦ ‖pvWindowErrorTruncation N P R α‖ ^ 2)
      volume a b := by
  apply (intervalIntegrable_const
    (c := (pvWindowErrorMajorant N P R) ^ 2)).mono_fun
  · exact
      ((measurable_pvWindowErrorTruncation N P R).norm.pow_const (2 : ℕ))
        |>.aestronglyMeasurable
  · filter_upwards with α
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_pvWindowErrorTruncation_le N P R α) 2

theorem pvWindowErrorTruncationEnergy_nonneg (N P R : ℕ) :
    0 ≤ pvWindowErrorTruncationEnergy N P R := by
  unfold pvWindowErrorTruncationEnergy
  exact intervalIntegral.integral_nonneg (by norm_num) fun α _hα ↦ sq_nonneg _

/-- A rigorous finite `L²` bound before any principal-value limit.  The
majorant is crude but completely explicit and contains no convergence or
arithmetic estimate. -/
theorem pvWindowErrorTruncationEnergy_le_majorant_sq (N P R : ℕ) :
    pvWindowErrorTruncationEnergy N P R ≤
      (pvWindowErrorMajorant N P R) ^ 2 := by
  unfold pvWindowErrorTruncationEnergy
  calc
    (∫ α in (0 : ℝ)..1, ‖pvWindowErrorTruncation N P R α‖ ^ 2) ≤
        ∫ _α in (0 : ℝ)..1, (pvWindowErrorMajorant N P R) ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (intervalIntegrable_sq_norm_pvWindowErrorTruncation N P R 0 1)
        intervalIntegrable_const
      intro α _hα
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_pvWindowErrorTruncation_le N P R α) 2
    _ = (pvWindowErrorMajorant N P R) ^ 2 := by
      rw [intervalIntegral.integral_const]
      norm_num

/-! ## The explicit coefficient table in the paper -/

/-- The sine integral with the manuscript's normalization.  Mathlib's
`Real.sinc` supplies the continuous value at the origin. -/
def paperSineIntegral (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.sinc t

/-- The displayed coefficient `\widehat L_d(m)` from Proposition 2.2.
The zero mode is recorded separately, exactly as in the manuscript. -/
def windowKernelCoefficient (d : ℕ) (m : ℤ) : ℂ :=
  if m = 0 then 0
  else
    Complex.I * (Real.pi * (Int.sign m : ℝ)) -
      (2 * Complex.I) *
        (paperSineIntegral (Real.pi * (m : ℝ) / (d : ℝ)) : ℂ)

@[simp]
theorem windowKernelCoefficient_zero (d : ℕ) :
    windowKernelCoefficient d 0 = 0 := by
  simp [windowKernelCoefficient]

/-! ## The finite arithmetic `C_ℓ(n)` reduction -/

/-- Admissible pairs `(d,r)` in the coefficient `C_ℓ(n)`: both
coordinates are positive, `dr ≤ P`, and `r` divides the positive Fourier
frequency `n`. -/
def windowDivisorPairs (P n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 P).product (Finset.Icc 1 P)).filter fun z ↦
    z.1 * z.2 ≤ P ∧ z.2 ∣ n

theorem mem_windowDivisorPairs_iff {P n : ℕ} {z : ℕ × ℕ} :
    z ∈ windowDivisorPairs P n ↔
      1 ≤ z.1 ∧ z.1 ≤ P ∧ 1 ≤ z.2 ∧ z.2 ≤ P ∧
        z.1 * z.2 ≤ P ∧ z.2 ∣ n := by
  simp [windowDivisorPairs, and_assoc]

/-- Every sum over `windowDivisorPairs` can be displayed as the paper's
nested `(d,r)` sum with its two arithmetic indicators explicit. -/
theorem sum_windowDivisorPairs_eq_nested
    {M : Type*} [AddCommMonoid M]
    (P n : ℕ) (f : ℕ × ℕ → M) :
    (∑ z ∈ windowDivisorPairs P n, f z) =
      ∑ d ∈ Finset.Icc 1 P, ∑ r ∈ Finset.Icc 1 P,
        if d * r ≤ P ∧ r ∣ n then f (d, r) else 0 := by
  rw [windowDivisorPairs, Finset.sum_filter]
  exact Finset.sum_product' (Finset.Icc 1 P) (Finset.Icc 1 P)
    (fun d r ↦ if d * r ≤ P ∧ r ∣ n then f (d, r) else 0)

/-- One exact summand of `C_ℓ(n)`.  It is defined on every pair; the
divisibility condition needed to interpret `n/r` is imposed by
`windowDivisorPairs`. -/
def windowModeSummand
    (N : ℕ) (ℓ : ℤ) (n : ℕ) (z : ℕ × ℕ) : ℂ :=
  ((ArithmeticFunction.moebius z.1 : ℤ) : ℂ) /
      ((z.1 : ℂ) ^ 2 * (z.2 : ℂ)) *
    windowKernelCoefficient z.1
      (((n / z.2 : ℕ) : ℤ) - ℓ * ((N * z.1 : ℕ) : ℤ))

/-- The finite coefficient `C_ℓ(n)` in equation (2.15) of the
manuscript. -/
def windowModeCoefficient (N P : ℕ) (ℓ : ℤ) (n : ℕ) : ℂ :=
  ∑ z ∈ windowDivisorPairs P n, windowModeSummand N ℓ n z

/-- Fully expanded finite `(d,r)` form of `C_ℓ(n)`. -/
theorem windowModeCoefficient_eq_nested
    (N P : ℕ) (ℓ : ℤ) (n : ℕ) :
    windowModeCoefficient N P ℓ n =
      ∑ d ∈ Finset.Icc 1 P, ∑ r ∈ Finset.Icc 1 P,
        if d * r ≤ P ∧ r ∣ n then
          windowModeSummand N ℓ n (d, r)
        else 0 := by
  exact sum_windowDivisorPairs_eq_nested P n (windowModeSummand N ℓ n)

private theorem norm_moebius_cast_le_one (d : ℕ) :
    ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or d with h | h | h
  · simp [h]
  · simp [h]
  · simp [h]

/-- Removing the Möbius sign exposes the exact denominator factor in one
arithmetic summand. -/
theorem norm_windowModeSummand_le
    (N : ℕ) (ℓ : ℤ) (n : ℕ) {P : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ windowDivisorPairs P n) :
    ‖windowModeSummand N ℓ n z‖ ≤
      ‖windowKernelCoefficient z.1
        (((n / z.2 : ℕ) : ℤ) - ℓ * ((N * z.1 : ℕ) : ℤ))‖ /
        ((z.1 : ℝ) ^ 2 * (z.2 : ℝ)) := by
  have hz' := mem_windowDivisorPairs_iff.mp hz
  have hd : 0 < (z.1 : ℝ) := Nat.cast_pos.mpr (by omega)
  have hr : 0 < (z.2 : ℝ) := Nat.cast_pos.mpr (by omega)
  have hden : 0 < (z.1 : ℝ) ^ 2 * (z.2 : ℝ) := mul_pos (sq_pos_of_pos hd) hr
  unfold windowModeSummand
  rw [norm_mul, norm_div, norm_mul, norm_pow,
    Complex.norm_natCast, Complex.norm_natCast]
  calc
    (‖((ArithmeticFunction.moebius z.1 : ℤ) : ℂ)‖ /
          ((z.1 : ℝ) ^ 2 * (z.2 : ℝ))) *
        ‖windowKernelCoefficient z.1
          (((n / z.2 : ℕ) : ℤ) - ℓ * ((N * z.1 : ℕ) : ℤ))‖ ≤
      (1 / ((z.1 : ℝ) ^ 2 * (z.2 : ℝ))) *
        ‖windowKernelCoefficient z.1
          (((n / z.2 : ℕ) : ℤ) - ℓ * ((N * z.1 : ℕ) : ℤ))‖ := by
        gcongr
        exact norm_moebius_cast_le_one z.1
    _ = ‖windowKernelCoefficient z.1
          (((n / z.2 : ℕ) : ℤ) - ℓ * ((N * z.1 : ℕ) : ℤ))‖ /
        ((z.1 : ℝ) ^ 2 * (z.2 : ℝ)) := by ring

/-- The paper's fixed Cauchy--Schwarz weight
`d^{-3/2} r^{-1}`, written without fractional-power notation. -/
def windowCauchyWeight (z : ℕ × ℕ) : ℝ :=
  1 / (Real.sqrt ((z.1 : ℝ) ^ 3) * (z.2 : ℝ))

theorem windowCauchyWeight_pos_of_mem
    {P n : ℕ} {z : ℕ × ℕ} (hz : z ∈ windowDivisorPairs P n) :
    0 < windowCauchyWeight z := by
  have hz' := mem_windowDivisorPairs_iff.mp hz
  have hd : 0 < (z.1 : ℝ) := Nat.cast_pos.mpr (by omega)
  have hr : 0 < (z.2 : ℝ) := Nat.cast_pos.mpr (by omega)
  unfold windowCauchyWeight
  exact one_div_pos.mpr (mul_pos (Real.sqrt_pos.2 (pow_pos hd 3)) hr)

/-- A general finite weighted Cauchy--Schwarz inequality for complex
vectors.  Strict positivity keeps all divisions honest. -/
theorem norm_finset_sum_sq_le_weighted
    { ι : Type* } [DecidableEq ι]
    (s : Finset ι) (f : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, ‖f i‖ ^ 2 / w i := by
  have htriangle :
      ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, ‖f i‖ := by positivity
  have hsquare :
      ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hsum_nonneg).2 htriangle
  refine hsquare.trans ?_
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s
  · intro i hi
    exact (hw i hi).le
  · intro i hi
    exact div_nonneg (sq_nonneg _) (hw i hi).le
  · intro i hi
    field_simp [(hw i hi).ne']

/-- The mass of the Cauchy--Schwarz weights at one frequency. -/
def windowWeightMass (P n : ℕ) : ℝ :=
  ∑ z ∈ windowDivisorPairs P n, windowCauchyWeight z

/-- The remaining explicit weighted arithmetic energy at one carrier and
one Fourier frequency. -/
def windowWeightedCoefficientEnergy
    (N P : ℕ) (ℓ : ℤ) (n : ℕ) : ℝ :=
  ∑ z ∈ windowDivisorPairs P n,
    ‖windowModeSummand N ℓ n z‖ ^ 2 / windowCauchyWeight z

/-- The same weighted energy after removing the Möbius signs and exposing
the exact `d⁻²r⁻¹` factor.  This is the finite sum to which the
analytic estimate for `\widehat L_d` is applied in the paper. -/
def windowKernelWeightedEnergy
    (N P : ℕ) (ℓ : ℤ) (n : ℕ) : ℝ :=
  ∑ z ∈ windowDivisorPairs P n,
    (‖windowKernelCoefficient z.1
        (((n / z.2 : ℕ) : ℤ) - ℓ * ((N * z.1 : ℕ) : ℤ))‖ /
      ((z.1 : ℝ) ^ 2 * (z.2 : ℝ))) ^ 2 /
        windowCauchyWeight z

theorem windowWeightMass_nonneg (P n : ℕ) :
    0 ≤ windowWeightMass P n := by
  unfold windowWeightMass
  apply Finset.sum_nonneg
  intro z hz
  exact (windowCauchyWeight_pos_of_mem hz).le

theorem windowWeightedCoefficientEnergy_nonneg
    (N P : ℕ) (ℓ : ℤ) (n : ℕ) :
    0 ≤ windowWeightedCoefficientEnergy N P ℓ n := by
  unfold windowWeightedCoefficientEnergy
  apply Finset.sum_nonneg
  intro z hz
  exact div_nonneg (sq_nonneg _) (windowCauchyWeight_pos_of_mem hz).le

theorem windowKernelWeightedEnergy_nonneg
    (N P : ℕ) (ℓ : ℤ) (n : ℕ) :
    0 ≤ windowKernelWeightedEnergy N P ℓ n := by
  unfold windowKernelWeightedEnergy
  apply Finset.sum_nonneg
  intro z hz
  exact div_nonneg (sq_nonneg _) (windowCauchyWeight_pos_of_mem hz).le

theorem windowWeightedCoefficientEnergy_le_kernel
    (N P : ℕ) (ℓ : ℤ) (n : ℕ) :
    windowWeightedCoefficientEnergy N P ℓ n ≤
      windowKernelWeightedEnergy N P ℓ n := by
  unfold windowWeightedCoefficientEnergy windowKernelWeightedEnergy
  apply Finset.sum_le_sum
  intro z hz
  apply div_le_div_of_nonneg_right
  · exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_windowModeSummand_le N ℓ n hz) 2
  · exact (windowCauchyWeight_pos_of_mem hz).le

/-- Exact finite Cauchy--Schwarz reduction of one coefficient. -/
theorem norm_windowModeCoefficient_sq_le
    (N P : ℕ) (ℓ : ℤ) (n : ℕ) :
    ‖windowModeCoefficient N P ℓ n‖ ^ 2 ≤
      windowWeightMass P n * windowWeightedCoefficientEnergy N P ℓ n := by
  exact norm_finset_sum_sq_le_weighted
    (windowDivisorPairs P n) (windowModeSummand N ℓ n) windowCauchyWeight
    (fun z hz ↦ windowCauchyWeight_pos_of_mem hz)

/-- The coefficient bound with every Möbius sign removed. -/
theorem norm_windowModeCoefficient_sq_le_kernelEnergy
    (N P : ℕ) (ℓ : ℤ) (n : ℕ) :
    ‖windowModeCoefficient N P ℓ n‖ ^ 2 ≤
      windowWeightMass P n * windowKernelWeightedEnergy N P ℓ n := by
  calc
    ‖windowModeCoefficient N P ℓ n‖ ^ 2 ≤
        windowWeightMass P n * windowWeightedCoefficientEnergy N P ℓ n :=
      norm_windowModeCoefficient_sq_le N P ℓ n
    _ ≤ windowWeightMass P n * windowKernelWeightedEnergy N P ℓ n := by
      exact mul_le_mul_of_nonneg_left
        (windowWeightedCoefficientEnergy_le_kernel N P ℓ n)
        (windowWeightMass_nonneg P n)

/-- Positive-frequency Fourier polynomial for one fixed mark mode. -/
def windowModeFourierPolynomial
    (N P K : ℕ) (ℓ : ℤ) : UnitCircleL2 :=
  ∑ n ∈ Finset.Icc 1 K,
    windowModeCoefficient N P ℓ n • fourierLp 2 (n : ℤ)

/-- Exact finite Parseval identity for one carrier mode. -/
theorem norm_windowModeFourierPolynomial_sq
    (N P K : ℕ) (ℓ : ℤ) :
    ‖windowModeFourierPolynomial N P K ℓ‖ ^ 2 =
      ∑ n ∈ Finset.Icc 1 K, ‖windowModeCoefficient N P ℓ n‖ ^ 2 := by
  unfold windowModeFourierPolynomial
  simpa using!
    (orthonormal_fourier.orthogonalFamily.norm_sum
      (fun n : ℤ ↦ windowModeCoefficient N P ℓ n.toNat)
      ((Finset.Icc 1 K).map
        ⟨(fun n : ℕ ↦ (n : ℤ)), fun _ _ h ↦ Int.ofNat_inj.mp h⟩))

/-- The explicit finite arithmetic sum which dominates the squared norm of
one carrier polynomial. -/
def windowModeArithmeticEnergy
    (N P K : ℕ) (ℓ : ℤ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 K,
    windowWeightMass P n * windowKernelWeightedEnergy N P ℓ n

theorem windowModeArithmeticEnergy_nonneg
    (N P K : ℕ) (ℓ : ℤ) :
    0 ≤ windowModeArithmeticEnergy N P K ℓ := by
  unfold windowModeArithmeticEnergy
  apply Finset.sum_nonneg
  intro n _hn
  exact mul_nonneg (windowWeightMass_nonneg P n)
    (windowKernelWeightedEnergy_nonneg N P ℓ n)

/-- Finite `L²` reduction to the explicit divisor/carrier sum. -/
theorem norm_windowModeFourierPolynomial_sq_le_arithmeticEnergy
    (N P K : ℕ) (ℓ : ℤ) :
    ‖windowModeFourierPolynomial N P K ℓ‖ ^ 2 ≤
      windowModeArithmeticEnergy N P K ℓ := by
  rw [norm_windowModeFourierPolynomial_sq]
  unfold windowModeArithmeticEnergy
  gcongr with n hn
  exact norm_windowModeCoefficient_sq_le_kernelEnergy N P ℓ n

/-- Finite sum over mark modes, using the exact Bernoulli coefficients
`v_ℓ`. -/
def finiteWindowFourierPolynomial
    (N P J K : ℕ) : UnitCircleL2 :=
  ∑ ℓ ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
    bernoulliMarkFourierCoefficient ℓ •
      windowModeFourierPolynomial N P K ℓ

/-- The completely explicit finite majorant produced by Parseval,
weighted Cauchy--Schwarz, and Minkowski. -/
def finiteWindowArithmeticMajorant (N P J K : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
    ‖bernoulliMarkFourierCoefficient ℓ‖ *
      Real.sqrt (windowModeArithmeticEnergy N P K ℓ)

theorem finiteWindowArithmeticMajorant_nonneg (N P J K : ℕ) :
    0 ≤ finiteWindowArithmeticMajorant N P J K := by
  unfold finiteWindowArithmeticMajorant
  positivity

/-- Finite Minkowski reduction across mark modes.  No overlap or
convergence assertion is used. -/
theorem norm_finiteWindowFourierPolynomial_le
    (N P J K : ℕ) :
    ‖finiteWindowFourierPolynomial N P J K‖ ≤
      finiteWindowArithmeticMajorant N P J K := by
  unfold finiteWindowFourierPolynomial
  calc
    ‖∑ ℓ ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
        bernoulliMarkFourierCoefficient ℓ •
          windowModeFourierPolynomial N P K ℓ‖ ≤
      ∑ ℓ ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
        ‖bernoulliMarkFourierCoefficient ℓ •
          windowModeFourierPolynomial N P K ℓ‖ := norm_sum_le _ _
    _ ≤ ∑ ℓ ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
        ‖bernoulliMarkFourierCoefficient ℓ‖ *
          Real.sqrt (windowModeArithmeticEnergy N P K ℓ) := by
      gcongr with ℓ hℓ
      rw [norm_smul]
      gcongr
      calc
        ‖windowModeFourierPolynomial N P K ℓ‖ =
            Real.sqrt (‖windowModeFourierPolynomial N P K ℓ‖ ^ 2) := by
          rw [Real.sqrt_sq (norm_nonneg _)]
        _ ≤ Real.sqrt (windowModeArithmeticEnergy N P K ℓ) :=
          Real.sqrt_le_sqrt
            (norm_windowModeFourierPolynomial_sq_le_arithmeticEnergy N P K ℓ)
    _ = finiteWindowArithmeticMajorant N P J K := rfl

/-- Squared finite `L²` reduction, in the form directly comparable with
the squared norm in Proposition 2.2. -/
theorem norm_finiteWindowFourierPolynomial_sq_le
    (N P J K : ℕ) :
    ‖finiteWindowFourierPolynomial N P J K‖ ^ 2 ≤
      (finiteWindowArithmeticMajorant N P J K) ^ 2 := by
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_finiteWindowFourierPolynomial_le N P J K) 2

end

end Erdos1002
