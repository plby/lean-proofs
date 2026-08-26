import ErdosProblems.Erdos1002.PrimitiveShotCellExpansion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Fourier integral of one nearest primitive cell

This file computes one finite half-open cell integral by an affine change of
variables.  It is independent of any principal-value limit.  The result is
the common truncated real-line transform multiplied by the exact residue
phase and the Jacobian `p⁻²`.
-/

open MeasureTheory Set
open scoped Real

namespace Erdos1002

noncomputable section

/-- Endpoints of the nearest cell with numerator `q`. -/
def nearestCellLeft (p q : ℕ) : ℝ :=
  ((q : ℝ) - (1 : ℝ) / 2) / (p : ℝ)

def nearestCellRight (p q : ℕ) : ℝ :=
  ((q : ℝ) + (1 : ℝ) / 2) / (p : ℝ)

/-- The Fourier integral of one periodization cell restricted to its
nearest-cell interval. -/
def nearestCellFourierIntegral (N n p q : ℕ) : ℂ :=
  ∫ alpha in nearestCellLeft p q..nearestCellRight p q,
    periodizationCell N p (q : ℤ) alpha *
      paperExp (-(n : ℝ) * alpha)

/-- The cell condition in the scaled coordinate is exactly the corresponding
half-open interval in `alpha`. -/
theorem mem_nearestCell_iff
    {p q : ℕ} (hp : 0 < p) (alpha : ℝ) :
    (p : ℝ) * alpha - (q : ℝ) ∈
        Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) ↔
      alpha ∈ Ioc (nearestCellLeft p q) (nearestCellRight p q) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  simp only [mem_Ioc]
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor
    · rw [nearestCellLeft, div_lt_iff₀ hpR]
      linarith
    · rw [nearestCellRight, le_div_iff₀ hpR]
      linarith
  · rintro ⟨hlower, hupper⟩
    constructor
    · rw [nearestCellLeft, div_lt_iff₀ hpR] at hlower
      linarith
    · rw [nearestCellRight, le_div_iff₀ hpR] at hupper
      linarith

/-- The integrand with its exact half-open nearest-cell cutoff. -/
def nearestCellFourierTerm (N n p q : ℕ) (alpha : ℝ) : ℂ :=
  if (p : ℝ) * alpha - (q : ℝ) ∈
      Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) then
    periodizationCell N p (q : ℤ) alpha *
      paperExp (-(n : ℝ) * alpha)
  else 0

private theorem measurable_paperExp_cell : Measurable paperExp := by
  unfold paperExp
  fun_prop

theorem measurable_nearestCellFourierTerm (N n p q : ℕ) :
    Measurable (nearestCellFourierTerm N n p q) := by
  unfold nearestCellFourierTerm
  apply Measurable.ite
  · exact measurableSet_Ioc.preimage
      (measurable_const.mul measurable_id |>.sub measurable_const)
  · exact (measurable_periodizationCell_window N p (q : ℤ)).mul
      (measurable_paperExp_cell.comp
        (measurable_const.mul measurable_id))
  · exact measurable_const

private theorem norm_paperExp_cell (t : ℝ) : ‖paperExp t‖ = 1 := by
  rw [paperExp, Complex.norm_exp]
  simp

theorem intervalIntegrable_nearestCellFourierTerm
    (N n p q : ℕ) (hp : 0 < p) (a b : ℝ) :
    IntervalIntegrable (nearestCellFourierTerm N n p q) volume a b := by
  apply (intervalIntegrable_const (c := (N : ℝ) / (2 * (p : ℝ)))).mono_fun
  · exact (measurable_nearestCellFourierTerm N n p q).aestronglyMeasurable
  · filter_upwards with alpha
    by_cases hcell :
        (p : ℝ) * alpha - (q : ℝ) ∈
          Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)
    · rw [nearestCellFourierTerm, if_pos hcell, norm_mul,
        norm_paperExp_cell, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) / (2 * (p : ℝ)))]
      exact norm_periodizationCell_le N p (q : ℤ) alpha hp
    · rw [nearestCellFourierTerm, if_neg hcell, norm_zero]
      positivity

theorem reducedResidue_pos
    {p q : ℕ} (hp : 2 ≤ p) (hq : q ∈ reducedResidues p) : 0 < q := by
  rw [reducedResidues, Finset.mem_filter, Finset.mem_range] at hq
  by_contra hqzero
  have hq0 : q = 0 := Nat.eq_zero_of_not_pos hqzero
  subst q
  have hpone : p = 1 := by simpa using! hq.2
  omega

theorem nearestCell_interval_subset_unit
    {p q : ℕ} (hp : 2 ≤ p) (hq : q ∈ reducedResidues p) :
    Ioc (nearestCellLeft p q) (nearestCellRight p q) ⊆
      Ioc (0 : ℝ) 1 := by
  have hpR : 0 < (p : ℝ) := by positivity
  have hqpos : 0 < q := reducedResidue_pos hp hq
  have hqlt : q < p := by
    have hqrange : q ∈ Finset.range p :=
      (Finset.mem_filter.mp (by
        simpa only [reducedResidues] using! hq)).1
    exact Finset.mem_range.mp hqrange
  have hleft : 0 ≤ nearestCellLeft p q := by
    unfold nearestCellLeft
    apply div_nonneg
    · have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
      linarith
    · exact hpR.le
  have hright : nearestCellRight p q ≤ 1 := by
    unfold nearestCellRight
    rw [div_le_one hpR]
    have hqle : q + 1 ≤ p := by omega
    have hqleR : (q : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hqle
    linarith
  intro alpha halpha
  exact ⟨hleft.trans_lt halpha.1, halpha.2.trans hright⟩

theorem nearestCellLeft_lt_right (p q : ℕ) (hp : 0 < p) :
    nearestCellLeft p q < nearestCellRight p q := by
  unfold nearestCellLeft nearestCellRight
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  apply (div_lt_div_iff_of_pos_right hpR).2
  linarith

theorem support_nearestCellFourierTerm_subset
    (N n p q : ℕ) (hp : 0 < p) :
    Function.support (nearestCellFourierTerm N n p q) ⊆
      Ioc (nearestCellLeft p q) (nearestCellRight p q) := by
  intro alpha halpha
  have hnonzero : nearestCellFourierTerm N n p q alpha ≠ 0 := halpha
  by_contra hnot
  have hscaled :
      ¬ ((p : ℝ) * alpha - (q : ℝ) ∈
        Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)) := by
    exact fun h ↦ hnot ((mem_nearestCell_iff hp alpha).1 h)
  rw [nearestCellFourierTerm, if_neg hscaled] at hnonzero
  exact hnonzero rfl

/-- Integrating the cut-off cell over the full unit interval is exactly the
same as integrating the uncut cell over its own affine interval. -/
theorem integral_unit_nearestCellFourierTerm_eq
    (N n p q : ℕ) (hp : 2 ≤ p) (hq : q ∈ reducedResidues p) :
    (∫ alpha in (0 : ℝ)..1, nearestCellFourierTerm N n p q alpha) =
      nearestCellFourierIntegral N n p q := by
  have hp0 : 0 < p := by omega
  let f : ℝ → ℂ := nearestCellFourierTerm N n p q
  have hsupportCell : Function.support f ⊆
      Ioc (nearestCellLeft p q) (nearestCellRight p q) :=
    support_nearestCellFourierTerm_subset N n p q hp0
  have hsupportUnit : Function.support f ⊆ Ioc (0 : ℝ) 1 :=
    hsupportCell.trans (nearestCell_interval_subset_unit hp hq)
  calc
    (∫ alpha in (0 : ℝ)..1, nearestCellFourierTerm N n p q alpha) =
        ∫ alpha, f alpha := by
      exact intervalIntegral.integral_eq_integral_of_support_subset hsupportUnit
    _ = ∫ alpha in nearestCellLeft p q..nearestCellRight p q, f alpha := by
      symm
      exact intervalIntegral.integral_eq_integral_of_support_subset hsupportCell
    _ = ∫ alpha in nearestCellLeft p q..nearestCellRight p q,
          periodizationCell N p (q : ℤ) alpha *
            paperExp (-(n : ℝ) * alpha) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with alpha
      intro halpha
      have hcell : alpha ∈ Ioc (nearestCellLeft p q) (nearestCellRight p q) := by
        simpa only [Set.uIoc_of_le (nearestCellLeft_lt_right p q hp0).le] using! halpha
      change nearestCellFourierTerm N n p q alpha = _
      rw [nearestCellFourierTerm,
        if_pos ((mem_nearestCell_iff hp0 alpha).2 hcell)]
    _ = nearestCellFourierIntegral N n p q := rfl

/-- Fourier coefficient of the finite reduced-cell expansion, before
factoring the common truncated transform. -/
theorem unitFourierCoefficient_nearestPrimitiveCellExpansion
    (N n p : ℕ) (hp : 2 ≤ p) :
    unitFourierCoefficient
        (nearestPrimitiveCellExpansion N p) n =
      ∑ q ∈ reducedResidues p,
        nearestCellFourierIntegral N n p q := by
  have hfun :
      (fun alpha ↦ nearestPrimitiveCellExpansion N p alpha *
        paperExp (-(n : ℝ) * alpha)) =
      fun alpha ↦ ∑ q ∈ reducedResidues p,
        nearestCellFourierTerm N n p q alpha := by
    funext alpha
    unfold nearestPrimitiveCellExpansion
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _hq
    by_cases hcell :
        (p : ℝ) * alpha - (q : ℝ) ∈
          Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)
    · rw [if_pos hcell, nearestCellFourierTerm, if_pos hcell]
    · rw [if_neg hcell, zero_mul, nearestCellFourierTerm, if_neg hcell]
  unfold unitFourierCoefficient
  rw [hfun, intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro q hq
    exact integral_unit_nearestCellFourierTerm_eq N n p q hp hq
  · intro q hq
    exact intervalIntegrable_nearestCellFourierTerm N n p q (by omega) 0 1

private theorem paperExp_add_cell (u v : ℝ) :
    paperExp u * paperExp v = paperExp (u + v) := by
  unfold paperExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem periodization_phase_split_cell
    (n p q : ℕ) (alpha : ℝ) (hp : 0 < p) :
    paperExp (-(n : ℝ) * alpha) =
      paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
        paperExp (-((n : ℝ) / (p : ℝ)) *
          ((p : ℝ) * alpha - (q : ℝ))) := by
  rw [paperExp_add_cell]
  congr 1
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpR]
  ring

theorem nearestCellLeft_mul_sub (p q : ℕ) (hp : 0 < p) :
    (p : ℝ) * nearestCellLeft p q - (q : ℝ) = -(1 : ℝ) / 2 := by
  unfold nearestCellLeft
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpR]
  ring

theorem nearestCellRight_mul_sub (p q : ℕ) (hp : 0 < p) :
    (p : ℝ) * nearestCellRight p q - (q : ℝ) = (1 : ℝ) / 2 := by
  unfold nearestCellRight
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpR]
  ring

/-- Exact finite Fourier calculation on one nearest cell. -/
theorem nearestCellFourierIntegral_eq
    (N n p q : ℕ) (hp : 0 < p) :
    nearestCellFourierIntegral N n p q =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
          (∫ x in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
            periodizedTransformIntegrand N n p x) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold nearestCellFourierIntegral periodizationCell
  calc
    (∫ alpha in nearestCellLeft p q..nearestCellRight p q,
        ((1 / (p : ℝ) : ℝ) : ℂ) *
          (transformKernel N ((p : ℝ) * alpha - (q : ℝ)) : ℂ) *
            paperExp (-(n : ℝ) * alpha)) =
      ∫ alpha in nearestCellLeft p q..nearestCellRight p q,
        (((1 / (p : ℝ) : ℝ) : ℂ) *
          paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ))) *
            periodizedTransformIntegrand N n p
              ((p : ℝ) * alpha - (q : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro alpha _halpha
        simp only [periodizedTransformIntegrand]
        rw [periodization_phase_split_cell n p q alpha hp]
        ring
    _ = (((1 / (p : ℝ) : ℝ) : ℂ) *
          paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ))) *
        (∫ alpha in nearestCellLeft p q..nearestCellRight p q,
          periodizedTransformIntegrand N n p
            ((p : ℝ) * alpha - (q : ℝ))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (((1 / (p : ℝ) : ℝ) : ℂ) *
          paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ))) *
        ((p : ℝ)⁻¹ •
          (∫ x in
              (p : ℝ) * nearestCellLeft p q - (q : ℝ)..
              (p : ℝ) * nearestCellRight p q - (q : ℝ),
            periodizedTransformIntegrand N n p x)) := by
      rw [intervalIntegral.integral_comp_mul_sub
        (periodizedTransformIntegrand N n p) hpR (q : ℝ)]
    _ = ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
          (∫ x in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
            periodizedTransformIntegrand N n p x) := by
      rw [nearestCellLeft_mul_sub p q hp,
        nearestCellRight_mul_sub p q hp, Complex.real_smul]
      push_cast
      field_simp [hpR]

/-- The common real-line transform truncated to the nearest cell. -/
def nearestCellTransform (N n p : ℕ) : ℂ :=
  ∫ x in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
    periodizedTransformIntegrand N n p x

/-- The nearest-cell transform has zero mean.  This is an ordinary bounded
interval integral of the odd transform kernel; no principal-value argument
is involved. -/
theorem nearestCellTransform_zero (N p : ℕ) :
    nearestCellTransform N 0 p = 0 := by
  unfold nearestCellTransform periodizedTransformIntegrand
  simp only [Nat.cast_zero, zero_div, zero_mul, neg_zero, paperExp]
  have hodd : Function.Odd (fun x : ℝ ↦ (transformKernel N x : ℂ)) := by
    intro x
    push_cast
    exact_mod_cast transformKernel_odd N x
  let a : ℝ := (1 : ℝ) / 2
  have hreflect :=
    intervalIntegral.integral_comp_neg
      (f := fun x : ℝ ↦ (transformKernel N x : ℂ))
      (a := -a) (b := a)
  have hsame :
      (∫ x in -a..a, (transformKernel N (-x) : ℂ)) =
        ∫ x in -a..a, (transformKernel N x : ℂ) := by
    simpa only [neg_neg] using! hreflect
  have hneg :
      (∫ x in -a..a, (transformKernel N (-x) : ℂ)) =
        -(∫ x in -a..a, (transformKernel N x : ℂ)) := by
    calc
      (∫ x in -a..a, (transformKernel N (-x) : ℂ)) =
          ∫ x in -a..a, -(transformKernel N x : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        exact hodd x
      _ = -(∫ x in -a..a, (transformKernel N x : ℂ)) := by
        rw [intervalIntegral.integral_neg]
  norm_num
  change (∫ x in -a..a, (transformKernel N x : ℂ)) = 0
  exact CharZero.eq_neg_self_iff.mp (hsame.symm.trans hneg)

/-- The reduced-cell Fourier coefficient factors into a Ramanujan sum and
the common truncated transform. -/
theorem unitFourierCoefficient_nearestPrimitiveCellExpansion_eq_ramanujan
    (N n p : ℕ) (hp : 2 ≤ p) :
    unitFourierCoefficient
        (nearestPrimitiveCellExpansion N p) n =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        ramanujanSum p (n : ℤ) * nearestCellTransform N n p := by
  rw [unitFourierCoefficient_nearestPrimitiveCellExpansion N n p hp]
  simp_rw [nearestCellFourierIntegral_eq N n p _ (by omega)]
  rw [← Finset.sum_mul, ← Finset.mul_sum,
    sum_reducedResidues_paperExp_neg]
  rfl

/-- Exact positive-frequency (and zero-frequency) formula for one literal
primitive shot, proved from finite cell integration. -/
theorem unitFourierCoefficient_primitiveShot_eq_ramanujan
    (N n p : ℕ) (hp : 2 ≤ p) :
    unitFourierCoefficient (fun alpha ↦ (primitiveShot N p alpha : ℂ)) n =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        ramanujanSum p (n : ℤ) * nearestCellTransform N n p := by
  rw [← unitFourierCoefficient_nearestPrimitiveCellExpansion_eq_ramanujan
    N n p hp]
  unfold unitFourierCoefficient
  apply intervalIntegral.integral_congr_ae
  have hone : ∀ᵐ alpha : ℝ ∂volume, alpha ≠ 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hone] with alpha halphaOne
  intro halpha
  have hmem : alpha ∈ Ioo (0 : ℝ) 1 := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at halpha
    exact ⟨halpha.1, lt_of_le_of_ne halpha.2 halphaOne⟩
  rw [primitiveShot_eq_nearestPrimitiveCellExpansion hp hmem]

private theorem paperExp_int_cell (z : ℤ) : paperExp (z : ℝ) = 1 := by
  unfold paperExp
  convert! Complex.exp_int_mul_two_pi_mul_I z using 2
  push_cast
  ring

/-- For modulus one the primitive condition is automatic. -/
theorem isPrimitiveResonance_one (alpha : ℝ) :
    IsPrimitiveResonance 1 alpha := by
  simp [IsPrimitiveResonance]

theorem primitiveShot_one_periodic (N : ℕ) :
    Function.Periodic (primitiveShot N 1) 1 := by
  intro alpha
  rw [primitiveShot_of_primitive N 1 (alpha + 1)
      (isPrimitiveResonance_one (alpha + 1)),
    primitiveShot_of_primitive N 1 alpha (isPrimitiveResonance_one alpha)]
  have hdelta : resonanceDelta 1 (alpha + 1) = resonanceDelta 1 alpha := by
    simpa using! resonanceDelta_add_int 1 alpha (1 : ℤ)
  rw [hdelta]

/-- The product with an integral Fourier character remains one-periodic. -/
theorem primitiveShotFourierIntegrand_one_periodic (N n : ℕ) :
    Function.Periodic
      (fun alpha ↦ (primitiveShot N 1 alpha : ℂ) *
        paperExp (-(n : ℝ) * alpha)) 1 := by
  intro alpha
  change (primitiveShot N 1 (alpha + 1) : ℂ) *
      paperExp (-(n : ℝ) * (alpha + 1)) = _
  rw [primitiveShot_one_periodic N alpha]
  have harg :
      -(n : ℝ) * (alpha + 1) = -(n : ℝ) * alpha + (-(n : ℤ) : ℤ) := by
    push_cast
    ring
  rw [harg, ← paperExp_add_cell, paperExp_int_cell, mul_one]

/-- The modulus-one endpoint pair is one complete nearest cell after
shifting the fundamental interval. -/
theorem unitFourierCoefficient_primitiveShot_one
    (N n : ℕ) :
    unitFourierCoefficient (fun alpha ↦ (primitiveShot N 1 alpha : ℂ)) n =
      nearestCellTransform N n 1 := by
  let f : ℝ → ℂ := fun alpha ↦ (primitiveShot N 1 alpha : ℂ) *
    paperExp (-(n : ℝ) * alpha)
  have hperiod : Function.Periodic f 1 :=
    primitiveShotFourierIntegrand_one_periodic N n
  have hshift := hperiod.intervalIntegral_add_eq (0 : ℝ) (-(1 : ℝ) / 2)
  have hinterval :
      (∫ alpha in (0 : ℝ)..1, f alpha) =
        ∫ alpha in (-(1 : ℝ) / 2)..((1 : ℝ) / 2), f alpha := by
    convert! hshift using 1 <;> norm_num
  unfold unitFourierCoefficient
  change (∫ alpha in (0 : ℝ)..1, f alpha) = _
  rw [hinterval]
  unfold nearestCellTransform
  apply intervalIntegral.integral_congr_ae
  filter_upwards with alpha
  intro halpha
  have hnum : resonanceNumerator 1 alpha = 0 := by
    apply resonanceNumerator_eq_of_delta_mem
    simpa only [Nat.cast_one, one_mul, Int.cast_zero, sub_zero,
      Set.uIoc_of_le (by norm_num : (-(1 : ℝ) / 2) ≤ (1 : ℝ) / 2)] using! halpha
  change (primitiveShot N 1 alpha : ℂ) *
      paperExp (-(n : ℝ) * alpha) = _
  rw [primitiveShot_of_primitive N 1 alpha
    (isPrimitiveResonance_one alpha)]
  simp only [resonanceDelta, hnum, Int.cast_zero, sub_zero, Nat.cast_one,
    one_mul, periodizedTransformIntegrand, div_one]
  by_cases hzero : alpha = 0
  · subst alpha
    simp [transformKernel, bernoulliMark]
  · rw [transformKernel, if_neg hzero]

/-- The one-cell Ramanujan formula also holds at `p = 1`; this is the
endpoint case omitted by the reduced-residue interior-cell argument. -/
theorem unitFourierCoefficient_primitiveShot_one_eq_ramanujan
    (N n : ℕ) :
    unitFourierCoefficient (fun alpha ↦ (primitiveShot N 1 alpha : ℂ)) n =
      ((1 / (1 : ℝ) ^ 2 : ℝ) : ℂ) *
        ramanujanSum 1 (n : ℤ) * nearestCellTransform N n 1 := by
  rw [unitFourierCoefficient_primitiveShot_one]
  simp

/-- Uniform one-denominator formula for every positive modulus. -/
theorem unitFourierCoefficient_primitiveShot_eq_ramanujan_of_pos
    (N n p : ℕ) (hp : 0 < p) :
    unitFourierCoefficient (fun alpha ↦ (primitiveShot N p alpha : ℂ)) n =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        ramanujanSum p (n : ℤ) * nearestCellTransform N n p := by
  by_cases hpone : p = 1
  · subst p
    convert! unitFourierCoefficient_primitiveShot_one_eq_ramanujan N n using 1
    norm_num
  · exact unitFourierCoefficient_primitiveShot_eq_ramanujan N n p
      (by omega)

theorem intervalIntegrable_primitiveShot_complex
    (N p : ℕ) (hp : 0 < p) (a b : ℝ) :
    IntervalIntegrable (fun alpha ↦ (primitiveShot N p alpha : ℂ))
      volume a b := by
  apply (intervalIntegrable_const (c := (N : ℝ) / (2 * (p : ℝ)))).mono_fun
  · exact (measurable_primitiveShot N p).complex_ofReal.aestronglyMeasurable
  · filter_upwards with alpha
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) / (2 * (p : ℝ)))]
    exact norm_primitiveShot_le N p alpha hp

theorem intervalIntegrable_primitiveShotFourierIntegrand
    (N n p : ℕ) (hp : 0 < p) (a b : ℝ) :
    IntervalIntegrable
      (fun alpha ↦ (primitiveShot N p alpha : ℂ) *
        paperExp (-(n : ℝ) * alpha)) volume a b := by
  apply (intervalIntegrable_const (c := (N : ℝ) / (2 * (p : ℝ)))).mono_fun
  · exact ((measurable_primitiveShot N p).complex_ofReal.mul
      (measurable_paperExp_cell.comp
        (measurable_const.mul measurable_id))).aestronglyMeasurable
  · filter_upwards with alpha
    rw [norm_mul, norm_paperExp_cell, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) / (2 * (p : ℝ)))]
    exact norm_primitiveShot_le N p alpha hp

/-- Exact finite Fourier coefficient of the whole primitive shot sum. -/
theorem unitFourierCoefficient_primitiveShotSum_eq
    (N P n : ℕ) :
    unitFourierCoefficient
        (fun alpha ↦ (primitiveShotSum N P alpha : ℂ)) n =
      ∑ p ∈ Finset.Icc 1 P,
        ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
          ramanujanSum p (n : ℤ) * nearestCellTransform N n p := by
  have hfun :
      (fun alpha ↦ (primitiveShotSum N P alpha : ℂ) *
        paperExp (-(n : ℝ) * alpha)) =
      fun alpha ↦ ∑ p ∈ Finset.Icc 1 P,
        (primitiveShot N p alpha : ℂ) * paperExp (-(n : ℝ) * alpha) := by
    funext alpha
    unfold primitiveShotSum
    push_cast
    rw [Finset.sum_mul]
  unfold unitFourierCoefficient
  rw [hfun, intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro p hpMem
    simpa only [unitFourierCoefficient] using!
      unitFourierCoefficient_primitiveShot_eq_ramanujan_of_pos
        N n p (Finset.mem_Icc.mp hpMem).1
  · intro p hpMem
    exact intervalIntegrable_primitiveShotFourierIntegrand N n p
      (Finset.mem_Icc.mp hpMem).1 0 1

/-- Fourier coefficient of the circle `L²` shot at a positive natural
frequency, identified with the concrete unit-interval coefficient. -/
theorem fourierCoeff_primitiveShotSumL2_nat
    (N P n : ℕ) :
    fourierCoeff
        (primitiveShotSumL2 N P : AddCircle (1 : ℝ) → ℂ) (n : ℤ) =
      unitFourierCoefficient
        (fun alpha ↦ (primitiveShotSum N P alpha : ℂ)) n := by
  rw [fourierCoeff_congr_ae (primitiveShotSumL2_coe_ae N P)]
  change fourierCoeff
      (AddCircle.liftIoc 1 0
        (fun alpha : ℝ ↦ (primitiveShotSum N P alpha : ℂ))) (n : ℤ) = _
  rw [fourierCoeff_liftIoc_eq]
  rw [fourierCoeffOn_eq_integral]
  unfold unitFourierCoefficient
  norm_num
  apply intervalIntegral.integral_congr
  intro alpha _halpha
  simp only
  have hphase :
      ((AddCircle.toCircle
          (-(n • (alpha : AddCircle ((0 : ℝ) + 1 - 0)))) : Circle) : ℂ) =
        paperExp (-(n : ℝ) * alpha) := by
    have hsmul :
        -(n • (alpha : AddCircle ((0 : ℝ) + 1 - 0))) =
          (-(n : ℤ)) • (alpha : AddCircle ((0 : ℝ) + 1 - 0)) := by
      simp
    rw [hsmul]
    change fourier (-(n : ℤ))
        (alpha : AddCircle ((0 : ℝ) + 1 - 0)) = _
    rw [fourier_coe_apply]
    unfold paperExp
    norm_num
    congr 1
    ring
  rw [hphase]
  simpa only [neg_mul] using!
    (mul_comm (paperExp (-(n : ℝ) * alpha))
      (primitiveShotSum N P alpha : ℂ))

/-- Exact positive-frequency coefficient of the reconstructed shot `Y_N`. -/
theorem fourierCoeff_reconstructedShotL2_nat (N n : ℕ) :
    fourierCoeff
        (reconstructedShotL2 N : AddCircle (1 : ℝ) → ℂ) (n : ℤ) =
      ∑ p ∈ Finset.Icc 1 N,
        ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
          ramanujanSum p (n : ℤ) * nearestCellTransform N n p := by
  rw [reconstructedShotL2, fourierCoeff_primitiveShotSumL2_nat,
    unitFourierCoefficient_primitiveShotSum_eq]

/-- The literal reconstructed shot has zero Fourier coefficient at the
origin. -/
theorem fourierCoeff_reconstructedShotL2_zero (N : ℕ) :
    fourierCoeff
        (reconstructedShotL2 N : AddCircle (1 : ℝ) → ℂ) 0 = 0 := by
  have h := fourierCoeff_reconstructedShotL2_nat N 0
  simp only [Nat.cast_zero] at h
  rw [h]
  apply Finset.sum_eq_zero
  intro p _hp
  rw [nearestCellTransform_zero]
  ring

end

end Erdos1002
