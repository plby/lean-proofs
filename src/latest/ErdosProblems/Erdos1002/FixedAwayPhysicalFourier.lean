import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import ErdosProblems.Erdos1002.FixedAwayPhysicalSubtraction
import ErdosProblems.Erdos1002.NearResonantCarrierSeries
import ErdosProblems.Erdos1002.NaturalCutoffWindowCarrierBridge
import ErdosProblems.Erdos1002.NaturalCutoffShotFullCoefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Fourier identification of the physical fixed-away cutoff

This file closes the analytic-to-physical bridge in the fixed-away argument.
The quotient `χ(v)/v` is an ordinary continuous function because the smooth
cutoff vanishes on a neighbourhood of zero.  Its integral over a nearest
rational cell is therefore a genuine interval integral, not an undeclared
principal value.
-/

open Filter MeasureTheory Set Finset AddCircle
open scoped BigOperators ComplexConjugate Real Topology

namespace Erdos1002

noncomputable section

/-- The nonsingular quotient used by the physical fixed-away shot. -/
def fixedAwaySmoothQuotient (t δ x : ℝ) : ℝ :=
  fixedAwaySmoothCutoff t δ x / x

theorem fixedAwaySmoothQuotient_eq_zero_of_abs_le_sub
    {t δ x : ℝ} (hδ : 0 < δ) (hx : |x| ≤ t - δ) :
    fixedAwaySmoothQuotient t δ x = 0 := by
  rw [fixedAwaySmoothQuotient,
    fixedAwaySmoothCutoff_eq_zero_of_abs_le_sub hδ hx, zero_div]

/-- The apparent pole is removable, uniformly on the whole line. -/
theorem continuous_fixedAwaySmoothQuotient
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) :
    Continuous (fixedAwaySmoothQuotient t δ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hgap : 0 < t - δ := sub_pos.mpr hδt
    have hevent : ∀ᶠ y : ℝ in 𝓝 0,
        fixedAwaySmoothQuotient t δ y = 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hgap] with y hy
      apply fixedAwaySmoothQuotient_eq_zero_of_abs_le_sub hδ
      simpa only [Real.dist_eq, sub_zero] using! (Metric.mem_ball.mp hy).le
    apply ContinuousAt.congr_of_eventuallyEq continuousAt_const
      (hevent.mono fun y hy ↦ hy)
  · exact ((fixedAwaySmoothCutoff_contDiff
      (m := (1 : ℕ∞)) t δ).continuous.continuousAt).div
        continuousAt_id hx

theorem fixedAwaySmoothQuotient_odd (t δ : ℝ) :
    Function.Odd (fixedAwaySmoothQuotient t δ) := by
  intro x
  unfold fixedAwaySmoothQuotient
  rw [fixedAwaySmoothCutoff_even t δ x]
  ring

/-- Ordinary finite Fourier transform of the smooth quotient. -/
def fixedAwaySmoothTruncation (t δ s R : ℝ) : ℂ :=
  ∫ v in -R..R,
    (fixedAwaySmoothQuotient t δ v : ℂ) * paperExp (-s * v)

/-- Pairing the two half intervals gives exactly the sine-kernel formula
used in the principal-value construction. -/
theorem fixedAwaySmoothTruncation_eq_paired
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (s R : ℝ) :
    fixedAwaySmoothTruncation t δ s R =
      pairedCutoffQuotientTruncation (fixedAwaySmoothCutoff t δ) s R := by
  let f : ℝ → ℂ := fun v ↦
    (fixedAwaySmoothQuotient t δ v : ℂ) * paperExp (-s * v)
  have hfcont : Continuous f := by
    dsimp [f]
    exact (Complex.continuous_ofReal.comp
      (continuous_fixedAwaySmoothQuotient hδ hδt)).mul (by
      unfold paperExp
      fun_prop)
  have hleft : IntervalIntegrable f volume (-R) 0 :=
    hfcont.intervalIntegrable _ _
  have hright : IntervalIntegrable f volume 0 R :=
    hfcont.intervalIntegrable _ _
  have hreflect : (∫ v in -R..0, f v) = ∫ v in 0..R, f (-v) := by
    simpa only [neg_zero] using!
      (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := R)).symm
  unfold fixedAwaySmoothTruncation
  change (∫ v in -R..R, f v) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright,
    hreflect]
  have hfneg : IntervalIntegrable (fun v ↦ f (-v)) volume 0 R :=
    (hfcont.comp continuous_neg).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add hfneg hright]
  unfold pairedCutoffQuotientTruncation
  let g : ℝ → ℝ := fun v ↦
    fixedAwaySmoothCutoff t δ v * sineKernel (2 * Real.pi * s) v
  calc
    (∫ v in 0..R, f (-v) + f v) =
        ∫ v in 0..R, (-2 * Complex.I) * (g v : ℂ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [(volume : Measure ℝ).ae_ne 0] with v hv _hv
      dsimp [f, g]
      rw [fixedAwaySmoothQuotient_odd t δ v]
      unfold fixedAwaySmoothQuotient
      have harg : 2 * Real.pi * (-s * v) =
          -(2 * Real.pi * s * v) := by ring
      have hdiff : paperExp (-s * v) - paperExp (s * v) =
          (-2 * Complex.I) * (Real.sin (2 * Real.pi * s * v) : ℂ) := by
        rw [paperExp_eq_cos_add_sin_mul_I,
          paperExp_eq_cos_add_sin_mul_I, harg,
          Real.cos_neg, Real.sin_neg]
        push_cast
        ring_nf
      have hsine : sineKernel (2 * Real.pi * s) v =
          Real.sin ((2 * Real.pi * s) * v) / v := by
        by_cases ha : 2 * Real.pi * s = 0
        · simp [sineKernel, ha]
        · have hs0 : s ≠ 0 := by
            intro hs
            subst s
            simp at ha
          rw [sineKernel, Real.sinc_of_ne_zero (mul_ne_zero ha hv)]
          field_simp [ha, hs0, hv]
      rw [show -s * -v = s * v by ring]
      push_cast
      rw [show
          -(fixedAwaySmoothCutoff t δ v / v : ℂ) * paperExp (s * v) +
              (fixedAwaySmoothCutoff t δ v / v : ℂ) * paperExp (-s * v) =
            (fixedAwaySmoothCutoff t δ v / v : ℂ) *
              (paperExp (-s * v) - paperExp (s * v)) by ring,
        hdiff, hsine]
      simp only [Complex.ofReal_div]
      have hvc : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv
      field_simp [hvc]
    _ = (-2 * Complex.I) * ∫ v in 0..R, (g v : ℂ) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (-2 * Complex.I) * (∫ v in 0..R, g v : ℝ) := by
      congr 1
      exact intervalIntegral.integral_ofReal

/-- Once the nearest cell reaches the support radius of the compact
correction, the ordinary smooth quotient integral is the rigorous
fixed-away transform. -/
theorem fixedAwaySmoothTruncation_eq_fixedAwayPVTruncation
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    {R : ℝ} (htR : t ≤ R) (s : ℝ) :
    fixedAwaySmoothTruncation t δ s R =
      fixedAwayPVTruncation (fixedAwaySmoothCorrection t δ) t s R := by
  rw [fixedAwaySmoothTruncation_eq_paired hδ hδt]
  rw [show fixedAwaySmoothCutoff t δ =
      fun v ↦ 1 - fixedAwaySmoothCorrection t δ v by
    funext v
    unfold fixedAwaySmoothCorrection
    ring]
  apply pairedCutoffQuotientTruncation_one_sub_eq
  · exact (fixedAwaySmoothCorrection_contDiff
      (m := (1 : ℕ∞)) t δ).continuous
  · exact (le_trans hδ.le hδt.le)
  · exact htR
  · intro v hv
    exact fixedAwaySmoothCorrection_eq_zero_of_le_abs hδ hδt.le
      (hv.trans (le_abs_self v))

/-- The sine integral depends only on the product of its frequency and
radius.  This form is valid without sign restrictions because interval
integrals are oriented. -/
theorem sineIntegralTruncation_eq_paperSineIntegral_mul
    (a R : ℝ) :
    sineIntegralTruncation a R = paperSineIntegral (a * R) := by
  unfold sineIntegralTruncation sineKernel paperSineIntegral
  rw [intervalIntegral.integral_const_mul]
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun x : ℝ ↦ Real.sinc x) a (a := (0 : ℝ)) (b := R)
  simp only [smul_eq_mul, mul_zero] at h
  exact h

theorem symmetricExponentialTruncation_scale_nat
    (m : ℤ) {p : ℕ} (hp : 0 < p) :
    symmetricExponentialTruncation
        ((m : ℝ) / (p : ℝ) ^ 2) ((p : ℝ) / 2) =
      symmetricExponentialTruncation
        ((m : ℝ) / (p : ℝ)) (1 / 2) := by
  rw [symmetricExponentialTruncation_eq,
    symmetricExponentialTruncation_eq,
    sineIntegralTruncation_eq_paperSineIntegral_mul,
    sineIntegralTruncation_eq_paperSineIntegral_mul]
  congr 2
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpR]

theorem signedExponentialPV_scale_nat
    (m : ℤ) {p : ℕ} (hp : 0 < p) :
    signedExponentialPV ((m : ℝ) / (p : ℝ)) =
      signedExponentialPV ((m : ℝ) / (p : ℝ) ^ 2) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · have hmR : (m : ℝ) < 0 := by exact_mod_cast hm
    have hleft : (m : ℝ) / (p : ℝ) < 0 := div_neg_of_neg_of_pos hmR hpR
    have hright : (m : ℝ) / (p : ℝ) ^ 2 < 0 :=
      div_neg_of_neg_of_pos hmR (sq_pos_of_pos hpR)
    simp [signedExponentialPV, hleft, hright,
      not_lt.mpr hleft.le, not_lt.mpr hright.le]
  · simp [signedExponentialPV]
  · have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hleft : 0 < (m : ℝ) / (p : ℝ) := div_pos hmR hpR
    have hright : 0 < (m : ℝ) / (p : ℝ) ^ 2 :=
      div_pos hmR (sq_pos_of_pos hpR)
    simp [signedExponentialPV, hleft, hright]

/-- The precise scalar identity behind the physical subtraction:
the smooth nearest-cell transform minus the natural-window coefficient is
the fixed-away multiplier at scale `p²`. -/
theorem fixedAwaySmoothTruncation_sub_windowKernelCoefficient
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    {p : ℕ} (hp : 0 < p) (htp : t ≤ (p : ℝ) / 2) (m : ℤ) :
    fixedAwaySmoothTruncation t δ
        ((m : ℝ) / (p : ℝ) ^ 2) ((p : ℝ) / 2) -
        windowKernelCoefficient p m =
      fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
        ((m : ℝ) / (p : ℝ) ^ 2) := by
  rw [fixedAwaySmoothTruncation_eq_fixedAwayPVTruncation
      hδ hδt htp,
    windowKernelCoefficient_eq_truncation_sub_principalValue p m hp,
    fixedAwayPVTruncation, fixedAwayPVTransform,
    symmetricExponentialTruncation_scale_nat m hp,
    signedExponentialPV_scale_nat m hp]
  ring

/-! ## Exact reduced-cell calculation for the smooth pole -/

/-- The fixed-away pole selected by the nearest primitive rational. -/
def fixedAwaySmoothPrimitivePole
    (t δ : ℝ) (p : ℕ) (alpha : ℝ) : ℂ :=
  if IsPrimitiveResonance p alpha then
    (fixedAwaySmoothQuotient t δ
      ((p : ℝ) * resonanceDelta p alpha) : ℂ)
  else 0

/-- The same pole on the affine cell with numerator `q`. -/
def fixedAwaySmoothPoleCell
    (t δ : ℝ) (p q : ℕ) (alpha : ℝ) : ℂ :=
  fixedAwaySmoothQuotient t δ
    ((p : ℝ) * ((p : ℝ) * alpha - (q : ℝ)))

def fixedAwaySmoothPoleCellFourierIntegral
    (t δ : ℝ) (n : ℤ) (p q : ℕ) : ℂ :=
  ∫ alpha in nearestCellLeft p q..nearestCellRight p q,
    fixedAwaySmoothPoleCell t δ p q alpha *
      paperExp (-(n : ℝ) * alpha)

private theorem paperExp_add_fixedAwayPhysical (u v : ℝ) :
    paperExp u * paperExp v = paperExp (u + v) := by
  unfold paperExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem fixedAwaySmoothPole_phase_split
    (n : ℤ) (p q : ℕ) (alpha : ℝ) (hp : 0 < p) :
    paperExp (-(n : ℝ) * alpha) =
      paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
        paperExp (-((n : ℝ) / (p : ℝ) ^ 2) *
          ((p : ℝ) ^ 2 * alpha - (p : ℝ) * (q : ℝ))) := by
  rw [paperExp_add_fixedAwayPhysical]
  congr 1
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpR]
  ring

/-- Affine change of variables on one cell, including the exact `p⁻²`
Jacobian and the residue phase. -/
theorem fixedAwaySmoothPoleCellFourierIntegral_eq
    (t δ : ℝ) (n : ℤ) (p q : ℕ) (hp : 0 < p) :
    fixedAwaySmoothPoleCellFourierIntegral t δ n p q =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
          fixedAwaySmoothTruncation t δ
            ((n : ℝ) / (p : ℝ) ^ 2) ((p : ℝ) / 2) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  let g : ℝ → ℂ := fun v ↦
    (fixedAwaySmoothQuotient t δ v : ℂ) *
      paperExp (-((n : ℝ) / (p : ℝ) ^ 2) * v)
  unfold fixedAwaySmoothPoleCellFourierIntegral
  calc
    (∫ alpha in nearestCellLeft p q..nearestCellRight p q,
        fixedAwaySmoothPoleCell t δ p q alpha *
          paperExp (-(n : ℝ) * alpha)) =
      ∫ alpha in nearestCellLeft p q..nearestCellRight p q,
        paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
          g ((p : ℝ) ^ 2 * alpha - (p : ℝ) * (q : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro alpha _halpha
        dsimp [g]
        rw [fixedAwaySmoothPole_phase_split n p q alpha hp]
        unfold fixedAwaySmoothPoleCell
        have harg :
            (p : ℝ) * ((p : ℝ) * alpha - (q : ℝ)) =
              (p : ℝ) ^ 2 * alpha - (p : ℝ) * (q : ℝ) := by ring
        rw [harg]
        ring
    _ = paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
        (∫ alpha in nearestCellLeft p q..nearestCellRight p q,
          g ((p : ℝ) ^ 2 * alpha - (p : ℝ) * (q : ℝ))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
        (((p : ℝ) ^ 2)⁻¹ •
          (∫ v in
              (p : ℝ) ^ 2 * nearestCellLeft p q - (p : ℝ) * (q : ℝ)..
              (p : ℝ) ^ 2 * nearestCellRight p q - (p : ℝ) * (q : ℝ),
            g v)) := by
      rw [intervalIntegral.integral_comp_mul_sub g (pow_ne_zero 2 hpR)
        ((p : ℝ) * (q : ℝ))]
    _ = ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
          fixedAwaySmoothTruncation t δ
            ((n : ℝ) / (p : ℝ) ^ 2) ((p : ℝ) / 2) := by
      rw [nearestCellLeft_sq_mul_sub p q hp,
        nearestCellRight_sq_mul_sub p q hp, Complex.real_smul]
      unfold fixedAwaySmoothTruncation
      dsimp [g]
      push_cast
      field_simp [hpR]

private theorem paperExp_eq_fourierChar_fixedAway (x : ℝ) :
    paperExp x = (Real.fourierChar x : ℂ) := by
  rw [Real.fourierChar_apply]
  unfold paperExp
  congr 1
  push_cast
  ring

theorem sum_reducedResidues_paperExp_neg_int (n : ℤ) (p : ℕ) :
    (∑ q ∈ reducedResidues p,
      paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ))) =
      ramanujanSum p n := by
  have hterm (q : ℕ) :
      paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) =
        ramanujanPhase p q (-n) := by
    rw [paperExp_eq_fourierChar_fixedAway]
    unfold ramanujanPhase
    congr 2
    push_cast
    ring
  simp_rw [hterm]
  exact ramanujanSum_even p n

def nearestFixedAwaySmoothPoleCellExpansion
    (t δ : ℝ) (p : ℕ) (alpha : ℝ) : ℂ :=
  ∑ q ∈ reducedResidues p,
    if (p : ℝ) * alpha - (q : ℝ) ∈
        Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) then
      fixedAwaySmoothPoleCell t δ p q alpha
    else 0

private theorem fixedAwaySmoothPrimitivePole_eq_cell_of_numerator
    {t δ : ℝ} {p : ℕ} {alpha : ℝ} {q : ℤ}
    (hprim : IsPrimitiveResonance p alpha)
    (hq : resonanceNumerator p alpha = q) :
    fixedAwaySmoothPrimitivePole t δ p alpha =
      fixedAwaySmoothQuotient t δ
        ((p : ℝ) * ((p : ℝ) * alpha - (q : ℝ))) := by
  unfold fixedAwaySmoothPrimitivePole
  rw [if_pos hprim]
  congr 2
  unfold resonanceDelta
  rw [hq]

theorem fixedAwaySmoothPrimitivePole_eq_cellExpansion
    {t δ : ℝ} {p : ℕ} (hp : 2 ≤ p) {alpha : ℝ}
    (halpha : alpha ∈ Ioo (0 : ℝ) 1) :
    fixedAwaySmoothPrimitivePole t δ p alpha =
      nearestFixedAwaySmoothPoleCellExpansion t δ p alpha := by
  classical
  by_cases hprim : IsPrimitiveResonance p alpha
  · let q : ℕ := (resonanceNumerator p alpha).natAbs
    have hqmem : q ∈ reducedResidues p :=
      resonanceNumerator_nat_mem_reducedResidues hp halpha hprim
    have hqnonneg : 0 ≤ resonanceNumerator p alpha :=
      (resonanceNumerator_bounds_of_mem_unitInterval p halpha).1
    have hqcast : (q : ℤ) = resonanceNumerator p alpha := by
      dsimp [q]
      rw [Int.natCast_natAbs, abs_of_nonneg hqnonneg]
    have hcell :
        (p : ℝ) * alpha - (q : ℝ) ∈
          Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
      rw [show (q : ℝ) = (resonanceNumerator p alpha : ℝ) by
        exact_mod_cast hqcast]
      exact resonanceDelta_mem p alpha
    symm
    unfold nearestFixedAwaySmoothPoleCellExpansion
    rw [Finset.sum_eq_single q]
    · rw [if_pos hcell]
      unfold fixedAwaySmoothPoleCell
      exact (fixedAwaySmoothPrimitivePole_eq_cell_of_numerator
        hprim hqcast.symm).symm
    · intro b hb hne
      have hnotcell :
          ¬ ((p : ℝ) * alpha - (b : ℝ) ∈
            Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)) := by
        intro hbcell
        have hnum : resonanceNumerator p alpha = (b : ℤ) :=
          resonanceNumerator_eq_of_delta_mem hbcell
        apply hne
        exact_mod_cast (hqcast.trans hnum).symm
      rw [if_neg hnotcell]
    · intro hqnot
      exact (hqnot hqmem).elim
  · have hzero : fixedAwaySmoothPrimitivePole t δ p alpha = 0 := by
      unfold fixedAwaySmoothPrimitivePole
      rw [if_neg hprim]
    rw [hzero]
    symm
    unfold nearestFixedAwaySmoothPoleCellExpansion
    apply Finset.sum_eq_zero
    intro q hqmem
    have hnotcell :
        ¬ ((p : ℝ) * alpha - (q : ℝ) ∈
          Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)) := by
      intro hcell
      apply hprim
      unfold IsPrimitiveResonance
      have hnum : resonanceNumerator p alpha = (q : ℤ) :=
        resonanceNumerator_eq_of_delta_mem hcell
      rw [hnum]
      have hqcop : Nat.Coprime q p := by
        rw [reducedResidues, Finset.mem_filter] at hqmem
        exact hqmem.2
      simpa using! hqcop
    rw [if_neg hnotcell]

def fixedAwaySmoothPoleCellFourierTerm
    (t δ : ℝ) (n : ℤ) (p q : ℕ) (alpha : ℝ) : ℂ :=
  if (p : ℝ) * alpha - (q : ℝ) ∈
      Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) then
    fixedAwaySmoothPoleCell t δ p q alpha *
      paperExp (-(n : ℝ) * alpha)
  else 0

theorem integrable_fixedAwaySmoothPoleCellFourierTerm
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (n : ℤ) (p q : ℕ) (hp : 0 < p) :
    Integrable (fixedAwaySmoothPoleCellFourierTerm t δ n p q) := by
  let f : ℝ → ℂ := fun alpha ↦
    fixedAwaySmoothPoleCell t δ p q alpha *
      paperExp (-(n : ℝ) * alpha)
  have hf : Continuous f := by
    dsimp [f]
    unfold fixedAwaySmoothPoleCell
    exact (Complex.continuous_ofReal.comp
      ((continuous_fixedAwaySmoothQuotient hδ hδt).comp
        (continuous_const.mul
          (continuous_const.mul continuous_id |>.sub continuous_const)))).mul (by
            unfold paperExp
            fun_prop)
  have hIoc : IntegrableOn f
      (Ioc (nearestCellLeft p q) (nearestCellRight p q)) :=
    hf.integrableOn_Ioc
  have hind : Integrable
      ((Ioc (nearestCellLeft p q) (nearestCellRight p q)).indicator f) :=
    (integrable_indicator_iff measurableSet_Ioc).2 hIoc
  apply hind.congr
  filter_upwards with alpha
  by_cases hmem : alpha ∈
      Ioc (nearestCellLeft p q) (nearestCellRight p q)
  · have hcell := (mem_nearestCell_iff hp alpha).2 hmem
    rw [Set.indicator_of_mem hmem,
      fixedAwaySmoothPoleCellFourierTerm, if_pos hcell]
  · have hcell : (p : ℝ) * alpha - (q : ℝ) ∉
        Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) :=
      fun h ↦ hmem ((mem_nearestCell_iff hp alpha).1 h)
    simp only [Set.indicator, if_neg hmem,
      fixedAwaySmoothPoleCellFourierTerm, if_neg hcell]

theorem support_fixedAwaySmoothPoleCellFourierTerm_subset
    (t δ : ℝ) (n : ℤ) (p q : ℕ) (hp : 0 < p) :
    Function.support (fixedAwaySmoothPoleCellFourierTerm t δ n p q) ⊆
      Ioc (nearestCellLeft p q) (nearestCellRight p q) := by
  intro alpha halpha
  by_contra hnot
  have hscaled :
      ¬ ((p : ℝ) * alpha - (q : ℝ) ∈
        Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)) :=
    fun h ↦ hnot ((mem_nearestCell_iff hp alpha).1 h)
  exact halpha (by
    rw [fixedAwaySmoothPoleCellFourierTerm, if_neg hscaled])

theorem integral_unit_fixedAwaySmoothPoleCellFourierTerm_eq
    (t δ : ℝ) (n : ℤ) (p q : ℕ) (hp : 2 ≤ p)
    (hq : q ∈ reducedResidues p) :
    (∫ alpha in (0 : ℝ)..1,
      fixedAwaySmoothPoleCellFourierTerm t δ n p q alpha) =
      fixedAwaySmoothPoleCellFourierIntegral t δ n p q := by
  have hp0 : 0 < p := by omega
  let f : ℝ → ℂ := fixedAwaySmoothPoleCellFourierTerm t δ n p q
  have hsupportCell : Function.support f ⊆
      Ioc (nearestCellLeft p q) (nearestCellRight p q) :=
    support_fixedAwaySmoothPoleCellFourierTerm_subset t δ n p q hp0
  have hsupportUnit : Function.support f ⊆ Ioc (0 : ℝ) 1 :=
    hsupportCell.trans (nearestCell_interval_subset_unit hp hq)
  calc
    (∫ alpha in (0 : ℝ)..1,
        fixedAwaySmoothPoleCellFourierTerm t δ n p q alpha) =
        ∫ alpha : ℝ, f alpha :=
      intervalIntegral.integral_eq_integral_of_support_subset hsupportUnit
    _ = ∫ alpha in nearestCellLeft p q..nearestCellRight p q,
        f alpha := by
      symm
      exact intervalIntegral.integral_eq_integral_of_support_subset hsupportCell
    _ = ∫ alpha in nearestCellLeft p q..nearestCellRight p q,
          fixedAwaySmoothPoleCell t δ p q alpha *
            paperExp (-(n : ℝ) * alpha) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with alpha
      intro halpha
      have hcell : alpha ∈
          Ioc (nearestCellLeft p q) (nearestCellRight p q) := by
        simpa only [Set.uIoc_of_le (nearestCellLeft_lt_right p q hp0).le]
          using! halpha
      change fixedAwaySmoothPoleCellFourierTerm t δ n p q alpha = _
      rw [fixedAwaySmoothPoleCellFourierTerm,
        if_pos ((mem_nearestCell_iff hp0 alpha).2 hcell)]
    _ = fixedAwaySmoothPoleCellFourierIntegral t δ n p q := rfl

theorem unitFourierCoefficientInt_cellExpansion_fixedAway
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (n : ℤ) (p : ℕ) (hp : 2 ≤ p) :
    unitFourierCoefficientInt
        (nearestFixedAwaySmoothPoleCellExpansion t δ p) n =
      ∑ q ∈ reducedResidues p,
        fixedAwaySmoothPoleCellFourierIntegral t δ n p q := by
  have hfun :
      (fun alpha ↦ nearestFixedAwaySmoothPoleCellExpansion t δ p alpha *
        paperExp (-(n : ℝ) * alpha)) =
      fun alpha ↦ ∑ q ∈ reducedResidues p,
        fixedAwaySmoothPoleCellFourierTerm t δ n p q alpha := by
    funext alpha
    unfold nearestFixedAwaySmoothPoleCellExpansion
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _hq
    by_cases hcell : (p : ℝ) * alpha - (q : ℝ) ∈
        Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)
    · rw [if_pos hcell, fixedAwaySmoothPoleCellFourierTerm, if_pos hcell]
    · rw [if_neg hcell, zero_mul,
        fixedAwaySmoothPoleCellFourierTerm, if_neg hcell]
  unfold unitFourierCoefficientInt
  rw [hfun, intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro q hq
    exact integral_unit_fixedAwaySmoothPoleCellFourierTerm_eq
      t δ n p q hp hq
  · intro q _hq
    exact (integrable_fixedAwaySmoothPoleCellFourierTerm
      hδ hδt n p q (by omega)).intervalIntegrable

theorem unitFourierCoefficientInt_fixedAwaySmoothPrimitivePole_eq_ramanujan
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (n : ℤ) (p : ℕ) (hp : 2 ≤ p) :
    unitFourierCoefficientInt (fixedAwaySmoothPrimitivePole t δ p) n =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) * ramanujanSum p n *
        fixedAwaySmoothTruncation t δ
          ((n : ℝ) / (p : ℝ) ^ 2) ((p : ℝ) / 2) := by
  rw [show unitFourierCoefficientInt
      (fixedAwaySmoothPrimitivePole t δ p) n =
        unitFourierCoefficientInt
          (nearestFixedAwaySmoothPoleCellExpansion t δ p) n by
    unfold unitFourierCoefficientInt
    apply intervalIntegral.integral_congr_ae
    have hone : ∀ᵐ alpha : ℝ ∂volume, alpha ≠ 1 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hone] with alpha halphaOne
    intro halpha
    have hmem : alpha ∈ Ioo (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at halpha
      exact ⟨halpha.1, lt_of_le_of_ne halpha.2 halphaOne⟩
    rw [fixedAwaySmoothPrimitivePole_eq_cellExpansion hp hmem]]
  rw [unitFourierCoefficientInt_cellExpansion_fixedAway hδ hδt n p hp]
  simp_rw [fixedAwaySmoothPoleCellFourierIntegral_eq t δ n p _ (by omega)]
  rw [← Finset.sum_mul, ← Finset.mul_sum,
    sum_reducedResidues_paperExp_neg_int]

private theorem paperExp_int_fixedAwayPhysical (z : ℤ) :
    paperExp (z : ℝ) = 1 := by
  unfold paperExp
  convert! Complex.exp_int_mul_two_pi_mul_I z using 2
  push_cast
  ring

theorem fixedAwaySmoothPrimitivePole_one_periodic (t δ : ℝ) :
    Function.Periodic (fixedAwaySmoothPrimitivePole t δ 1) 1 := by
  intro alpha
  unfold fixedAwaySmoothPrimitivePole
  rw [if_pos (isPrimitiveResonance_one (alpha + 1)),
    if_pos (isPrimitiveResonance_one alpha)]
  have hdelta : resonanceDelta 1 (alpha + 1) = resonanceDelta 1 alpha := by
    simpa using! resonanceDelta_add_int 1 alpha (1 : ℤ)
  rw [hdelta]

theorem fixedAwaySmoothPrimitivePoleFourierIntegrand_one_periodic
    (t δ : ℝ) (n : ℤ) :
    Function.Periodic
      (fun alpha ↦ fixedAwaySmoothPrimitivePole t δ 1 alpha *
        paperExp (-(n : ℝ) * alpha)) 1 := by
  intro alpha
  change fixedAwaySmoothPrimitivePole t δ 1 (alpha + 1) *
      paperExp (-(n : ℝ) * (alpha + 1)) = _
  rw [fixedAwaySmoothPrimitivePole_one_periodic t δ alpha]
  have harg :
      -(n : ℝ) * (alpha + 1) =
        -(n : ℝ) * alpha + ((-n : ℤ) : ℝ) := by
    push_cast
    ring
  rw [harg, ← paperExp_add_fixedAwayPhysical,
    paperExp_int_fixedAwayPhysical, mul_one]

theorem unitFourierCoefficientInt_fixedAwaySmoothPrimitivePole_one
    (t δ : ℝ) (n : ℤ) :
    unitFourierCoefficientInt (fixedAwaySmoothPrimitivePole t δ 1) n =
      fixedAwaySmoothPoleCellFourierIntegral t δ n 1 0 := by
  let f : ℝ → ℂ := fun alpha ↦ fixedAwaySmoothPrimitivePole t δ 1 alpha *
    paperExp (-(n : ℝ) * alpha)
  have hperiod : Function.Periodic f 1 :=
    fixedAwaySmoothPrimitivePoleFourierIntegrand_one_periodic t δ n
  have hshift := hperiod.intervalIntegral_add_eq
    (0 : ℝ) (-(1 : ℝ) / 2)
  have hinterval :
      (∫ alpha in (0 : ℝ)..1, f alpha) =
        ∫ alpha in (-(1 : ℝ) / 2)..((1 : ℝ) / 2), f alpha := by
    convert! hshift using 1 <;> norm_num
  unfold unitFourierCoefficientInt
  change (∫ alpha in (0 : ℝ)..1, f alpha) = _
  rw [hinterval]
  unfold fixedAwaySmoothPoleCellFourierIntegral
  norm_num [nearestCellLeft, nearestCellRight]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with alpha
  intro halpha
  have hcell : alpha ∈ Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
    have halpha' : alpha ∈
        uIoc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
      simpa only [neg_div] using! halpha
    rw [Set.uIoc_of_le
      (by norm_num : (-(1 : ℝ) / 2) ≤ (1 : ℝ) / 2)] at halpha'
    exact halpha'
  have hnum : resonanceNumerator 1 alpha = 0 := by
    apply resonanceNumerator_eq_of_delta_mem
    simpa only [Nat.cast_one, one_mul, Int.cast_zero, sub_zero] using! hcell
  dsimp [f]
  unfold fixedAwaySmoothPrimitivePole fixedAwaySmoothPoleCell resonanceDelta
  rw [if_pos (isPrimitiveResonance_one alpha), hnum]
  norm_num

/-- Uniform exact coefficient formula, including the endpoint denominator
`p = 1`. -/
theorem unitFourierCoefficientInt_fixedAwaySmoothPrimitivePole_eq_ramanujan_of_pos
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (n : ℤ) (p : ℕ) (hp : 0 < p) :
    unitFourierCoefficientInt (fixedAwaySmoothPrimitivePole t δ p) n =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) * ramanujanSum p n *
        fixedAwaySmoothTruncation t δ
          ((n : ℝ) / (p : ℝ) ^ 2) ((p : ℝ) / 2) := by
  by_cases hpone : p = 1
  · subst p
    rw [unitFourierCoefficientInt_fixedAwaySmoothPrimitivePole_one
      t δ n,
      fixedAwaySmoothPoleCellFourierIntegral_eq t δ n 1 0 (by omega)]
    simp [paperExp]
  · exact unitFourierCoefficientInt_fixedAwaySmoothPrimitivePole_eq_ramanujan
      hδ hδt n p (by omega)

/-! ## Bernoulli carriers and termwise Fourier integration -/

theorem norm_paperExp_fixedAwayPhysical (x : ℝ) : ‖paperExp x‖ = 1 := by
  rw [paperExp, Complex.norm_exp]
  simp

theorem norm_fixedAwaySmoothQuotient_le_gapInv
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (x : ℝ) :
    ‖fixedAwaySmoothQuotient t δ x‖ ≤ (t - δ)⁻¹ := by
  have hgap : 0 < t - δ := sub_pos.mpr hδt
  by_cases hx : |x| ≤ t - δ
  · rw [fixedAwaySmoothQuotient_eq_zero_of_abs_le_sub hδ hx, norm_zero]
    exact inv_nonneg.mpr hgap.le
  · have hxgap : t - δ ≤ |x| := le_of_not_ge hx
    have hxpos : 0 < |x| := hgap.trans_le hxgap
    unfold fixedAwaySmoothQuotient
    rw [Real.norm_eq_abs, abs_div]
    have hcut := fixedAwaySmoothCutoff_mem_Icc hδ hδt.le x
    calc
      |fixedAwaySmoothCutoff t δ x| / |x| ≤ 1 / |x| := by
        gcongr
        simpa only [abs_of_nonneg hcut.1] using! hcut.2
      _ ≤ 1 / (t - δ) := one_div_le_one_div_of_le hgap hxgap
      _ = (t - δ)⁻¹ := one_div _

theorem measurable_fixedAwaySmoothPrimitivePole
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (p : ℕ) :
    Measurable (fixedAwaySmoothPrimitivePole t δ p) := by
  unfold fixedAwaySmoothPrimitivePole
  apply Measurable.ite (measurableSet_isPrimitiveResonance p)
  · exact (Complex.continuous_ofReal.comp
      (continuous_fixedAwaySmoothQuotient hδ hδt) |>.measurable).comp
        (measurable_const.mul (measurable_resonanceDelta p))
  · exact measurable_const

theorem norm_fixedAwaySmoothPrimitivePole_le_gapInv
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (p : ℕ) (alpha : ℝ) :
    ‖fixedAwaySmoothPrimitivePole t δ p alpha‖ ≤ (t - δ)⁻¹ := by
  unfold fixedAwaySmoothPrimitivePole
  split_ifs
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using!
      norm_fixedAwaySmoothQuotient_le_gapInv hδ hδt
        ((p : ℝ) * resonanceDelta p alpha)
  · simpa only [norm_zero] using! (inv_nonneg.mpr (sub_pos.mpr hδt).le)

/-- Exact factorization of the smooth physical shot into its periodic mark
and its primitive pole. -/
theorem fixedAwaySmoothShotTerm_eq_mark_mul_pole
    (t δ : ℝ) (N p : ℕ) (alpha : ℝ) :
    fixedAwaySmoothShotTerm t δ N p alpha =
      (bernoulliMark ((N * p : ℕ) * alpha) : ℂ) *
        fixedAwaySmoothPrimitivePole t δ p alpha := by
  rw [bernoulliMark_nat_mul_eq_resonanceDelta]
  by_cases hprim : IsPrimitiveResonance p alpha
  · rw [fixedAwaySmoothShotTerm, primitiveShot_of_primitive N p alpha hprim]
    unfold fixedAwaySmoothPrimitivePole fixedAwaySmoothQuotient
    rw [if_pos hprim]
    push_cast
    ring
  · rw [fixedAwaySmoothShotTerm, primitiveShot_of_not_primitive N p alpha hprim]
    unfold fixedAwaySmoothPrimitivePole
    rw [if_neg hprim]
    simp

/-- The actual physical `ell`-carrier for one fixed-away denominator. -/
def fixedAwaySmoothPoleCarrierTerm
    (N : ℕ) (ell : ℤ) (t δ : ℝ) (p : ℕ) (alpha : ℝ) : ℂ :=
  bernoulliMarkFourierCoefficient ell *
    unitModulate (nearBernoulliCarrierFrequency N p ell)
      (fixedAwaySmoothPrimitivePole t δ p) alpha

theorem measurable_fixedAwaySmoothPoleCarrierTerm
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (N : ℕ) (ell : ℤ) (p : ℕ) :
    Measurable (fixedAwaySmoothPoleCarrierTerm N ell t δ p) := by
  unfold fixedAwaySmoothPoleCarrierTerm unitModulate
  exact measurable_const.mul
    (((by
      unfold paperExp
      fun_prop : Continuous fun alpha : ℝ ↦
        paperExp ((nearBernoulliCarrierFrequency N p ell : ℝ) * alpha)).measurable).mul
      (measurable_fixedAwaySmoothPrimitivePole hδ hδt p))

theorem norm_fixedAwaySmoothPoleCarrierTerm_le
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (N : ℕ) (ell : ℤ) (p : ℕ) (alpha : ℝ) :
    ‖fixedAwaySmoothPoleCarrierTerm N ell t δ p alpha‖ ≤
      bernoulliCarrierMajorant ell * (t - δ)⁻¹ := by
  unfold fixedAwaySmoothPoleCarrierTerm unitModulate
  rw [norm_mul, norm_mul, norm_paperExp_fixedAwayPhysical, one_mul]
  exact (mul_le_mul
    (norm_bernoulliMarkFourierCoefficient_le_majorant ell)
    (norm_fixedAwaySmoothPrimitivePole_le_gapInv hδ hδt p alpha)
    (norm_nonneg _) (bernoulliCarrierMajorant_nonneg ell))

theorem hasSum_fixedAwaySmoothPoleCarrierTerm
    (N : ℕ) (t δ : ℝ) (p : ℕ) (alpha : ℝ) :
    HasSum
      (fun ell : ℤ ↦ fixedAwaySmoothPoleCarrierTerm N ell t δ p alpha)
      (fixedAwaySmoothShotTerm t δ N p alpha) := by
  have h := (hasSum_bernoulliMark_pointwiseFourier
    (((N * p : ℕ) : ℝ) * alpha)).mul_right
      (fixedAwaySmoothPrimitivePole t δ p alpha)
  rw [fixedAwaySmoothShotTerm_eq_mark_mul_pole]
  convert! h using 1
  funext ell
  unfold fixedAwaySmoothPoleCarrierTerm unitModulate
    nearBernoulliCarrierFrequency
  push_cast
  ring_nf

theorem hasSum_unitFourierCoefficientInt_fixedAwaySmoothPoleCarrierTerm
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (N : ℕ) (n : ℤ) (p : ℕ) :
    HasSum
      (fun ell : ℤ ↦ unitFourierCoefficientInt
        (fixedAwaySmoothPoleCarrierTerm N ell t δ p) n)
      (unitFourierCoefficientInt (fixedAwaySmoothShotTerm t δ N p) n) := by
  let F : ℤ → ℝ → ℂ := fun ell alpha ↦
    fixedAwaySmoothPoleCarrierTerm N ell t δ p alpha *
      paperExp (-(n : ℝ) * alpha)
  let f : ℝ → ℂ := fun alpha ↦
    fixedAwaySmoothShotTerm t δ N p alpha *
      paperExp (-(n : ℝ) * alpha)
  let bound : ℤ → ℝ → ℝ := fun ell _alpha ↦
    bernoulliCarrierMajorant ell * (t - δ)⁻¹
  have hFmeas : ∀ ell : ℤ,
      AEStronglyMeasurable (F ell)
        (volume.restrict (uIoc (0 : ℝ) 1)) := by
    intro ell
    exact ((measurable_fixedAwaySmoothPoleCarrierTerm
      hδ hδt N ell p).mul ((by
        unfold paperExp
        fun_prop : Continuous fun alpha : ℝ ↦
          paperExp (-(n : ℝ) * alpha)).measurable)).aestronglyMeasurable.restrict
  have hbound : ∀ ell : ℤ, ∀ᵐ alpha : ℝ ∂volume,
      alpha ∈ uIoc (0 : ℝ) 1 → ‖F ell alpha‖ ≤ bound ell alpha := by
    intro ell
    filter_upwards with alpha
    intro _halpha
    dsimp [F, bound]
    rw [norm_mul, norm_paperExp_fixedAwayPhysical, mul_one]
    exact norm_fixedAwaySmoothPoleCarrierTerm_le hδ hδt N ell p alpha
  have hboundSum : ∀ᵐ alpha : ℝ ∂volume,
      alpha ∈ uIoc (0 : ℝ) 1 → Summable fun ell : ℤ ↦ bound ell alpha := by
    filter_upwards with alpha
    intro _halpha
    simpa only [bound] using!
      summable_bernoulliCarrierMajorant.mul_right (t - δ)⁻¹
  have hboundInt : IntervalIntegrable
      (fun alpha : ℝ ↦ ∑' ell : ℤ, bound ell alpha) volume 0 1 := by
    have heq : (fun alpha : ℝ ↦ ∑' ell : ℤ, bound ell alpha) =
        fun _alpha : ℝ ↦ windowCarrierMassConstant * (t - δ)⁻¹ := by
      funext alpha
      dsimp [bound, windowCarrierMassConstant]
      rw [tsum_mul_right]
    rw [heq]
    exact intervalIntegrable_const
  have hlim : ∀ᵐ alpha : ℝ ∂volume,
      alpha ∈ uIoc (0 : ℝ) 1 →
        HasSum (fun ell : ℤ ↦ F ell alpha) (f alpha) := by
    filter_upwards with alpha
    intro _halpha
    exact (hasSum_fixedAwaySmoothPoleCarrierTerm N t δ p alpha).mul_right
      (paperExp (-(n : ℝ) * alpha))
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    bound hFmeas hbound hboundSum hboundInt hlim
  simpa only [unitFourierCoefficientInt, F, f] using! h

theorem unitFourierCoefficientInt_fixedAwaySmoothPoleCarrierTerm
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (N : ℕ) (ell n : ℤ) (p : ℕ) (hp : 0 < p) :
    unitFourierCoefficientInt
        (fixedAwaySmoothPoleCarrierTerm N ell t δ p) n =
      bernoulliMarkFourierCoefficient ell *
        (((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) * ramanujanSum p n *
          fixedAwaySmoothTruncation t δ
            (((n - nearBernoulliCarrierFrequency N p ell : ℤ) : ℝ) /
              (p : ℝ) ^ 2) ((p : ℝ) / 2)) := by
  unfold fixedAwaySmoothPoleCarrierTerm
  rw [unitFourierCoefficientInt_const_mul,
    unitFourierCoefficientInt_unitModulate,
    unitFourierCoefficientInt_fixedAwaySmoothPrimitivePole_eq_ramanujan_of_pos
      hδ hδt _ p hp]
  have hram : ramanujanSum p
      (n - nearBernoulliCarrierFrequency N p ell) = ramanujanSum p n := by
    have hper := (ramanujanSum_periodic p).int_mul
      (-(ell * (N : ℤ))) n
    have harg :
        n + (-(ell * (N : ℤ))) * (p : ℤ) =
          n - nearBernoulliCarrierFrequency N p ell := by
      unfold nearBernoulliCarrierFrequency
      push_cast
      ring
    change ramanujanSum p
      (n + (-(ell * (N : ℤ))) * (p : ℤ)) = ramanujanSum p n at hper
    rw [harg] at hper
    exact hper
  rw [hram]

/-! ## Coefficient blocks and cancellation of the natural window -/

def fixedAwaySmoothShiftedProfile
    (t δ : ℝ) (N : ℕ) (ell : ℤ) (p : ℕ) (n : ℤ) : ℂ :=
  fixedAwaySmoothTruncation t δ
    (((n - nearBernoulliCarrierFrequency N p ell : ℤ) : ℝ) /
      (p : ℝ) ^ 2) ((p : ℝ) / 2)

def fixedAwayWindowShiftedProfile
    (N : ℕ) (ell : ℤ) (p : ℕ) (n : ℤ) : ℂ :=
  windowKernelCoefficient p
    (n - nearBernoulliCarrierFrequency N p ell)

def fixedAwaySmoothCarrierBlock
    (P : ℕ) (t δ : ℝ) (N : ℕ) (ell : ℤ) (n : ℤ) : ℂ :=
  fixedAwayRamanujanProfileBlock (Finset.Icc 1 P)
    (fixedAwaySmoothShiftedProfile t δ N ell) n

def fixedAwayWindowCarrierBlock
    (P N : ℕ) (ell : ℤ) (n : ℤ) : ℂ :=
  fixedAwayRamanujanProfileBlock (Finset.Icc 1 P)
    (fixedAwayWindowShiftedProfile N ell) n

def fixedAwayFullCarrierBlock
    (P : ℕ) (t δ : ℝ) (N : ℕ) (ell : ℤ) (n : ℤ) : ℂ :=
  fixedAwayRamanujanProfileBlock (Finset.Icc 1 P)
    (fixedAwayShiftedProfile t δ N ell) n

/-- Denominator by denominator, smooth cell minus natural window is the
fixed-away `Rχ` profile.  The single hypothesis `t ≤ 1/2` covers every
positive denominator, including `p=1`. -/
theorem fixedAwaySmoothCarrierBlock_sub_window_eq_full
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (ht : t ≤ 1 / 2)
    (P N : ℕ) (ell n : ℤ) :
    fixedAwaySmoothCarrierBlock P t δ N ell n -
        fixedAwayWindowCarrierBlock P N ell n =
      fixedAwayFullCarrierBlock P t δ N ell n := by
  unfold fixedAwaySmoothCarrierBlock fixedAwayWindowCarrierBlock
    fixedAwayFullCarrierBlock fixedAwayRamanujanProfileBlock
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hpMem
  have hp : 0 < p := (Finset.mem_Icc.mp hpMem).1
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have htp : t ≤ (p : ℝ) / 2 := ht.trans (by linarith)
  unfold fixedAwayRamanujanProfileTerm fixedAwaySmoothShiftedProfile
    fixedAwayWindowShiftedProfile fixedAwayShiftedProfile
    fixedAwayScaledPV
  rw [← mul_sub]
  rw [fixedAwaySmoothTruncation_sub_windowKernelCoefficient
    hδ hδt hp htp
      (n - nearBernoulliCarrierFrequency N p ell)]
  push_cast
  ring

theorem unitFourierCoefficientInt_fixedAwaySmoothPoleCarrierTerm_eq_blockTerm
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (N : ℕ) (ell n : ℤ) (p : ℕ) (hp : 0 < p) :
    unitFourierCoefficientInt
        (fixedAwaySmoothPoleCarrierTerm N ell t δ p) n =
      bernoulliMarkFourierCoefficient ell *
        fixedAwayRamanujanProfileTerm
          (fixedAwaySmoothShiftedProfile t δ N ell) p n := by
  rw [unitFourierCoefficientInt_fixedAwaySmoothPoleCarrierTerm
    hδ hδt N ell n p hp]
  unfold fixedAwayRamanujanProfileTerm fixedAwaySmoothShiftedProfile
  rw [ramanujanSum_even p n]

theorem windowCarrierKernelTerm_eq_blockTerm
    (N : ℕ) (ell n : ℤ) (p : ℕ) :
    (((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) * ramanujanSum p n) *
        windowCarrierKernelTerm N p n ell =
      bernoulliMarkFourierCoefficient ell *
        fixedAwayRamanujanProfileTerm
          (fixedAwayWindowShiftedProfile N ell) p n := by
  unfold windowCarrierKernelTerm fixedAwayRamanujanProfileTerm
    fixedAwayWindowShiftedProfile nearBernoulliCarrierFrequency
  rw [ramanujanSum_even p n]
  ring

theorem intervalIntegrable_fixedAwaySmoothShotFourierIntegrand
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (N : ℕ) (n : ℤ) (p : ℕ) (hp : 0 < p) :
    IntervalIntegrable
      (fun alpha ↦ fixedAwaySmoothShotTerm t δ N p alpha *
        paperExp (-(n : ℝ) * alpha)) volume 0 1 := by
  apply (intervalIntegrable_const (c := (N : ℝ) / (2 * (p : ℝ)))).mono_fun
  · exact ((measurable_fixedAwaySmoothShotTerm t δ N p).mul ((by
      unfold paperExp
      fun_prop : Continuous fun alpha : ℝ ↦
        paperExp (-(n : ℝ) * alpha)).measurable)).aestronglyMeasurable
  · filter_upwards with alpha
    rw [norm_mul, norm_paperExp_fixedAwayPhysical, mul_one,
      Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) / (2 * (p : ℝ)))]
    exact norm_fixedAwaySmoothShotTerm_le hδ hδt.le N p alpha |>.trans
      (norm_primitiveShot_le N p alpha hp)

theorem unitFourierCoefficientInt_fixedAwaySmoothShotSum_eq_sum
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (N P : ℕ) (n : ℤ) :
    unitFourierCoefficientInt (fixedAwaySmoothShotSum t δ N P) n =
      ∑ p ∈ Finset.Icc 1 P,
        unitFourierCoefficientInt (fixedAwaySmoothShotTerm t δ N p) n := by
  unfold unitFourierCoefficientInt fixedAwaySmoothShotSum
  rw [show (fun alpha ↦
      (∑ p ∈ Finset.Icc 1 P, fixedAwaySmoothShotTerm t δ N p alpha) *
        paperExp (-(n : ℝ) * alpha)) =
      fun alpha ↦ ∑ p ∈ Finset.Icc 1 P,
        fixedAwaySmoothShotTerm t δ N p alpha *
          paperExp (-(n : ℝ) * alpha) by
    funext alpha
    rw [Finset.sum_mul]]
  rw [intervalIntegral.integral_finset_sum]
  intro p hpMem
  exact intervalIntegrable_fixedAwaySmoothShotFourierIntegrand
    hδ hδt N n p (Finset.mem_Icc.mp hpMem).1

/-- Complete carrier expansion of every Fourier coefficient of the literal
smooth physical shot.  Both the denominator sum and the carrier sum have
been exchanged by finite `HasSum` algebra after the dominated-convergence
theorem above. -/
theorem hasSum_fixedAwaySmoothCarrierBlock
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (N P : ℕ) (n : ℤ) :
    HasSum
      (fun ell : ℤ ↦ bernoulliMarkFourierCoefficient ell *
        fixedAwaySmoothCarrierBlock P t δ N ell n)
      (unitFourierCoefficientInt (fixedAwaySmoothShotSum t δ N P) n) := by
  let S : Finset ℕ := Finset.Icc 1 P
  have hpHas : ∀ p ∈ S,
      HasSum
        (fun ell : ℤ ↦ unitFourierCoefficientInt
          (fixedAwaySmoothPoleCarrierTerm N ell t δ p) n)
        (unitFourierCoefficientInt (fixedAwaySmoothShotTerm t δ N p) n) := by
    intro p _hp
    exact hasSum_unitFourierCoefficientInt_fixedAwaySmoothPoleCarrierTerm
      hδ hδt N n p
  have hfiniteAux : ∀ T : Finset ℕ,
      (∀ p ∈ T, HasSum
        (fun ell : ℤ ↦ unitFourierCoefficientInt
          (fixedAwaySmoothPoleCarrierTerm N ell t δ p) n)
        (unitFourierCoefficientInt (fixedAwaySmoothShotTerm t δ N p) n)) →
      HasSum
        (fun ell : ℤ ↦ ∑ p ∈ T,
          unitFourierCoefficientInt
            (fixedAwaySmoothPoleCarrierTerm N ell t δ p) n)
        (∑ p ∈ T,
          unitFourierCoefficientInt (fixedAwaySmoothShotTerm t δ N p) n) := by
    intro T hT
    induction T using Finset.induction_on with
    | empty =>
        simpa using! (hasSum_zero : HasSum (fun _ell : ℤ ↦ (0 : ℂ)) 0)
    | @insert p T hpNot ih =>
        have hpOne := hT p (Finset.mem_insert_self p T)
        have hrest := ih fun q hq ↦ hT q (Finset.mem_insert_of_mem hq)
        simpa only [Finset.sum_insert hpNot] using! hpOne.add hrest
  have hfinite : HasSum
      (fun ell : ℤ ↦ ∑ p ∈ S,
        unitFourierCoefficientInt
          (fixedAwaySmoothPoleCarrierTerm N ell t δ p) n)
      (∑ p ∈ S,
        unitFourierCoefficientInt (fixedAwaySmoothShotTerm t δ N p) n) :=
    hfiniteAux S hpHas
  convert! hfinite using 1
  · funext ell
    unfold fixedAwaySmoothCarrierBlock fixedAwayRamanujanProfileBlock
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hpMem
    exact (unitFourierCoefficientInt_fixedAwaySmoothPoleCarrierTerm_eq_blockTerm
      hδ hδt N ell n p (Finset.mem_Icc.mp hpMem).1).symm
  · simpa only [S] using!
      unitFourierCoefficientInt_fixedAwaySmoothShotSum_eq_sum
        hδ hδt N P n

/-- Carrier expansion of the natural-window correction at every positive
frequency.  The sign is explicit: the natural reconstruction error is the
negative of the window-carrier block. -/
theorem hasSum_fixedAwayWindowCarrierBlock_pos
    (N : ℕ+) (n : ℕ) (hn : 0 < n) :
    HasSum
      (fun ell : ℤ ↦ bernoulliMarkFourierCoefficient ell *
        fixedAwayWindowCarrierBlock (N : ℕ) (N : ℕ) ell (n : ℤ))
      (-naturalCutoffShotErrorCoefficient N (n : ℤ)) := by
  let S : Finset ℕ := Finset.Icc 1 (N : ℕ)
  let A : ℕ → ℂ := fun p ↦
    ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) * ramanujanSum p (n : ℤ)
  have hpHas : ∀ p ∈ S,
      HasSum
        (fun ell : ℤ ↦ A p *
          windowCarrierKernelTerm (N : ℕ) p (n : ℤ) ell)
        (-(A p * nearestCellWindowTransform (N : ℕ) n p)) := by
    intro p hpMem
    have hp : 0 < p := (Finset.mem_Icc.mp hpMem).1
    have hs := (summable_windowCarrierKernelTerm
      (N : ℕ) p (n : ℤ) hp).hasSum.mul_left (A p)
    have hcarrier := nearestCellWindowTransform_eq_neg_tsum_carrier
      (N : ℕ) n p N.pos hn hp
    convert! hs using 1
    rw [hcarrier]
    ring
  have hfiniteAux : ∀ T : Finset ℕ,
      (∀ p ∈ T, HasSum
        (fun ell : ℤ ↦ A p *
          windowCarrierKernelTerm (N : ℕ) p (n : ℤ) ell)
        (-(A p * nearestCellWindowTransform (N : ℕ) n p))) →
      HasSum
        (fun ell : ℤ ↦ ∑ p ∈ T,
          A p * windowCarrierKernelTerm (N : ℕ) p (n : ℤ) ell)
        (∑ p ∈ T,
          -(A p * nearestCellWindowTransform (N : ℕ) n p)) := by
    intro T hT
    induction T using Finset.induction_on with
    | empty =>
        simpa using! (hasSum_zero : HasSum (fun _ell : ℤ ↦ (0 : ℂ)) 0)
    | @insert p T hpNot ih =>
        have hpOne := hT p (Finset.mem_insert_self p T)
        have hrest := ih fun q hq ↦ hT q (Finset.mem_insert_of_mem hq)
        simpa only [Finset.sum_insert hpNot] using! hpOne.add hrest
  have hfinite := hfiniteAux S hpHas
  convert! hfinite using 1
  · funext ell
    unfold fixedAwayWindowCarrierBlock fixedAwayRamanujanProfileBlock
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _hpMem
    simpa only [A] using!
      (windowCarrierKernelTerm_eq_blockTerm
        (N : ℕ) ell (n : ℤ) p).symm
  · rw [naturalCutoffShotErrorCoefficient_nat N n hn]
    simp only [S, A]
    rw [Finset.sum_neg_distrib]

/-- The smooth physical coefficient and the natural-window error combine
carrier by carrier into the full `Rχ` coefficient block. -/
theorem hasSum_fixedAwayFullCarrierBlock_pos
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (ht : t ≤ 1 / 2)
    (N : ℕ+) (n : ℕ) (hn : 0 < n) :
    HasSum
      (fun ell : ℤ ↦ bernoulliMarkFourierCoefficient ell *
        fixedAwayFullCarrierBlock (N : ℕ) t δ (N : ℕ) ell (n : ℤ))
      (unitFourierCoefficientInt
          (fixedAwaySmoothShotSum t δ (N : ℕ) (N : ℕ)) (n : ℤ) +
        naturalCutoffShotErrorCoefficient N (n : ℤ)) := by
  have hsmooth := hasSum_fixedAwaySmoothCarrierBlock
    hδ hδt (N : ℕ) (N : ℕ) (n : ℤ)
  have hwindow := hasSum_fixedAwayWindowCarrierBlock_pos N n hn
  have hsub := hsmooth.sub hwindow
  convert! hsub using 1
  · funext ell
    rw [← mul_sub]
    rw [fixedAwaySmoothCarrierBlock_sub_window_eq_full
      hδ hδt ht (N : ℕ) (N : ℕ) ell (n : ℤ)]
  · ring

/-- The subtraction definition is equivalently smooth physical shot plus
the already constructed natural-window error. -/
theorem fixedAwaySmoothReconstructionL2_eq_shot_add_error
    (N : ℕ+) {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) :
    fixedAwaySmoothReconstructionL2 N (N : ℕ) t δ hδ hδt.le =
      fixedAwaySmoothShotL2 t δ (N : ℕ) (N : ℕ) hδ hδt.le +
        naturalCutoffShotErrorL2 N := by
  unfold fixedAwaySmoothReconstructionL2 naturalCutoffShotErrorL2
  have hdecomp := fixedAwaySmoothShotL2_add_correction
    hδ hδt.le (N : ℕ) (N : ℕ)
  rw [show primitiveShotSumL2 (N : ℕ) (N : ℕ) =
      reconstructedShotL2 (N : ℕ) by rfl] at hdecomp
  rw [← hdecomp]
  abel

private theorem fourierCoeffOn_zero_one_eq_unitFourierCoefficientInt_fixedAway
    (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n =
      unitFourierCoefficientInt f n := by
  rw [fourierCoeffOn_eq_integral]
  unfold unitFourierCoefficientInt
  norm_num [fourier_coe_apply, paperExp]
  apply intervalIntegral.integral_congr
  intro alpha _halpha
  have hstar :
      (starRingEnd ℂ)
          (Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * n * alpha)) =
        Complex.exp
          (-(2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) * alpha))) := by
    rw [← Complex.exp_conj]
    congr 1
    push_cast
    simp [map_mul, map_ofNat, Complex.conj_I]
    ring
  change
    (starRingEnd ℂ)
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * n * alpha)) *
      f alpha =
    f alpha *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) * alpha)))
  rw [hstar]
  ring

theorem fourierCoeff_fixedAwaySmoothShotL2_int
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (N P : ℕ) (n : ℤ) :
    fourierCoeff
        (fixedAwaySmoothShotL2 t δ N P hδ hδt.le :
          AddCircle (1 : ℝ) → ℂ) n =
      unitFourierCoefficientInt (fixedAwaySmoothShotSum t δ N P) n := by
  rw [fourierCoeff_congr_ae
    (fixedAwaySmoothShotL2_coe_ae hδ hδt.le N P)]
  change fourierCoeff
      (AddCircle.liftIoc 1 0 (fixedAwaySmoothShotSum t δ N P)) n = _
  rw [fourierCoeff_liftIoc_eq]
  simpa using!
    (fourierCoeffOn_zero_one_eq_unitFourierCoefficientInt_fixedAway
      (fixedAwaySmoothShotSum t δ N P) n)

/-- Positive Fourier coefficients of the literal physical reconstruction
are exactly the absolutely convergent full fixed-away carrier series. -/
theorem hasSum_fourierCoeff_fixedAwaySmoothReconstructionL2_pos
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (ht : t ≤ 1 / 2)
    (N : ℕ+) (n : ℕ) (hn : 0 < n) :
    HasSum
      (fun ell : ℤ ↦ bernoulliMarkFourierCoefficient ell *
        fixedAwayFullCarrierBlock (N : ℕ) t δ (N : ℕ) ell (n : ℤ))
      (fourierCoeff
        (fixedAwaySmoothReconstructionL2 N (N : ℕ) t δ hδ hδt.le :
          AddCircle (1 : ℝ) → ℂ) (n : ℤ)) := by
  have h := hasSum_fixedAwayFullCarrierBlock_pos hδ hδt ht N n hn
  rw [fixedAwaySmoothReconstructionL2_eq_shot_add_error N hδ hδt]
  rw [← fourierCoefficientCLM_apply, map_add,
    fourierCoefficientCLM_apply, fourierCoefficientCLM_apply,
    fourierCoeff_fixedAwaySmoothShotL2_int hδ hδt,
    fourierCoeff_naturalCutoffShotErrorL2]
  exact h

theorem fixedAwaySmoothTruncation_neg
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (s R : ℝ) :
    fixedAwaySmoothTruncation t δ (-s) R =
      -fixedAwaySmoothTruncation t δ s R := by
  rw [fixedAwaySmoothTruncation_eq_paired hδ hδt,
    fixedAwaySmoothTruncation_eq_paired hδ hδt]
  unfold pairedCutoffQuotientTruncation
  have hint :
      (∫ v in (0 : ℝ)..R,
        fixedAwaySmoothCutoff t δ v * sineKernel (2 * Real.pi * -s) v) =
        -(∫ v in (0 : ℝ)..R,
          fixedAwaySmoothCutoff t δ v * sineKernel (2 * Real.pi * s) v) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro v _hv
    unfold sineKernel
    rw [show 2 * Real.pi * -s = -(2 * Real.pi * s) by ring]
    change fixedAwaySmoothCutoff t δ v *
        (-(2 * Real.pi * s) * Real.sinc (-(2 * Real.pi * s) * v)) = _
    rw [show -(2 * Real.pi * s) * v = -(2 * Real.pi * s * v) by ring,
      Real.sinc_neg]
    ring
  rw [hint]
  push_cast
  ring

theorem fixedAwaySmoothTruncation_zero
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (R : ℝ) :
    fixedAwaySmoothTruncation t δ 0 R = 0 := by
  rw [fixedAwaySmoothTruncation_eq_paired hδ hδt]
  simp [pairedCutoffQuotientTruncation, sineKernel]

theorem bernoulliMarkFourierCoefficient_neg (ell : ℤ) :
    bernoulliMarkFourierCoefficient (-ell) =
      bernoulliMarkFourierCoefficient ell := by
  by_cases hell : ell = 0
  · subst ell
    simp [bernoulliMarkFourierCoefficient]
  · rw [bernoulliMarkFourierCoefficient,
      bernoulliMarkFourierCoefficient,
      if_neg (neg_ne_zero.mpr hell), if_neg hell]
    push_cast
    ring

theorem fixedAwaySmoothCarrierBlock_negCarrier_zeroFrequency
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (P N : ℕ) (ell : ℤ) :
    fixedAwaySmoothCarrierBlock P t δ N (-ell) 0 =
      -fixedAwaySmoothCarrierBlock P t δ N ell 0 := by
  unfold fixedAwaySmoothCarrierBlock fixedAwayRamanujanProfileBlock
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _hpMem
  unfold fixedAwayRamanujanProfileTerm fixedAwaySmoothShiftedProfile
    nearBernoulliCarrierFrequency
  have hfreq :
      (((0 - (-ell) * ((N * p : ℕ) : ℤ) : ℤ) : ℝ) /
          (p : ℝ) ^ 2) =
        -(((0 - ell * ((N * p : ℕ) : ℤ) : ℤ) : ℝ) /
          (p : ℝ) ^ 2) := by
    push_cast
    ring
  rw [hfreq, fixedAwaySmoothTruncation_neg hδ hδt]
  ring

theorem unitFourierCoefficientInt_fixedAwaySmoothShotSum_zero
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (N P : ℕ) :
    unitFourierCoefficientInt (fixedAwaySmoothShotSum t δ N P) 0 = 0 := by
  let f : ℤ → ℂ := fun ell ↦ bernoulliMarkFourierCoefficient ell *
    fixedAwaySmoothCarrierBlock P t δ N ell 0
  have hhas := hasSum_fixedAwaySmoothCarrierBlock hδ hδt N P 0
  have hsum : Summable f := by
    simpa only [f] using! hhas.summable
  have hodd (ell : ℤ) : f (-ell) = -f ell := by
    dsimp [f]
    rw [bernoulliMarkFourierCoefficient_neg,
      fixedAwaySmoothCarrierBlock_negCarrier_zeroFrequency hδ hδt]
    ring
  have hreindex := (Equiv.neg ℤ).tsum_eq f
  have hneg : (∑' ell : ℤ, f (-ell)) = -(∑' ell : ℤ, f ell) := by
    calc
      (∑' ell : ℤ, f (-ell)) = ∑' ell : ℤ, -f ell := by
        apply tsum_congr
        exact hodd
      _ = -(∑' ell : ℤ, f ell) := tsum_neg
  have hself : (∑' ell : ℤ, f ell) = -(∑' ell : ℤ, f ell) := by
    rw [← hneg]
    exact hreindex.symm
  have hzero : (∑' ell : ℤ, f ell) = 0 :=
    CharZero.eq_neg_self_iff.mp hself
  have hvalue := hhas.tsum_eq
  simpa only [f, hzero] using! hvalue.symm

theorem fourierCoeff_fixedAwaySmoothReconstructionL2_zero
    (N : ℕ+) {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) :
    fourierCoeff
      (fixedAwaySmoothReconstructionL2 N (N : ℕ) t δ hδ hδt.le :
        AddCircle (1 : ℝ) → ℂ) 0 = 0 := by
  rw [fixedAwaySmoothReconstructionL2_eq_shot_add_error N hδ hδt]
  rw [← fourierCoefficientCLM_apply, map_add,
    fourierCoefficientCLM_apply, fourierCoefficientCLM_apply,
    fourierCoeff_fixedAwaySmoothShotL2_int hδ hδt,
    fourierCoeff_naturalCutoffShotErrorL2,
    unitFourierCoefficientInt_fixedAwaySmoothShotSum_zero hδ hδt,
    naturalCutoffShotErrorCoefficient_zero, add_zero]

theorem fixedAwaySmoothShotCircle_star
    (t δ : ℝ) (N P : ℕ) (x : AddCircle (1 : ℝ)) :
    starRingEnd ℂ (fixedAwaySmoothShotCircle t δ N P x) =
      fixedAwaySmoothShotCircle t δ N P x := by
  unfold fixedAwaySmoothShotCircle
  have hcomp :
      AddCircle.liftIoc (1 : ℝ) 0
          ((starRingEnd ℂ) ∘ fixedAwaySmoothShotSum t δ N P) x =
        starRingEnd ℂ
          (AddCircle.liftIoc (1 : ℝ) 0
            (fixedAwaySmoothShotSum t δ N P) x) :=
    AddCircle.liftIoc_comp_apply
  rw [← hcomp]
  congr 1
  funext alpha
  unfold Function.comp fixedAwaySmoothShotSum fixedAwaySmoothShotTerm
  simp

theorem fourierCoeff_fixedAwaySmoothShotL2_neg
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (N P : ℕ) (n : ℤ) :
    fourierCoeff
        (fixedAwaySmoothShotL2 t δ N P hδ hδt.le :
          AddCircle (1 : ℝ) → ℂ) (-n) =
      starRingEnd ℂ
        (fourierCoeff
          (fixedAwaySmoothShotL2 t δ N P hδ hδt.le :
            AddCircle (1 : ℝ) → ℂ) n) := by
  apply fourierCoeff_neg_eq_conj_of_ae_real
  filter_upwards [fixedAwaySmoothShotL2_coe_ae hδ hδt.le N P] with x hx
  rw [hx]
  exact fixedAwaySmoothShotCircle_star t δ N P x

theorem fourierCoeff_fixedAwaySmoothReconstructionL2_neg
    (N : ℕ+) {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (n : ℤ) :
    fourierCoeff
        (fixedAwaySmoothReconstructionL2 N (N : ℕ) t δ hδ hδt.le :
          AddCircle (1 : ℝ) → ℂ) (-n) =
      starRingEnd ℂ
        (fourierCoeff
          (fixedAwaySmoothReconstructionL2 N (N : ℕ) t δ hδ hδt.le :
            AddCircle (1 : ℝ) → ℂ) n) := by
  rw [fixedAwaySmoothReconstructionL2_eq_shot_add_error N hδ hδt]
  let Y : UnitCircleL2 :=
    fixedAwaySmoothShotL2 t δ (N : ℕ) (N : ℕ) hδ hδt.le
  let E : UnitCircleL2 := naturalCutoffShotErrorL2 N
  have hadd (A B : UnitCircleL2) (k : ℤ) :
      fourierCoeff ((A + B : UnitCircleL2) :
          AddCircle (1 : ℝ) → ℂ) k =
        fourierCoeff (A : AddCircle (1 : ℝ) → ℂ) k +
          fourierCoeff (B : AddCircle (1 : ℝ) → ℂ) k := by
    simpa only [fourierCoefficientCLM_apply] using!
      (fourierCoefficientCLM k).map_add A B
  change fourierCoeff ((Y + E : UnitCircleL2) :
      AddCircle (1 : ℝ) → ℂ) (-n) =
    starRingEnd ℂ
      (fourierCoeff ((Y + E : UnitCircleL2) :
        AddCircle (1 : ℝ) → ℂ) n)
  calc
    fourierCoeff ((Y + E : UnitCircleL2) : AddCircle (1 : ℝ) → ℂ) (-n) =
        fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (-n) +
          fourierCoeff (E : AddCircle (1 : ℝ) → ℂ) (-n) :=
      hadd Y E (-n)
    _ = starRingEnd ℂ
          (fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) n) +
        starRingEnd ℂ
          (fourierCoeff (E : AddCircle (1 : ℝ) → ℂ) n) := by
      dsimp [Y, E]
      rw [fourierCoeff_fixedAwaySmoothShotL2_neg hδ hδt,
        fourierCoeff_naturalCutoffShotErrorL2,
        fourierCoeff_naturalCutoffShotErrorL2,
        naturalCutoffShotErrorCoefficient_neg]
    _ = starRingEnd ℂ
        (fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) n +
          fourierCoeff (E : AddCircle (1 : ℝ) → ℂ) n) := by
      rw [map_add]
    _ = starRingEnd ℂ
        (fourierCoeff ((Y + E : UnitCircleL2) :
          AddCircle (1 : ℝ) → ℂ) n) := by
      rw [hadd]

def fixedAwayFullCarrierCoefficient
    (N : ℕ) (t δ : ℝ) (n : ℤ) : ℂ :=
  ∑' ell : ℤ, bernoulliMarkFourierCoefficient ell *
    fixedAwayFullCarrierBlock N t δ N ell n

theorem fourierCoeff_fixedAwaySmoothReconstructionL2_pos_eq_carriers
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (ht : t ≤ 1 / 2)
    (N : ℕ+) (n : ℕ) (hn : 0 < n) :
    fourierCoeff
        (fixedAwaySmoothReconstructionL2 N (N : ℕ) t δ hδ hδt.le :
          AddCircle (1 : ℝ) → ℂ) (n : ℤ) =
      fixedAwayFullCarrierCoefficient (N : ℕ) t δ (n : ℤ) := by
  unfold fixedAwayFullCarrierCoefficient
  exact (hasSum_fourierCoeff_fixedAwaySmoothReconstructionL2_pos
    hδ hδt ht N n hn).tsum_eq.symm

/-- Exact physical Parseval formula reduced to positive frequencies of the
absolutely convergent full carrier coefficient.  This is the final
function-level bridge needed before inserting the dyadic/BV estimates. -/
theorem norm_fixedAwaySmoothReconstructionL2_sq_eq_positiveCarriers
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (ht : t ≤ 1 / 2)
    (N : ℕ+) :
    ‖fixedAwaySmoothReconstructionL2 N (N : ℕ) t δ hδ hδt.le‖ ^ 2 =
      2 * ∑' n : ℕ+,
        ‖fixedAwayFullCarrierCoefficient (N : ℕ) t δ (n : ℤ)‖ ^ 2 := by
  let F : UnitCircleL2 :=
    fixedAwaySmoothReconstructionL2 N (N : ℕ) t δ hδ hδt.le
  let e : ℤ → ℝ := fun n ↦
    ‖fourierCoeff (F : AddCircle (1 : ℝ) → ℂ) n‖ ^ 2
  have heSummable : Summable e := by
    have h := (hasSum_sq_fourierCoeff F).summable
    simpa only [e] using! h
  have heEven : e.Even := by
    intro n
    dsimp [e, F]
    rw [fourierCoeff_fixedAwaySmoothReconstructionL2_neg N hδ hδt,
      starRingEnd_apply, norm_star]
  have hsplit := tsum_int_eq_zero_add_two_mul_tsum_pnat heEven heSummable
  have hzero : e 0 = 0 := by
    dsimp [e, F]
    rw [fourierCoeff_fixedAwaySmoothReconstructionL2_zero N hδ hδt,
      norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0)]
  rw [hzero, zero_add, nsmul_eq_mul] at hsplit
  have hparseval := tsum_sq_fourierCoeff F
  have hinner := congrArg RCLike.re
    (@L2.inner_def (AddCircle (1 : ℝ)) ℂ ℂ _ _ _ _ _ F F)
  rw [← integral_re] at hinner
  · simp only [← norm_sq_eq_re_inner] at hinner
    calc
      ‖fixedAwaySmoothReconstructionL2 N (N : ℕ) t δ hδ hδt.le‖ ^ 2 =
          ‖F‖ ^ 2 := rfl
      _ = ∫ x : AddCircle (1 : ℝ), ‖(F : AddCircle (1 : ℝ) → ℂ) x‖ ^ 2
          ∂AddCircle.haarAddCircle := hinner
      _ = ∑' n : ℤ, e n := by
        rw [← hparseval]
      _ = 2 * ∑' n : ℕ+, e (n : ℤ) := hsplit
      _ = 2 * ∑' n : ℕ+,
          ‖fixedAwayFullCarrierCoefficient (N : ℕ) t δ (n : ℤ)‖ ^ 2 := by
        congr 1
        apply tsum_congr
        intro n
        dsimp [e, F]
        rw [fourierCoeff_fixedAwaySmoothReconstructionL2_pos_eq_carriers
          hδ hδt ht N (n : ℕ) n.pos]
  · exact L2.integrable_inner F F

end

end Erdos1002
