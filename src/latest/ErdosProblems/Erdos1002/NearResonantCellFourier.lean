import ErdosProblems.Erdos1002.NearResonantMultipliers
import ErdosProblems.Erdos1002.PrimitiveShotCellFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact cell Fourier coefficients for the smooth near-resonant pole

This file connects the analytic multiplier `nearJ` to the literal
nearest-rational cells.  In particular, the factor `p⁻²`, the residue phase,
and the argument `n / p²` all come from a proved affine change of variables;
none is inserted as a formal Fourier ansatz.
-/

open Filter MeasureTheory Set
open scoped BigOperators Real

namespace Erdos1002

noncomputable section

private theorem measurable_paperExp_near : Measurable paperExp := by
  unfold paperExp
  fun_prop

private theorem norm_paperExp_near (t : ℝ) : ‖paperExp t‖ = 1 := by
  rw [paperExp, Complex.norm_exp]
  simp

private theorem paperExp_add_near (u v : ℝ) :
    paperExp u * paperExp v = paperExp (u + v) := by
  unfold paperExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem paperExp_eq_fourierChar_near (t : ℝ) :
    paperExp t = (Real.fourierChar t : ℂ) := by
  rw [Real.fourierChar_apply]
  unfold paperExp
  congr 1
  push_cast
  ring

/-- A positive dilation of the fixed bump vanishes once the argument is at
least twice the dilation scale. -/
theorem scaledNearProfile_eq_zero_of_two_mul_le_abs
    (s x : ℝ) (hs : 0 < s) (hx : 2 * s ≤ |x|) :
    scaledNearProfile s x = 0 := by
  unfold scaledNearProfile nearBaseProfile
  have hscaled : (2 : ℝ) ≤ |x / s| := by
    rw [abs_div, abs_of_pos hs]
    exact (le_div_iff₀ hs).2 (by simpa [mul_comm] using! hx)
  rw [gevreyOuterCutoff_eq_zero_of_le_abs
    (by norm_num : (0 : ℝ) < 2) hscaled]
  norm_num

/-- The outer scale really cuts `ρ` off outside `[-ε,ε]`.  The hypothesis
`a ≤ ε/4` also puts the inner bump inside that interval. -/
theorem nearRho_eq_zero_of_epsilon_le_abs
    (a ε x : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hx : ε ≤ |x|) :
    nearRho a ε x = 0 := by
  have hout : scaledNearProfile (ε / 2) x = 0 := by
    apply scaledNearProfile_eq_zero_of_two_mul_le_abs (ε / 2) x (by positivity)
    linarith
  have hin : scaledNearProfile a x = 0 := by
    apply scaledNearProfile_eq_zero_of_two_mul_le_abs a x ha
    linarith
  unfold nearRho
  rw [hout, hin]
  ring

theorem nearW_eq_zero_of_epsilon_le_abs
    (a ε x : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hx : ε ≤ |x|) :
    nearW a ε x = 0 := by
  unfold nearW
  rw [nearRho_eq_zero_of_epsilon_le_abs a ε x ha hε haε hx]
  exact zero_div _

/-- The real-line integrand whose integral is `nearJ`. -/
def nearJIntegrand (a ε t x : ℝ) : ℂ :=
  nearW a ε x * paperExp (-t * x)

theorem nearJIntegrand_integrable
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    Integrable (nearJIntegrand a ε t) := by
  unfold nearJIntegrand
  apply (nearW_integrable a ε ha hε haε).mul_bdd
  · exact (measurable_paperExp_near.comp
      (measurable_const.mul measurable_id)).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_paperExp_near]

theorem integral_nearJIntegrand_eq_nearJ
    (a ε t : ℝ) :
    (∫ x : ℝ, nearJIntegrand a ε t x) = nearJ a ε t := by
  unfold nearJ nearJIntegrand
  rw [Real.fourier_eq]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [paperExp_eq_fourierChar_near]
  simp only [Circle.smul_def, smul_eq_mul]
  rw [show inner ℝ x t = x * t by simp [mul_comm]]
  change nearW a ε x * (Real.fourierChar (-t * x) : ℂ) =
    (Real.fourierChar (-(x * t)) : ℂ) * nearW a ε x
  rw [show -t * x = -(x * t) by ring]
  ring

/-- The smooth pole written in the affine coordinate attached to a reduced
cell.  Its argument is `p(pα-q)`, exactly as in the manuscript. -/
def nearPoleCell (a ε : ℝ) (p q : ℕ) (alpha : ℝ) : ℂ :=
  nearW a ε ((p : ℝ) * ((p : ℝ) * alpha - (q : ℝ)))

/-- Fourier integral of one smooth nearest cell. -/
def nearPoleCellFourierIntegral
    (a ε : ℝ) (n p q : ℕ) : ℂ :=
  ∫ alpha in nearestCellLeft p q..nearestCellRight p q,
    nearPoleCell a ε p q alpha * paperExp (-(n : ℝ) * alpha)

private theorem nearPole_phase_split
    (n p q : ℕ) (alpha : ℝ) (hp : 0 < p) :
    paperExp (-(n : ℝ) * alpha) =
      paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
        paperExp (-((n : ℝ) / (p : ℝ) ^ 2) *
          ((p : ℝ) ^ 2 * alpha - (p : ℝ) * (q : ℝ))) := by
  rw [paperExp_add_near]
  congr 1
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpR]
  ring

private theorem nearPole_affine_eq
    (p q : ℕ) (alpha : ℝ) :
    (p : ℝ) * ((p : ℝ) * alpha - (q : ℝ)) =
      (p : ℝ) ^ 2 * alpha - (p : ℝ) * (q : ℝ) := by
  ring

theorem nearestCellLeft_sq_mul_sub (p q : ℕ) (hp : 0 < p) :
    (p : ℝ) ^ 2 * nearestCellLeft p q - (p : ℝ) * (q : ℝ) =
      -(p : ℝ) / 2 := by
  unfold nearestCellLeft
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpR]
  ring

theorem nearestCellRight_sq_mul_sub (p q : ℕ) (hp : 0 < p) :
    (p : ℝ) ^ 2 * nearestCellRight p q - (p : ℝ) * (q : ℝ) =
      (p : ℝ) / 2 := by
  unfold nearestCellRight
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpR]
  ring

theorem support_nearJIntegrand_subset_nearestCell
    (a ε t : ℝ) (p : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    Function.support (nearJIntegrand a ε t) ⊆
      Ioc (-(p : ℝ) / 2) ((p : ℝ) / 2) := by
  intro x hx
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hεp : ε ≤ (p : ℝ) / 2 := by linarith
  have hW : nearW a ε x ≠ 0 := by
    intro hzero
    apply hx
    unfold nearJIntegrand
    rw [hzero, zero_mul]
  have habs : |x| < ε := by
    by_contra hnot
    have : ε ≤ |x| := le_of_not_gt hnot
    exact hW (nearW_eq_zero_of_epsilon_le_abs a ε x ha hε haε this)
  constructor
  · have hneg : -(p : ℝ) / 2 ≤ -ε := by linarith
    have hxlower : -ε < x := (abs_lt.mp habs).1
    exact hneg.trans_lt hxlower
  · exact (le_abs_self x).trans (habs.le.trans hεp)

/-- Exact affine-cell Fourier formula.  The compact support hypothesis
`ε ≤ 1/2` turns the finite nearest-cell integral into the full transform
`nearJ`; this is where no unmentioned tail is left over. -/
theorem nearPoleCellFourierIntegral_eq
    (a ε : ℝ) (n p q : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    nearPoleCellFourierIntegral a ε n p q =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
          nearJ a ε ((n : ℝ) / (p : ℝ) ^ 2) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  let g : ℝ → ℂ := nearJIntegrand a ε ((n : ℝ) / (p : ℝ) ^ 2)
  have hfull :
      (∫ x in (-(p : ℝ) / 2)..((p : ℝ) / 2), g x) =
        nearJ a ε ((n : ℝ) / (p : ℝ) ^ 2) := by
    calc
      (∫ x in (-(p : ℝ) / 2)..((p : ℝ) / 2), g x) =
          ∫ x : ℝ, g x :=
        intervalIntegral.integral_eq_integral_of_support_subset
          (support_nearJIntegrand_subset_nearestCell
            a ε ((n : ℝ) / (p : ℝ) ^ 2) p hp ha hε haε hεhalf)
      _ = nearJ a ε ((n : ℝ) / (p : ℝ) ^ 2) := by
        exact integral_nearJIntegrand_eq_nearJ _ _ _
  unfold nearPoleCellFourierIntegral
  calc
    (∫ alpha in nearestCellLeft p q..nearestCellRight p q,
        nearPoleCell a ε p q alpha * paperExp (-(n : ℝ) * alpha)) =
      ∫ alpha in nearestCellLeft p q..nearestCellRight p q,
        paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
          g ((p : ℝ) ^ 2 * alpha - (p : ℝ) * (q : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro alpha _halpha
        dsimp [g, nearJIntegrand]
        rw [nearPole_phase_split n p q alpha hp]
        unfold nearPoleCell
        rw [nearPole_affine_eq]
        ring
    _ = paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
        (∫ alpha in nearestCellLeft p q..nearestCellRight p q,
          g ((p : ℝ) ^ 2 * alpha - (p : ℝ) * (q : ℝ))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
        (((p : ℝ) ^ 2)⁻¹ •
          (∫ x in
              (p : ℝ) ^ 2 * nearestCellLeft p q - (p : ℝ) * (q : ℝ)..
              (p : ℝ) ^ 2 * nearestCellRight p q - (p : ℝ) * (q : ℝ),
            g x)) := by
      rw [intervalIntegral.integral_comp_mul_sub g (pow_ne_zero 2 hpR)
        ((p : ℝ) * (q : ℝ))]
    _ = ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
          nearJ a ε ((n : ℝ) / (p : ℝ) ^ 2) := by
      rw [nearestCellLeft_sq_mul_sub p q hp,
        nearestCellRight_sq_mul_sub p q hp, hfull, Complex.real_smul]
      push_cast
      field_simp [hpR]

/-! ## Reconnection to the literal nearest primitive resonance -/

/-- The literal smooth pole selected by the nearest primitive rational. -/
def nearPrimitivePole (a ε : ℝ) (p : ℕ) (alpha : ℝ) : ℂ :=
  if IsPrimitiveResonance p alpha then
    nearW a ε ((p : ℝ) * resonanceDelta p alpha)
  else 0

/-- Finite reduced-residue cell expansion of the smooth pole. -/
def nearestNearPoleCellExpansion
    (a ε : ℝ) (p : ℕ) (alpha : ℝ) : ℂ :=
  ∑ q ∈ reducedResidues p,
    if (p : ℝ) * alpha - (q : ℝ) ∈
        Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) then
      nearPoleCell a ε p q alpha
    else 0

private theorem nearPrimitivePole_eq_nearPoleCell_of_numerator
    {a ε : ℝ} {p : ℕ} {alpha : ℝ} {q : ℤ}
    (hprim : IsPrimitiveResonance p alpha)
    (hq : resonanceNumerator p alpha = q) :
    nearPrimitivePole a ε p alpha =
      nearW a ε ((p : ℝ) * ((p : ℝ) * alpha - (q : ℝ))) := by
  unfold nearPrimitivePole
  rw [if_pos hprim]
  congr 2
  unfold resonanceDelta
  rw [hq]

/-- Pointwise exactness of the finite cell expansion on the open unit
interval.  Coprimality is used only to select the unique reduced residue;
the indicator creates no extra jump. -/
theorem nearPrimitivePole_eq_nearestNearPoleCellExpansion
    {a ε : ℝ} {p : ℕ} (hp : 2 ≤ p) {alpha : ℝ}
    (halpha : alpha ∈ Ioo (0 : ℝ) 1) :
    nearPrimitivePole a ε p alpha =
      nearestNearPoleCellExpansion a ε p alpha := by
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
    unfold nearestNearPoleCellExpansion
    rw [Finset.sum_eq_single q]
    · rw [if_pos hcell]
      unfold nearPoleCell
      exact (nearPrimitivePole_eq_nearPoleCell_of_numerator
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
  · have hzero : nearPrimitivePole a ε p alpha = 0 := by
      unfold nearPrimitivePole
      rw [if_neg hprim]
    rw [hzero]
    symm
    unfold nearestNearPoleCellExpansion
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

/-- The exact Fourier integrand with its half-open nearest-cell cutoff. -/
def nearPoleCellFourierTerm
    (a ε : ℝ) (n p q : ℕ) (alpha : ℝ) : ℂ :=
  if (p : ℝ) * alpha - (q : ℝ) ∈
      Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) then
    nearPoleCell a ε p q alpha * paperExp (-(n : ℝ) * alpha)
  else 0

private theorem nearPoleCellFourierIntegrand_eq
    (a ε : ℝ) (n p q : ℕ) (alpha : ℝ) (hp : 0 < p) :
    nearPoleCell a ε p q alpha * paperExp (-(n : ℝ) * alpha) =
      paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
        nearJIntegrand a ε ((n : ℝ) / (p : ℝ) ^ 2)
          ((p : ℝ) ^ 2 * alpha - (p : ℝ) * (q : ℝ)) := by
  unfold nearPoleCell nearJIntegrand
  rw [nearPole_phase_split n p q alpha hp, nearPole_affine_eq]
  ring

theorem nearPoleCellFourierIntegrand_integrable
    (a ε : ℝ) (n p q : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    Integrable (fun alpha : ℝ ↦
      nearPoleCell a ε p q alpha * paperExp (-(n : ℝ) * alpha)) := by
  let g : ℝ → ℂ := nearJIntegrand a ε ((n : ℝ) / (p : ℝ) ^ 2)
  have hg : Integrable g := nearJIntegrand_integrable a ε _ ha hε haε
  have htrans : Integrable (fun y : ℝ ↦
      g (y - (p : ℝ) * (q : ℝ))) :=
    hg.comp_sub_right ((p : ℝ) * (q : ℝ))
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have haff : Integrable (fun alpha : ℝ ↦
      g ((p : ℝ) ^ 2 * alpha - (p : ℝ) * (q : ℝ))) := by
    simpa only using! htrans.comp_mul_left' (pow_ne_zero 2 hpR)
  have hconst := haff.const_mul
    (paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)))
  exact hconst.congr
    (Filter.Eventually.of_forall fun alpha ↦
      (nearPoleCellFourierIntegrand_eq a ε n p q alpha hp).symm)

theorem nearPoleCellFourierTerm_integrable
    (a ε : ℝ) (n p q : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    Integrable (nearPoleCellFourierTerm a ε n p q) := by
  let s : Set ℝ := {alpha : ℝ |
    (p : ℝ) * alpha - (q : ℝ) ∈
      Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)}
  have hs : MeasurableSet s :=
    measurableSet_Ioc.preimage
      (measurable_const.mul measurable_id |>.sub measurable_const)
  have hi := (nearPoleCellFourierIntegrand_integrable
    a ε n p q hp ha hε haε).indicator hs
  apply hi.congr
  filter_upwards with alpha
  by_cases hcell : (p : ℝ) * alpha - (q : ℝ) ∈
      Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)
  · simp [s, Set.indicator, nearPoleCellFourierTerm]
  · simp [s, Set.indicator, nearPoleCellFourierTerm]

theorem support_nearPoleCellFourierTerm_subset
    (a ε : ℝ) (n p q : ℕ) (hp : 0 < p) :
    Function.support (nearPoleCellFourierTerm a ε n p q) ⊆
      Ioc (nearestCellLeft p q) (nearestCellRight p q) := by
  intro alpha halpha
  by_contra hnot
  have hscaled :
      ¬ ((p : ℝ) * alpha - (q : ℝ) ∈
        Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)) := by
    exact fun h ↦ hnot ((mem_nearestCell_iff hp alpha).1 h)
  exact halpha (by
    rw [nearPoleCellFourierTerm, if_neg hscaled])

/-- The unit-interval integral of a cut-off reduced cell is its affine cell
integral; support and endpoint conventions are both explicit. -/
theorem integral_unit_nearPoleCellFourierTerm_eq
    (a ε : ℝ) (n p q : ℕ) (hp : 2 ≤ p)
    (hq : q ∈ reducedResidues p) :
    (∫ alpha in (0 : ℝ)..1,
      nearPoleCellFourierTerm a ε n p q alpha) =
      nearPoleCellFourierIntegral a ε n p q := by
  have hp0 : 0 < p := by omega
  let f : ℝ → ℂ := nearPoleCellFourierTerm a ε n p q
  have hsupportCell : Function.support f ⊆
      Ioc (nearestCellLeft p q) (nearestCellRight p q) :=
    support_nearPoleCellFourierTerm_subset a ε n p q hp0
  have hsupportUnit : Function.support f ⊆ Ioc (0 : ℝ) 1 :=
    hsupportCell.trans (nearestCell_interval_subset_unit hp hq)
  calc
    (∫ alpha in (0 : ℝ)..1, nearPoleCellFourierTerm a ε n p q alpha) =
        ∫ alpha : ℝ, f alpha := by
      exact intervalIntegral.integral_eq_integral_of_support_subset hsupportUnit
    _ = ∫ alpha in nearestCellLeft p q..nearestCellRight p q, f alpha := by
      symm
      exact intervalIntegral.integral_eq_integral_of_support_subset hsupportCell
    _ = ∫ alpha in nearestCellLeft p q..nearestCellRight p q,
          nearPoleCell a ε p q alpha * paperExp (-(n : ℝ) * alpha) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with alpha
      intro halpha
      have hcell : alpha ∈
          Ioc (nearestCellLeft p q) (nearestCellRight p q) := by
        simpa only [Set.uIoc_of_le (nearestCellLeft_lt_right p q hp0).le]
          using! halpha
      change nearPoleCellFourierTerm a ε n p q alpha = _
      rw [nearPoleCellFourierTerm,
        if_pos ((mem_nearestCell_iff hp0 alpha).2 hcell)]
    _ = nearPoleCellFourierIntegral a ε n p q := rfl

/-- Fourier coefficient of the finite reduced-cell expansion. -/
theorem unitFourierCoefficient_nearestNearPoleCellExpansion
    (a ε : ℝ) (n p : ℕ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    unitFourierCoefficient (nearestNearPoleCellExpansion a ε p) n =
      ∑ q ∈ reducedResidues p,
        nearPoleCellFourierIntegral a ε n p q := by
  have hfun :
      (fun alpha ↦ nearestNearPoleCellExpansion a ε p alpha *
        paperExp (-(n : ℝ) * alpha)) =
      fun alpha ↦ ∑ q ∈ reducedResidues p,
        nearPoleCellFourierTerm a ε n p q alpha := by
    funext alpha
    unfold nearestNearPoleCellExpansion
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _hq
    by_cases hcell :
        (p : ℝ) * alpha - (q : ℝ) ∈
          Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)
    · rw [if_pos hcell, nearPoleCellFourierTerm, if_pos hcell]
    · rw [if_neg hcell, zero_mul, nearPoleCellFourierTerm, if_neg hcell]
  unfold unitFourierCoefficient
  rw [hfun, intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro q hq
    exact integral_unit_nearPoleCellFourierTerm_eq a ε n p q hp hq
  · intro q _hq
    exact (nearPoleCellFourierTerm_integrable
      a ε n p q (by omega) ha hε haε).intervalIntegrable

/-- The finite reduced-cell coefficient factors as a Ramanujan sum times
the exact multiplier `nearJ(n/p²)`. -/
theorem unitFourierCoefficient_nearestNearPoleCellExpansion_eq_ramanujan
    (a ε : ℝ) (n p : ℕ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    unitFourierCoefficient (nearestNearPoleCellExpansion a ε p) n =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        ramanujanSum p (n : ℤ) *
          nearJ a ε ((n : ℝ) / (p : ℝ) ^ 2) := by
  rw [unitFourierCoefficient_nearestNearPoleCellExpansion
    a ε n p hp ha hε haε]
  simp_rw [nearPoleCellFourierIntegral_eq
    a ε n p _ (by omega) ha hε haε hεhalf]
  rw [← Finset.sum_mul, ← Finset.mul_sum,
    sum_reducedResidues_paperExp_neg]

/-- Exact positive-frequency formula for one literal smooth primitive pole,
for every modulus `p ≥ 2`. -/
theorem unitFourierCoefficient_nearPrimitivePole_eq_ramanujan
    (a ε : ℝ) (n p : ℕ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    unitFourierCoefficient (nearPrimitivePole a ε p) n =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        ramanujanSum p (n : ℤ) *
          nearJ a ε ((n : ℝ) / (p : ℝ) ^ 2) := by
  rw [← unitFourierCoefficient_nearestNearPoleCellExpansion_eq_ramanujan
    a ε n p hp ha hε haε hεhalf]
  unfold unitFourierCoefficient
  apply intervalIntegral.integral_congr_ae
  have hone : ∀ᵐ alpha : ℝ ∂volume, alpha ≠ 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hone] with alpha halphaOne
  intro halpha
  have hmem : alpha ∈ Ioo (0 : ℝ) 1 := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at halpha
    exact ⟨halpha.1, lt_of_le_of_ne halpha.2 halphaOne⟩
  rw [nearPrimitivePole_eq_nearestNearPoleCellExpansion hp hmem]

private theorem paperExp_int_near (z : ℤ) : paperExp (z : ℝ) = 1 := by
  unfold paperExp
  convert! Complex.exp_int_mul_two_pi_mul_I z using 2
  push_cast
  ring

theorem nearPrimitivePole_one_periodic (a ε : ℝ) :
    Function.Periodic (nearPrimitivePole a ε 1) 1 := by
  intro alpha
  unfold nearPrimitivePole
  rw [if_pos (isPrimitiveResonance_one (alpha + 1)),
    if_pos (isPrimitiveResonance_one alpha)]
  have hdelta : resonanceDelta 1 (alpha + 1) = resonanceDelta 1 alpha := by
    simpa using! resonanceDelta_add_int 1 alpha (1 : ℤ)
  rw [hdelta]

theorem nearPrimitivePoleFourierIntegrand_one_periodic
    (a ε : ℝ) (n : ℕ) :
    Function.Periodic
      (fun alpha ↦ nearPrimitivePole a ε 1 alpha *
        paperExp (-(n : ℝ) * alpha)) 1 := by
  intro alpha
  change nearPrimitivePole a ε 1 (alpha + 1) *
      paperExp (-(n : ℝ) * (alpha + 1)) = _
  rw [nearPrimitivePole_one_periodic a ε alpha]
  have harg :
      -(n : ℝ) * (alpha + 1) = -(n : ℝ) * alpha + (-(n : ℤ) : ℤ) := by
    push_cast
    ring
  rw [harg, ← paperExp_add_near, paperExp_int_near, mul_one]

/-- The modulus-one endpoint pair is one complete smooth nearest cell. -/
theorem unitFourierCoefficient_nearPrimitivePole_one
    (a ε : ℝ) (n : ℕ) :
    unitFourierCoefficient (nearPrimitivePole a ε 1) n =
      nearPoleCellFourierIntegral a ε n 1 0 := by
  let f : ℝ → ℂ := fun alpha ↦ nearPrimitivePole a ε 1 alpha *
    paperExp (-(n : ℝ) * alpha)
  have hperiod : Function.Periodic f 1 :=
    nearPrimitivePoleFourierIntegrand_one_periodic a ε n
  have hshift := hperiod.intervalIntegral_add_eq (0 : ℝ) (-(1 : ℝ) / 2)
  have hinterval :
      (∫ alpha in (0 : ℝ)..1, f alpha) =
        ∫ alpha in (-(1 : ℝ) / 2)..((1 : ℝ) / 2), f alpha := by
    convert! hshift using 1 <;> norm_num
  unfold unitFourierCoefficient
  change (∫ alpha in (0 : ℝ)..1, f alpha) = _
  rw [hinterval]
  unfold nearPoleCellFourierIntegral
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
  unfold f nearPrimitivePole
  rw [if_pos (isPrimitiveResonance_one alpha)]
  unfold nearPoleCell resonanceDelta
  simp only [hnum, Int.cast_zero, sub_zero, Nat.cast_one, one_mul,
    Nat.cast_zero]
  ring_nf

/-- The exact Ramanujan formula at the endpoint modulus `p=1`. -/
theorem unitFourierCoefficient_nearPrimitivePole_one_eq_ramanujan
    (a ε : ℝ) (n : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    unitFourierCoefficient (nearPrimitivePole a ε 1) n =
      ((1 / (1 : ℝ) ^ 2 : ℝ) : ℂ) *
        ramanujanSum 1 (n : ℤ) * nearJ a ε (n : ℝ) := by
  rw [unitFourierCoefficient_nearPrimitivePole_one,
    nearPoleCellFourierIntegral_eq a ε n 1 0 (by omega)
      ha hε haε hεhalf]
  simp [paperExp]

/-- Uniform one-denominator coefficient formula for every positive modulus. -/
theorem unitFourierCoefficient_nearPrimitivePole_eq_ramanujan_of_pos
    (a ε : ℝ) (n p : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    unitFourierCoefficient (nearPrimitivePole a ε p) n =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        ramanujanSum p (n : ℤ) *
          nearJ a ε ((n : ℝ) / (p : ℝ) ^ 2) := by
  by_cases hpone : p = 1
  · subst p
    simpa using! unitFourierCoefficient_nearPrimitivePole_one_eq_ramanujan
      a ε n ha hε haε hεhalf
  · exact unitFourierCoefficient_nearPrimitivePole_eq_ramanujan
      a ε n p (by omega) ha hε haε hεhalf

/-- Exact coefficient of a finite sum of smooth primitive poles. -/
theorem unitFourierCoefficient_nearPrimitivePoleSum_eq
    (a ε : ℝ) (P n : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    unitFourierCoefficient
        (fun alpha ↦ ∑ p ∈ Finset.Icc 1 P,
          nearPrimitivePole a ε p alpha) n =
      ∑ p ∈ Finset.Icc 1 P,
        ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
          ramanujanSum p (n : ℤ) *
            nearJ a ε ((n : ℝ) / (p : ℝ) ^ 2) := by
  unfold unitFourierCoefficient
  rw [show (fun alpha ↦
      (∑ p ∈ Finset.Icc 1 P, nearPrimitivePole a ε p alpha) *
        paperExp (-(n : ℝ) * alpha)) =
      (fun alpha ↦ ∑ p ∈ Finset.Icc 1 P,
        nearPrimitivePole a ε p alpha *
          paperExp (-(n : ℝ) * alpha)) by
    funext alpha
    rw [Finset.sum_mul]]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro p hpMem
    simpa only [unitFourierCoefficient] using!
      unitFourierCoefficient_nearPrimitivePole_eq_ramanujan_of_pos
        a ε n p (Finset.mem_Icc.mp hpMem).1 ha hε haε hεhalf
  · intro p hpMem
    have hp0 := (Finset.mem_Icc.mp hpMem).1
    by_cases hpone : p = 1
    · subst p
      let f : ℝ → ℂ := fun alpha ↦ nearPrimitivePole a ε 1 alpha *
        paperExp (-(n : ℝ) * alpha)
      have hperiod : Function.Periodic f 1 :=
        nearPrimitivePoleFourierIntegrand_one_periodic a ε n
      have hcellInt : IntervalIntegrable f volume
          (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
        have hraw : IntervalIntegrable
            (fun alpha : ℝ ↦ nearPoleCell a ε 1 0 alpha *
              paperExp (-(n : ℝ) * alpha)) volume
              (-(1 : ℝ) / 2) ((1 : ℝ) / 2) :=
          (nearPoleCellFourierIntegrand_integrable
            a ε n 1 0 (by omega) ha hε haε).intervalIntegrable
        apply hraw.congr
        intro alpha halpha
        have hcell : alpha ∈ Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
          have halpha' : alpha ∈
              uIoc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
            simpa only [neg_div] using! halpha
          rw [Set.uIoc_of_le
            (by norm_num : (-(1 : ℝ) / 2) ≤ (1 : ℝ) / 2)] at halpha'
          exact halpha'
        have hnum : resonanceNumerator 1 alpha = 0 :=
          resonanceNumerator_eq_of_delta_mem (by simpa using! hcell)
        unfold f nearPrimitivePole nearPoleCell resonanceDelta
        rw [if_pos (isPrimitiveResonance_one alpha), hnum]
        norm_num
      exact Function.Periodic.intervalIntegrable
        (t := (-(1 : ℝ) / 2)) hperiod
        (hT := by norm_num)
        (h₂f := by
          have hend : (-(1 : ℝ) / 2) + 1 = (1 : ℝ) / 2 := by norm_num
          simpa only [hend] using! hcellInt)
        (a₁ := 0) (a₂ := 1)
    · -- For `p≥2`, equality with the finite cell expansion holds a.e. on `[0,1]`.
      have hp2 : 2 ≤ p := by omega
      have hsumInt : IntervalIntegrable
          (fun alpha ↦ nearestNearPoleCellExpansion a ε p alpha *
            paperExp (-(n : ℝ) * alpha)) volume 0 1 := by
        rw [show (fun alpha ↦ nearestNearPoleCellExpansion a ε p alpha *
              paperExp (-(n : ℝ) * alpha)) =
            (fun alpha ↦ ∑ q ∈ reducedResidues p,
              nearPoleCellFourierTerm a ε n p q alpha) by
          funext alpha
          unfold nearestNearPoleCellExpansion
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro q _hq
          by_cases hcell : (p : ℝ) * alpha - (q : ℝ) ∈
              Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)
          · rw [if_pos hcell, nearPoleCellFourierTerm, if_pos hcell]
          · rw [if_neg hcell, zero_mul, nearPoleCellFourierTerm, if_neg hcell]]
        have hpi := IntervalIntegrable.sum (reducedResidues p)
          (fun q _hq ↦ (nearPoleCellFourierTerm_integrable
            a ε n p q hp0 ha hε haε).intervalIntegrable
              (a := (0 : ℝ)) (b := (1 : ℝ)))
        convert! hpi using 1
        ext alpha
        simp only [Finset.sum_apply]
      apply hsumInt.congr_ae
      have hone : ∀ᵐ alpha : ℝ ∂volume, alpha ≠ 1 := by
        simp [ae_iff, measure_singleton]
      filter_upwards [ae_restrict_mem measurableSet_uIoc,
        ae_restrict_of_ae hone] with alpha halpha halphaOne
      have hmem : alpha ∈ Ioo (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at halpha
        exact ⟨halpha.1, lt_of_le_of_ne halpha.2 halphaOne⟩
      rw [nearPrimitivePole_eq_nearestNearPoleCellExpansion hp2 hmem]

end

end Erdos1002
