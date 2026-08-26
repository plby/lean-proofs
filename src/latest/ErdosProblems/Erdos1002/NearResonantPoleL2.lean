import ErdosProblems.Erdos1002.NearResonantCellFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact `L²` mass of a smooth primitive resonance pole

The disjoint reduced cells give an exact mass formula, including the
modulus-one endpoint cell.  This is the rigorous source of the factor
`φ(p) p⁻²` in the near-resonant argument.
-/

open Filter MeasureTheory Set
open scoped BigOperators Real

namespace Erdos1002

noncomputable section

theorem norm_scaledNearProfile_le_one (s x : ℝ) :
    ‖scaledNearProfile s x‖ ≤ 1 := by
  have hcut :=
    gevreyOuterCutoff_mem_Icc (by norm_num : (0 : ℝ) < 2) (x / s)
  unfold scaledNearProfile nearBaseProfile
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hcut.1]
  exact hcut.2

theorem norm_nearRho_le_two (a ε x : ℝ) :
    ‖nearRho a ε x‖ ≤ 2 := by
  unfold nearRho
  calc
    ‖scaledNearProfile (ε / 2) x - scaledNearProfile a x‖ ≤
        ‖scaledNearProfile (ε / 2) x‖ + ‖scaledNearProfile a x‖ :=
      norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add
      (norm_scaledNearProfile_le_one _ _) (norm_scaledNearProfile_le_one _ _)
    _ = 2 := by norm_num

/-- The squared pole profile is integrable.  This preliminary domination is
deliberately explicit; the sharper `O(a⁻¹)` bound is proved separately. -/
theorem integrable_norm_nearW_sq
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    Integrable (fun x : ℝ ↦ ‖nearW a ε x‖ ^ 2) := by
  let g : ℝ → ℝ := fun x ↦ 2 * a⁻¹ ^ 2 * ‖nearRho a ε x‖
  have hg : Integrable g :=
    (nearRho_integrable a ε ha hε).norm.const_mul (2 * a⁻¹ ^ 2)
  apply hg.mono'
  · exact ((nearW_aestronglyMeasurable a ε ha hε).norm.pow 2)
  · filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg ‖nearW a ε x‖)]
    have hW := norm_nearW_le a ε x ha haε
    have hρ := norm_nearRho_le_two a ε x
    have haInv : 0 ≤ a⁻¹ := (inv_pos.mpr ha).le
    have hρnonneg : 0 ≤ ‖nearRho a ε x‖ := norm_nonneg _
    dsimp [g]
    calc
      ‖nearW a ε x‖ ^ 2 ≤
          (a⁻¹ * ‖nearRho a ε x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hW 2
      _ = a⁻¹ ^ 2 * ‖nearRho a ε x‖ ^ 2 := by ring
      _ ≤ a⁻¹ ^ 2 * (2 * ‖nearRho a ε x‖) := by
        gcongr
        nlinarith
      _ = 2 * a⁻¹ ^ 2 * ‖nearRho a ε x‖ := by ring

/-- Total real-line squared mass of the pole profile. -/
def nearWNormSqMass (a ε : ℝ) : ℝ :=
  ∫ x : ℝ, ‖nearW a ε x‖ ^ 2

theorem nearWNormSqMass_nonneg (a ε : ℝ) :
    0 ≤ nearWNormSqMass a ε := by
  unfold nearWNormSqMass
  exact integral_nonneg fun _ ↦ sq_nonneg _

theorem nearWNormSqMass_eq_two_mul_integral_Ioi (a ε : ℝ) :
    nearWNormSqMass a ε =
      2 * ∫ x in Ioi (0 : ℝ), ‖nearW a ε x‖ ^ 2 := by
  have hfun :
      (fun x : ℝ ↦ ‖nearW a ε x‖ ^ 2) =
        (fun x : ℝ ↦ ‖nearW a ε |x|‖ ^ 2) := by
    funext x
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · have hxneg : x < 0 := lt_of_not_ge hx
      rw [abs_of_neg hxneg, nearW_neg, norm_neg]
  unfold nearWNormSqMass
  conv_lhs => rw [hfun]
  exact integral_comp_abs (f := fun x : ℝ ↦ ‖nearW a ε x‖ ^ 2)

/-- A simple integrable positive-half-line majorant for `|W_a|²`. -/
def nearWPositiveSqEnvelope (a : ℝ) (x : ℝ) : ℝ :=
  (16 / a) * scaleDecayEnvelope a⁻¹ x

theorem nearWPositiveSqEnvelope_integrableOn_Ioi
    (a : ℝ) (ha : 0 < a) :
    IntegrableOn (nearWPositiveSqEnvelope a) (Ioi 0) := by
  unfold nearWPositiveSqEnvelope
  exact (scaleDecayEnvelope_integrableOn_Ioi a⁻¹ (inv_pos.mpr ha)).const_mul
    (16 / a)

theorem integral_nearWPositiveSqEnvelope_Ioi
    (a : ℝ) (ha : 0 < a) :
    ∫ x in Ioi (0 : ℝ), nearWPositiveSqEnvelope a x = 16 / a := by
  unfold nearWPositiveSqEnvelope
  rw [integral_const_mul,
    integral_scaleDecayEnvelope_Ioi a⁻¹ (inv_pos.mpr ha), mul_one]

theorem norm_nearW_sq_le_positiveEnvelope
    (a ε x : ℝ) (ha : 0 < a) (_hε : 0 < ε)
    (haε : a ≤ ε / 4) (hx : 0 < x) :
    ‖nearW a ε x‖ ^ 2 ≤ nearWPositiveSqEnvelope a x := by
  by_cases hxa : x ≤ a
  · have habs : |x| ≤ a := by rwa [abs_of_pos hx]
    have hρzero := nearRho_eq_zero_of_abs_le a ε x ha haε habs
    unfold nearW
    rw [hρzero, zero_div, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0)]
    unfold nearWPositiveSqEnvelope scaleDecayEnvelope
    positivity
  · have hax : a < x := lt_of_not_ge hxa
    have hnorm : ‖nearW a ε x‖ ≤ 2 / x := by
      unfold nearW
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
      exact div_le_div_of_nonneg_right (norm_nearRho_le_two a ε x) hx.le
    have hsq : ‖nearW a ε x‖ ^ 2 ≤ 4 / x ^ 2 := by
      calc
        ‖nearW a ε x‖ ^ 2 ≤ (2 / x) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ = 4 / x ^ 2 := by ring
    have henv : nearWPositiveSqEnvelope a x = 16 / (a + x) ^ 2 := by
      unfold nearWPositiveSqEnvelope scaleDecayEnvelope
      field_simp [ha.ne']
    rw [henv]
    refine hsq.trans ?_
    have hsum : a + x ≤ 2 * x := by linarith
    have hsquare : (a + x) ^ 2 ≤ (2 * x) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsum 2
    rw [div_le_div_iff₀ (sq_pos_of_pos hx)
      (sq_pos_of_pos (add_pos ha hx))]
    nlinarith

/-- Sharp scale dependence needed in the pole square-function estimate. -/
theorem nearWNormSqMass_le
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    nearWNormSqMass a ε ≤ 32 / a := by
  have hf : IntegrableOn (fun x : ℝ ↦ ‖nearW a ε x‖ ^ 2) (Ioi 0) :=
    (integrable_norm_nearW_sq a ε ha hε haε).integrableOn
  have hg := nearWPositiveSqEnvelope_integrableOn_Ioi a ha
  have hpoint : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0),
      ‖nearW a ε x‖ ^ 2 ≤ nearWPositiveSqEnvelope a x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_nearW_sq_le_positiveEnvelope a ε x ha hε haε hx
  have hhalf := MeasureTheory.integral_mono_ae hf hg hpoint
  rw [integral_nearWPositiveSqEnvelope_Ioi a ha] at hhalf
  rw [nearWNormSqMass_eq_two_mul_integral_Ioi]
  calc
    2 * ∫ x in Ioi (0 : ℝ), ‖nearW a ε x‖ ^ 2 ≤
        2 * (16 / a) := mul_le_mul_of_nonneg_left hhalf (by norm_num)
    _ = 32 / a := by ring

/-- Squared mass of one reduced affine cell. -/
def nearPoleCellNormSqIntegral
    (a ε : ℝ) (p q : ℕ) : ℝ :=
  ∫ alpha in nearestCellLeft p q..nearestCellRight p q,
    ‖nearPoleCell a ε p q alpha‖ ^ 2

private theorem support_norm_nearW_sq_subset_nearestCell
    (a ε : ℝ) (p : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    Function.support (fun x : ℝ ↦ ‖nearW a ε x‖ ^ 2) ⊆
      Ioc (-(p : ℝ) / 2) ((p : ℝ) / 2) := by
  intro x hx
  have hW : nearW a ε x ≠ 0 := by
    intro hzero
    apply hx
    simp [hzero]
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hεp : ε ≤ (p : ℝ) / 2 := by linarith
  have habs : |x| < ε := by
    by_contra hnot
    exact hW (nearW_eq_zero_of_epsilon_le_abs
      a ε x ha hε haε (le_of_not_gt hnot))
  constructor
  · have hneg : -(p : ℝ) / 2 ≤ -ε := by linarith
    exact hneg.trans_lt (abs_lt.mp habs).1
  · exact (le_abs_self x).trans (habs.le.trans hεp)

/-- Exact affine change of variables for one cell's squared mass. -/
theorem nearPoleCellNormSqIntegral_eq
    (a ε : ℝ) (p q : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    nearPoleCellNormSqIntegral a ε p q =
      (1 / (p : ℝ) ^ 2) * nearWNormSqMass a ε := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  let f : ℝ → ℝ := fun x ↦ ‖nearW a ε x‖ ^ 2
  have hfull :
      (∫ x in (-(p : ℝ) / 2)..((p : ℝ) / 2), f x) =
        nearWNormSqMass a ε := by
    calc
      (∫ x in (-(p : ℝ) / 2)..((p : ℝ) / 2), f x) =
          ∫ x : ℝ, f x :=
        intervalIntegral.integral_eq_integral_of_support_subset
          (support_norm_nearW_sq_subset_nearestCell
            a ε p hp ha hε haε hεhalf)
      _ = nearWNormSqMass a ε := rfl
  unfold nearPoleCellNormSqIntegral nearPoleCell
  rw [show (fun alpha : ℝ ↦
      ‖nearW a ε ((p : ℝ) * ((p : ℝ) * alpha - (q : ℝ)))‖ ^ 2) =
      (fun alpha : ℝ ↦
        f ((p : ℝ) ^ 2 * alpha - (p : ℝ) * (q : ℝ))) by
    funext alpha
    unfold f
    rw [show (p : ℝ) * ((p : ℝ) * alpha - (q : ℝ)) =
      (p : ℝ) ^ 2 * alpha - (p : ℝ) * (q : ℝ) by ring]]
  rw [intervalIntegral.integral_comp_mul_sub f (pow_ne_zero 2 hpR)
    ((p : ℝ) * (q : ℝ)), nearestCellLeft_sq_mul_sub p q hp,
    nearestCellRight_sq_mul_sub p q hp, hfull]
  simp only [smul_eq_mul]
  field_simp [hpR]

/-- Half-open cell cutoff for a nonnegative squared mass. -/
def nearPoleCellNormSqTerm
    (a ε : ℝ) (p q : ℕ) (alpha : ℝ) : ℝ :=
  if (p : ℝ) * alpha - (q : ℝ) ∈
      Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) then
    ‖nearPoleCell a ε p q alpha‖ ^ 2
  else 0

theorem nearPoleCellNormSqIntegrand_integrable
    (a ε : ℝ) (p q : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    Integrable (fun alpha : ℝ ↦ ‖nearPoleCell a ε p q alpha‖ ^ 2) := by
  let f : ℝ → ℝ := fun x ↦ ‖nearW a ε x‖ ^ 2
  have hf : Integrable f := integrable_norm_nearW_sq a ε ha hε haε
  have htrans : Integrable (fun y : ℝ ↦
      f (y - (p : ℝ) * (q : ℝ))) :=
    hf.comp_sub_right ((p : ℝ) * (q : ℝ))
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have haff := htrans.comp_mul_left' (pow_ne_zero 2 hpR)
  apply haff.congr
  filter_upwards with alpha
  unfold f nearPoleCell
  rw [show (p : ℝ) * ((p : ℝ) * alpha - (q : ℝ)) =
    (p : ℝ) ^ 2 * alpha - (p : ℝ) * (q : ℝ) by ring]

theorem nearPoleCellNormSqTerm_integrable
    (a ε : ℝ) (p q : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    Integrable (nearPoleCellNormSqTerm a ε p q) := by
  let s : Set ℝ := {alpha : ℝ |
    (p : ℝ) * alpha - (q : ℝ) ∈
      Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)}
  have hs : MeasurableSet s :=
    measurableSet_Ioc.preimage
      (measurable_const.mul measurable_id |>.sub measurable_const)
  have hi := (nearPoleCellNormSqIntegrand_integrable
    a ε p q hp ha hε haε).indicator hs
  apply hi.congr
  filter_upwards with alpha
  by_cases hcell : (p : ℝ) * alpha - (q : ℝ) ∈
      Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)
  · simp [s, Set.indicator, nearPoleCellNormSqTerm]
  · simp [s, Set.indicator, nearPoleCellNormSqTerm]

theorem support_nearPoleCellNormSqTerm_subset
    (a ε : ℝ) (p q : ℕ) (hp : 0 < p) :
    Function.support (nearPoleCellNormSqTerm a ε p q) ⊆
      Ioc (nearestCellLeft p q) (nearestCellRight p q) := by
  intro alpha halpha
  by_contra hnot
  have hscaled :
      ¬ ((p : ℝ) * alpha - (q : ℝ) ∈
        Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)) := by
    exact fun h ↦ hnot ((mem_nearestCell_iff hp alpha).1 h)
  exact halpha (by rw [nearPoleCellNormSqTerm, if_neg hscaled])

theorem integral_unit_nearPoleCellNormSqTerm_eq
    (a ε : ℝ) (p q : ℕ) (hp : 2 ≤ p)
    (hq : q ∈ reducedResidues p) :
    (∫ alpha in (0 : ℝ)..1,
      nearPoleCellNormSqTerm a ε p q alpha) =
      nearPoleCellNormSqIntegral a ε p q := by
  have hp0 : 0 < p := by omega
  let f : ℝ → ℝ := nearPoleCellNormSqTerm a ε p q
  have hsupportCell : Function.support f ⊆
      Ioc (nearestCellLeft p q) (nearestCellRight p q) :=
    support_nearPoleCellNormSqTerm_subset a ε p q hp0
  have hsupportUnit : Function.support f ⊆ Ioc (0 : ℝ) 1 :=
    hsupportCell.trans (nearestCell_interval_subset_unit hp hq)
  calc
    (∫ alpha in (0 : ℝ)..1, nearPoleCellNormSqTerm a ε p q alpha) =
        ∫ alpha : ℝ, f alpha :=
      intervalIntegral.integral_eq_integral_of_support_subset hsupportUnit
    _ = ∫ alpha in nearestCellLeft p q..nearestCellRight p q, f alpha := by
      symm
      exact intervalIntegral.integral_eq_integral_of_support_subset hsupportCell
    _ = ∫ alpha in nearestCellLeft p q..nearestCellRight p q,
          ‖nearPoleCell a ε p q alpha‖ ^ 2 := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with alpha
      intro halpha
      have hcell : alpha ∈
          Ioc (nearestCellLeft p q) (nearestCellRight p q) := by
        simpa only [Set.uIoc_of_le (nearestCellLeft_lt_right p q hp0).le]
          using! halpha
      change nearPoleCellNormSqTerm a ε p q alpha = _
      rw [nearPoleCellNormSqTerm,
        if_pos ((mem_nearestCell_iff hp0 alpha).2 hcell)]
    _ = nearPoleCellNormSqIntegral a ε p q := rfl

/-- On the open unit interval the primitive pole's squared norm is exactly
the sum of the disjoint reduced-cell squared norms. -/
theorem norm_nearPrimitivePole_sq_eq_sum_cells
    {a ε : ℝ} {p : ℕ} (hp : 2 ≤ p) {alpha : ℝ}
    (halpha : alpha ∈ Ioo (0 : ℝ) 1) :
    ‖nearPrimitivePole a ε p alpha‖ ^ 2 =
      ∑ q ∈ reducedResidues p,
        nearPoleCellNormSqTerm a ε p q alpha := by
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
    rw [Finset.sum_eq_single q]
    · rw [nearPoleCellNormSqTerm, if_pos hcell]
      unfold nearPrimitivePole nearPoleCell resonanceDelta
      rw [if_pos hprim]
      have hqreal : (q : ℝ) = (resonanceNumerator p alpha : ℝ) := by
        exact_mod_cast hqcast
      rw [hqreal]
    · intro b hb hne
      have hnotcell :
          ¬ ((p : ℝ) * alpha - (b : ℝ) ∈
            Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)) := by
        intro hbcell
        have hnum : resonanceNumerator p alpha = (b : ℤ) :=
          resonanceNumerator_eq_of_delta_mem hbcell
        apply hne
        exact_mod_cast (hqcast.trans hnum).symm
      rw [nearPoleCellNormSqTerm, if_neg hnotcell]
    · intro hqnot
      exact (hqnot hqmem).elim
  · have hzero : nearPrimitivePole a ε p alpha = 0 := by
      unfold nearPrimitivePole
      rw [if_neg hprim]
    rw [hzero, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0)]
    symm
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
    rw [nearPoleCellNormSqTerm, if_neg hnotcell]

/-- Exact squared mass for every modulus `p≥2`. -/
theorem integral_unit_norm_nearPrimitivePole_sq_eq
    (a ε : ℝ) (p : ℕ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    (∫ alpha in (0 : ℝ)..1, ‖nearPrimitivePole a ε p alpha‖ ^ 2) =
      (Nat.totient p : ℝ) / (p : ℝ) ^ 2 * nearWNormSqMass a ε := by
  have heq : ∀ᵐ alpha : ℝ ∂volume,
      alpha ∈ uIoc (0 : ℝ) 1 →
        ‖nearPrimitivePole a ε p alpha‖ ^ 2 =
          ∑ q ∈ reducedResidues p,
            nearPoleCellNormSqTerm a ε p q alpha := by
    have hone : ∀ᵐ alpha : ℝ ∂volume, alpha ≠ 1 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hone] with alpha halphaOne
    intro halpha
    have hmem : alpha ∈ Ioo (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at halpha
      exact ⟨halpha.1, lt_of_le_of_ne halpha.2 halphaOne⟩
    exact norm_nearPrimitivePole_sq_eq_sum_cells hp hmem
  rw [intervalIntegral.integral_congr_ae heq,
    intervalIntegral.integral_finset_sum]
  · calc
      (∑ q ∈ reducedResidues p,
          ∫ alpha in (0 : ℝ)..1,
            nearPoleCellNormSqTerm a ε p q alpha) =
          ∑ q ∈ reducedResidues p,
            nearPoleCellNormSqIntegral a ε p q := by
        apply Finset.sum_congr rfl
        intro q hq
        exact integral_unit_nearPoleCellNormSqTerm_eq a ε p q hp hq
      _ = ∑ _q ∈ reducedResidues p,
          (1 / (p : ℝ) ^ 2) * nearWNormSqMass a ε := by
        apply Finset.sum_congr rfl
        intro q _hq
        exact nearPoleCellNormSqIntegral_eq a ε p q (by omega)
          ha hε haε hεhalf
      _ = (Nat.totient p : ℝ) / (p : ℝ) ^ 2 *
          nearWNormSqMass a ε := by
        rw [Finset.sum_const, nsmul_eq_mul, card_reducedResidues]
        ring
  · intro q _hq
    exact (nearPoleCellNormSqTerm_integrable
      a ε p q (by omega) ha hε haε).intervalIntegrable

theorem nearPrimitivePoleNormSq_one_periodic (a ε : ℝ) :
    Function.Periodic (fun alpha ↦ ‖nearPrimitivePole a ε 1 alpha‖ ^ 2) 1 := by
  intro alpha
  change ‖nearPrimitivePole a ε 1 (alpha + 1)‖ ^ 2 =
    ‖nearPrimitivePole a ε 1 alpha‖ ^ 2
  rw [nearPrimitivePole_one_periodic]

/-- Exact squared mass for the endpoint modulus `p=1`. -/
theorem integral_unit_norm_nearPrimitivePole_one_sq_eq
    (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    (∫ alpha in (0 : ℝ)..1, ‖nearPrimitivePole a ε 1 alpha‖ ^ 2) =
      nearWNormSqMass a ε := by
  let f : ℝ → ℝ := fun alpha ↦ ‖nearPrimitivePole a ε 1 alpha‖ ^ 2
  have hperiod : Function.Periodic f 1 :=
    nearPrimitivePoleNormSq_one_periodic a ε
  have hshift := hperiod.intervalIntegral_add_eq (0 : ℝ) (-(1 : ℝ) / 2)
  have hinterval :
      (∫ alpha in (0 : ℝ)..1, f alpha) =
        ∫ alpha in (-(1 : ℝ) / 2)..((1 : ℝ) / 2), f alpha := by
    convert! hshift using 1 <;> norm_num
  change (∫ alpha in (0 : ℝ)..1, f alpha) = _
  rw [hinterval]
  calc
    (∫ alpha in (-(1 : ℝ) / 2)..((1 : ℝ) / 2), f alpha) =
        nearPoleCellNormSqIntegral a ε 1 0 := by
      unfold nearPoleCellNormSqIntegral
      norm_num [nearestCellLeft, nearestCellRight]
      apply intervalIntegral.integral_congr_ae
      filter_upwards with alpha
      intro halpha
      have hcell : alpha ∈ Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
        have halpha' : alpha ∈
            uIoc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
          simpa only [neg_div] using! halpha
        rw [uIoc_of_le
          (by norm_num : (-(1 : ℝ) / 2) ≤ (1 : ℝ) / 2)] at halpha'
        exact halpha'
      have hnum : resonanceNumerator 1 alpha = 0 :=
        resonanceNumerator_eq_of_delta_mem (by simpa using! hcell)
      unfold f nearPrimitivePole nearPoleCell resonanceDelta
      rw [if_pos (isPrimitiveResonance_one alpha), hnum]
      norm_num
    _ = nearWNormSqMass a ε := by
      rw [nearPoleCellNormSqIntegral_eq a ε 1 0 (by omega)
        ha hε haε hεhalf]
      norm_num

/-- Uniform exact formula for every positive denominator. -/
theorem integral_unit_norm_nearPrimitivePole_sq_eq_of_pos
    (a ε : ℝ) (p : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    (∫ alpha in (0 : ℝ)..1, ‖nearPrimitivePole a ε p alpha‖ ^ 2) =
      (Nat.totient p : ℝ) / (p : ℝ) ^ 2 * nearWNormSqMass a ε := by
  by_cases hpone : p = 1
  · subst p
    simpa using! integral_unit_norm_nearPrimitivePole_one_sq_eq
      a ε ha hε haε hεhalf
  · exact integral_unit_norm_nearPrimitivePole_sq_eq
      a ε p (by omega) ha hε haε hεhalf

/-- The uniform pole-mass estimate used by the near-resonant square function.
The exact totient factor is harmless because `φ(p) ≤ p`. -/
theorem integral_unit_norm_nearPrimitivePole_sq_le
    (a ε : ℝ) (p : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    (∫ alpha in (0 : ℝ)..1, ‖nearPrimitivePole a ε p alpha‖ ^ 2) ≤
      32 / (a * p) := by
  rw [integral_unit_norm_nearPrimitivePole_sq_eq_of_pos
    a ε p hp ha hε haε hεhalf]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have htot : (Nat.totient p : ℝ) ≤ p := by
    exact_mod_cast Nat.totient_le p
  have hratio :
      (Nat.totient p : ℝ) / (p : ℝ) ^ 2 ≤ 1 / p := by
    rw [div_le_iff₀ (sq_pos_of_pos hpR)]
    field_simp
    exact htot
  calc
    (Nat.totient p : ℝ) / (p : ℝ) ^ 2 * nearWNormSqMass a ε ≤
        (1 / p) * nearWNormSqMass a ε :=
      mul_le_mul_of_nonneg_right hratio (nearWNormSqMass_nonneg a ε)
    _ ≤ (1 / p) * (32 / a) :=
      mul_le_mul_of_nonneg_left (nearWNormSqMass_le a ε ha hε haε)
        (by positivity)
    _ = 32 / (a * p) := by field_simp

end

end Erdos1002
