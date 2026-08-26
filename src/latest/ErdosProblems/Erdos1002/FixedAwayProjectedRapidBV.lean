import ErdosProblems.Erdos1002.FixedAwayRapidSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Projected rapid BV bounds for fixed-away carriers

This file treats the carrier-annulus projection itself.  The original
regulated jumps lie strictly inside the deleted interval and therefore do
not contribute.  The only new jumps are the two projection boundaries,
whose actual sampled values are displayed explicitly.
-/

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate Real Topology

namespace Erdos1002

noncomputable section

theorem fixedAwayRapidEnvelope_antitone_abs
    (J : ℕ) {x y : ℝ} (hxy : |y| ≤ |x|) :
    fixedAwayRapidEnvelope J x ≤ fixedAwayRapidEnvelope J y := by
  unfold fixedAwayRapidEnvelope
  have hx : 0 < 1 + |x| := by positivity
  have hy : 0 < 1 + |y| := by positivity
  have hinv : (1 + |x|)⁻¹ ≤ (1 + |y|)⁻¹ :=
    (inv_le_inv₀ hx hy).2 (by linarith)
  exact pow_le_pow_left₀ (by positivity) hinv J

def fixedAwayScaledRapidDensity (s a x : ℝ) : ℝ :=
  s⁻¹ * fixedAwayRapidEnvelope 2 ((x - a) / s)

theorem fixedAwayScaledRapidDensity_nonneg
    {s : ℝ} (hs : 0 < s) (a x : ℝ) :
    0 ≤ fixedAwayScaledRapidDensity s a x := by
  unfold fixedAwayScaledRapidDensity
  exact mul_nonneg (inv_nonneg.mpr hs.le)
    (fixedAwayRapidEnvelope_nonneg 2 _)

theorem integrable_fixedAwayScaledRapidDensity
    {s : ℝ} (hs : 0 < s) (a : ℝ) :
    Integrable (fixedAwayScaledRapidDensity s a) := by
  have hdiv := integrable_fixedAwayRapidEnvelope_two.comp_div hs.ne'
  have hshift := hdiv.comp_sub_right a
  have hmul := hshift.const_mul s⁻¹
  simpa only [fixedAwayScaledRapidDensity, Function.comp_apply] using! hmul

theorem integral_fixedAwayScaledRapidDensity
    {s : ℝ} (hs : 0 < s) (a : ℝ) :
    (∫ x : ℝ, fixedAwayScaledRapidDensity s a x) =
      fixedAwayRapidEnvelopeTwoMass := by
  let F : ℝ → ℝ := fun x ↦ fixedAwayRapidEnvelope 2 ((x - a) / s)
  have htranslation := integral_add_right_eq_self (μ := volume) F a
  have hscale := Measure.integral_comp_mul_left (fun z ↦ F (z + a)) s
  have hchange : s⁻¹ * (∫ x : ℝ, F x) =
      fixedAwayRapidEnvelopeTwoMass := by
    calc
      s⁻¹ * (∫ x : ℝ, F x) =
          |s⁻¹| * (∫ z : ℝ, F (z + a)) := by
            rw [abs_of_pos (inv_pos.mpr hs), htranslation]
      _ = ∫ x : ℝ, F (s * x + a) := hscale.symm
      _ = ∫ x : ℝ, fixedAwayRapidEnvelope 2 x := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [F]
        congr 2
        field_simp [hs.ne']
        ring
      _ = fixedAwayRapidEnvelopeTwoMass := rfl
  unfold fixedAwayScaledRapidDensity
  rw [integral_const_mul]
  exact hchange

/-- Away from both carrier points, the product derivative is bounded by an
integrable density times one common far-away envelope. -/
theorem norm_deriv_fixedAwayScaledHermitianProduct_le_of_both_far
    {t δ s a s' a' x h : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (hs : 0 < s) (hs' : 0 < s') (hh : 0 < h)
    (hfar : h ≤ |(x - a) / s|)
    (hfar' : h ≤ |(x - a') / s'|)
    (J : ℕ) :
    ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖ ≤
      (fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
        fixedAwayPVRapidDecayConstant t δ (J + 2)) *
      fixedAwayRapidEnvelope J h *
        (fixedAwayScaledRapidDensity s a x +
          fixedAwayScaledRapidDensity s' a' x) := by
  have hxa : x ≠ a := by
    intro hEq
    subst x
    simp only [sub_self, zero_div, abs_zero] at hfar
    linarith
  have hxa' : x ≠ a' := by
    intro hEq
    subst x
    simp only [sub_self, zero_div, abs_zero] at hfar'
    linarith
  have hraw := norm_deriv_fixedAwayScaledHermitianProduct_le_rapidEnvelope
    hδ hδt hs hs' hxa hxa' J
  let D : ℝ := fixedAwayDerivativeRapidDecayConstant t δ (J + 2)
  let C : ℝ := fixedAwayPVRapidDecayConstant t δ (J + 2)
  let Eu : ℝ := fixedAwayRapidEnvelope (J + 2) ((x - a) / s)
  let Ev : ℝ := fixedAwayRapidEnvelope (J + 2) ((x - a') / s')
  let E2u : ℝ := fixedAwayRapidEnvelope 2 ((x - a) / s)
  let E2v : ℝ := fixedAwayRapidEnvelope 2 ((x - a') / s')
  let Eh : ℝ := fixedAwayRapidEnvelope J h
  have hD : 0 ≤ D := fixedAwayDerivativeRapidDecayConstant_nonneg t δ _
  have hC : 0 ≤ C := fixedAwayPVRapidDecayConstant_nonneg t δ (by omega)
  have hEu : 0 ≤ Eu := fixedAwayRapidEnvelope_nonneg _ _
  have hEv : 0 ≤ Ev := fixedAwayRapidEnvelope_nonneg _ _
  have hE2u : 0 ≤ E2u := fixedAwayRapidEnvelope_nonneg _ _
  have hE2v : 0 ≤ E2v := fixedAwayRapidEnvelope_nonneg _ _
  have hEh : 0 ≤ Eh := fixedAwayRapidEnvelope_nonneg _ _
  have hEuTwo : Eu ≤ E2u := by
    dsimp only [Eu, E2u]
    rw [fixedAwayRapidEnvelope_add_two]
    exact mul_le_of_le_one_left hE2u
      (fixedAwayRapidEnvelope_le_one J ((x - a) / s))
  have hEvTwo : Ev ≤ E2v := by
    dsimp only [Ev, E2v]
    rw [fixedAwayRapidEnvelope_add_two]
    exact mul_le_of_le_one_left hE2v
      (fixedAwayRapidEnvelope_le_one J ((x - a') / s'))
  have hEuJ : Eu ≤ fixedAwayRapidEnvelope J ((x - a) / s) := by
    dsimp only [Eu]
    rw [fixedAwayRapidEnvelope_add_two]
    exact mul_le_of_le_one_right
      (fixedAwayRapidEnvelope_nonneg J ((x - a) / s))
      (fixedAwayRapidEnvelope_le_one 2 ((x - a) / s))
  have hEvJ : Ev ≤ fixedAwayRapidEnvelope J ((x - a') / s') := by
    dsimp only [Ev]
    rw [fixedAwayRapidEnvelope_add_two]
    exact mul_le_of_le_one_right
      (fixedAwayRapidEnvelope_nonneg J ((x - a') / s'))
      (fixedAwayRapidEnvelope_le_one 2 ((x - a') / s'))
  have hEuFar : Eu ≤ Eh := by
    calc
      Eu ≤ fixedAwayRapidEnvelope J ((x - a) / s) := hEuJ
      _ ≤ Eh := fixedAwayRapidEnvelope_antitone_abs J (by
        simpa only [abs_of_pos hh] using! hfar)
  have hEvFar : Ev ≤ Eh := by
    calc
      Ev ≤ fixedAwayRapidEnvelope J ((x - a') / s') := hEvJ
      _ ≤ Eh := fixedAwayRapidEnvelope_antitone_abs J (by
        simpa only [abs_of_pos hh] using! hfar')
  change _ ≤ (D * C) * Eh *
    (fixedAwayScaledRapidDensity s a x +
      fixedAwayScaledRapidDensity s' a' x)
  change _ ≤ (D * C) * Eh *
    (s⁻¹ * E2u + s'⁻¹ * E2v)
  change _ ≤ _ at hraw
  calc
    ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖ ≤
      s⁻¹ * (D * Eu) * (C * Ev) +
        (C * Eu) * (s'⁻¹ * (D * Ev)) := hraw
    _ ≤ s⁻¹ * (D * E2u) * (C * Eh) +
        (C * Eh) * (s'⁻¹ * (D * E2v)) := by
      apply add_le_add
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hEuTwo hD)
            (inv_nonneg.mpr hs.le))
          (mul_le_mul_of_nonneg_left hEvFar hC)
          (mul_nonneg hC hEv)
          (mul_nonneg (inv_nonneg.mpr hs.le) (mul_nonneg hD hE2u))
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_left hEuFar hC)
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hEvTwo hD)
            (inv_nonneg.mpr hs'.le))
          (mul_nonneg (inv_nonneg.mpr hs'.le) (mul_nonneg hD hEv))
          (mul_nonneg hC hEh)
    _ = (D * C) * Eh * (s⁻¹ * E2u + s'⁻¹ * E2v) := by ring

/-- Outside the deleted integer interval, or on either of its two boundary
cells, the projected variation is controlled by the original cell variation
and the two literal endpoint values.  On cells wholly inside the interval
the projected sequence is identically zero. -/
theorem norm_integerIntervalComplementMultiplier_sub_succ_le_relevant
    {u v : ℤ} (huv : u ≤ v) (w : ℤ → ℂ) (n : ℤ) :
    ‖integerIntervalComplementMultiplier u v w n -
        integerIntervalComplementMultiplier u v w (n + 1)‖ ≤
      (if n < u ∨ v ≤ n then ‖w n - w (n + 1)‖ else 0) +
        leftIntervalBoundaryVariation u w n +
        rightIntervalBoundaryVariation v w n := by
  by_cases hrel : n < u ∨ v ≤ n
  · rw [if_pos hrel]
    simpa only [leftIntervalBoundaryVariation,
      rightIntervalBoundaryVariation, add_assoc] using!
        norm_integerIntervalComplementMultiplier_sub_succ_le huv w n
  · push_neg at hrel
    have hn : u ≤ n ∧ n ≤ v := ⟨hrel.1, hrel.2.le⟩
    have hn1 : u ≤ n + 1 ∧ n + 1 ≤ v := ⟨by omega, by omega⟩
    have hnu : n + 1 ≠ u := by omega
    have hnv : n ≠ v := by omega
    rw [if_neg (by omega)]
    simp [integerIntervalComplementMultiplier, hn, hn1,
      leftIntervalBoundaryVariation,
      rightIntervalBoundaryVariation, hnu, hnv]

theorem fixedAwayHermitianCellJumpCharge_eq_zero_of_left
    {t δ s a s' a' : ℝ} {u : ℤ}
    (ha : (u : ℝ) < a) (ha' : (u : ℝ) < a')
    (n : ℤ) (hn : n < u) :
    fixedAwayHermitianCellJumpCharge t δ s a s' a'
      (n : ℝ) ((n : ℝ) + 1) = 0 := by
  have hna : a ∉ Icc (n : ℝ) ((n : ℝ) + 1) := by
    intro hmem
    have hnu : ((n : ℝ) + 1) ≤ (u : ℝ) := by exact_mod_cast (show n + 1 ≤ u by omega)
    linarith [hmem.2]
  have hna' : a' ∉ Icc (n : ℝ) ((n : ℝ) + 1) := by
    intro hmem
    have hnu : ((n : ℝ) + 1) ≤ (u : ℝ) := by exact_mod_cast (show n + 1 ≤ u by omega)
    linarith [hmem.2]
  unfold fixedAwayHermitianCellJumpCharge
  split_ifs <;> simp_all

theorem fixedAwayHermitianCellJumpCharge_eq_zero_of_right
    {t δ s a s' a' : ℝ} {v : ℤ}
    (ha : a < (v : ℝ)) (ha' : a' < (v : ℝ))
    (n : ℤ) (hn : v ≤ n) :
    fixedAwayHermitianCellJumpCharge t δ s a s' a'
      (n : ℝ) ((n : ℝ) + 1) = 0 := by
  have hna : a ∉ Icc (n : ℝ) ((n : ℝ) + 1) := by
    intro hmem
    have hvn : (v : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith [hmem.1]
  have hna' : a' ∉ Icc (n : ℝ) ((n : ℝ) + 1) := by
    intro hmem
    have hvn : (v : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith [hmem.1]
  unfold fixedAwayHermitianCellJumpCharge
  split_ifs <;> simp_all

/-- One exterior cell of the projected sequence is controlled by the common
far-away derivative density.  Original carrier jumps vanish because both
carriers lie strictly inside the deleted interval. -/
theorem integerSampleVariation_fixedAway_le_farDensity_of_relevant
    {t δ s a s' a' h : ℝ} {u v n : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hs : 0 < s) (hs' : 0 < s')
    (hua : (u : ℝ) < a) (hua' : (u : ℝ) < a')
    (hav : a < (v : ℝ)) (ha'v : a' < (v : ℝ))
    (hh : 0 < h)
    (hfar : ∀ x : ℝ, x ≤ (u : ℝ) ∨ (v : ℝ) ≤ x →
      h ≤ |(x - a) / s| ∧ h ≤ |(x - a') / s'|)
    (J : ℕ) (hrel : n < u ∨ v ≤ n) :
    ‖fixedAwayHermitianIntegerWeight t δ s a s' a' n -
        fixedAwayHermitianIntegerWeight t δ s a s' a' (n + 1)‖ ≤
      ∫ x in (n : ℝ)..((n : ℝ) + 1),
        (fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
          fixedAwayPVRapidDecayConstant t δ (J + 2)) *
        fixedAwayRapidEnvelope J h *
          (fixedAwayScaledRapidDensity s a x +
            fixedAwayScaledRapidDensity s' a' x) := by
  have hcell :=
    norm_sub_fixedAwayScaledHermitianProduct_le_integral_add_cellJumpCharge
      (t := t) (δ := δ) (s := s) (a := a) (s' := s') (a' := a')
      hδ hδt hs hs' (show (n : ℝ) < (n : ℝ) + 1 by norm_num)
  have hjump : fixedAwayHermitianCellJumpCharge t δ s a s' a'
      (n : ℝ) ((n : ℝ) + 1) = 0 := by
    rcases hrel with hn | hn
    · exact fixedAwayHermitianCellJumpCharge_eq_zero_of_left
        hua hua' n hn
    · exact fixedAwayHermitianCellJumpCharge_eq_zero_of_right
        hav ha'v n hn
  rw [hjump, add_zero] at hcell
  have hderivInt : IntervalIntegrable (fun x : ℝ ↦
      ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖)
      volume (n : ℝ) ((n : ℝ) + 1) :=
    (integrable_deriv_fixedAwayScaledHermitianProduct
      hδ hδt hs.ne' hs'.ne').norm.intervalIntegrable
  have hdensityInt : Integrable (fun x : ℝ ↦
      (fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
        fixedAwayPVRapidDecayConstant t δ (J + 2)) *
      fixedAwayRapidEnvelope J h *
        (fixedAwayScaledRapidDensity s a x +
          fixedAwayScaledRapidDensity s' a' x)) := by
    exact ((integrable_fixedAwayScaledRapidDensity hs a).add
      (integrable_fixedAwayScaledRapidDensity hs' a')).const_mul
        ((fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
          fixedAwayPVRapidDecayConstant t δ (J + 2)) *
            fixedAwayRapidEnvelope J h)
  have hintBound :
      (∫ x in (n : ℝ)..((n : ℝ) + 1),
        ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖) ≤
      ∫ x in (n : ℝ)..((n : ℝ) + 1),
        (fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
          fixedAwayPVRapidDecayConstant t δ (J + 2)) *
        fixedAwayRapidEnvelope J h *
          (fixedAwayScaledRapidDensity s a x +
            fixedAwayScaledRapidDensity s' a' x) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      hderivInt hdensityInt.intervalIntegrable
    intro x hx
    have hxExterior : x ≤ (u : ℝ) ∨ (v : ℝ) ≤ x := by
      rcases hrel with hn | hn
      · left
        have hnu : (n : ℝ) + 1 ≤ (u : ℝ) := by
          exact_mod_cast (show n + 1 ≤ u by omega)
        exact hx.2.trans hnu
      · right
        have hvn : (v : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        exact hvn.trans hx.1
    exact norm_deriv_fixedAwayScaledHermitianProduct_le_of_both_far
      hδ hδt hs hs' hh (hfar x hxExterior).1 (hfar x hxExterior).2 J
  simpa only [fixedAwayHermitianIntegerWeight, Int.cast_add,
    Int.cast_one] using! hcell.trans hintBound

theorem norm_fixedAwayScaledHermitianProduct_le_of_both_far
    {t δ s a s' a' x h : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (hh : 0 < h) (hfar : h ≤ |(x - a) / s|)
    (hfar' : h ≤ |(x - a') / s'|)
    {J : ℕ} (hJ : 0 < J) :
    ‖fixedAwayScaledHermitianProduct t δ s a s' a' x‖ ≤
      fixedAwayPVRapidDecayConstant t δ J ^ 2 *
        fixedAwayRapidEnvelope J h := by
  let C : ℝ := fixedAwayPVRapidDecayConstant t δ J
  let Eu : ℝ := fixedAwayRapidEnvelope J ((x - a) / s)
  let Ev : ℝ := fixedAwayRapidEnvelope J ((x - a') / s')
  let Eh : ℝ := fixedAwayRapidEnvelope J h
  have hC : 0 ≤ C := fixedAwayPVRapidDecayConstant_nonneg t δ hJ
  have hEu : 0 ≤ Eu := fixedAwayRapidEnvelope_nonneg _ _
  have hEv : 0 ≤ Ev := fixedAwayRapidEnvelope_nonneg _ _
  have hEh : 0 ≤ Eh := fixedAwayRapidEnvelope_nonneg _ _
  have hEhOne : Eh ≤ 1 := fixedAwayRapidEnvelope_le_one _ _
  have hEuFar : Eu ≤ Eh := fixedAwayRapidEnvelope_antitone_abs J (by
    simpa only [abs_of_pos hh] using! hfar)
  have hEvFar : Ev ≤ Eh := fixedAwayRapidEnvelope_antitone_abs J (by
    simpa only [abs_of_pos hh] using! hfar')
  have hleft := norm_fixedAwayPVTransform_smooth_le_rapidDecay
    hδ hδt hJ ((x - a) / s)
  have hright := norm_fixedAwayPVTransform_smooth_le_rapidDecay
    hδ hδt hJ ((x - a') / s')
  unfold fixedAwayScaledHermitianProduct fixedAwayScaledPV
  rw [norm_mul, Complex.norm_conj]
  change _ ≤ C ^ 2 * Eh
  change _ ≤ C * Eu at hleft
  change _ ≤ C * Ev at hright
  calc
    ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
          ((x - a) / s)‖ *
        ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
          ((x - a') / s')‖ ≤
      (C * Eu) * (C * Ev) :=
        mul_le_mul hleft hright (norm_nonneg _) (mul_nonneg hC hEu)
    _ ≤ (C * Eh) * (C * Eh) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hEuFar hC)
        (mul_le_mul_of_nonneg_left hEvFar hC)
        (mul_nonneg hC hEv) (mul_nonneg hC hEh)
    _ = C ^ 2 * Eh ^ 2 := by ring
    _ ≤ C ^ 2 * Eh := by
      have hsq : Eh ^ 2 ≤ Eh := by
        simpa only [pow_two] using! mul_le_of_le_one_right hEh hEhOne
      exact mul_le_mul_of_nonneg_left
        hsq (sq_nonneg C)

def fixedAwayProjectedRapidVariationConstant
    (t δ : ℝ) (J : ℕ) : ℝ :=
  2 * (fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
      fixedAwayPVRapidDecayConstant t δ (J + 2)) *
      fixedAwayRapidEnvelopeTwoMass +
    2 * fixedAwayPVRapidDecayConstant t δ J ^ 2

theorem fixedAwayProjectedRapidVariationConstant_nonneg
    (t δ : ℝ) {J : ℕ} (hJ : 0 < J) :
    0 ≤ fixedAwayProjectedRapidVariationConstant t δ J := by
  unfold fixedAwayProjectedRapidVariationConstant
  have hD := fixedAwayDerivativeRapidDecayConstant_nonneg t δ (J + 2)
  have hC2 := fixedAwayPVRapidDecayConstant_nonneg t δ (by omega : 0 < J + 2)
  have hCJ := fixedAwayPVRapidDecayConstant_nonneg t δ hJ
  have hmass := fixedAwayRapidEnvelopeTwoMass_nonneg
  positivity

/-- Complete projected sampled-TV estimate.  The original carrier jumps are
absent; the last two terms in the constant are exactly the two projection
boundary values. -/
theorem tsum_variation_projected_fixedAwayHermitianIntegerWeight_le_rapid
    {t δ s a s' a' h : ℝ} {u v : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hs : 0 < s) (hs' : 0 < s')
    (huv : u ≤ v)
    (hua : (u : ℝ) < a) (hua' : (u : ℝ) < a')
    (hav : a < (v : ℝ)) (ha'v : a' < (v : ℝ))
    (hh : 0 < h)
    (hfar : ∀ x : ℝ, x ≤ (u : ℝ) ∨ (v : ℝ) ≤ x →
      h ≤ |(x - a) / s| ∧ h ≤ |(x - a') / s'|)
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖integerIntervalComplementMultiplier u v
          (fixedAwayHermitianIntegerWeight t δ s a s' a') n -
        integerIntervalComplementMultiplier u v
          (fixedAwayHermitianIntegerWeight t δ s a s' a') (n + 1)‖) ≤
      fixedAwayProjectedRapidVariationConstant t δ J *
        fixedAwayRapidEnvelope J h := by
  let w : ℤ → ℂ := fixedAwayHermitianIntegerWeight t δ s a s' a'
  let K : ℝ :=
    (fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
      fixedAwayPVRapidDecayConstant t δ (J + 2)) *
        fixedAwayRapidEnvelope J h
  let H : ℝ → ℝ := fun x ↦ K *
    (fixedAwayScaledRapidDensity s a x +
      fixedAwayScaledRapidDensity s' a' x)
  let g : ℤ → ℝ := fun n ↦ ∫ x in (n : ℝ)..((n : ℝ) + 1), H x
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg
      (mul_nonneg
        (fixedAwayDerivativeRapidDecayConstant_nonneg t δ (J + 2))
        (fixedAwayPVRapidDecayConstant_nonneg t δ (by omega)))
      (fixedAwayRapidEnvelope_nonneg J h)
  have hHnonneg : ∀ x, 0 ≤ H x := by
    intro x
    dsimp only [H]
    exact mul_nonneg hK (add_nonneg
      (fixedAwayScaledRapidDensity_nonneg hs a x)
      (fixedAwayScaledRapidDensity_nonneg hs' a' x))
  have hHint : Integrable H := by
    exact ((integrable_fixedAwayScaledRapidDensity hs a).add
      (integrable_fixedAwayScaledRapidDensity hs' a')).const_mul K
  have hgHas : HasSum g (∫ x : ℝ, H x) := by
    have hraw := hHint.hasSum_intervalIntegral (0 : ℝ)
    simpa only [zero_add, g] using! hraw
  have hleft := summable_leftIntervalBoundaryVariation u w
  have hright := summable_rightIntervalBoundaryVariation v w
  have hpoint : ∀ n : ℤ,
      ‖integerIntervalComplementMultiplier u v w n -
          integerIntervalComplementMultiplier u v w (n + 1)‖ ≤
        g n + leftIntervalBoundaryVariation u w n +
          rightIntervalBoundaryVariation v w n := by
    intro n
    have hproj :=
      norm_integerIntervalComplementMultiplier_sub_succ_le_relevant
        huv w n
    by_cases hrel : n < u ∨ v ≤ n
    · rw [if_pos hrel] at hproj
      have hcell :=
        integerSampleVariation_fixedAway_le_farDensity_of_relevant
          hδ hδt hs hs' hua hua' hav ha'v hh hfar J hrel
      change ‖w n - w (n + 1)‖ ≤ g n at hcell
      exact hproj.trans (by linarith)
    · rw [if_neg hrel] at hproj
      have hg0 : 0 ≤ g n := by
        dsimp only [g]
        exact intervalIntegral.integral_nonneg (by norm_num)
          (fun x _hx ↦ hHnonneg x)
      exact hproj.trans (by linarith)
  have hprojSummable : Summable fun n : ℤ ↦
      ‖integerIntervalComplementMultiplier u v w n -
        integerIntervalComplementMultiplier u v w (n + 1)‖ :=
    (hgHas.summable.add (hleft.add hright)).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (by
        intro n
        simpa only [add_assoc] using! hpoint n)
  have hsumBound : (∑' n : ℤ,
      ‖integerIntervalComplementMultiplier u v w n -
        integerIntervalComplementMultiplier u v w (n + 1)‖) ≤
      (∫ x : ℝ, H x) + ‖w u‖ + ‖w v‖ := by
    calc
      (∑' n : ℤ,
          ‖integerIntervalComplementMultiplier u v w n -
            integerIntervalComplementMultiplier u v w (n + 1)‖) ≤
        ∑' n : ℤ, (g n +
          (leftIntervalBoundaryVariation u w n +
            rightIntervalBoundaryVariation v w n)) := by
          apply hprojSummable.tsum_le_tsum
          · intro n
            simpa only [add_assoc] using! hpoint n
          · exact hgHas.summable.add (hleft.add hright)
      _ = (∫ x : ℝ, H x) +
          ((∑' n : ℤ, leftIntervalBoundaryVariation u w n) +
            ∑' n : ℤ, rightIntervalBoundaryVariation v w n) := by
        rw [hgHas.summable.tsum_add (hleft.add hright),
          hgHas.tsum_eq, hleft.tsum_add hright]
      _ = (∫ x : ℝ, H x) + ‖w u‖ + ‖w v‖ := by
        rw [tsum_leftIntervalBoundaryVariation,
          tsum_rightIntervalBoundaryVariation]
        ring
  have hIntegral : (∫ x : ℝ, H x) =
      2 * (fixedAwayDerivativeRapidDecayConstant t δ (J + 2) *
        fixedAwayPVRapidDecayConstant t δ (J + 2)) *
        fixedAwayRapidEnvelopeTwoMass *
          fixedAwayRapidEnvelope J h := by
    dsimp only [H, K]
    rw [integral_const_mul,
      integral_add (integrable_fixedAwayScaledRapidDensity hs a)
        (integrable_fixedAwayScaledRapidDensity hs' a'),
      integral_fixedAwayScaledRapidDensity hs a,
      integral_fixedAwayScaledRapidDensity hs' a']
    ring
  have hwu : ‖w u‖ ≤
      fixedAwayPVRapidDecayConstant t δ J ^ 2 *
        fixedAwayRapidEnvelope J h := by
    dsimp only [w, fixedAwayHermitianIntegerWeight]
    exact norm_fixedAwayScaledHermitianProduct_le_of_both_far
      hδ hδt hh (hfar (u : ℝ) (Or.inl le_rfl)).1
        (hfar (u : ℝ) (Or.inl le_rfl)).2 hJ
  have hwv : ‖w v‖ ≤
      fixedAwayPVRapidDecayConstant t δ J ^ 2 *
        fixedAwayRapidEnvelope J h := by
    dsimp only [w, fixedAwayHermitianIntegerWeight]
    exact norm_fixedAwayScaledHermitianProduct_le_of_both_far
      hδ hδt hh (hfar (v : ℝ) (Or.inr le_rfl)).1
        (hfar (v : ℝ) (Or.inr le_rfl)).2 hJ
  rw [hIntegral] at hsumBound
  unfold fixedAwayProjectedRapidVariationConstant
  simpa only [w] using! hsumBound.trans (by linarith)

theorem norm_projected_fixedAwayHermitianIntegerWeight_le_rapid
    {t δ s a s' a' h : ℝ} {u v n : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (_huv : u ≤ v) (hh : 0 < h)
    (hfar : ∀ x : ℝ, x ≤ (u : ℝ) ∨ (v : ℝ) ≤ x →
      h ≤ |(x - a) / s| ∧ h ≤ |(x - a') / s'|)
    {J : ℕ} (hJ : 0 < J) :
    ‖integerIntervalComplementMultiplier u v
        (fixedAwayHermitianIntegerWeight t δ s a s' a') n‖ ≤
      fixedAwayPVRapidDecayConstant t δ J ^ 2 *
        fixedAwayRapidEnvelope J h := by
  unfold integerIntervalComplementMultiplier
  split_ifs with hn
  · simp only [norm_zero]
    exact mul_nonneg (sq_nonneg _)
      (fixedAwayRapidEnvelope_nonneg J h)
  · have hout : n < u ∨ v < n := by
      push_neg at hn
      omega
    have hxExterior : (n : ℝ) ≤ (u : ℝ) ∨ (v : ℝ) ≤ (n : ℝ) := by
      rcases hout with hn | hn
      · left
        exact_mod_cast hn.le
      · right
        exact_mod_cast hn.le
    exact norm_fixedAwayScaledHermitianProduct_le_of_both_far
      hδ hδt hh (hfar (n : ℝ) hxExterior).1
        (hfar (n : ℝ) hxExterior).2 hJ

def fixedAwayProjectedRapidBVConstant
    (t δ : ℝ) (J : ℕ) : ℝ :=
  fixedAwayPVRapidDecayConstant t δ J ^ 2 +
    fixedAwayProjectedRapidVariationConstant t δ J

theorem fixedAwayProjectedRapidBVConstant_nonneg
    (t δ : ℝ) {J : ℕ} (hJ : 0 < J) :
    0 ≤ fixedAwayProjectedRapidBVConstant t δ J := by
  unfold fixedAwayProjectedRapidBVConstant
  exact add_nonneg (sq_nonneg _)
    (fixedAwayProjectedRapidVariationConstant_nonneg t δ hJ)

/-- Final projected all-integer Hermitian BV--Abel estimate.  This theorem
includes the two projection endpoint jumps and omits the original carrier
jumps because the carriers lie strictly in the deleted interval. -/
theorem norm_tsum_projected_fixedAwayHermitianRamanujanMultiplier_le_rapid
    {t δ s a s' a' h : ℝ} {u v : ℤ} {p p' : ℕ}
    (hδ : 0 < δ) (hδt : δ < t) (hs : 0 < s) (hs' : 0 < s')
    (huv : u ≤ v)
    (hua : (u : ℝ) < a) (hua' : (u : ℝ) < a')
    (hav : a < (v : ℝ)) (ha'v : a' < (v : ℝ))
    (hh : 0 < h)
    (hfar : ∀ x : ℝ, x ≤ (u : ℝ) ∨ (v : ℝ) ≤ x →
      h ≤ |(x - a) / s| ∧ h ≤ |(x - a') / s'|)
    {J : ℕ} (hJ : 0 < J)
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ‖∑' n : ℤ,
        hermitianRamanujanMultiplierTerm
          (integerIntervalComplementMultiplier u v
            (fixedAwayHermitianIntegerWeight t δ s a s' a')) p p' n‖ ≤
      (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ))) *
        (fixedAwayProjectedRapidBVConstant t δ J *
          fixedAwayRapidEnvelope J h) := by
  let w : ℤ → ℂ := fixedAwayHermitianIntegerWeight t δ s a s' a'
  let wp : ℤ → ℂ := integerIntervalComplementMultiplier u v w
  let B : ℝ := fixedAwayPVRapidDecayConstant t δ J ^ 2 *
    fixedAwayRapidEnvelope J h
  let V : ℝ := fixedAwayProjectedRapidVariationConstant t δ J *
    fixedAwayRapidEnvelope J h
  have hw : Summable fun n : ℤ ↦ ‖w n‖ := by
    simpa only [w] using! summable_norm_fixedAwayHermitianIntegerWeight
      (t := t) (δ := δ) (s := s) (a := a) (s' := s') (a' := a')
      hδ hδt hs hs'
  have hwp : Summable fun n : ℤ ↦ ‖wp n‖ := by
    simpa only [wp] using!
      summable_norm_integerIntervalComplementMultiplier u v w hw
  have hwvar : Summable fun n : ℤ ↦ ‖w n - w (n + 1)‖ := by
    simpa only [w] using!
      summable_variation_fixedAwayHermitianIntegerWeight
        (t := t) (δ := δ) (s := s) (a := a) (s' := s') (a' := a')
        hδ hδt hs hs'
  have hwpvar : Summable fun n : ℤ ↦ ‖wp n - wp (n + 1)‖ := by
    simpa only [wp] using!
      summable_variation_integerIntervalComplementMultiplier huv w hwvar
  have hsup : ∀ n : ℤ, ‖wp n‖ ≤ B := by
    intro n
    dsimp only [wp, w, B]
    exact norm_projected_fixedAwayHermitianIntegerWeight_le_rapid
      hδ hδt huv hh hfar hJ
  have hvar : (∑' n : ℤ, ‖wp n - wp (n + 1)‖) ≤ V := by
    dsimp only [wp, w, V]
    exact tsum_variation_projected_fixedAwayHermitianIntegerWeight_le_rapid
      hδ hδt hs hs' huv hua hua' hav ha'v hh hfar hJ
  have hraw := norm_tsum_hermitianRamanujanMultiplierTerm_le
    wp hp hp' hpp' hwp hwpvar hsup hvar
  simpa only [wp, w, B, V, fixedAwayProjectedRapidBVConstant,
    add_mul] using! hraw

end

end Erdos1002
