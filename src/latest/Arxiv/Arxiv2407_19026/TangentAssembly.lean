import Arxiv.Arxiv2407_19026.TangentNumerics

/-!
# Analytic assembly of tangent-round witnesses

The native affine checker proves inequalities between cancellation-free
logarithmic expressions.  This file converts those inequalities into the
three alternatives required by `TangentRoundCertificate`.
-/

noncomputable section

namespace Arxiv2407_19026

lemma optimizationX_le_tangentA_of_log
    {β₀ β₁ z t : ℝ}
    (hβ₁ : 0 ≤ β₁) (hz : 0 < z) (hz1 : z ≤ 1)
    (hlog : tangentXLog β₁ z ≤ tangentALog β₀ t) :
    optimizationX β₁ z ≤
      tangentRegionX (optimizedRamseyExponent β₀)
        (optimizedRamseySlope β₀) t := by
  rw [← tangentA_eq_tangentRegionX,
    ← tangentXCoord_eq_optimizationX hβ₁ hz hz1,
    ← tangentXLog_exp hβ₁ hz.le hz1,
    ← tangentA_exp]
  exact Real.exp_le_exp.mpr hlog

lemma optimizationX_le_tangentB_of_log
    {β₀ β₁ z t : ℝ}
    (hβ₁ : 0 ≤ β₁) (hz : 0 < z) (hz1 : z ≤ 1) (ht : 0 < t)
    (hlog : tangentXLog β₁ z ≤ tangentBLog β₀ t) :
    optimizationX β₁ z ≤
      tangentRegionY (optimizedRamseySlope β₀) t := by
  rw [← tangentB_eq_tangentRegionY ht,
    ← tangentXCoord_eq_optimizationX hβ₁ hz hz1,
    ← tangentXLog_exp hβ₁ hz.le hz1,
    ← tangentBLog_exp ht]
  exact Real.exp_le_exp.mpr hlog

lemma tangentB_le_optimizationX_of_log
    {β₀ β₁ z t : ℝ}
    (hβ₁ : 0 ≤ β₁) (hz : 0 < z) (hz1 : z ≤ 1) (ht : 0 < t)
    (hlog : tangentBLog β₀ t ≤ tangentXLog β₁ z) :
    tangentRegionY (optimizedRamseySlope β₀) t ≤
      optimizationX β₁ z := by
  rw [← tangentB_eq_tangentRegionY ht,
    ← tangentXCoord_eq_optimizationX hβ₁ hz hz1,
    ← tangentBLog_exp ht,
    ← tangentXLog_exp hβ₁ hz.le hz1]
  exact Real.exp_le_exp.mpr hlog

lemma tangentSmallY_eq_tangentB
    {β z : ℝ} :
    z * Real.exp (tangentSmallYLogOverZ β z) =
      tangentB β (tangentSmallT z) := by
  have hc : (0 : ℝ) < 11 / 5 := by norm_num
  unfold tangentSmallYLogOverZ tangentSmallT tangentB
  rw [show
      Real.log (11 / 5 : ℝ) -
          Real.log (1 + 11 / 5 * z) -
          tangentCorrectionSlope β (11 / 5 * z) =
        Real.log (11 / 5 : ℝ) +
          (-Real.log (1 + 11 / 5 * z) -
            tangentCorrectionSlope β (11 / 5 * z)) by ring,
    Real.exp_add, Real.exp_log hc]
  ring

lemma tangentForwardY_eq_tangentB
    {β z t : ℝ} (hz : 0 < z) (ht : 0 < t) :
    z * Real.exp (tangentBLog β t - Real.log z) =
      tangentB β t := by
  rw [Real.exp_sub, tangentBLog_exp ht, Real.exp_log hz]
  field_simp

lemma tangentBackwardY_eq_tangentA
    {β z t : ℝ} (hz : 0 < z) :
    z * Real.exp (tangentALog β t - Real.log z) =
      tangentA β t := by
  rw [Real.exp_sub, tangentA_exp, Real.exp_log hz]
  field_simp

lemma tangentPlateauY_eq
    {β₀ β₁ z t : ℝ}
    (hβ₁ : 0 ≤ β₁) (hz : 0 < z) (hz1 : z ≤ 1) (ht : 0 < t) :
    z * Real.exp
        (tangentALog β₀ t + tangentBLog β₀ t -
          tangentXLog β₁ z - Real.log z) =
      tangentA β₀ t * tangentB β₀ t / tangentXCoord β₁ z := by
  have hX : tangentXCoord β₁ z ≠ 0 := by
    rw [← tangentXLog_exp hβ₁ hz.le hz1]
    exact Real.exp_ne_zero _
  rw [show
      tangentALog β₀ t + tangentBLog β₀ t -
          tangentXLog β₁ z - Real.log z =
        (tangentALog β₀ t + tangentBLog β₀ t) -
          tangentXLog β₁ z - Real.log z by ring,
    Real.exp_sub, Real.exp_sub, Real.exp_add,
    tangentA_exp, tangentBLog_exp ht, tangentXLog_exp hβ₁ hz.le hz1,
    Real.exp_log hz]
  field_simp

lemma tangentSmallBookMargin_to_round
    {β₀ β₁ z : ℝ}
    (hβ₁ : 0 ≤ β₁) (hz : 0 < z) (hz1 : z ≤ 1)
    (hbook : 0 < tangentSmallBookMargin β₀ β₁ z) :
    0 < tangentRoundBookMargin β₁ z
      (optimizationX β₁ z)
      (tangentRegionY (optimizedRamseySlope β₀)
        (tangentSmallT z)) := by
  have ht : 0 < tangentSmallT z := by
    unfold tangentSmallT
    positivity
  rw [tangentSmallBookMargin,
    tangentCleanBookMargin_eq hβ₁ hz hz1,
    tangentSmallY_eq_tangentB,
    tangentB_eq_tangentRegionY ht,
    tangentXCoord_eq_optimizationX hβ₁ hz hz1] at hbook
  exact hbook

lemma tangentForwardBookMargin_to_round
    {β₀ β₁ z t : ℝ}
    (hβ₁ : 0 ≤ β₁) (hz : 0 < z) (hz1 : z ≤ 1) (ht : 0 < t)
    (hbook :
      0 < tangentCleanBookMargin β₁ z
        (tangentBLog β₀ t - Real.log z)) :
    0 < tangentRoundBookMargin β₁ z
      (optimizationX β₁ z)
      (tangentRegionY (optimizedRamseySlope β₀) t) := by
  rw [tangentCleanBookMargin_eq hβ₁ hz hz1,
    tangentForwardY_eq_tangentB hz ht,
    tangentB_eq_tangentRegionY ht,
    tangentXCoord_eq_optimizationX hβ₁ hz hz1] at hbook
  exact hbook

lemma tangentBackwardBookMargin_to_round
    {β₀ β₁ z t : ℝ}
    (hβ₁ : 0 ≤ β₁) (hz : 0 < z) (hz1 : z ≤ 1)
    (hbook :
      0 < tangentCleanBookMargin β₁ z
        (tangentALog β₀ t - Real.log z)) :
    0 < tangentRoundBookMargin β₁ z
      (optimizationX β₁ z)
      (tangentRegionX (optimizedRamseyExponent β₀)
        (optimizedRamseySlope β₀) t) := by
  rw [tangentCleanBookMargin_eq hβ₁ hz hz1,
    tangentBackwardY_eq_tangentA hz,
    tangentA_eq_tangentRegionX,
    tangentXCoord_eq_optimizationX hβ₁ hz hz1] at hbook
  exact hbook

lemma tangentPlateauBookMargin_to_round
    {β₀ β₁ z t : ℝ}
    (hβ₁ : 0 ≤ β₁) (hz : 0 < z) (hz1 : z ≤ 1) (ht : 0 < t)
    (hbook :
      0 < tangentCleanBookMargin β₁ z
        (tangentALog β₀ t + tangentBLog β₀ t -
          tangentXLog β₁ z - Real.log z)) :
    let A :=
      tangentRegionX (optimizedRamseyExponent β₀)
        (optimizedRamseySlope β₀) t
    let B := tangentRegionY (optimizedRamseySlope β₀) t
    let X := optimizationX β₁ z
    0 < tangentRoundBookMargin β₁ z X (A * B / X) := by
  dsimp only
  rw [tangentCleanBookMargin_eq hβ₁ hz hz1,
    tangentPlateauY_eq hβ₁ hz hz1 ht,
    tangentA_eq_tangentRegionX,
    tangentB_eq_tangentRegionY ht,
    tangentXCoord_eq_optimizationX hβ₁ hz hz1] at hbook
  exact hbook

lemma tangentSmall_domain
    {β z : ℝ} (hβ : 0 ≤ β)
    (hz : z ∈ Set.Icc (0 : ℝ) (1 / 10)) :
    0 < 1 - tangentBlue β z ∧
      0 < 1 - optimizationM z ∧
      0 < 1 + z ∧
      0 < 1 + tangentSmallT z := by
  have hz1 : z ≤ 1 := by nlinarith [hz.2]
  constructor
  · exact sub_pos.mpr (tangentBlue_lt_one hβ hz.1 hz1)
  constructor
  · exact sub_pos.mpr (optimizationM_lt_one_of_Icc hz.1 hz1)
  constructor
  · linarith [hz.1]
  · unfold tangentSmallT
    nlinarith [hz.1]

lemma tangentSmallCoord_pos_of_deriv_lower
    {β₀ β₁ : ℝ} (hβ₁ : 0 ≤ β₁)
    (hprime :
      ∀ z ∈ Set.Icc (0 : ℝ) (1 / 10),
        (1 / 20 : ℝ) ≤ tangentSmallCoordLogPrime β₀ β₁ z) :
    ∀ z ∈ Set.Ioc (0 : ℝ) (1 / 10),
      0 < tangentSmallCoordLog β₀ β₁ z := by
  have hderiv :
      ∀ x ∈ Set.Icc (0 : ℝ) (1 / 10),
        HasDerivAt (tangentSmallCoordLog β₀ β₁)
          (tangentSmallCoordLogPrime β₀ β₁ x) x := by
    intro x hx
    obtain ⟨hp, hom, hplus, htplus⟩ :=
      tangentSmall_domain hβ₁ hx
    exact hasDerivAt_tangentSmallCoordLog β₀ β₁
      hp hom hplus.ne' htplus.ne'
  have hcont :
      ContinuousOn (tangentSmallCoordLog β₀ β₁)
        (Set.Icc (0 : ℝ) (1 / 10)) := by
    intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt
  have hmono :
      StrictMonoOn (tangentSmallCoordLog β₀ β₁)
        (Set.Icc (0 : ℝ) (1 / 10)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) (1 / 10) :=
      interior_subset hx
    rw [(hderiv x hx').deriv]
    exact lt_of_lt_of_le (by norm_num) (hprime x hx')
  have hzero : tangentSmallCoordLog β₀ β₁ 0 = 0 := by
    norm_num [tangentSmallCoordLog, tangentSmallT, tangentALog,
      tangentXLog, tangentBlue, optimizationM, tangentCorrectionSlope]
  intro z hz
  rw [← hzero]
  exact hmono (by norm_num) ⟨hz.1.le, hz.2⟩ hz.1

lemma tangentSmallBook_pos_of_bounds
    {β₀ β₁ : ℝ} (hβ₁ : 0 ≤ β₁)
    (hprime :
      ∀ z ∈ Set.Icc (0 : ℝ) (1 / 50),
        (1 / 1000 : ℝ) ≤ tangentSmallBookMarginPrime β₀ β₁ z)
    (hdirect :
      ∀ z ∈ Set.Icc (1 / 50 : ℝ) (1 / 10),
        (1 / 10000 : ℝ) ≤ tangentSmallBookMargin β₀ β₁ z) :
    ∀ z ∈ Set.Ioc (0 : ℝ) (1 / 10),
      0 < tangentSmallBookMargin β₀ β₁ z := by
  have hderiv :
      ∀ x ∈ Set.Icc (0 : ℝ) (1 / 50),
        HasDerivAt (tangentSmallBookMargin β₀ β₁)
          (tangentSmallBookMarginPrime β₀ β₁ x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) (1 / 10) := by
      constructor
      · exact hx.1
      · nlinarith [hx.2]
    obtain ⟨hp, hom, hplus, htplus⟩ :=
      tangentSmall_domain hβ₁ hx'
    exact hasDerivAt_tangentSmallBookMargin β₀ β₁
      hp hom hplus.ne' htplus.ne'
  have hcont :
      ContinuousOn (tangentSmallBookMargin β₀ β₁)
        (Set.Icc (0 : ℝ) (1 / 50)) := by
    intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt
  have hmono :
      StrictMonoOn (tangentSmallBookMargin β₀ β₁)
        (Set.Icc (0 : ℝ) (1 / 50)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) (1 / 50) :=
      interior_subset hx
    rw [(hderiv x hx').deriv]
    exact lt_of_lt_of_le (by norm_num) (hprime x hx')
  have hzero : tangentSmallBookMargin β₀ β₁ 0 = 0 := by
    norm_num [tangentSmallBookMargin, tangentCleanBookMargin,
      tangentSmallYLogOverZ, tangentSmallT, tangentXLog, tangentBlue,
      optimizationM, tangentCorrectionSlope, ramseyCorrection]
  intro z hz
  by_cases hsmall : z ≤ 1 / 50
  · rw [← hzero]
    exact hmono (by norm_num) ⟨hz.1.le, hsmall⟩ hz.1
  · have h := hdirect z ⟨le_of_not_ge hsmall, hz.2⟩
    positivity

/-- Real inequalities needed for one tangent-envelope round.  The cuts are
`0.1`, `zForward`, `zBackward`, `0.6`, and `1`. -/
structure TangentRoundWitnessData
    (β₀ β₁ zForward zBackward : ℝ) where
  forwardT : ℝ → ℝ
  back1T : ℝ → ℝ
  back2T : ℝ → ℝ
  cut_order :
    (1 / 10 : ℝ) ≤ zForward ∧
      zForward ≤ zBackward ∧ zBackward ≤ 3 / 5
  forwardT_mem :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) zForward,
      forwardT z ∈ Set.Ioc (0 : ℝ) 1
  back1T_mem :
    ∀ z ∈ Set.Icc zBackward (3 / 5 : ℝ),
      back1T z ∈ Set.Ioc (0 : ℝ) 1
  back2T_mem :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      back2T z ∈ Set.Ioc (0 : ℝ) 1
  smallCoord :
    ∀ z ∈ Set.Ioc (0 : ℝ) (1 / 10),
      0 < tangentSmallCoordLog β₀ β₁ z
  smallBook :
    ∀ z ∈ Set.Ioc (0 : ℝ) (1 / 10),
      0 < tangentSmallBookMargin β₀ β₁ z
  forwardCoord :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) zForward,
      tangentXLog β₁ z ≤ tangentALog β₀ (forwardT z)
  forwardBook :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) zForward,
      0 < tangentCleanBookMargin β₁ z
        (tangentBLog β₀ (forwardT z) - Real.log z)
  plateauLow :
    ∀ z ∈ Set.Icc zForward zBackward,
      tangentBLog β₀ (99 / 100) ≤ tangentXLog β₁ z
  plateauHigh :
    ∀ z ∈ Set.Icc zForward zBackward,
      tangentXLog β₁ z ≤ tangentALog β₀ (99 / 100)
  plateauBook :
    ∀ z ∈ Set.Icc zForward zBackward,
      0 < tangentCleanBookMargin β₁ z
        (tangentALog β₀ (99 / 100) +
          tangentBLog β₀ (99 / 100) -
          tangentXLog β₁ z - Real.log z)
  back1Coord :
    ∀ z ∈ Set.Icc zBackward (3 / 5 : ℝ),
      tangentXLog β₁ z ≤ tangentBLog β₀ (back1T z)
  back1Book :
    ∀ z ∈ Set.Icc zBackward (3 / 5 : ℝ),
      0 < tangentCleanBookMargin β₁ z
        (tangentALog β₀ (back1T z) - Real.log z)
  back2Coord :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      tangentXLog β₁ z ≤ tangentBLog β₀ (back2T z)
  back2Book :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      0 < tangentCleanBookMargin β₁ z
        (tangentALog β₀ (back2T z) - Real.log z)

theorem TangentRoundWitnessData.toCertificate
    {β₀ β₁ zForward zBackward : ℝ}
    (hβ₁ : 0 ≤ β₁)
    (D : TangentRoundWitnessData β₀ β₁ zForward zBackward) :
    TangentRoundCertificate β₀ β₁ := by
  constructor
  intro z hz
  by_cases hsmall : z ≤ 1 / 10
  · let t := tangentSmallT z
    have ht : t ∈ Set.Ioc (0 : ℝ) 1 := by
      dsimp [t, tangentSmallT]
      constructor
      · nlinarith [hz.1]
      · nlinarith [hz.1]
    refine ⟨t, ht, Or.inl ⟨?_, ?_⟩⟩
    · apply optimizationX_le_tangentA_of_log
        hβ₁ hz.1 hz.2
      simpa [t, tangentSmallCoordLog] using
        (D.smallCoord z ⟨hz.1, hsmall⟩).le
    · exact tangentSmallBookMargin_to_round
        hβ₁ hz.1 hz.2 (D.smallBook z ⟨hz.1, hsmall⟩)
  · have hzForward : (1 / 10 : ℝ) ≤ z := by
      exact le_of_not_ge hsmall
    by_cases hforward : z ≤ zForward
    · let t := D.forwardT z
      have hzI : z ∈ Set.Icc (1 / 10 : ℝ) zForward :=
        ⟨hzForward, hforward⟩
      have ht := D.forwardT_mem z hzI
      refine ⟨t, ht, Or.inl ⟨?_, ?_⟩⟩
      · apply optimizationX_le_tangentA_of_log
          hβ₁ hz.1 hz.2
        exact D.forwardCoord z hzI
      · exact tangentForwardBookMargin_to_round
          hβ₁ hz.1 hz.2 ht.1 (D.forwardBook z hzI)
    · have hzPlateau : zForward ≤ z := le_of_not_ge hforward
      by_cases hplateau : z ≤ zBackward
      · have hzI : z ∈ Set.Icc zForward zBackward :=
          ⟨hzPlateau, hplateau⟩
        have ht : (99 / 100 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
          norm_num
        refine ⟨99 / 100, ht, Or.inr (Or.inr ⟨?_, ?_, ?_⟩)⟩
        · exact tangentB_le_optimizationX_of_log
            hβ₁ hz.1 hz.2 ht.1 (D.plateauLow z hzI)
        · exact optimizationX_le_tangentA_of_log
            hβ₁ hz.1 hz.2 (D.plateauHigh z hzI)
        · exact tangentPlateauBookMargin_to_round
            hβ₁ hz.1 hz.2 ht.1 (D.plateauBook z hzI)
      · have hzBackward : zBackward ≤ z := le_of_not_ge hplateau
        by_cases hback1 : z ≤ 3 / 5
        · let t := D.back1T z
          have hzI : z ∈ Set.Icc zBackward (3 / 5 : ℝ) :=
            ⟨hzBackward, hback1⟩
          have ht := D.back1T_mem z hzI
          refine ⟨t, ht, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
          · exact optimizationX_le_tangentB_of_log
              hβ₁ hz.1 hz.2 ht.1 (D.back1Coord z hzI)
          · exact tangentBackwardBookMargin_to_round
              hβ₁ hz.1 hz.2 (D.back1Book z hzI)
        · let t := D.back2T z
          have hzI : z ∈ Set.Icc (3 / 5 : ℝ) 1 :=
            ⟨le_of_not_ge hback1, hz.2⟩
          have ht := D.back2T_mem z hzI
          refine ⟨t, ht, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
          · exact optimizationX_le_tangentB_of_log
              hβ₁ hz.1 hz.2 ht.1 (D.back2Coord z hzI)
          · exact tangentBackwardBookMargin_to_round
              hβ₁ hz.1 hz.2 (D.back2Book z hzI)

end Arxiv2407_19026
