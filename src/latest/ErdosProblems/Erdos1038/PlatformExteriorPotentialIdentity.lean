import ErdosProblems.Erdos1038.HighKPlatformIntervalFormula
import ErdosProblems.Erdos1038.PlatformPotential

/-!
# The exterior platform formula as a logarithmic potential

The interval checker uses an explicit square-root expression for the
platform exterior function.  Here we identify that expression with the
angular logarithmic potential of the platform reference density.
-/

set_option warningAsError false
set_option maxHeartbeats 800000

open MeasureTheory Set

namespace Erdos1038

noncomputable section

private theorem integral_intervalEquilibrium_log_exterior_left_minimal
    {A B d : ℝ} (hAB : A < B) (hd : d < A) :
    (1 / Real.pi) *
        (∫ theta : ℝ in 0..Real.pi,
          Real.log |d - intervalAngularDistance A B theta|) =
      Real.log (intervalExteriorD0 (A - d) (B - d)) := by
  have hA : 0 < A - d := sub_pos.mpr hd
  have hAB' : A - d < B - d := sub_lt_sub_right hAB d
  have hExt := integral_intervalEquilibrium_log_exterior hA hAB'
  rw [← hExt]
  congr 1
  apply intervalIntegral.integral_congr
  intro theta htheta
  rw [uIcc_of_le Real.pi_pos.le] at htheta
  have hJge : A ≤ intervalAngularDistance A B theta := by
    have hcos : Real.cos theta ≤ 1 := Real.cos_le_one theta
    unfold intervalAngularDistance
    nlinarith
  have htranslate :
      intervalAngularDistance (A - d) (B - d) theta =
        intervalAngularDistance A B theta - d := by
    unfold intervalAngularDistance
    ring
  change Real.log |d - intervalAngularDistance A B theta| =
    Real.log (intervalAngularDistance (A - d) (B - d) theta)
  rw [abs_of_neg (sub_neg.mpr (hd.trans_le hJge)), neg_sub, htranslate]

private theorem integral_intervalEquilibrium_log_exterior_right_minimal
    {A B d : ℝ} (hAB : A < B) (hd : B < d) :
    (1 / Real.pi) *
        (∫ theta : ℝ in 0..Real.pi,
          Real.log |d - intervalAngularDistance A B theta|) =
      Real.log (intervalExteriorD0 (d - B) (d - A)) := by
  have hA : 0 < d - B := sub_pos.mpr hd
  have hAB' : d - B < d - A := sub_lt_sub_left hAB d
  have hExt := integral_intervalEquilibrium_log_exterior hA hAB'
  rw [← hExt]
  congr 1
  calc
    (∫ theta : ℝ in 0..Real.pi,
        Real.log |d - intervalAngularDistance A B theta|) =
        ∫ theta : ℝ in 0..Real.pi,
          Real.log |d - intervalAngularDistance A B (Real.pi - theta)| := by
      symm
      simpa only [sub_self, sub_zero] using!
        (intervalIntegral.integral_comp_sub_left
          (a := 0) (b := Real.pi)
          (fun theta : ℝ ↦
            Real.log |d - intervalAngularDistance A B theta|) Real.pi)
    _ = ∫ theta : ℝ in 0..Real.pi,
        Real.log (intervalAngularDistance (d - B) (d - A) theta) := by
      apply intervalIntegral.integral_congr
      intro theta htheta
      rw [uIcc_of_le Real.pi_pos.le] at htheta
      have hJle : intervalAngularDistance A B (Real.pi - theta) ≤ B := by
        have hcos : Real.cos theta ≤ 1 := Real.cos_le_one theta
        unfold intervalAngularDistance
        rw [Real.cos_pi_sub]
        nlinarith
      have hpos : 0 < d - intervalAngularDistance A B (Real.pi - theta) :=
        sub_pos.mpr (hJle.trans_lt hd)
      have hreflect :
          intervalAngularDistance (d - B) (d - A) theta =
            d - intervalAngularDistance A B (Real.pi - theta) := by
        unfold intervalAngularDistance
        rw [Real.cos_pi_sub]
        ring
      change Real.log |d - intervalAngularDistance A B (Real.pi - theta)| =
        Real.log (intervalAngularDistance (d - B) (d - A) theta)
      rw [abs_of_pos hpos, ← hreflect]

private lemma platformExterior_correction_eq
    {a x : ℝ} (ha : 0 < a) (ha2 : a < 2) (hx : x < a) :
    1 - ((Real.sqrt 2 - Real.sqrt a) /
          (Real.sqrt 2 + Real.sqrt a)) * platformRho a x =
      (Real.sqrt (2 * a) + platformCrossingScale a x - x) /
        (platformCenter a - x + platformCrossingScale a x) := by
  let p : ℝ := Real.sqrt 2
  let q : ℝ := Real.sqrt a
  let S : ℝ := Real.sqrt (2 * a)
  let K : ℝ := platformCrossingScale a x
  have hp : 0 < p := Real.sqrt_pos.2 (by norm_num)
  have hq : 0 < q := Real.sqrt_pos.2 ha
  have hS : 0 < S := Real.sqrt_pos.2 (mul_pos (by norm_num) ha)
  have hK : 0 < K := platformCrossingScale_pos hx ha2
  have hp_sq : p ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hq_sq : q ^ 2 = a := Real.sq_sqrt ha.le
  have hS_eq : S = p * q := by
    dsimp only [S, p, q]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hcenter : 0 < platformCenter a := by
    unfold platformCenter
    linarith
  have hcenterS : 0 < platformCenter a + S := add_pos hcenter hS
  have hz : 0 < platformCenter a - x := by
    have hca : a < platformCenter a := by
      unfold platformCenter
      linarith
    linarith
  have hzK : 0 < platformCenter a - x + K := add_pos hz hK
  have hcross :
      (p - q) * (platformCenter a + S) =
        platformRadius a * (p + q) := by
    rw [hS_eq]
    calc
      (p - q) * (platformCenter a + p * q) =
          (p - q) * ((p ^ 2 + q ^ 2) / 2 + p * q) := by
        rw [hp_sq, hq_sq]
        unfold platformCenter
        ring
      _ = ((p ^ 2 - q ^ 2) / 2) * (p + q) := by ring
      _ = platformRadius a * (p + q) := by
        rw [hp_sq, hq_sq]
        unfold platformRadius
        rfl
  have hqzero :
      (Real.sqrt 2 - Real.sqrt a) / (Real.sqrt 2 + Real.sqrt a) =
        platformRadius a / (platformCenter a + S) := by
    change (p - q) / (p + q) = _
    exact (div_eq_div_iff (ne_of_gt (add_pos hp hq)) hcenterS.ne').2 hcross
  have hcenter_sq :
      platformCenter a ^ 2 - platformRadius a ^ 2 = 2 * a := by
    unfold platformCenter platformRadius
    ring
  have hS_sq : S ^ 2 = 2 * a := by
    dsimp only [S]
    exact Real.sq_sqrt (mul_nonneg (by norm_num) ha.le)
  have hradius_sq :
      platformRadius a ^ 2 =
        (platformCenter a - S) * (platformCenter a + S) := by
    nlinarith
  rw [hqzero, platformRho]
  change 1 -
      (platformRadius a / (platformCenter a + S)) *
        (platformRadius a / (platformCenter a - x + K)) =
    (S + K - x) / (platformCenter a - x + K)
  field_simp [hcenterS.ne', hzK.ne']
  rw [hradius_sq]
  ring

/-- Public form of the stable correction-factor identity.  The high-`k`
bridge uses it to identify the derivative of the continuum reference
potential with the explicit interval-checker expression. -/
theorem platformExteriorCorrection_eq
    {a x : ℝ} (ha : 0 < a) (ha2 : a < 2) (hx : x < a) :
    1 - ((Real.sqrt 2 - Real.sqrt a) /
          (Real.sqrt 2 + Real.sqrt a)) * platformRho a x =
      (Real.sqrt (2 * a) + platformCrossingScale a x - x) /
        (platformCenter a - x + platformCrossingScale a x) :=
  platformExterior_correction_eq ha ha2 hx

private lemma platformExterior_log_balance
    {a x : ℝ} (ha : 0 < a) (ha2 : a < 2)
    (hx : x < a) (hx0 : x ≠ 0) :
    Real.log |x| +
          (1 / Real.pi) *
            (∫ psi : ℝ in 0..Real.pi,
              Real.log |x⁻¹ -
                intervalAngularDistance (1 / 2 : ℝ) a⁻¹ psi|) -
        Real.log (intervalExteriorD0 (1 / 2 : ℝ) a⁻¹) =
      Real.log
          ((platformCenter a - x + platformCrossingScale a x) / 2) +
        2 * Real.log
          (1 - ((Real.sqrt 2 - Real.sqrt a) /
              (Real.sqrt 2 + Real.sqrt a)) * platformRho a x) := by
  let S : ℝ := Real.sqrt (2 * a)
  let K : ℝ := platformCrossingScale a x
  let z : ℝ := platformCenter a - x
  let C : ℝ := 1 - ((Real.sqrt 2 - Real.sqrt a) /
    (Real.sqrt 2 + Real.sqrt a)) * platformRho a x
  let D : ℝ := (z + K) / 2
  have hS : 0 < S := Real.sqrt_pos.2 (mul_pos (by norm_num) ha)
  have hK : 0 < K := platformCrossingScale_pos hx ha2
  have hz : 0 < z := by
    have hca : a < platformCenter a := by
      unfold platformCenter
      linarith
    dsimp only [z]
    linarith
  have hzK : 0 < z + K := add_pos hz hK
  have hD : 0 < D := div_pos hzK (by norm_num)
  have hS_sq : S ^ 2 = 2 * a := by
    dsimp only [S]
    exact Real.sq_sqrt (mul_nonneg (by norm_num) ha.le)
  have hK_sq : K ^ 2 = (a - x) * (2 - x) := by
    dsimp only [K]
    exact platformCrossingScale_sq hx ha2
  have hCeq : C = (S + K - x) / (z + K) := by
    dsimp only [C, S, K, z]
    exact platformExterior_correction_eq ha ha2 hx
  have hCnum : 0 < S + K - x := by
    by_cases hxneg : x < 0
    · linarith
    · have hxpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hxneg) (Ne.symm hx0)
      have hKgt : x < S + K := by
        have hcross : (S + K) ^ 2 - x ^ 2 =
            4 * a - (a + 2) * x + 2 * S * K := by
          nlinarith
        have hright : 0 < 4 * a - (a + 2) * x + 2 * S * K := by
          have hax : 0 < a - x := sub_pos.mpr hx
          nlinarith [mul_pos hax (by norm_num : (0 : ℝ) < 4)]
        nlinarith [sq_nonneg (S + K + x)]
      linarith
  have hC : 0 < C := by
    rw [hCeq]
    exact div_pos hCnum hzK
  have hD0sqrt :
      Real.sqrt ((1 / 2 : ℝ) * a⁻¹) = 1 / S := by
    have honeS : 0 < 1 / S := one_div_pos.mpr hS
    have hsq : (1 / 2 : ℝ) * a⁻¹ = (1 / S) ^ 2 := by
      field_simp [ha.ne', hS.ne']
      nlinarith [hS_sq]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos honeS]
  have hD0 :
      intervalExteriorD0 (1 / 2 : ℝ) a⁻¹ =
        (platformCenter a + S) / (4 * a) := by
    rw [intervalExteriorD0, hD0sqrt]
    change ((1 / 2 : ℝ) + a⁻¹ + 2 * (1 / S)) / 4 =
      (((a + 2) / 2) + S) / (4 * a)
    field_simp [ha.ne', hS.ne']
    nlinarith [hS_sq]
  have hcenterS : 0 < platformCenter a + S := by
    have hc : 0 < platformCenter a := by
      unfold platformCenter
      linarith
    exact add_pos hc hS
  have hD0pos : 0 < intervalExteriorD0 (1 / 2 : ℝ) a⁻¹ := by
    rw [hD0]
    exact div_pos hcenterS (mul_pos (by norm_num) ha)
  have hNfactor :
      4 * a - (a + 2) * x + 2 * S * K =
        (S + K - x) * (S + K + x) := by
    nlinarith
  have hbridge :
      (S + K + x) * (z + K) =
        (S + K - x) * (platformCenter a + S) := by
    dsimp only [z]
    have hc : platformCenter a = (a + 2) / 2 := rfl
    rw [hc]
    nlinarith
  have hCplus : 0 < S + K + x := by
    have hprod : 0 < (S + K + x) * (z + K) := by
      rw [hbridge]
      exact mul_pos hCnum hcenterS
    rcases (mul_pos_iff.mp hprod) with hpos | hneg
    · exact hpos.1
    · linarith [hzK]
  have hNpos : 0 < 4 * a - (a + 2) * x + 2 * S * K := by
    rw [hNfactor]
    exact mul_pos hCnum hCplus
  have hratio (E : ℝ) (hE :
      |x| * E =
        (4 * a - (a + 2) * x + 2 * S * K) / (8 * a)) :
      |x| * E / intervalExteriorD0 (1 / 2 : ℝ) a⁻¹ = D * C ^ 2 := by
    rw [hE, hD0, hCeq]
    dsimp only [D]
    rw [hNfactor]
    field_simp [ha.ne', hcenterS.ne', hzK.ne']
    nlinarith [hbridge]
  have hlogRatio (E : ℝ) (hEpos : 0 < E)
      (hratioE :
        |x| * E / intervalExteriorD0 (1 / 2 : ℝ) a⁻¹ = D * C ^ 2) :
      Real.log |x| + Real.log E -
          Real.log (intervalExteriorD0 (1 / 2 : ℝ) a⁻¹) =
        Real.log D + 2 * Real.log C := by
    rw [← Real.log_mul (abs_ne_zero.mpr hx0) hEpos.ne',
      ← Real.log_div
        (mul_ne_zero (abs_ne_zero.mpr hx0) hEpos.ne') hD0pos.ne',
      hratioE, Real.log_mul hD.ne' (pow_ne_zero 2 hC.ne'), Real.log_pow]
    norm_num
  by_cases hxneg : x < 0
  · have hxinv : x⁻¹ < (1 / 2 : ℝ) := by
      exact (inv_lt_zero'.mpr hxneg).trans (by norm_num)
    have hExt := integral_intervalEquilibrium_log_exterior_left_minimal
      (show (1 / 2 : ℝ) < a⁻¹ by
        rw [one_div, inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) ha]
        exact ha2)
      hxinv
    let E : ℝ := intervalExteriorD0
      ((1 / 2 : ℝ) - x⁻¹) (a⁻¹ - x⁻¹)
    have hEval :
        (1 / Real.pi) *
            (∫ psi : ℝ in 0..Real.pi,
              Real.log |x⁻¹ -
                intervalAngularDistance (1 / 2 : ℝ) a⁻¹ psi|) =
          Real.log E := by
      simpa only [E] using! hExt
    have hsqrtE :
        Real.sqrt (((1 / 2 : ℝ) - x⁻¹) * (a⁻¹ - x⁻¹)) =
          K / (S * (-x)) := by
      have hright : 0 < K / (S * (-x)) :=
        div_pos hK (mul_pos hS (neg_pos.mpr hxneg))
      have hsq :
          ((1 / 2 : ℝ) - x⁻¹) * (a⁻¹ - x⁻¹) =
            (K / (S * (-x))) ^ 2 := by
        field_simp [ha.ne', hx0, hS.ne']
        rw [hS_sq, hK_sq]
        ring
      rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos hright]
    have hE :
        |x| * E =
          (4 * a - (a + 2) * x + 2 * S * K) / (8 * a) := by
      rw [abs_of_neg hxneg]
      dsimp only [E]
      rw [intervalExteriorD0, hsqrtE]
      field_simp [ha.ne', hx0, hS.ne']
      linear_combination -16 * K * hS_sq
    have hratioE := hratio E hE
    have hprodE : 0 < |x| * E := by
      rw [hE]
      exact div_pos hNpos (mul_pos (by norm_num) ha)
    have hEpos : 0 < E :=
      pos_of_mul_pos_right hprodE (abs_nonneg x)
    rw [hEval]
    simpa only [D, C, z, K] using! hlogRatio E hEpos hratioE
  · have hxpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hxneg) (Ne.symm hx0)
    have hxinv : a⁻¹ < x⁻¹ := (inv_lt_inv₀ ha hxpos).mpr hx
    have hExt := integral_intervalEquilibrium_log_exterior_right_minimal
      (show (1 / 2 : ℝ) < a⁻¹ by
        rw [one_div, inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) ha]
        exact ha2)
      hxinv
    let E : ℝ := intervalExteriorD0
      (x⁻¹ - a⁻¹) (x⁻¹ - (1 / 2 : ℝ))
    have hEval :
        (1 / Real.pi) *
            (∫ psi : ℝ in 0..Real.pi,
              Real.log |x⁻¹ -
                intervalAngularDistance (1 / 2 : ℝ) a⁻¹ psi|) =
          Real.log E := by
      simpa only [E] using! hExt
    have hsqrtE :
        Real.sqrt ((x⁻¹ - a⁻¹) * (x⁻¹ - (1 / 2 : ℝ))) =
          K / (S * x) := by
      have hright : 0 < K / (S * x) :=
        div_pos hK (mul_pos hS hxpos)
      have hsq :
          (x⁻¹ - a⁻¹) * (x⁻¹ - (1 / 2 : ℝ)) =
            (K / (S * x)) ^ 2 := by
        field_simp [ha.ne', hx0, hS.ne']
        rw [hS_sq, hK_sq]
        ring
      rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos hright]
    have hE :
        |x| * E =
          (4 * a - (a + 2) * x + 2 * S * K) / (8 * a) := by
      rw [abs_of_pos hxpos]
      dsimp only [E]
      rw [intervalExteriorD0, hsqrtE]
      field_simp [ha.ne', hx0, hS.ne']
      linear_combination -16 * K * hS_sq
    have hratioE := hratio E hE
    have hprodE : 0 < |x| * E := by
      rw [hE]
      exact div_pos hNpos (mul_pos (by norm_num) ha)
    have hEpos : 0 < E :=
      pos_of_mul_pos_right hprodE (abs_nonneg x)
    rw [hEval]
    simpa only [D, C, z, K] using! hlogRatio E hEpos hratioE

private lemma integral_platformExterior_balayage_log
    {a x : ℝ} (ha : 0 < a) (ha2 : a < 2)
    (hx : x < a) (hx0 : x ≠ 0) :
    (1 / Real.pi) *
        (∫ theta : ℝ in 0..Real.pi,
          (Real.sqrt (2 * a) / platformAngularDistance a theta) *
            Real.log (platformAngularDistance a theta - x)) =
      Real.log
          ((platformCenter a - x + platformCrossingScale a x) / 2) +
        2 * Real.log
          (1 - ((Real.sqrt 2 - Real.sqrt a) /
              (Real.sqrt 2 + Real.sqrt a)) * platformRho a x) := by
  let J : ℝ → ℝ := intervalAngularDistance (1 / 2 : ℝ) a⁻¹
  have hJ : (1 / 2 : ℝ) < a⁻¹ := by
    rw [one_div, inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) ha]
    exact ha2
  have hJmem : ∀ psi ∈ Icc (0 : ℝ) Real.pi,
      J psi ∈ Icc (1 / 2 : ℝ) a⁻¹ := by
    intro psi hpsi
    rw [← intervalAngularDistance_image_Icc hJ]
    exact ⟨psi, hpsi, rfl⟩
  have hJpos : ∀ psi ∈ Icc (0 : ℝ) Real.pi, 0 < J psi := by
    intro psi hpsi
    exact (by norm_num : (0 : ℝ) < 1 / 2) |>.trans_le
      (hJmem psi hpsi).1
  have hJinvLower : ∀ psi ∈ Icc (0 : ℝ) Real.pi, a ≤ (J psi)⁻¹ := by
    intro psi hpsi
    have hinv := inv_anti₀ (hJpos psi hpsi) (hJmem psi hpsi).2
    simpa only [inv_inv] using! hinv
  have hneq : ∀ psi ∈ Icc (0 : ℝ) Real.pi,
      x⁻¹ - J psi ≠ 0 := by
    intro psi hpsi heq
    by_cases hxneg : x < 0
    · have hinvneg : x⁻¹ < 0 := inv_lt_zero'.mpr hxneg
      linarith [hJpos psi hpsi]
    · have hxpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hxneg) (Ne.symm hx0)
      have hinv : a⁻¹ < x⁻¹ := (inv_lt_inv₀ ha hxpos).mpr hx
      linarith [(hJmem psi hpsi).2]
  have hJcont : ContinuousOn J (Set.uIcc (0 : ℝ) Real.pi) := by
    unfold J intervalAngularDistance
    fun_prop
  have hEqIntegrable : IntervalIntegrable
      (fun psi : ℝ ↦ Real.log |x⁻¹ - J psi|)
      volume 0 Real.pi := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_const.sub hJcont).abs.log fun psi hpsi ↦ by
      rw [uIcc_of_le Real.pi_pos.le] at hpsi
      exact abs_ne_zero.mpr (hneq psi hpsi)
  have hJIntegrable : IntervalIntegrable
      (fun psi : ℝ ↦ Real.log (J psi)) volume 0 Real.pi := by
    apply ContinuousOn.intervalIntegrable
    exact hJcont.log fun psi hpsi ↦ by
      rw [uIcc_of_le Real.pi_pos.le] at hpsi
      exact (hJpos psi hpsi).ne'
  have hdecomp :
      (∫ psi : ℝ in 0..Real.pi,
          Real.log ((J psi)⁻¹ - x)) =
        ∫ psi : ℝ in 0..Real.pi,
          Real.log |x| + Real.log |x⁻¹ - J psi| - Real.log (J psi) := by
    apply intervalIntegral.integral_congr
    intro psi hpsi
    rw [uIcc_of_le Real.pi_pos.le] at hpsi
    have hJp := hJpos psi hpsi
    have hdiffPos : 0 < (J psi)⁻¹ - x :=
      sub_pos.mpr (hx.trans_le (hJinvLower psi hpsi))
    have hne := hneq psi hpsi
    have hfactor : x - (J psi)⁻¹ =
        x * (J psi - x⁻¹) / J psi := by
      field_simp [hx0, hJp.ne']
    have hsub : J psi - x⁻¹ ≠ 0 :=
      sub_ne_zero.mpr (fun h ↦ hne (sub_eq_zero.mpr h.symm))
    change Real.log ((J psi)⁻¹ - x) =
      Real.log |x| + Real.log |x⁻¹ - J psi| - Real.log (J psi)
    rw [← abs_of_pos hdiffPos, abs_sub_comm, hfactor, abs_div, abs_mul,
      Real.log_div
        (mul_ne_zero (abs_ne_zero.mpr hx0) (abs_ne_zero.mpr hsub))
        (abs_ne_zero.mpr hJp.ne'),
      Real.log_mul (abs_ne_zero.mpr hx0) (abs_ne_zero.mpr hsub),
      abs_of_pos hJp, abs_sub_comm]
  have hExt := integral_intervalEquilibrium_log_exterior
    (show (0 : ℝ) < 1 / 2 by norm_num) hJ
  change (1 / Real.pi) *
      (∫ psi : ℝ in 0..Real.pi, Real.log (J psi)) =
    Real.log (intervalExteriorD0 (1 / 2 : ℝ) a⁻¹) at hExt
  have hInv := integral_platformBalayage_comp_eq_invertedInterval ha ha2
    (fun e ↦ Real.log (e - x))
  change (∫ theta : ℝ in 0..Real.pi,
      (Real.sqrt (2 * a) / platformAngularDistance a theta) *
        Real.log (platformAngularDistance a theta - x)) =
    ∫ psi : ℝ in 0..Real.pi, Real.log ((J psi)⁻¹ - x) at hInv
  have hbalance := platformExterior_log_balance ha ha2 hx hx0
  calc
    (1 / Real.pi) *
        (∫ theta : ℝ in 0..Real.pi,
          (Real.sqrt (2 * a) / platformAngularDistance a theta) *
            Real.log (platformAngularDistance a theta - x)) =
        (1 / Real.pi) *
          (∫ psi : ℝ in 0..Real.pi, Real.log ((J psi)⁻¹ - x)) := by
      rw [hInv]
    _ = (1 / Real.pi) *
        (∫ psi : ℝ in 0..Real.pi,
          Real.log |x| + Real.log |x⁻¹ - J psi| - Real.log (J psi)) := by
      rw [hdecomp]
    _ = (1 / Real.pi) *
        (Real.pi * Real.log |x| +
            (∫ psi : ℝ in 0..Real.pi, Real.log |x⁻¹ - J psi|) -
          ∫ psi : ℝ in 0..Real.pi, Real.log (J psi)) := by
      rw [intervalIntegral.integral_sub
          ((intervalIntegrable_const : IntervalIntegrable
            (fun _ : ℝ ↦ Real.log |x|) volume 0 Real.pi).add hEqIntegrable)
          hJIntegrable,
        intervalIntegral.integral_add intervalIntegrable_const hEqIntegrable,
        intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
    _ = Real.log |x| +
          (1 / Real.pi) *
            (∫ psi : ℝ in 0..Real.pi, Real.log |x⁻¹ - J psi|) -
        (1 / Real.pi) *
          (∫ psi : ℝ in 0..Real.pi, Real.log (J psi)) := by
      field_simp [Real.pi_ne_zero]
    _ = Real.log |x| +
          (1 / Real.pi) *
            (∫ psi : ℝ in 0..Real.pi, Real.log |x⁻¹ - J psi|) -
        Real.log (intervalExteriorD0 (1 / 2 : ℝ) a⁻¹) := by
      rw [hExt]
    _ = Real.log
          ((platformCenter a - x + platformCrossingScale a x) / 2) +
        2 * Real.log
          (1 - ((Real.sqrt 2 - Real.sqrt a) /
              (Real.sqrt 2 + Real.sqrt a)) * platformRho a x) := by
      simpa only [J] using! hbalance

/-- The explicit exterior function used by the high-`k` interval checker is
exactly the logarithmic potential of the platform angular reference density. -/
theorem platformExteriorW_eq_angularPotential
    {k a x : ℝ} (ha : 0 < a) (ha2 : a < 2)
    (hx : x < a) (hx0 : x ≠ 0) :
    platformExteriorW k a x =
      k * Real.log |x| +
        (1 / Real.pi) *
          ∫ theta : ℝ in 0..Real.pi,
            Real.log (platformAngularDistance a theta - x) *
              platformAngularDensity k a theta := by
  let F : ℝ → ℝ := fun theta ↦
    Real.log (platformAngularDistance a theta - x)
  let W : ℝ → ℝ := fun theta ↦
    (Real.sqrt (2 * a) / platformAngularDistance a theta) * F theta
  have hdistancePos : ∀ theta ∈ Set.uIcc (0 : ℝ) Real.pi,
      0 < platformAngularDistance a theta - x := by
    intro theta htheta
    rw [uIcc_of_le Real.pi_pos.le] at htheta
    exact sub_pos.mpr (hx.trans_le
      (platformAngularDistance_mem_Icc ha2.le htheta).1)
  have hF : IntervalIntegrable F volume 0 Real.pi := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.log
    · try dsimp only [F]
      unfold platformAngularDistance
      fun_prop
    · intro theta htheta
      exact (hdistancePos theta htheta).ne'
  have hweightContinuous : ContinuousOn
      (fun theta : ℝ ↦
        Real.sqrt (2 * a) / platformAngularDistance a theta)
      (Set.uIcc (0 : ℝ) Real.pi) := by
    apply continuousOn_const.div
    · unfold platformAngularDistance
      fun_prop
    · intro theta htheta
      rw [uIcc_of_le Real.pi_pos.le] at htheta
      exact (platformAngularDistance_pos ha ha2.le htheta).ne'
  have hW : IntervalIntegrable W volume 0 Real.pi := by
    simpa only [W] using! hF.continuousOn_mul hweightContinuous
  have hEqBase := integral_intervalEquilibrium_log_exterior
    (sub_pos.mpr hx) (sub_lt_sub_right ha2 x)
  have htranslate : ∀ theta : ℝ,
      intervalAngularDistance (a - x) (2 - x) theta =
        platformAngularDistance a theta - x := by
    intro theta
    unfold intervalAngularDistance platformAngularDistance
      platformCenter platformRadius
    ring
  have hD : intervalExteriorD0 (a - x) (2 - x) =
      (platformCenter a - x + platformCrossingScale a x) / 2 := by
    unfold intervalExteriorD0 platformCrossingScale platformCenter
    ring
  have hEq :
      (1 / Real.pi) * (∫ theta : ℝ in 0..Real.pi, F theta) =
        Real.log
          ((platformCenter a - x + platformCrossingScale a x) / 2) := by
    change (1 / Real.pi) *
        (∫ theta : ℝ in 0..Real.pi,
          Real.log (platformAngularDistance a theta - x)) = _
    rw [← hD]
    simpa only [htranslate] using! hEqBase
  have hBal := integral_platformExterior_balayage_log ha ha2 hx hx0
  change (1 / Real.pi) * (∫ theta : ℝ in 0..Real.pi, W theta) =
      Real.log
          ((platformCenter a - x + platformCrossingScale a x) / 2) +
        2 * Real.log
          (1 - ((Real.sqrt 2 - Real.sqrt a) /
              (Real.sqrt 2 + Real.sqrt a)) * platformRho a x) at hBal
  have hDensity :
      (fun theta : ℝ ↦ F theta * platformAngularDensity k a theta) =
        fun theta ↦ (k + 1) * F theta - k * W theta := by
    funext theta
    simp only [F, W, platformAngularDensity, platformDensityCoefficient]
    ring
  have hsplit :
      (∫ theta : ℝ in 0..Real.pi,
          F theta * platformAngularDensity k a theta) =
        (k + 1) * (∫ theta : ℝ in 0..Real.pi, F theta) -
          k * (∫ theta : ℝ in 0..Real.pi, W theta) := by
    rw [hDensity,
      intervalIntegral.integral_sub (hF.const_mul (k + 1)) (hW.const_mul k),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [platformExteriorW_eq]
  change k * Real.log |x| +
          Real.log
            ((platformCenter a - x + platformCrossingScale a x) / 2) -
        2 * k * Real.log
          (1 - ((Real.sqrt 2 - Real.sqrt a) /
              (Real.sqrt 2 + Real.sqrt a)) * platformRho a x) =
      k * Real.log |x| +
        (1 / Real.pi) *
          (∫ theta : ℝ in 0..Real.pi,
            F theta * platformAngularDensity k a theta)
  rw [hsplit]
  calc
    k * Real.log |x| +
          Real.log
            ((platformCenter a - x + platformCrossingScale a x) / 2) -
        2 * k * Real.log
          (1 - ((Real.sqrt 2 - Real.sqrt a) /
              (Real.sqrt 2 + Real.sqrt a)) * platformRho a x) =
        k * Real.log |x| +
          (k + 1) *
            Real.log
              ((platformCenter a - x + platformCrossingScale a x) / 2) -
          k *
            (Real.log
                ((platformCenter a - x + platformCrossingScale a x) / 2) +
              2 * Real.log
                (1 - ((Real.sqrt 2 - Real.sqrt a) /
                    (Real.sqrt 2 + Real.sqrt a)) * platformRho a x)) := by
      ring
    _ = k * Real.log |x| +
          (k + 1) * ((1 / Real.pi) *
            (∫ theta : ℝ in 0..Real.pi, F theta)) -
          k * ((1 / Real.pi) *
            (∫ theta : ℝ in 0..Real.pi, W theta)) := by
      rw [hEq, hBal]
    _ = k * Real.log |x| +
        (1 / Real.pi) *
          ((k + 1) * (∫ theta : ℝ in 0..Real.pi, F theta) -
            k * (∫ theta : ℝ in 0..Real.pi, W theta)) := by ring

end

end Erdos1038
