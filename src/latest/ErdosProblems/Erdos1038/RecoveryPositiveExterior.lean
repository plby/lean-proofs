import ErdosProblems.Erdos1038.RecoveryPositivePointwise

/-!
# Exterior formulae for positive-buffer recovery

This file evaluates the zero-platform positive-buffer potential off its
continuous support and identifies its two crossings with the scalar
`exteriorFunction` roots.
-/

open scoped ENNReal Real
open Filter MeasureTheory Set Topology

namespace Erdos1038

noncomputable section

/-- The equilibrium potential of `[A,B]` at a point strictly to its left,
written as the exterior-at-zero formula for the translated interval. -/
theorem integral_intervalEquilibrium_log_exterior_left
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
  have hcos : Real.cos theta ≤ 1 := Real.cos_le_one theta
  have hJge : A ≤ intervalAngularDistance A B theta := by
    unfold intervalAngularDistance
    nlinarith
  have hpos : 0 < intervalAngularDistance A B theta - d :=
    sub_pos.mpr (hd.trans_le hJge)
  have htranslate :
      intervalAngularDistance (A - d) (B - d) theta =
        intervalAngularDistance A B theta - d := by
    unfold intervalAngularDistance
    ring
  change Real.log |d - intervalAngularDistance A B theta| =
    Real.log (intervalAngularDistance (A - d) (B - d) theta)
  rw [abs_of_neg (sub_neg.mpr (hd.trans_le hJge)), neg_sub, htranslate]

/-- The analogous exterior formula for a point strictly to the right of
`[A,B]`. -/
theorem integral_intervalEquilibrium_log_exterior_right
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
      have hcosUpper : Real.cos theta ≤ 1 := Real.cos_le_one theta
      have hJle : intervalAngularDistance A B (Real.pi - theta) ≤ B := by
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

/-- Joukowski distance coordinate on the component to the left of the
continuous one-cut support.  The support endpoint is `u = 1`, the endpoint
atom is `u = q⁻¹`, and the far-left component has `u > q⁻¹`. -/
def oneCutExteriorDistance (q u : ℝ) : ℝ :=
  H q * (q + q⁻¹ - u - u⁻¹)

theorem positiveBufferDistanceLeft_sub_oneCutExteriorDistance
    {q u : ℝ} (hq : q ≠ 0) (hqNeg : q ≠ -1) (hu : u ≠ 0) :
    positiveBufferDistanceLeft (s q) - oneCutExteriorDistance q u =
      H q * (u - 1) ^ 2 / u := by
  have hden : 1 + q ≠ 0 := by
    intro h
    apply hqNeg
    linarith
  have hpoly : 1 + q * 2 + q ^ 2 ≠ 0 := by
    rw [show 1 + q * 2 + q ^ 2 = (1 + q) ^ 2 by ring]
    exact pow_ne_zero 2 hden
  rw [positiveBufferDistanceLeft, oneCutExteriorDistance, s, H]
  field_simp [hq, hu, hden, hpoly]
  ring

theorem two_sub_oneCutExteriorDistance
    {q u : ℝ} (hq : q ≠ 0) (hqNeg : q ≠ -1) (hu : u ≠ 0) :
    2 - oneCutExteriorDistance q u =
      H q * (u + 1) ^ 2 / u := by
  have hden : 1 + q ≠ 0 := by
    intro h
    apply hqNeg
    linarith
  have hpoly : 1 + q * 2 + q ^ 2 ≠ 0 := by
    rw [show 1 + q * 2 + q ^ 2 = (1 + q) ^ 2 by ring]
    exact pow_ne_zero 2 hden
  rw [oneCutExteriorDistance, H]
  field_simp [hq, hu, hden, hpoly]
  ring

theorem intervalExteriorD0_oneCutExteriorDistance
    {q u : ℝ} (hq : 0 < q) (hu : 1 < u) :
    intervalExteriorD0
        (positiveBufferDistanceLeft (s q) - oneCutExteriorDistance q u)
        (2 - oneCutExteriorDistance q u) =
      H q * u := by
  have hH : 0 < H q := H_pos hq
  have hu0 : 0 < u := (by norm_num : (0 : ℝ) < 1).trans hu
  have hleft := positiveBufferDistanceLeft_sub_oneCutExteriorDistance
    hq.ne' (by linarith) hu0.ne'
  have hright := two_sub_oneCutExteriorDistance hq.ne' (by linarith) hu0.ne'
  have hsqrt : Real.sqrt
      ((positiveBufferDistanceLeft (s q) - oneCutExteriorDistance q u) *
        (2 - oneCutExteriorDistance q u)) =
      H q * (u ^ 2 - 1) / u := by
    rw [hleft, hright]
    have htarget : 0 < H q * (u ^ 2 - 1) / u := by
      exact div_pos (mul_pos hH (by nlinarith)) hu0
    rw [show
      (H q * (u - 1) ^ 2 / u) * (H q * (u + 1) ^ 2 / u) =
        (H q * (u ^ 2 - 1) / u) ^ 2 by
          field_simp [hu0.ne']
          ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos htarget]
  rw [intervalExteriorD0, hsqrt, hleft, hright]
  field_simp [hu0.ne']
  ring

/-- The equilibrium part of the platform potential at a one-cut exterior
coordinate is `log (H(q)u)`. -/
theorem integral_platformEquilibrium_log_oneCutExteriorDistance
    {q u : ℝ} (hq : q ∈ Ioo (0 : ℝ) qCeiling) (hu : 1 < u) :
    (1 / Real.pi) *
        (∫ theta : ℝ in 0..Real.pi,
          Real.log |oneCutExteriorDistance q u -
            platformAngularDistance
              (positiveBufferDistanceLeft (s q)) theta|) =
      Real.log (H q * u) := by
  have hs := s_mem_Ioo_of_mem_Ioo hq
  have hdistLeft : oneCutExteriorDistance q u <
      positiveBufferDistanceLeft (s q) := by
    rw [← sub_pos]
    rw [positiveBufferDistanceLeft_sub_oneCutExteriorDistance
      hq.1.ne' (by linarith [hq.1])
      ((by norm_num : (0 : ℝ) < 1).trans hu).ne']
    exact div_pos
      (mul_pos (H_pos hq.1) (sq_pos_of_pos (sub_pos.mpr hu)))
      ((by norm_num : (0 : ℝ) < 1).trans hu)
  have hAB : positiveBufferDistanceLeft (s q) < 2 :=
    positiveBufferDistanceLeft_lt_two hs.1 hs.2
  have h := integral_intervalEquilibrium_log_exterior_left hAB hdistLeft
  rw [← intervalExteriorD0_oneCutExteriorDistance hq.1 hu]
  simpa only [platformAngularDistance_eq_intervalAngularDistance] using! h

/-- Off the platform support, inversion expresses the balayage potential as
the equilibrium potential of the inverted interval. -/
theorem integral_platformBalayage_log_exterior_decomp
    {a d : ℝ} (ha : 0 < a) (ha2 : a < 2)
    (hdleft : d < a) (hdzero : d ≠ 0) :
    (1 / Real.pi) *
        (∫ theta : ℝ in 0..Real.pi,
          (Real.sqrt (2 * a) / platformAngularDistance a theta) *
            Real.log |d - platformAngularDistance a theta|) =
      Real.log |d| +
        (1 / Real.pi) *
          (∫ psi : ℝ in 0..Real.pi,
            Real.log |d⁻¹ -
              intervalAngularDistance (1 / 2 : ℝ) a⁻¹ psi|) -
        Real.log (intervalExteriorD0 (1 / 2 : ℝ) a⁻¹) := by
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
    exact (by norm_num : (0 : ℝ) < 1 / 2) |>.trans_le (hJmem psi hpsi).1
  have hneq : ∀ psi ∈ Icc (0 : ℝ) Real.pi, d⁻¹ - J psi ≠ 0 := by
    intro psi hpsi heq
    have hmem := hJmem psi hpsi
    by_cases hdneg : d < 0
    · have hinvneg : d⁻¹ < 0 := inv_lt_zero'.mpr hdneg
      linarith [hJpos psi hpsi]
    · have hdpos : 0 < d := lt_of_le_of_ne (le_of_not_gt hdneg) (Ne.symm hdzero)
      have hinv : a⁻¹ < d⁻¹ := (inv_lt_inv₀ ha hdpos).mpr hdleft
      linarith [hmem.2]
  have hdecomp :
      (∫ psi : ℝ in 0..Real.pi,
          Real.log |d - (J psi)⁻¹|) =
        ∫ psi : ℝ in 0..Real.pi,
          Real.log |d| + Real.log |d⁻¹ - J psi| - Real.log (J psi) := by
    apply intervalIntegral.integral_congr
    intro psi hpsi
    rw [uIcc_of_le Real.pi_pos.le] at hpsi
    have hJp := hJpos psi hpsi
    have hne := hneq psi hpsi
    have hfactor : d - (J psi)⁻¹ =
        d * (J psi - d⁻¹) / J psi := by
      field_simp [hdzero, hJp.ne']
    have hsub : J psi - d⁻¹ ≠ 0 :=
      sub_ne_zero.mpr (fun h ↦ hne (sub_eq_zero.mpr h.symm))
    change Real.log |d - (J psi)⁻¹| =
      Real.log |d| + Real.log |d⁻¹ - J psi| - Real.log (J psi)
    rw [hfactor, abs_div, abs_mul,
      Real.log_div
        (mul_ne_zero (abs_ne_zero.mpr hdzero) (abs_ne_zero.mpr hsub))
        (abs_ne_zero.mpr hJp.ne'),
      Real.log_mul (abs_ne_zero.mpr hdzero) (abs_ne_zero.mpr hsub),
      abs_of_pos hJp, abs_sub_comm]
  have hEqIntegrable : IntervalIntegrable
      (fun psi : ℝ ↦ Real.log |d⁻¹ - J psi|)
      volume 0 Real.pi := by
    have han : AnalyticOnNhd ℝ (fun psi ↦ d⁻¹ - J psi) Set.univ :=
      fun _ _ ↦ by
        dsimp only [J, intervalAngularDistance]
        fun_prop
    have hmer : MeromorphicOn (fun psi ↦ d⁻¹ - J psi)
        (Set.uIcc 0 Real.pi) :=
      fun x _hx ↦ han.meromorphicOn x (Set.mem_univ x)
    simpa only [Real.norm_eq_abs] using!
      MeromorphicOn.intervalIntegrable_log_norm hmer
  have hJIntegrable : IntervalIntegrable
      (fun psi : ℝ ↦ Real.log (J psi)) volume 0 Real.pi := by
    apply ContinuousOn.intervalIntegrable
    have hJcont : ContinuousOn J (Set.uIcc 0 Real.pi) := by
      unfold J intervalAngularDistance
      fun_prop
    exact hJcont.log (fun psi hpsi ↦ by
      rw [uIcc_of_le Real.pi_pos.le] at hpsi
      exact (hJpos psi hpsi).ne')
  have hExt := integral_intervalEquilibrium_log_exterior
    (show (0 : ℝ) < 1 / 2 by norm_num) hJ
  change (1 / Real.pi) *
      (∫ psi : ℝ in 0..Real.pi, Real.log (J psi)) =
    Real.log (intervalExteriorD0 (1 / 2 : ℝ) a⁻¹) at hExt
  have hInv := integral_platformBalayage_comp_eq_invertedInterval ha ha2
    (fun e ↦ Real.log |d - e|)
  change (∫ theta : ℝ in 0..Real.pi,
      (Real.sqrt (2 * a) / platformAngularDistance a theta) *
        Real.log |d - platformAngularDistance a theta|) =
    ∫ psi : ℝ in 0..Real.pi,
      Real.log |d - (J psi)⁻¹| at hInv
  rw [hInv, hdecomp,
    intervalIntegral.integral_sub
      ((intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ ↦ Real.log |d|) volume 0 Real.pi).add hEqIntegrable)
      hJIntegrable,
    intervalIntegral.integral_add intervalIntegrable_const hEqIntegrable,
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  let IE : ℝ := ∫ psi : ℝ in 0..Real.pi,
    Real.log |d⁻¹ - J psi|
  let IJ : ℝ := ∫ psi : ℝ in 0..Real.pi, Real.log (J psi)
  change (1 / Real.pi) * (Real.pi * Real.log |d| + IE - IJ) =
    Real.log |d| + (1 / Real.pi) * IE -
      Real.log (intervalExteriorD0 (1 / 2 : ℝ) a⁻¹)
  change (1 / Real.pi) * IJ =
    Real.log (intervalExteriorD0 (1 / 2 : ℝ) a⁻¹) at hExt
  rw [← hExt]
  field_simp [Real.pi_ne_zero]

theorem oneCutExteriorDistance_factor
    {q u : ℝ} (hq : q ≠ 0) (hqNeg : q ≠ -1) (hu : u ≠ 0) :
    oneCutExteriorDistance q u =
      H q * (u - q) * (1 - q * u) / (q * u) := by
  have hden : 1 + q ≠ 0 := by
    intro h
    apply hqNeg
    linarith
  have hpoly : 1 + q * 2 + q ^ 2 ≠ 0 := by
    rw [show 1 + q * 2 + q ^ 2 = (1 + q) ^ 2 by ring]
    exact pow_ne_zero 2 hden
  rw [oneCutExteriorDistance, H]
  field_simp [hq, hu, hden, hpoly]
  ring

theorem intervalExteriorD0_inverted_positiveBufferDistanceLeft
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) qCeiling) :
    intervalExteriorD0 (1 / 2 : ℝ)
        (positiveBufferDistanceLeft (s q))⁻¹ =
      1 / (2 * (1 - q) ^ 2) := by
  have hq1 : q < 1 := mem_Ioo_zero_qCeiling_imp_lt_one hq
  have hden : 1 + q ≠ 0 := ne_of_gt (by linarith [hq.1])
  have hsubPos : 0 < 1 - q := sub_pos.mpr hq1
  have hsub : 1 - q ≠ 0 := by linarith
  have hratio : 0 < (1 + q) / (2 * (1 - q)) :=
    div_pos (by linarith [hq.1]) (mul_pos (by norm_num) hsubPos)
  have hprod :
      (1 / 2 : ℝ) * (positiveBufferDistanceLeft (s q))⁻¹ =
        ((1 + q) / (2 * (1 - q))) ^ 2 := by
    rw [positiveBufferDistanceLeft, s]
    field_simp [hden, hsub]
  rw [intervalExteriorD0, hprod, Real.sqrt_sq_eq_abs,
    abs_of_pos hratio, positiveBufferDistanceLeft, s]
  field_simp [hden, hsub]
  ring

/-- Exterior value for the inverted equilibrium interval on the gap side
of the endpoint atom (`1 < u < q⁻¹`). -/
theorem intervalExteriorD0_inverted_oneCut_inner
    {q u : ℝ} (hq : q ∈ Ioo (0 : ℝ) qCeiling)
    (hu : 1 < u) (huq : u < q⁻¹) :
    intervalExteriorD0
        ((oneCutExteriorDistance q u)⁻¹ -
          (positiveBufferDistanceLeft (s q))⁻¹)
        ((oneCutExteriorDistance q u)⁻¹ - (1 / 2 : ℝ)) =
      q * (u - q) /
        (2 * (1 - q) ^ 2 * (1 - q * u)) := by
  have hq1 : q < 1 := mem_Ioo_zero_qCeiling_imp_lt_one hq
  have hu0 : 0 < u := (by norm_num : (0 : ℝ) < 1).trans hu
  have huqsub : 0 < u - q := sub_pos.mpr (hq1.trans hu)
  have h1qu : 0 < 1 - q * u := by
    have hmul := mul_lt_mul_of_pos_left huq hq.1
    rw [mul_inv_cancel₀ hq.1.ne'] at hmul
    linarith
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have h1pq : 0 < 1 + q := by linarith [hq.1]
  have hH : 0 < H q := H_pos hq.1
  have hdFactor := oneCutExteriorDistance_factor hq.1.ne'
    (by linarith [hq.1]) hu0.ne'
  have hdpos : 0 < oneCutExteriorDistance q u := by
    rw [hdFactor]
    exact div_pos (mul_pos (mul_pos hH huqsub) h1qu)
      (mul_pos hq.1 hu0)
  let T : ℝ :=
    q * (1 + q) * (u ^ 2 - 1) /
      (2 * (1 - q) * (u - q) * (1 - q * u))
  have hT : 0 < T := by
    dsimp only [T]
    exact div_pos
      (mul_pos (mul_pos hq.1 h1pq) (by nlinarith : 0 < u ^ 2 - 1))
      (mul_pos (mul_pos (mul_pos (by norm_num) h1q) huqsub) h1qu)
  have hsq :
      ((oneCutExteriorDistance q u)⁻¹ -
          (positiveBufferDistanceLeft (s q))⁻¹) *
        ((oneCutExteriorDistance q u)⁻¹ - (1 / 2 : ℝ)) =
      T ^ 2 := by
    rw [hdFactor, H, positiveBufferDistanceLeft, s]
    dsimp only [T]
    field_simp [hq.1.ne', hu0.ne', h1qu.ne', huqsub.ne', h1q.ne', h1pq.ne']
    ring
  have hsqrt : Real.sqrt
      (((oneCutExteriorDistance q u)⁻¹ -
          (positiveBufferDistanceLeft (s q))⁻¹) *
        ((oneCutExteriorDistance q u)⁻¹ - (1 / 2 : ℝ))) = T := by
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos hT]
  rw [intervalExteriorD0, hsqrt, hdFactor, H,
    positiveBufferDistanceLeft, s]
  dsimp only [T]
  field_simp [hq.1.ne', hu0.ne', h1qu.ne', huqsub.ne', h1q.ne', h1pq.ne']
  ring

/-- Exterior value for the inverted equilibrium interval on the far-left
side of the endpoint atom (`q⁻¹ < u`). -/
theorem intervalExteriorD0_inverted_oneCut_outer
    {q u : ℝ} (hq : q ∈ Ioo (0 : ℝ) qCeiling)
    (huq : q⁻¹ < u) :
    intervalExteriorD0
        ((1 / 2 : ℝ) - (oneCutExteriorDistance q u)⁻¹)
        ((positiveBufferDistanceLeft (s q))⁻¹ -
          (oneCutExteriorDistance q u)⁻¹) =
      q * (u - q) /
        (2 * (1 - q) ^ 2 * (q * u - 1)) := by
  have hq1 : q < 1 := mem_Ioo_zero_qCeiling_imp_lt_one hq
  have hu : 1 < u := (one_lt_inv_q hq.1 hq1).trans huq
  have hu0 : 0 < u := (by norm_num : (0 : ℝ) < 1).trans hu
  have huqsub : 0 < u - q := sub_pos.mpr (hq1.trans hu)
  have hqu : 0 < q * u - 1 := by
    have hmul := mul_lt_mul_of_pos_left huq hq.1
    rw [mul_inv_cancel₀ hq.1.ne'] at hmul
    linarith
  have h1quNe : 1 - q * u ≠ 0 := by linarith [hqu]
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have h1pq : 0 < 1 + q := by linarith [hq.1]
  have hH : 0 < H q := H_pos hq.1
  have hdFactor := oneCutExteriorDistance_factor hq.1.ne'
    (by linarith [hq.1]) hu0.ne'
  have hdneg : oneCutExteriorDistance q u < 0 := by
    rw [hdFactor]
    have hneg : 1 - q * u < 0 := by linarith [hqu]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (mul_pos hH huqsub) hneg)
      (mul_pos hq.1 hu0)
  let T : ℝ :=
    q * (1 + q) * (u ^ 2 - 1) /
      (2 * (1 - q) * (u - q) * (q * u - 1))
  have hT : 0 < T := by
    dsimp only [T]
    exact div_pos
      (mul_pos (mul_pos hq.1 h1pq) (by nlinarith : 0 < u ^ 2 - 1))
      (mul_pos (mul_pos (mul_pos (by norm_num) h1q) huqsub) hqu)
  have hsq :
      ((1 / 2 : ℝ) - (oneCutExteriorDistance q u)⁻¹) *
        ((positiveBufferDistanceLeft (s q))⁻¹ -
          (oneCutExteriorDistance q u)⁻¹) =
      T ^ 2 := by
    rw [hdFactor, H, positiveBufferDistanceLeft, s]
    dsimp only [T]
    field_simp [hq.1.ne', hu0.ne', hqu.ne', h1quNe, huqsub.ne',
      h1q.ne', h1pq.ne']
    ring
  have hsqrt : Real.sqrt
      (((1 / 2 : ℝ) - (oneCutExteriorDistance q u)⁻¹) *
        ((positiveBufferDistanceLeft (s q))⁻¹ -
          (oneCutExteriorDistance q u)⁻¹)) = T := by
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos hT]
  rw [intervalExteriorD0, hsqrt, hdFactor, H,
    positiveBufferDistanceLeft, s]
  dsimp only [T]
  field_simp [hq.1.ne', hu0.ne', hqu.ne', h1quNe, huqsub.ne',
    h1q.ne', h1pq.ne']
  ring

/-- The balayage part of the platform potential in the gap-side
Joukowski coordinate. -/
theorem integral_platformBalayage_log_oneCut_inner
    {q u : ℝ} (hq : q ∈ Ioo (0 : ℝ) qCeiling)
    (hu : 1 < u) (huq : u < q⁻¹) :
    (1 / Real.pi) *
        (∫ theta : ℝ in 0..Real.pi,
          (Real.sqrt (2 * positiveBufferDistanceLeft (s q)) /
              platformAngularDistance
                (positiveBufferDistanceLeft (s q)) theta) *
            Real.log |oneCutExteriorDistance q u -
              platformAngularDistance
                (positiveBufferDistanceLeft (s q)) theta|) =
      Real.log (H q * (u - q) ^ 2 / u) := by
  have hq1 : q < 1 := mem_Ioo_zero_qCeiling_imp_lt_one hq
  have hs := s_mem_Ioo_of_mem_Ioo hq
  have ha : 0 < positiveBufferDistanceLeft (s q) :=
    positiveBufferDistanceLeft_pos hs.1
  have ha2 : positiveBufferDistanceLeft (s q) < 2 :=
    positiveBufferDistanceLeft_lt_two hs.1 hs.2
  have hu0 : 0 < u := (by norm_num : (0 : ℝ) < 1).trans hu
  have huqsub : 0 < u - q := sub_pos.mpr (hq1.trans hu)
  have h1qu : 0 < 1 - q * u := by
    have hmul := mul_lt_mul_of_pos_left huq hq.1
    rw [mul_inv_cancel₀ hq.1.ne'] at hmul
    linarith
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have hdFactor := oneCutExteriorDistance_factor hq.1.ne'
    (by linarith [hq.1]) hu0.ne'
  have hH : 0 < H q := H_pos hq.1
  have hdpos : 0 < oneCutExteriorDistance q u := by
    rw [hdFactor]
    exact div_pos (mul_pos (mul_pos hH huqsub) h1qu)
      (mul_pos hq.1 hu0)
  have hdleft : oneCutExteriorDistance q u <
      positiveBufferDistanceLeft (s q) := by
    rw [← sub_pos,
      positiveBufferDistanceLeft_sub_oneCutExteriorDistance
        hq.1.ne' (by linarith [hq.1]) hu0.ne']
    exact div_pos (mul_pos hH (sq_pos_of_pos (sub_pos.mpr hu))) hu0
  have hJ : (1 / 2 : ℝ) < (positiveBufferDistanceLeft (s q))⁻¹ := by
    rw [one_div, inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) ha]
    exact ha2
  have hwinv : (positiveBufferDistanceLeft (s q))⁻¹ <
      (oneCutExteriorDistance q u)⁻¹ :=
    (inv_lt_inv₀ ha hdpos).mpr hdleft
  have hEq := integral_intervalEquilibrium_log_exterior_right hJ hwinv
  have hEq' :
      (1 / Real.pi) *
          (∫ psi : ℝ in 0..Real.pi,
            Real.log |(oneCutExteriorDistance q u)⁻¹ -
              intervalAngularDistance (1 / 2 : ℝ)
                (positiveBufferDistanceLeft (s q))⁻¹ psi|) =
        Real.log
          (q * (u - q) /
            (2 * (1 - q) ^ 2 * (1 - q * u))) := by
    rw [intervalExteriorD0_inverted_oneCut_inner hq hu huq] at hEq
    exact hEq
  have hdecomp := integral_platformBalayage_log_exterior_decomp
    ha ha2 hdleft hdpos.ne'
  rw [hEq', intervalExteriorD0_inverted_positiveBufferDistanceLeft hq]
    at hdecomp
  let E : ℝ := q * (u - q) /
    (2 * (1 - q) ^ 2 * (1 - q * u))
  let D : ℝ := 1 / (2 * (1 - q) ^ 2)
  have hE : 0 < E := by
    dsimp only [E]
    exact div_pos (mul_pos hq.1 huqsub)
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos h1q)) h1qu)
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have hproduct :
      |oneCutExteriorDistance q u| * E / D =
        H q * (u - q) ^ 2 / u := by
    rw [abs_of_pos hdpos, hdFactor, H]
    dsimp only [E, D]
    field_simp [hq.1.ne', hu0.ne', huqsub.ne', h1qu.ne', h1q.ne']
  change _ = Real.log |oneCutExteriorDistance q u| + Real.log E - Real.log D
    at hdecomp
  rw [hdecomp]
  calc
    Real.log |oneCutExteriorDistance q u| + Real.log E - Real.log D =
        Real.log (|oneCutExteriorDistance q u| * E / D) := by
      rw [Real.log_div (mul_ne_zero (abs_ne_zero.mpr hdpos.ne') hE.ne') hD.ne',
        Real.log_mul (abs_ne_zero.mpr hdpos.ne') hE.ne']
    _ = Real.log (H q * (u - q) ^ 2 / u) := by rw [hproduct]

/-- The same balayage formula on the far-left side of the endpoint atom. -/
theorem integral_platformBalayage_log_oneCut_outer
    {q u : ℝ} (hq : q ∈ Ioo (0 : ℝ) qCeiling)
    (huq : q⁻¹ < u) :
    (1 / Real.pi) *
        (∫ theta : ℝ in 0..Real.pi,
          (Real.sqrt (2 * positiveBufferDistanceLeft (s q)) /
              platformAngularDistance
                (positiveBufferDistanceLeft (s q)) theta) *
            Real.log |oneCutExteriorDistance q u -
              platformAngularDistance
                (positiveBufferDistanceLeft (s q)) theta|) =
      Real.log (H q * (u - q) ^ 2 / u) := by
  have hq1 : q < 1 := mem_Ioo_zero_qCeiling_imp_lt_one hq
  have hs := s_mem_Ioo_of_mem_Ioo hq
  have ha : 0 < positiveBufferDistanceLeft (s q) :=
    positiveBufferDistanceLeft_pos hs.1
  have ha2 : positiveBufferDistanceLeft (s q) < 2 :=
    positiveBufferDistanceLeft_lt_two hs.1 hs.2
  have hu : 1 < u := (one_lt_inv_q hq.1 hq1).trans huq
  have hu0 : 0 < u := (by norm_num : (0 : ℝ) < 1).trans hu
  have huqsub : 0 < u - q := sub_pos.mpr (hq1.trans hu)
  have hqu : 0 < q * u - 1 := by
    have hmul := mul_lt_mul_of_pos_left huq hq.1
    rw [mul_inv_cancel₀ hq.1.ne'] at hmul
    linarith
  have h1quNeg : 1 - q * u < 0 := by linarith [hqu]
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have hdFactor := oneCutExteriorDistance_factor hq.1.ne'
    (by linarith [hq.1]) hu0.ne'
  have hH : 0 < H q := H_pos hq.1
  have hdneg : oneCutExteriorDistance q u < 0 := by
    rw [hdFactor]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (mul_pos hH huqsub) h1quNeg)
      (mul_pos hq.1 hu0)
  have hdleft : oneCutExteriorDistance q u <
      positiveBufferDistanceLeft (s q) := hdneg.trans
        (positiveBufferDistanceLeft_pos hs.1)
  have hJ : (1 / 2 : ℝ) < (positiveBufferDistanceLeft (s q))⁻¹ := by
    rw [one_div, inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) ha]
    exact ha2
  have hwinv : (oneCutExteriorDistance q u)⁻¹ < (1 / 2 : ℝ) :=
    (inv_lt_zero'.mpr hdneg).trans (by norm_num)
  have hEq := integral_intervalEquilibrium_log_exterior_left hJ hwinv
  have hEq' :
      (1 / Real.pi) *
          (∫ psi : ℝ in 0..Real.pi,
            Real.log |(oneCutExteriorDistance q u)⁻¹ -
              intervalAngularDistance (1 / 2 : ℝ)
                (positiveBufferDistanceLeft (s q))⁻¹ psi|) =
        Real.log
          (q * (u - q) /
            (2 * (1 - q) ^ 2 * (q * u - 1))) := by
    rw [intervalExteriorD0_inverted_oneCut_outer hq huq] at hEq
    exact hEq
  have hdecomp := integral_platformBalayage_log_exterior_decomp
    ha ha2 hdleft hdneg.ne
  rw [hEq', intervalExteriorD0_inverted_positiveBufferDistanceLeft hq]
    at hdecomp
  let E : ℝ := q * (u - q) /
    (2 * (1 - q) ^ 2 * (q * u - 1))
  let D : ℝ := 1 / (2 * (1 - q) ^ 2)
  have hE : 0 < E := by
    dsimp only [E]
    exact div_pos (mul_pos hq.1 huqsub)
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos h1q)) hqu)
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have hproduct :
      |oneCutExteriorDistance q u| * E / D =
        H q * (u - q) ^ 2 / u := by
    rw [abs_of_neg hdneg, hdFactor, H]
    dsimp only [E, D]
    field_simp [hq.1.ne', hu0.ne', huqsub.ne', hqu.ne', h1q.ne']
    ring
  change _ = Real.log |oneCutExteriorDistance q u| + Real.log E - Real.log D
    at hdecomp
  rw [hdecomp]
  calc
    Real.log |oneCutExteriorDistance q u| + Real.log E - Real.log D =
        Real.log (|oneCutExteriorDistance q u| * E / D) := by
      rw [Real.log_div (mul_ne_zero (abs_ne_zero.mpr hdneg.ne) hE.ne') hD.ne',
        Real.log_mul (abs_ne_zero.mpr hdneg.ne) hE.ne']
    _ = Real.log (H q * (u - q) ^ 2 / u) := by rw [hproduct]

/-- Globally off the support, the positive-buffer potential is the interval
equilibrium potential plus `alpha` times the atom-minus-balayage potential.
This also makes its affine dependence on `alpha` explicit. -/
theorem positiveBufferPotential_eq_equilibrium_add_atom_sub_balayage
    {s alpha d : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    positiveBufferPotential s alpha (d - 1) =
      (1 / Real.pi) *
          (∫ theta : ℝ in 0..Real.pi,
            Real.log |d -
              platformAngularDistance (positiveBufferDistanceLeft s) theta|) +
        alpha *
          (Real.log |d| -
            (1 / Real.pi) *
              (∫ theta : ℝ in 0..Real.pi,
                (Real.sqrt (2 * positiveBufferDistanceLeft s) /
                    platformAngularDistance
                      (positiveBufferDistanceLeft s) theta) *
                  Real.log |d -
                    platformAngularDistance
                      (positiveBufferDistanceLeft s) theta|)) := by
  let a : ℝ := positiveBufferDistanceLeft s
  let F : ℝ → ℝ := fun theta ↦
    Real.log |d - platformAngularDistance a theta|
  let W : ℝ → ℝ := fun theta ↦
    (Real.sqrt (2 * a) / platformAngularDistance a theta) * F theta
  have halpha1 : alpha < 1 := halphas.trans_lt hs1
  have ha : 0 < a := positiveBufferDistanceLeft_pos hs
  have ha2 : a < 2 := positiveBufferDistanceLeft_lt_two hs hs1
  have hF : IntervalIntegrable F volume 0 Real.pi := by
    have han : AnalyticOnNhd ℝ
        (fun theta ↦ d - platformAngularDistance a theta) Set.univ :=
      fun _ _ ↦ by
        unfold platformAngularDistance
        fun_prop
    have hmer : MeromorphicOn
        (fun theta ↦ d - platformAngularDistance a theta)
        (Set.uIcc 0 Real.pi) :=
      fun x _hx ↦ han.meromorphicOn x (Set.mem_univ x)
    simpa only [F, Real.norm_eq_abs] using!
      MeromorphicOn.intervalIntegrable_log_norm hmer
  have hweight : ContinuousOn
      (fun theta : ℝ ↦
        Real.sqrt (2 * a) / platformAngularDistance a theta)
      (Set.uIcc 0 Real.pi) := by
    apply continuousOn_const.div
    · unfold platformAngularDistance
      fun_prop
    · intro theta htheta
      rw [uIcc_of_le Real.pi_pos.le] at htheta
      exact (platformAngularDistance_pos ha ha2.le htheta).ne'
  have hW : IntervalIntegrable W volume 0 Real.pi := by
    simpa only [W, mul_comm] using! hF.continuousOn_mul hweight
  have hAngular :=
    integral_platformConstantReferenceMeasure_log_kernel_eq_angular
      (positiveBufferRatio_nonneg halpha halpha1) ha ha2
      (positiveBuffer_threshold_le hs.le hs1 halpha halphas)
      (d := d)
  change
      (∫ e : ℝ, Real.log |d - e|
        ∂(positiveBufferContinuousDistanceMeasure s alpha)) =
        (1 / Real.pi) *
          (∫ theta : ℝ in 0..Real.pi,
            F theta * platformAngularDensity
              (positiveBufferRatio alpha) a theta) at hAngular
  have hdensity :
      (1 - alpha) *
          (∫ theta : ℝ in 0..Real.pi,
            F theta * platformAngularDensity
              (positiveBufferRatio alpha) a theta) =
        (∫ theta : ℝ in 0..Real.pi, F theta) -
          alpha * (∫ theta : ℝ in 0..Real.pi, W theta) := by
    calc
      (1 - alpha) *
            (∫ theta : ℝ in 0..Real.pi,
              F theta * platformAngularDensity
                (positiveBufferRatio alpha) a theta) =
          ∫ theta : ℝ in 0..Real.pi,
            (1 - alpha) *
              (F theta * platformAngularDensity
                (positiveBufferRatio alpha) a theta) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ∫ theta : ℝ in 0..Real.pi,
          (F theta - alpha * W theta) := by
        apply intervalIntegral.integral_congr
        intro theta htheta
        simp only [F, W, platformAngularDensity,
          platformDensityCoefficient, positiveBufferRatio]
        field_simp [(sub_pos.mpr halpha1).ne']
        ring
      _ = (∫ theta : ℝ in 0..Real.pi, F theta) -
            alpha * (∫ theta : ℝ in 0..Real.pi, W theta) := by
        rw [intervalIntegral.integral_sub hF (hW.const_mul alpha),
          intervalIntegral.integral_const_mul]
  have hatom : (d - 1) + 1 = d := by ring
  rw [positiveBufferPotential_eq_atom_add_continuous
    hs hs1 halpha halphas, hatom, hAngular]
  change alpha * Real.log |d| +
      (1 - alpha) *
        ((1 / Real.pi) *
          (∫ theta : ℝ in 0..Real.pi,
            F theta * platformAngularDensity
              (positiveBufferRatio alpha) a theta)) =
    (1 / Real.pi) * (∫ theta : ℝ in 0..Real.pi, F theta) +
      alpha *
        (Real.log |d| -
          (1 / Real.pi) *
            (∫ theta : ℝ in 0..Real.pi, W theta))
  calc
    alpha * Real.log |d| +
          (1 - alpha) *
            ((1 / Real.pi) *
              (∫ theta : ℝ in 0..Real.pi,
                F theta * platformAngularDensity
                  (positiveBufferRatio alpha) a theta)) =
        alpha * Real.log |d| +
          (1 / Real.pi) *
            ((1 - alpha) *
              (∫ theta : ℝ in 0..Real.pi,
                F theta * platformAngularDensity
                  (positiveBufferRatio alpha) a theta)) := by ring
    _ = alpha * Real.log |d| +
          (1 / Real.pi) *
            ((∫ theta : ℝ in 0..Real.pi, F theta) -
              alpha * (∫ theta : ℝ in 0..Real.pi, W theta)) := by
      rw [hdensity]
    _ = (1 / Real.pi) * (∫ theta : ℝ in 0..Real.pi, F theta) +
          alpha *
            (Real.log |d| -
              (1 / Real.pi) *
                (∫ theta : ℝ in 0..Real.pi, W theta)) := by ring

theorem oneCutExterior_log_identity
    {q u : ℝ} (hq : q ∈ Ioo (0 : ℝ) qCeiling)
    (hu : 1 < u) (huinv : u ≠ q⁻¹) :
    Real.log (H q * u) +
        A q *
          (Real.log |oneCutExteriorDistance q u| -
            Real.log (H q * (u - q) ^ 2 / u)) =
      -exteriorFunction q u := by
  have hq1 : q < 1 := mem_Ioo_zero_qCeiling_imp_lt_one hq
  have hu0 : 0 < u := (by norm_num : (0 : ℝ) < 1).trans hu
  have huqsub : 0 < u - q := sub_pos.mpr (hq1.trans hu)
  have hH : 0 < H q := H_pos hq.1
  have hlogq : Real.log q ≠ 0 := log_q_ne_zero hq.1 hq1
  have h1qu : 1 - q * u ≠ 0 := by
    intro hzero
    apply huinv
    field_simp [hq.1.ne']
    linarith
  have hdFactor := oneCutExteriorDistance_factor hq.1.ne'
    (by linarith [hq.1]) hu0.ne'
  have hdabs : |oneCutExteriorDistance q u| =
      H q * (u - q) * |1 - q * u| / (q * u) := by
    rw [hdFactor, abs_div, abs_mul, abs_mul, abs_mul,
      abs_of_pos hH, abs_of_pos huqsub, abs_of_pos hq.1,
      abs_of_pos hu0]
  have hlogE : Real.log (H q * u) =
      Real.log (H q) + Real.log u := by
    rw [Real.log_mul hH.ne' hu0.ne']
  have hlogB : Real.log (H q * (u - q) ^ 2 / u) =
      Real.log (H q) + 2 * Real.log (u - q) - Real.log u := by
    rw [Real.log_div
      (mul_ne_zero hH.ne' (pow_ne_zero 2 huqsub.ne')) hu0.ne',
      Real.log_mul hH.ne' (pow_ne_zero 2 huqsub.ne'), Real.log_pow]
    norm_num
  have hlogd : Real.log |oneCutExteriorDistance q u| =
      Real.log (H q) + Real.log (u - q) + Real.log |1 - q * u| -
        Real.log q - Real.log u := by
    rw [hdabs,
      Real.log_div
        (mul_ne_zero
          (mul_ne_zero hH.ne' huqsub.ne') (abs_ne_zero.mpr h1qu))
        (mul_ne_zero hq.1.ne' hu0.ne'),
      Real.log_mul (mul_ne_zero hH.ne' huqsub.ne')
        (abs_ne_zero.mpr h1qu),
      Real.log_mul hH.ne' huqsub.ne',
      Real.log_mul hq.1.ne' hu0.ne']
    ring
  have hlogR :
      Real.log ((u - q) / |1 - q * u|) =
        Real.log (u - q) - Real.log |1 - q * u| := by
    rw [Real.log_div huqsub.ne' (abs_ne_zero.mpr h1qu)]
  have hAlogq : A q * Real.log q = Real.log (H q) := by
    rw [A]
    field_simp [hlogq]
  rw [exteriorFunction, hlogE, hlogB, hlogd, hlogR]
  nlinarith

/-- Exact gap-side identification of the zero-platform positive-buffer
potential with the negative scalar exterior residual. -/
theorem positiveBufferPotential_zeroPlatform_oneCut_inner
    {q u : ℝ} (hq : q ∈ Ioo (0 : ℝ) qCeiling)
    (hqs : q ≤ qSoft) (hu : 1 < u) (huq : u < q⁻¹) :
    positiveBufferPotential (s q) (A q)
        (oneCutExteriorDistance q u - 1) =
      -exteriorFunction q u := by
  have hs := s_mem_Ioo_of_mem_Ioo hq
  have hA := A_mem_Ioo_of_mem_Ioo hq
  have hAle : A q ≤ s q := A_le_s_of_pos_le_qSoft hq.1 hqs
  rw [positiveBufferPotential_eq_equilibrium_add_atom_sub_balayage
    hs.1 hs.2 hA.1.le hAle,
    integral_platformEquilibrium_log_oneCutExteriorDistance hq hu,
    integral_platformBalayage_log_oneCut_inner hq hu huq]
  exact oneCutExterior_log_identity hq hu (ne_of_lt huq)

/-- Far-left counterpart of the zero-platform exterior identity. -/
theorem positiveBufferPotential_zeroPlatform_oneCut_outer
    {q u : ℝ} (hq : q ∈ Ioo (0 : ℝ) qCeiling)
    (hqs : q ≤ qSoft) (huq : q⁻¹ < u) :
    positiveBufferPotential (s q) (A q)
        (oneCutExteriorDistance q u - 1) =
      -exteriorFunction q u := by
  have hq1 : q < 1 := mem_Ioo_zero_qCeiling_imp_lt_one hq
  have hu : 1 < u := (one_lt_inv_q hq.1 hq1).trans huq
  have hs := s_mem_Ioo_of_mem_Ioo hq
  have hA := A_mem_Ioo_of_mem_Ioo hq
  have hAle : A q ≤ s q := A_le_s_of_pos_le_qSoft hq.1 hqs
  rw [positiveBufferPotential_eq_equilibrium_add_atom_sub_balayage
    hs.1 hs.2 hA.1.le hAle,
    integral_platformEquilibrium_log_oneCutExteriorDistance hq hu,
    integral_platformBalayage_log_oneCut_outer hq huq]
  exact oneCutExterior_log_identity hq hu (ne_of_gt huq)

/-! ## The exterior coordinate as an order isomorphism -/

theorem hasDerivAt_oneCutExteriorDistance
    {q u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (oneCutExteriorDistance q)
      (H q * (-1 + (u ^ 2)⁻¹)) u := by
  unfold oneCutExteriorDistance
  have hinner := (((hasDerivAt_const u q).add
      (hasDerivAt_const u q⁻¹)).sub (hasDerivAt_id u)).sub
        (hasDerivAt_inv hu)
  have hinner' : HasDerivAt
      (fun x : ℝ ↦ q + q⁻¹ - x - x⁻¹)
      (-1 + (u ^ 2)⁻¹) u := by
    convert! hinner using 1
    ring
  exact hinner'.const_mul (H q)

/-- The Joukowski distance is strictly decreasing from the support edge
towards the far-left end of the real line. -/
theorem oneCutExteriorDistance_strictAntiOn_Ici
    {q : ℝ} (hq : 0 < q) :
    StrictAntiOn (oneCutExteriorDistance q) (Ici 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (1 : ℝ))
  · intro u hu
    change 1 ≤ u at hu
    exact (hasDerivAt_oneCutExteriorDistance
      (q := q) (u := u) (by linarith)).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ici] at hu
    change 1 < u at hu
    rw [(hasDerivAt_oneCutExteriorDistance
      (q := q) (u := u) (by linarith)).deriv]
    have hinv : (u ^ 2)⁻¹ < 1 := by
      rw [inv_lt_one₀ (sq_pos_of_pos (by linarith))]
      nlinarith
    apply mul_neg_of_pos_of_neg (H_pos hq)
    linarith

theorem tendsto_oneCutExteriorDistance_atTop
    {q : ℝ} (hq : 0 < q) :
    Tendsto (oneCutExteriorDistance q) atTop atBot := by
  unfold oneCutExteriorDistance
  apply Tendsto.const_mul_atBot (H_pos hq)
  have hc : Tendsto (fun _ : ℝ ↦ q + q⁻¹) atTop
      (nhds (q + q⁻¹)) := tendsto_const_nhds
  have hsmall : Tendsto (fun u : ℝ ↦ q + q⁻¹ - u⁻¹) atTop
      (nhds (q + q⁻¹)) := by
    simpa using! hc.sub tendsto_inv_atTop_zero
  have hlarge : Tendsto (fun u : ℝ ↦ -u) atTop atBot :=
    tendsto_neg_atTop_atBot
  convert! hsmall.add_atBot hlarge using 1
  ext u
  ring

theorem oneCutExteriorDistance_one
    {q : ℝ} (hq : 0 < q) :
    oneCutExteriorDistance q 1 = positiveBufferDistanceLeft (s q) := by
  have h := positiveBufferDistanceLeft_sub_oneCutExteriorDistance
    hq.ne' (by linarith) (by norm_num : (1 : ℝ) ≠ 0)
  norm_num at h
  linarith

theorem oneCutExteriorDistance_inv
    (q : ℝ) :
    oneCutExteriorDistance q q⁻¹ = 0 := by
  rw [oneCutExteriorDistance, inv_inv]
  ring

/-- Every distance strictly to the left of the continuous support has a
unique exterior coordinate `u > 1`. -/
theorem existsUnique_oneCutExteriorDistance_eq
    {q d : ℝ} (hq : 0 < q)
    (hd : d < positiveBufferDistanceLeft (s q)) :
    ∃! u : ℝ, 1 < u ∧ oneCutExteriorDistance q u = d := by
  have hcont : ContinuousOn (oneCutExteriorDistance q) (Ici 1) := by
    intro u hu
    change 1 ≤ u at hu
    exact (hasDerivAt_oneCutExteriorDistance
      (q := q) (u := u) (by linarith)).continuousAt.continuousWithinAt
  have himage : d ∈ oneCutExteriorDistance q '' Ici 1 := by
    apply isPreconnected_Ici.intermediate_value_Iic
      (a := (1 : ℝ)) (l := atTop)
      self_mem_Ici (le_principal_iff.mpr (Ici_mem_atTop 1))
      hcont (tendsto_oneCutExteriorDistance_atTop hq)
    rw [oneCutExteriorDistance_one hq]
    exact hd.le
  obtain ⟨u, hu1, hud⟩ := himage
  have hu : 1 < u := by
    apply lt_of_le_of_ne hu1
    intro heq
    subst u
    rw [oneCutExteriorDistance_one hq] at hud
    linarith
  refine ⟨u, ⟨hu, hud⟩, ?_⟩
  intro v hv
  by_contra huv
  rcases lt_or_gt_of_ne huv with huv | huv
  · have hstrict := oneCutExteriorDistance_strictAntiOn_Ici hq
      hv.1.le hu.le huv
    linarith [hud, hv.2]
  · have hstrict := oneCutExteriorDistance_strictAntiOn_Ici hq
      hu.le hv.1.le huv
    linarith [hud, hv.2]

end

end Erdos1038
