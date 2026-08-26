import ErdosProblems.Erdos1038.OneCutSoftExpr

/-!
# Analytic bridge for the regularized soft chart

This file connects the rational soft-coordinate expressions to the actual
inner root `uPlus` and to `LambdaDerivativeFormula`.
-/

open Filter Set
open scoped Topology

namespace Erdos1038

noncomputable section

/-- The positive Cayley coordinate of an inner root. -/
def softTanhCoordinate (u : ℝ) : ℝ := (u - 1) / (u + 1)

/-- The squared soft coordinate of the actual inner root. -/
def oneCutSoftS (q : ℝ) : ℝ := softTanhCoordinate (uPlus q) ^ 2

/-- The inverse Cayley transform on the nonnegative soft coordinate. -/
def softUOfS (s : ℝ) : ℝ := (1 + Real.sqrt s) / (1 - Real.sqrt s)

def softCoordinateSlope (u : ℝ) : ℝ := 4 * (u - 1) / (u + 1) ^ 3

theorem softTanhCoordinate_pos {u : ℝ} (hu : 1 < u) :
    0 < softTanhCoordinate u := by
  rw [softTanhCoordinate]
  exact div_pos (sub_pos.2 hu) (by linarith)

theorem softTanhCoordinate_lt_one {u : ℝ} (hu : 1 < u) :
    softTanhCoordinate u < 1 := by
  rw [softTanhCoordinate]
  exact (div_lt_one (by linarith : 0 < u + 1)).2 (by linarith)

theorem oneCutSoftS_mem_Ioo {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    oneCutSoftS q ∈ Ioo (0 : ℝ) 1 := by
  have hu := (uPlus_spec hq hqs).1
  have ht0 := softTanhCoordinate_pos hu
  have ht1 := softTanhCoordinate_lt_one hu
  rw [oneCutSoftS]
  constructor
  · positivity
  · have hprod : 0 < (1 - softTanhCoordinate (uPlus q)) *
        (1 + softTanhCoordinate (uPlus q)) :=
      mul_pos (sub_pos.2 ht1) (by linarith)
    nlinarith

theorem sqrt_oneCutSoftS {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    Real.sqrt (oneCutSoftS q) = softTanhCoordinate (uPlus q) := by
  rw [oneCutSoftS, Real.sqrt_sq_eq_abs,
    abs_of_pos (softTanhCoordinate_pos (uPlus_spec hq hqs).1)]

theorem softUOfS_oneCutSoftS {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    softUOfS (oneCutSoftS q) = uPlus q := by
  rw [softUOfS, sqrt_oneCutSoftS hq hqs, softTanhCoordinate]
  have hden : uPlus q + 1 ≠ 0 := by
    have := (uPlus_spec hq hqs).1
    linarith
  field_simp [hden]
  ring

theorem softUOfS_gt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    1 < softUOfS x := by
  have ht0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have htsq : Real.sqrt x ^ 2 = x := by
    nlinarith [Real.sq_sqrt hx0.le]
  have ht1 : Real.sqrt x < 1 := by
    nlinarith [sq_lt_sq₀ (Real.sqrt_nonneg x)
      (by norm_num : (0 : ℝ) ≤ 1), htsq, hx1]
  rw [softUOfS]
  exact (one_lt_div (sub_pos.2 ht1)).2 (by linarith)

theorem softTanhCoordinate_softUOfS {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    softTanhCoordinate (softUOfS x) = Real.sqrt x := by
  have ht0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have htsq : Real.sqrt x ^ 2 = x := by
    nlinarith [Real.sq_sqrt hx0.le]
  have ht1 : Real.sqrt x < 1 := by
    nlinarith [sq_lt_sq₀ (Real.sqrt_nonneg x)
      (by norm_num : (0 : ℝ) ≤ 1), htsq, hx1]
  rw [softTanhCoordinate, softUOfS]
  have hden : 1 - Real.sqrt x ≠ 0 := by linarith
  field_simp [hden]
  ring

theorem softUOfS_lt_inv {q x : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hx0 : 0 < x) (hx1 : x < 1)
    (hw1 : softW q x < 1) : softUOfS x < q⁻¹ := by
  have ht0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have htsq : Real.sqrt x ^ 2 = x := by
    nlinarith [Real.sq_sqrt hx0.le]
  have ht1 : Real.sqrt x < 1 := by
    nlinarith [sq_lt_sq₀ (Real.sqrt_nonneg x)
      (by norm_num : (0 : ℝ) ≤ 1), htsq, hx1]
  have hk : 0 < softKappa q := by
    rw [softKappa]
    exact div_pos (by linarith) (by linarith)
  have hkt0 : 0 < softKappa q * Real.sqrt x := mul_pos hk ht0
  have hktSq : (softKappa q * Real.sqrt x) ^ 2 < 1 := by
    rw [mul_pow, htsq]
    simpa [softW] using! hw1
  have hkt1 : softKappa q * Real.sqrt x < 1 := by nlinarith
  have hqu : q * softUOfS x < 1 := by
    rw [softUOfS]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (sub_pos.2 ht1)).2
    have hkt1' : (1 + q) * Real.sqrt x / (1 - q) < 1 := by
      simpa [softKappa, div_mul_eq_mul_div] using! hkt1
    have hlin := (div_lt_one (by linarith : 0 < 1 - q)).1 hkt1'
    nlinarith
  rw [← one_div]
  exact (lt_div_iff₀ hq).2 (by simpa [mul_comm] using! hqu)

theorem softUOfS_mono {a b : ℝ}
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b < 1) :
    softUOfS a ≤ softUOfS b := by
  have hb0 : 0 ≤ b := ha0.trans hab
  have hta := Real.sqrt_nonneg a
  have htb := Real.sqrt_nonneg b
  have hta1 : Real.sqrt a < 1 := by
    have hasq : Real.sqrt a ^ 2 = a := by
      nlinarith [Real.sq_sqrt ha0]
    nlinarith [hab, hb1, hasq]
  have htb1 : Real.sqrt b < 1 := by
    have hbsq : Real.sqrt b ^ 2 = b := by
      nlinarith [Real.sq_sqrt hb0]
    nlinarith [hb1, hbsq]
  have hroot : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  rw [softUOfS, softUOfS]
  apply (div_le_div_iff₀ (sub_pos.2 hta1) (sub_pos.2 htb1)).2
  nlinarith

theorem one_add_sub_softTanhCoordinate {u : ℝ} (hu : 1 < u) :
    (1 + softTanhCoordinate u) / (1 - softTanhCoordinate u) = u := by
  rw [softTanhCoordinate]
  have hden : u + 1 ≠ 0 := by linarith
  field_simp [hden]
  ring

theorem artanh_softTanhCoordinate {u : ℝ} (hu : 1 < u) :
    Real.artanh (softTanhCoordinate u) = Real.log u / 2 := by
  have ht0 := softTanhCoordinate_pos hu
  have ht1 := softTanhCoordinate_lt_one hu
  rw [Real.artanh_eq_half_log ⟨(by linarith), ht1.le⟩,
    one_add_sub_softTanhCoordinate hu]
  ring

theorem softKappa_mul_tanhCoordinate_pos {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hu : 1 < u) :
    0 < softKappa q * softTanhCoordinate u := by
  apply mul_pos
  · rw [softKappa]
    exact div_pos (by linarith) (by linarith)
  · exact softTanhCoordinate_pos hu

theorem softKappa_mul_tanhCoordinate_lt_one {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hu : 1 < u) (huq : u < q⁻¹) :
    softKappa q * softTanhCoordinate u < 1 := by
  have hqu : q * u < 1 := by
    have hmul := mul_lt_mul_of_pos_left huq hq
    rw [mul_inv_cancel₀ hq.ne'] at hmul
    exact hmul
  rw [softKappa, softTanhCoordinate, div_mul_div_comm]
  apply (div_lt_one (mul_pos (by linarith : 0 < 1 - q)
    (by linarith : 0 < u + 1))).2
  nlinarith

theorem one_add_sub_softKappa_mul_tanhCoordinate {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hu : 1 < u) (huq : u < q⁻¹) :
    (1 + softKappa q * softTanhCoordinate u) /
        (1 - softKappa q * softTanhCoordinate u) =
      (u - q) / (1 - q * u) := by
  have hleftden : 1 - softKappa q * softTanhCoordinate u ≠ 0 :=
    ne_of_gt (sub_pos.2
      (softKappa_mul_tanhCoordinate_lt_one hq hq1 hu huq))
  have hpole : 1 - q * u ≠ 0 := by
    have hqu : q * u < 1 := by
      have hmul := mul_lt_mul_of_pos_left huq hq
      rw [mul_inv_cancel₀ hq.ne'] at hmul
      exact hmul
    linarith
  apply (div_eq_div_iff hleftden hpole).2
  rw [softKappa, softTanhCoordinate]
  have hqden : 1 - q ≠ 0 := by linarith
  have huden : u + 1 ≠ 0 := by linarith
  field_simp [hqden, huden]
  ring

theorem artanh_softKappa_mul_tanhCoordinate {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hu : 1 < u) (huq : u < q⁻¹) :
    Real.artanh (softKappa q * softTanhCoordinate u) =
      Real.log ((u - q) / (1 - q * u)) / 2 := by
  have ht0 := softKappa_mul_tanhCoordinate_pos hq hq1 hu
  have ht1 := softKappa_mul_tanhCoordinate_lt_one hq hq1 hu huq
  rw [Real.artanh_eq_half_log ⟨(by linarith), ht1.le⟩,
    one_add_sub_softKappa_mul_tanhCoordinate hq hq1 hu huq]
  ring

theorem softT_tanhCoordinate_sq {u : ℝ} (hu : 1 < u) :
    softT (softTanhCoordinate u ^ 2) =
      Real.log u / (2 * softTanhCoordinate u) := by
  have ht0 := softTanhCoordinate_pos hu
  rw [softT, if_neg (pow_ne_zero 2 ht0.ne'),
    Real.sqrt_sq_eq_abs, abs_of_pos ht0,
    artanh_softTanhCoordinate hu]
  ring

theorem softW_tanhCoordinate_sq (q u : ℝ) :
    softW q (softTanhCoordinate u ^ 2) =
      (softKappa q * softTanhCoordinate u) ^ 2 := by
  rw [softW]
  ring

theorem softW_oneCutSoftS_mem_Ioo {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    softW q (oneCutSoftS q) ∈ Ioo (0 : ℝ) 1 := by
  have hup := uPlus_spec hq hqs
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have ht0 := softKappa_mul_tanhCoordinate_pos hq hq1 hup.1
  have ht1 := softKappa_mul_tanhCoordinate_lt_one hq hq1 hup.1 hup.2.1
  rw [oneCutSoftS, softW_tanhCoordinate_sq]
  constructor
  · positivity
  · have hprod : 0 <
        (1 - softKappa q * softTanhCoordinate (uPlus q)) *
          (1 + softKappa q * softTanhCoordinate (uPlus q)) :=
      mul_pos (sub_pos.2 ht1) (by linarith)
    nlinarith

theorem softT_softW_tanhCoordinate_sq {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hu : 1 < u) (huq : u < q⁻¹) :
    softT (softW q (softTanhCoordinate u ^ 2)) =
      Real.log ((u - q) / (1 - q * u)) /
        (2 * softKappa q * softTanhCoordinate u) := by
  have ht0 := softKappa_mul_tanhCoordinate_pos hq hq1 hu
  rw [softW_tanhCoordinate_sq, softT,
    if_neg (pow_ne_zero 2 ht0.ne'), Real.sqrt_sq_eq_abs,
    abs_of_pos ht0, artanh_softKappa_mul_tanhCoordinate hq hq1 hu huq]
  ring

theorem softDividedInnerAt_tanhCoordinate_sq {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hu : 1 < u) (huq : u < q⁻¹) :
    softDividedInnerAt q (softT (softTanhCoordinate u ^ 2))
        (softT (softW q (softTanhCoordinate u ^ 2))) =
      innerResidual (q, u) / (2 * softTanhCoordinate u) := by
  rw [softDividedInnerAt, softT_tanhCoordinate_sq hu,
    softT_softW_tanhCoordinate_sq hq hq1 hu huq, innerResidual]
  have ht : softTanhCoordinate u ≠ 0 :=
    (softTanhCoordinate_pos hu).ne'
  have hk : softKappa q ≠ 0 := by
    rw [softKappa]
    exact div_ne_zero (by linarith) (by linarith)
  field_simp [ht, hk]

theorem softDividedInnerAt_eq_exteriorFunction_div {q x : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hx0 : 0 < x) (hx1 : x < 1)
    (hw1 : softW q x < 1) :
    softDividedInnerAt q (softT x) (softT (softW q x)) =
      exteriorFunction q (softUOfS x) / (2 * Real.sqrt x) := by
  have hu1 := softUOfS_gt_one hx0 hx1
  have huq := softUOfS_lt_inv hq hq1 hx0 hx1 hw1
  have hcoord := softTanhCoordinate_softUOfS hx0 hx1
  have hxSq : Real.sqrt x ^ 2 = x := by
    nlinarith [Real.sq_sqrt hx0.le]
  have hxform : softTanhCoordinate (softUOfS x) ^ 2 = x := by
    rw [hcoord, hxSq]
  conv_lhs => rw [← hxform]
  rw [softDividedInnerAt_tanhCoordinate_sq hq hq1 hu1 huq,
    innerResidual_eq_exteriorFunction hq huq, hcoord]

theorem softDividedInner_neg_imp_lt_actual {q x : ℝ}
    (hq : 0 < q) (hqs : q < qSoft)
    (hx0 : 0 < x) (hx1 : x < 1) (hw1 : softW q x < 1)
    (hneg : softDividedInnerAt q (softT x) (softT (softW q x)) < 0) :
    x < oneCutSoftS q := by
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hactual := oneCutSoftS_mem_Ioo hq hqs
  have hformula := softDividedInnerAt_eq_exteriorFunction_div
    hq hq1 hx0 hx1 hw1
  have hu1 := softUOfS_gt_one hx0 hx1
  have huq := softUOfS_lt_inv hq hq1 hx0 hx1 hw1
  by_contra hn
  have hle : oneCutSoftS q ≤ x := le_of_not_gt hn
  have hule : uPlus q ≤ softUOfS x := by
    rw [← softUOfS_oneCutSoftS hq hqs]
    exact softUOfS_mono hactual.1.le hle hx1
  rcases hule.eq_or_lt with heq | hlt
  · have hzero : exteriorFunction q (softUOfS x) = 0 := by
      rw [← heq]
      exact exteriorEquation_iff_exteriorFunction_eq_zero.1
        (uPlus_spec hq hqs).2.2
    rw [hformula, hzero, zero_div] at hneg
    exact lt_irrefl 0 hneg
  · have hpos := exteriorFunction_inner_pos_after_uPlus hq hqs huq hlt
    have hden : 0 < 2 * Real.sqrt x :=
      mul_pos (by norm_num) (Real.sqrt_pos.2 hx0)
    rw [hformula] at hneg
    have := div_pos hpos hden
    linarith

theorem softDividedInner_pos_imp_actual_lt {q x : ℝ}
    (hq : 0 < q) (hqs : q < qSoft)
    (hx0 : 0 < x) (hx1 : x < 1) (hw1 : softW q x < 1)
    (hpos : 0 < softDividedInnerAt q (softT x) (softT (softW q x))) :
    oneCutSoftS q < x := by
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hactual := oneCutSoftS_mem_Ioo hq hqs
  have hformula := softDividedInnerAt_eq_exteriorFunction_div
    hq hq1 hx0 hx1 hw1
  have hu1 := softUOfS_gt_one hx0 hx1
  have huq := softUOfS_lt_inv hq hq1 hx0 hx1 hw1
  by_contra hn
  have hle : x ≤ oneCutSoftS q := le_of_not_gt hn
  have hule : softUOfS x ≤ uPlus q := by
    rw [← softUOfS_oneCutSoftS hq hqs]
    exact softUOfS_mono hx0.le hle hactual.2
  rcases hule.eq_or_lt with heq | hlt
  · have hzero : exteriorFunction q (softUOfS x) = 0 := by
      rw [heq]
      exact exteriorEquation_iff_exteriorFunction_eq_zero.1
        (uPlus_spec hq hqs).2.2
    rw [hformula, hzero, zero_div] at hpos
    exact lt_irrefl 0 hpos
  · have hneg := exteriorFunction_inner_neg_before_uPlus hq hqs hu1 huq hlt
    have hden : 0 < 2 * Real.sqrt x :=
      mul_pos (by norm_num) (Real.sqrt_pos.2 hx0)
    rw [hformula] at hpos
    have := div_neg_of_neg_of_pos hneg hden
    linarith

theorem softDividedInner_actual_eq_zero {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    softDividedInnerAt q (softT (oneCutSoftS q))
        (softT (softW q (oneCutSoftS q))) = 0 := by
  have hup := uPlus_spec hq hqs
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  rw [oneCutSoftS,
    softDividedInnerAt_tanhCoordinate_sq hq hq1 hup.1 hup.2.1]
  have hres : innerResidual (q, uPlus q) = 0 := by
    rw [innerResidual_eq_exteriorFunction hq hup.2.1]
    exact exteriorEquation_iff_exteriorFunction_eq_zero.1 hup.2.2
  rw [hres, zero_div]

theorem hasDerivAt_softKappa {q : ℝ} (hq1 : q ≠ 1) :
    HasDerivAt softKappa (softKappaPrime q) q := by
  have hn : HasDerivAt (fun r : ℝ => 1 + r) 1 q := by
    simpa using! (hasDerivAt_const q (1 : ℝ)).add (hasDerivAt_id q)
  have hd : HasDerivAt (fun r : ℝ => 1 - r) (-1) q := by
    simpa using! (hasDerivAt_const q (1 : ℝ)).sub (hasDerivAt_id q)
  have hden : 1 - q ≠ 0 := sub_ne_zero.2 hq1.symm
  convert! hn.div hd hden using 1
  rw [softKappaPrime]
  field_simp [hden]
  ring

theorem hasDerivAt_softTanhCoordinate {u : ℝ} (hu : u ≠ -1) :
    HasDerivAt softTanhCoordinate (2 / (u + 1) ^ 2) u := by
  have hn : HasDerivAt (fun v : ℝ => v - 1) 1 u := by
    simpa using! (hasDerivAt_id u).sub_const 1
  have hd : HasDerivAt (fun v : ℝ => v + 1) 1 u := by
    simpa using! (hasDerivAt_id u).add_const 1
  have hden : u + 1 ≠ 0 := by
    intro hzero
    apply hu
    linarith
  unfold softTanhCoordinate
  convert! hn.div hd hden using 1
  field_simp [hden]
  ring

theorem hasDerivAt_softCoordinate_sq {u : ℝ} (hu : u ≠ -1) :
    HasDerivAt (fun v => softTanhCoordinate v ^ 2)
      (softCoordinateSlope u) u := by
  have hden : u + 1 ≠ 0 := by
    intro hzero
    apply hu
    linarith
  have ht := hasDerivAt_softTanhCoordinate hu
  convert! ht.pow 2 using 1
  rw [softCoordinateSlope, softTanhCoordinate]
  have hden' : 1 + u ≠ 0 := by
    intro hzero
    apply hu
    linarith
  field_simp [hden, hden']
  norm_num
  field_simp [hden]
  ring

theorem softCoordinateSlope_pos {u : ℝ} (hu : 1 < u) :
    0 < softCoordinateSlope u := by
  rw [softCoordinateSlope]
  exact div_pos (mul_pos (by norm_num) (sub_pos.2 hu))
    (pow_pos (by linarith) 3)

theorem hasDerivAt_softDividedInner_q {q s : ℝ}
    (hq : 0 < q) (hq1 : q < 1)
    (hw0 : 0 < softW q s) (hw1 : softW q s < 1) :
    HasDerivAt
      (fun r => softDividedInnerAt r (softT s) (softT (softW r s)))
      (softDividedInnerPartialQAt q s (softT (softW q s))
        (softTPrime (softW q s))) q := by
  have hk := hasDerivAt_softKappa (by linarith : q ≠ 1)
  have hA := hasDerivAt_A hq hq1
  have hw : HasDerivAt (fun r => softW r s)
      (2 * softKappa q * softKappaPrime q * s) q := by
    convert! (hk.pow 2).mul_const s using 1
    simp only [Nat.cast_ofNat]
    ring
  have htw := (hasDerivAt_softT hw0 hw1).comp q hw
  have hmain := (hA.mul hk).mul htw
  have hres := hmain.sub_const (softT s)
  convert! hres using 1
  rw [softDividedInnerPartialQAt]
  simp only [Function.comp_apply, Pi.mul_apply]
  ring

theorem hasDerivAt_softDividedInner_s {q s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hw0 : 0 < softW q s) (hw1 : softW q s < 1) :
    HasDerivAt
      (fun x => softDividedInnerAt q (softT x) (softT (softW q x)))
      (softDividedInnerPartialSAt q (softTPrime s)
        (softTPrime (softW q s))) s := by
  have hw : HasDerivAt (fun x => softW q x) (softKappa q ^ 2) s := by
    convert! (hasDerivAt_id s).const_mul (softKappa q ^ 2) using 1
    simp only [mul_one]
  have htw := (hasDerivAt_softT hw0 hw1).comp s hw
  have hts := hasDerivAt_softT hs0 hs1
  have hmain := htw.const_mul (A q * softKappa q)
  have hres := hmain.sub hts
  convert! hres using 1
  rw [softDividedInnerPartialSAt]
  ring

theorem softDividedInnerPartialQ_actual_eq {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    softDividedInnerPartialQAt q (oneCutSoftS q)
        (softT (softW q (oneCutSoftS q)))
        (softTPrime (softW q (oneCutSoftS q))) =
      innerPartialQ q (uPlus q) /
        (2 * softTanhCoordinate (uPlus q)) := by
  have hup := uPlus_spec hq hqs
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hu0 : 0 < uPlus q := (by linarith : 0 < uPlus q)
  have hquMul : q * uPlus q < 1 := by
    have hmul := mul_lt_mul_of_pos_left hup.2.1 hq
    rw [mul_inv_cancel₀ hq.ne'] at hmul
    exact hmul
  have hqInv : q < (uPlus q)⁻¹ := by
    rw [← one_div]
    exact (lt_div_iff₀ hu0).2 (by simpa [mul_comm] using! hquMul)
  have hevent :
      (fun r => softDividedInnerAt r (softT (oneCutSoftS q))
          (softT (softW r (oneCutSoftS q)))) =ᶠ[𝓝 q]
        (fun r => innerResidual (r, uPlus q) /
          (2 * softTanhCoordinate (uPlus q))) := by
    filter_upwards [Ioi_mem_nhds hq, Iio_mem_nhds hqInv] with r hr0 hrInv
    have hr1 : r < 1 :=
      hrInv.trans ((inv_lt_one₀ hu0).2 hup.1)
    have hur : uPlus q < r⁻¹ := by
      rw [← one_div]
      apply (lt_div_iff₀ hr0).2
      have hmul := mul_lt_mul_of_pos_right hrInv hu0
      rw [inv_mul_cancel₀ hu0.ne'] at hmul
      simpa [mul_comm] using! hmul
    simpa [oneCutSoftS] using!
      softDividedInnerAt_tanhCoordinate_sq hr0 hr1 hup.1 hur
  have hw := softW_oneCutSoftS_mem_Ioo hq hqs
  have hleft := hasDerivAt_softDividedInner_q hq hq1 hw.1 hw.2
  have hright :=
    (hasDerivAt_innerResidual_left hq hq1 hu0
      (hq1.trans hup.1) hup.2.1).div_const
        (2 * softTanhCoordinate (uPlus q))
  exact hleft.unique (hright.congr_of_eventuallyEq hevent)

theorem softDividedInnerPartialS_actual_mul_slope_eq {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    softDividedInnerPartialSAt q (softTPrime (oneCutSoftS q))
        (softTPrime (softW q (oneCutSoftS q))) *
        softCoordinateSlope (uPlus q) =
      innerPartialU q (uPlus q) /
        (2 * softTanhCoordinate (uPlus q)) := by
  have hup := uPlus_spec hq hqs
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hu0 : 0 < uPlus q := by linarith
  have hs := oneCutSoftS_mem_Ioo hq hqs
  have hw := softW_oneCutSoftS_mem_Ioo hq hqs
  have hDs := hasDerivAt_softDividedInner_s hs.1 hs.2 hw.1 hw.2
  have hcoord := hasDerivAt_softCoordinate_sq
    (by linarith [hup.1] : uPlus q ≠ -1)
  have hleft := hDs.comp (uPlus q) hcoord
  have hnum := hasDerivAt_innerResidual_right hq hu0
    (hq1.trans hup.1) hup.2.1
  have ht := hasDerivAt_softTanhCoordinate
    (by linarith [hup.1] : uPlus q ≠ -1)
  have hden : HasDerivAt
      (fun v => 2 * softTanhCoordinate v)
      (2 * (2 / (uPlus q + 1) ^ 2)) (uPlus q) := by
    simpa using! ht.const_mul 2
  have hdenne : 2 * softTanhCoordinate (uPlus q) ≠ 0 :=
    mul_ne_zero (by norm_num) (softTanhCoordinate_pos hup.1).ne'
  have hrightRaw := hnum.div hden hdenne
  have hres : innerResidual (q, uPlus q) = 0 := by
    rw [innerResidual_eq_exteriorFunction hq hup.2.1]
    exact exteriorEquation_iff_exteriorFunction_eq_zero.1 hup.2.2
  have hright : HasDerivAt
      (fun v => innerResidual (q, v) /
        (2 * softTanhCoordinate v))
      (innerPartialU q (uPlus q) /
        (2 * softTanhCoordinate (uPlus q))) (uPlus q) := by
    convert! hrightRaw using 1
    rw [hres]
    have htne : softTanhCoordinate (uPlus q) ≠ 0 :=
      (softTanhCoordinate_pos hup.1).ne'
    field_simp [htne]
    ring
  have hevent :
      (fun v => softDividedInnerAt q
          (softT (softTanhCoordinate v ^ 2))
          (softT (softW q (softTanhCoordinate v ^ 2)))) =ᶠ[𝓝 (uPlus q)]
        (fun v => innerResidual (q, v) /
          (2 * softTanhCoordinate v)) := by
    filter_upwards [Ioi_mem_nhds hup.1, Iio_mem_nhds hup.2.1] with v hv1 hvq
    exact softDividedInnerAt_tanhCoordinate_sq hq hq1 hv1 hvq
  exact hleft.unique (hright.congr_of_eventuallyEq hevent)

theorem softDividedInnerPartialS_actual_pos {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    0 < softDividedInnerPartialSAt q (softTPrime (oneCutSoftS q))
      (softTPrime (softW q (oneCutSoftS q))) := by
  have hup := uPlus_spec hq hqs
  have hrel := softDividedInnerPartialS_actual_mul_slope_eq hq hqs
  have ht : 0 < softTanhCoordinate (uPlus q) :=
    softTanhCoordinate_pos hup.1
  have hright : 0 < innerPartialU q (uPlus q) /
      (2 * softTanhCoordinate (uPlus q)) :=
    div_pos (innerPartialU_uPlus_pos hq hqs) (mul_pos (by norm_num) ht)
  have hslope := softCoordinateSlope_pos hup.1
  have hprod : 0 <
      softDividedInnerPartialSAt q (softTPrime (oneCutSoftS q))
          (softTPrime (softW q (oneCutSoftS q))) *
        softCoordinateSlope (uPlus q) := by
    rw [hrel]
    exact hright
  nlinarith

theorem hasDerivAt_oneCutSoftS {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    HasDerivAt oneCutSoftS
      (-softDividedInnerPartialQAt q (oneCutSoftS q)
          (softT (softW q (oneCutSoftS q)))
          (softTPrime (softW q (oneCutSoftS q))) /
        softDividedInnerPartialSAt q (softTPrime (oneCutSoftS q))
          (softTPrime (softW q (oneCutSoftS q)))) q := by
  have hup := uPlus_spec hq hqs
  have hcoord := hasDerivAt_softCoordinate_sq
    (by linarith [hup.1] : uPlus q ≠ -1)
  have hu := hasDerivAt_uPlus hq hqs
  have hcomp := hcoord.comp q hu
  have hQ := softDividedInnerPartialQ_actual_eq hq hqs
  have hS := softDividedInnerPartialS_actual_mul_slope_eq hq hqs
  have ht : softTanhCoordinate (uPlus q) ≠ 0 :=
    (softTanhCoordinate_pos hup.1).ne'
  have hU : innerPartialU q (uPlus q) ≠ 0 :=
    (innerPartialU_uPlus_pos hq hqs).ne'
  have hD : softDividedInnerPartialSAt q (softTPrime (oneCutSoftS q))
      (softTPrime (softW q (oneCutSoftS q))) ≠ 0 :=
    (softDividedInnerPartialS_actual_pos hq hqs).ne'
  have hS' := hS
  field_simp [ht] at hS'
  convert! hcomp using 1
  rw [hQ]
  field_simp [ht, hU, hD]
  linear_combination (innerPartialQ q (uPlus q)) * hS'

theorem softC_tanhCoordinate_sq {u : ℝ} (hu0 : u ≠ 0) (hu1 : u ≠ -1) :
    2 * softC (softTanhCoordinate u ^ 2) = reciprocalSum u := by
  unfold softC softTanhCoordinate reciprocalSum
  have hden : u + 1 ≠ 0 := by
    intro hzero
    apply hu1
    linarith
  have htden : 1 - ((u - 1) / (u + 1)) ^ 2 ≠ 0 := by
    intro hzero
    field_simp [hden] at hzero
    apply hu0
    nlinarith
  have hquad : (u + 1) ^ 2 - (u - 1) ^ 2 ≠ 0 := by
    intro hzero
    apply hu0
    nlinarith
  field_simp [hu0, hden, htden]
  ring

theorem softLength_actual_eq_Lambda {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    softLengthAt q (oneCutSoftS q) (zMinus q) = Lambda q := by
  have hup := uPlus_spec hq hqs
  have hum := uMinus_spec hq hqs.le
  have hup0 : uPlus q ≠ 0 := by linarith [hup.1]
  have hupn : uPlus q ≠ -1 := by linarith [hup.1]
  have hum0 : uMinus q ≠ 0 := by
    have := (inv_pos.2 hq).trans hum.1
    linarith
  have hqadd : 1 + q ≠ 0 := by linarith
  have hC : softC (oneCutSoftS q) = reciprocalSum (uPlus q) / 2 := by
    rw [oneCutSoftS]
    nlinarith [softC_tanhCoordinate_sq hup0 hupn]
  rw [softLengthAt, zMinus, scaledH, scaledK, Lambda, H, hC,
    reciprocalSum]
  field_simp [hq.ne', hum0, hup0, hqadd]
  ring

theorem hasDerivAt_softC {s : ℝ} (hs : s ≠ 1) :
    HasDerivAt softC (softCPrime s) s := by
  have hn : HasDerivAt (fun x : ℝ => 1 + x) 1 s := by
    simpa using! (hasDerivAt_const s (1 : ℝ)).add (hasDerivAt_id s)
  have hd : HasDerivAt (fun x : ℝ => 1 - x) (-1) s := by
    simpa using! (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)
  have hden : 1 - s ≠ 0 := sub_ne_zero.2 hs.symm
  convert! hn.div hd hden using 1
  rw [softCPrime]
  field_simp [hden]
  ring

theorem hasDerivAt_softLength_actual {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    HasDerivAt
      (fun r => softLengthAt r (oneCutSoftS r) (zMinus r))
      (softLambdaDerivativeAt q (oneCutSoftS q) (zMinus q)
        (softTPrime (oneCutSoftS q))
        (softT (softW q (oneCutSoftS q)))
        (softTPrime (softW q (oneCutSoftS q)))) q := by
  have hsBounds := oneCutSoftS_mem_Ioo hq hqs
  have hs := hasDerivAt_oneCutSoftS hq hqs
  have hc := (hasDerivAt_softC (ne_of_lt hsBounds.2)).comp q hs
  have hzm := hasDerivAt_zMinus hq hqs
  have hzm0 : zMinus q ≠ 0 := by
    have hz := one_lt_zMinus hq hqs.le
    linarith
  have hqadd : 1 + q ≠ 0 := by linarith
  have hD : softDividedInnerPartialSAt q
      (softTPrime (oneCutSoftS q))
      (softTPrime (softW q (oneCutSoftS q))) ≠ 0 :=
    (softDividedInnerPartialS_actual_pos hq hqs).ne'
  have hOuter : scaledOuterPartialZ q (zMinus q) ≠ 0 := by
    rw [scaledOuterPartialZ_zMinus_eq hq hqs.le]
    exact div_ne_zero (outerPartialU_uMinus_neg hq hqs.le).ne hq.ne'
  have hh := hasDerivAt_scaledH (by linarith : q ≠ -1)
  have hk := hasDerivAt_scaledK (by linarith : q ≠ -1)
  have hH := hasDerivAt_H (by linarith : q ≠ -1)
  have htotal := (hh.mul hzm).add (hk.div hzm hzm0) |>.sub
    ((hH.mul hc).const_mul 2)
  convert! htotal using 1
  · funext r
    simp only [softLengthAt, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.div_apply, Function.comp_apply]
    ring
  · rw [softLambdaDerivativeAt, softLengthPartialQAt,
      softLengthPartialSAt, softLengthPartialZmAt,
      softCPrime, IntervalExpr.scaledZMinusSlopeAt, scaledZMinusSlope]
    simp only [Function.comp_apply]
    field_simp [hzm0, ne_of_lt hsBounds.2, hqadd, hD, hOuter]
    ring

theorem softLambdaDerivativeAt_actual_eq {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    softLambdaDerivativeAt q (oneCutSoftS q) (zMinus q)
        (softTPrime (oneCutSoftS q))
        (softT (softW q (oneCutSoftS q)))
        (softTPrime (softW q (oneCutSoftS q))) =
      LambdaDerivativeFormula q := by
  have hsoft := hasDerivAt_softLength_actual hq hqs
  have hevent :
      (fun r => softLengthAt r (oneCutSoftS r) (zMinus r)) =ᶠ[𝓝 q]
        Lambda := by
    filter_upwards [Ioi_mem_nhds hq, Iio_mem_nhds hqs] with r hr hrs
    exact softLength_actual_eq_Lambda hr hrs
  have hsoft' := hsoft.congr_of_eventuallyEq hevent.symm
  have hLambda := hasDerivAt_Lambda hq hqs
  rw [LambdaDerivative_eq_formula hq hqs] at hLambda
  exact hsoft'.unique hLambda

end

end Erdos1038
