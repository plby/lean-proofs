import ErdosProblems.Erdos1038.LambdaAnalysis

/-!
# Stable scaled derivative for the one-cut certificate

The external verifier works with `z = q * u`, because the outer root `uMinus`
diverges as `q \downarrow 0` whereas `zMinus` stays bounded.  This file gives
the kernel-checked analytic bridge between that chart and
`LambdaDerivativeFormula`.
-/

open Filter Set
open scoped Topology

namespace Erdos1038

noncomputable section

/-- The scaled residual on the inner side `z < 1`, with the absolute value
resolved. -/
def scaledInnerResidual (p : ℝ × ℝ) : ℝ :=
  A p.1 * Real.log ((p.2 - p.1 ^ 2) / (1 - p.2)) -
    Real.log p.2 - scaledD p.1

/-- The scaled residual on the outer side `1 < z`, with the absolute value
resolved. -/
def scaledOuterResidual (p : ℝ × ℝ) : ℝ :=
  A p.1 * Real.log ((p.2 - p.1 ^ 2) / (p.2 - 1)) -
    Real.log p.2 - scaledD p.1

def scaledInnerPartialZ (q z : ℝ) : ℝ :=
  A q * (1 / (z - q ^ 2) + 1 / (1 - z)) - 1 / z

def scaledOuterPartialZ (q z : ℝ) : ℝ :=
  A q * (1 / (z - q ^ 2) - 1 / (z - 1)) - 1 / z

def scaledDprime (q : ℝ) : ℝ := -2 / (1 + q)

def scaledInnerPartialQ (q z : ℝ) : ℝ :=
  Aprime q * Real.log ((z - q ^ 2) / (1 - z)) -
    A q * (2 * q) / (z - q ^ 2) - scaledDprime q

def scaledOuterPartialQ (q z : ℝ) : ℝ :=
  Aprime q * Real.log ((z - q ^ 2) / (z - 1)) -
    A q * (2 * q) / (z - q ^ 2) - scaledDprime q

def scaledZPlusSlope (q : ℝ) : ℝ :=
  -scaledInnerPartialQ q (zPlus q) / scaledInnerPartialZ q (zPlus q)

def scaledZMinusSlope (q : ℝ) : ℝ :=
  -scaledOuterPartialQ q (zMinus q) / scaledOuterPartialZ q (zMinus q)

def scaledH (q : ℝ) : ℝ := 2 / (1 + q) ^ 2

def scaledK (q : ℝ) : ℝ := 2 * q ^ 2 / (1 + q) ^ 2

def scaledHprime (q : ℝ) : ℝ := -4 / (1 + q) ^ 3

def scaledKprime (q : ℝ) : ℝ := 4 * q / (1 + q) ^ 3

/-- The first derivative evaluated entirely in the bounded scaled-root chart. -/
def scaledLambdaDerivativeFormula (q : ℝ) : ℝ :=
  scaledHprime q * (zMinus q - zPlus q) +
    scaledH q * (scaledZMinusSlope q - scaledZPlusSlope q) +
    scaledKprime q * ((zMinus q)⁻¹ - (zPlus q)⁻¹) +
    scaledK q *
      (-scaledZMinusSlope q / zMinus q ^ 2 +
        scaledZPlusSlope q / zPlus q ^ 2)

theorem scaledInnerResidual_eq_scaledResidual {q z : ℝ} (hz : z < 1) :
    scaledInnerResidual (q, z) = scaledResidual q z := by
  rw [scaledInnerResidual, scaledResidual, abs_of_pos (sub_pos.mpr hz)]

theorem scaledOuterResidual_eq_scaledResidual {q z : ℝ} (hz : 1 < z) :
    scaledOuterResidual (q, z) = scaledResidual q z := by
  rw [scaledOuterResidual, scaledResidual, abs_of_neg (sub_neg.mpr hz)]
  congr 3
  ring_nf

theorem hasDerivAt_scaledD {q : ℝ} (hq : q ≠ -1) :
    HasDerivAt scaledD (scaledDprime q) q := by
  have hden : 1 + q ≠ 0 := by
    intro h
    apply hq
    linarith
  have hbase : HasDerivAt (fun x : ℝ ↦ 2 / (1 + x) ^ 2)
      (-4 / (1 + q) ^ 3) q := by
    have hadd : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 q := by
      simpa using! (hasDerivAt_const q (1 : ℝ)).add (hasDerivAt_id q)
    have hpow := hadd.pow 2
    have hconst := hasDerivAt_const q (2 : ℝ)
    have hquot := hconst.div hpow (pow_ne_zero 2 hden)
    convert! hquot using 1
    · simp only [Pi.pow_apply]
      field_simp [hden]
      ring
  unfold scaledD scaledDprime
  have hlog := hbase.log (by positivity : 2 / (1 + q) ^ 2 ≠ 0)
  convert! hlog using 1
  field_simp [hden]
  ring

theorem contDiffAt_scaledD {q : ℝ} (hq : q ≠ -1) :
    ContDiffAt ℝ ⊤ scaledD q := by
  have hbase : 1 + q ≠ 0 := by
    intro h
    apply hq
    linarith
  have hden : (1 + q) ^ 2 ≠ 0 := pow_ne_zero 2 hbase
  unfold scaledD
  have hnum : ContDiffAt ℝ ⊤ (fun _ : ℝ ↦ (2 : ℝ)) q := contDiffAt_const
  have hadd : ContDiffAt ℝ ⊤ (fun x : ℝ ↦ 1 + x) q :=
    contDiffAt_const.add contDiffAt_id
  exact (hnum.div (hadd.pow 2) hden).log
    (by positivity : 2 / (1 + q) ^ 2 ≠ 0)

theorem contDiffAt_scaledInnerResidual {q z : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hz0 : 0 < z)
    (hqz : q ^ 2 < z) (hz1 : z < 1) :
    ContDiffAt ℝ ⊤ scaledInnerResidual (q, z) := by
  have hnum : z - q ^ 2 ≠ 0 := (sub_pos.mpr hqz).ne'
  have hden : 1 - z ≠ 0 := (sub_pos.mpr hz1).ne'
  have harg : (z - q ^ 2) / (1 - z) ≠ 0 := div_ne_zero hnum hden
  have hA : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ ↦ A p.1) (q, z) :=
    (contDiffAt_A hq hq1).comp (q, z) contDiffAt_fst
  have hnumcd : ContDiffAt ℝ ⊤
      (fun p : ℝ × ℝ ↦ p.2 - p.1 ^ 2) (q, z) :=
    contDiffAt_snd.sub (contDiffAt_fst.pow 2)
  have hdencd : ContDiffAt ℝ ⊤
      (fun p : ℝ × ℝ ↦ 1 - p.2) (q, z) :=
    contDiffAt_const.sub contDiffAt_snd
  have hlogarg := (hnumcd.div hdencd hden).log harg
  have hsnd : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ ↦ p.2) (q, z) := contDiffAt_snd
  have hlogz := hsnd.log hz0.ne'
  have hD := (contDiffAt_scaledD (by linarith : q ≠ -1)).comp
    (q, z) contDiffAt_fst
  exact (hA.mul hlogarg).sub hlogz |>.sub hD

theorem contDiffAt_scaledOuterResidual {q z : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hqz : q ^ 2 < z) (hz1 : 1 < z) :
    ContDiffAt ℝ ⊤ scaledOuterResidual (q, z) := by
  have hnum : z - q ^ 2 ≠ 0 := (sub_pos.mpr hqz).ne'
  have hden : z - 1 ≠ 0 := (sub_pos.mpr hz1).ne'
  have harg : (z - q ^ 2) / (z - 1) ≠ 0 := div_ne_zero hnum hden
  have hA : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ ↦ A p.1) (q, z) :=
    (contDiffAt_A hq hq1).comp (q, z) contDiffAt_fst
  have hnumcd : ContDiffAt ℝ ⊤
      (fun p : ℝ × ℝ ↦ p.2 - p.1 ^ 2) (q, z) :=
    contDiffAt_snd.sub (contDiffAt_fst.pow 2)
  have hdencd : ContDiffAt ℝ ⊤
      (fun p : ℝ × ℝ ↦ p.2 - 1) (q, z) :=
    contDiffAt_snd.sub contDiffAt_const
  have hlogarg := (hnumcd.div hdencd hden).log harg
  have hsnd : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ ↦ p.2) (q, z) := contDiffAt_snd
  have hlogz := hsnd.log (by linarith : z ≠ 0)
  have hD := (contDiffAt_scaledD (by linarith : q ≠ -1)).comp
    (q, z) contDiffAt_fst
  exact (hA.mul hlogarg).sub hlogz |>.sub hD

theorem hasDerivAt_scaledInnerResidual_right {q z : ℝ}
    (hz0 : 0 < z) (hqz : q ^ 2 < z) (hz1 : z < 1) :
    HasDerivAt (fun w : ℝ ↦ scaledInnerResidual (q, w))
      (scaledInnerPartialZ q z) z := by
  have hnum : z - q ^ 2 ≠ 0 := (sub_pos.mpr hqz).ne'
  have hden : 1 - z ≠ 0 := (sub_pos.mpr hz1).ne'
  have harg : (z - q ^ 2) / (1 - z) ≠ 0 := div_ne_zero hnum hden
  have hn := (hasDerivAt_id z).sub_const (q ^ 2)
  have hd := (hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id z)
  have hlog := (hn.div hd hden).log harg
  have hmain := hlog.const_mul (A q)
  have hzlog := Real.hasDerivAt_log hz0.ne'
  have h := (hmain.sub hzlog).sub_const (scaledD q)
  convert! h using 1
  · rw [scaledInnerPartialZ]
    simp only [Pi.sub_apply, Pi.div_apply, id_eq]
    field_simp [hnum, hden, hz0.ne']
    ring

theorem hasDerivAt_scaledOuterResidual_right {q z : ℝ}
    (hqz : q ^ 2 < z) (hz1 : 1 < z) :
    HasDerivAt (fun w : ℝ ↦ scaledOuterResidual (q, w))
      (scaledOuterPartialZ q z) z := by
  have hnum : z - q ^ 2 ≠ 0 := (sub_pos.mpr hqz).ne'
  have hden : z - 1 ≠ 0 := (sub_pos.mpr hz1).ne'
  have hn := (hasDerivAt_id z).sub_const (q ^ 2)
  have hd := (hasDerivAt_id z).sub_const 1
  have harg : (z - q ^ 2) / (z - 1) ≠ 0 := div_ne_zero hnum hden
  have hlog := (hn.div hd hden).log harg
  have hmain := hlog.const_mul (A q)
  have hzlog := Real.hasDerivAt_log (by linarith : z ≠ 0)
  have h := (hmain.sub hzlog).sub_const (scaledD q)
  convert! h using 1
  · rw [scaledOuterPartialZ]
    simp only [Pi.div_apply, id_eq]
    field_simp [hnum, hden, (by linarith : z ≠ 0)]

theorem hasDerivAt_scaledInnerResidual_left {q z : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hqz : q ^ 2 < z) (hz1 : z < 1) :
    HasDerivAt (fun r : ℝ ↦ scaledInnerResidual (r, z))
      (scaledInnerPartialQ q z) q := by
  have hnum : z - q ^ 2 ≠ 0 := (sub_pos.mpr hqz).ne'
  have hden : 1 - z ≠ 0 := (sub_pos.mpr hz1).ne'
  have harg : (z - q ^ 2) / (1 - z) ≠ 0 := div_ne_zero hnum hden
  have hn : HasDerivAt (fun r : ℝ ↦ z - r ^ 2) (-2 * q) q := by
    convert! (hasDerivAt_const q z).sub ((hasDerivAt_id q).pow 2) using 1
    simp
  have hquot := hn.div_const (1 - z)
  have hlog := hquot.log harg
  have hmain := (hasDerivAt_A hq hq1).mul hlog
  have h := (hmain.sub_const (Real.log z)).sub
    (hasDerivAt_scaledD (by linarith : q ≠ -1))
  convert! h using 1
  · rw [scaledInnerPartialQ]
    field_simp [hnum, hden]
    ring

theorem hasDerivAt_scaledOuterResidual_left {q z : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hqz : q ^ 2 < z) (hz1 : 1 < z) :
    HasDerivAt (fun r : ℝ ↦ scaledOuterResidual (r, z))
      (scaledOuterPartialQ q z) q := by
  have hnum : z - q ^ 2 ≠ 0 := (sub_pos.mpr hqz).ne'
  have hden : z - 1 ≠ 0 := (sub_pos.mpr hz1).ne'
  have harg : (z - q ^ 2) / (z - 1) ≠ 0 := div_ne_zero hnum hden
  have hn : HasDerivAt (fun r : ℝ ↦ z - r ^ 2) (-2 * q) q := by
    convert! (hasDerivAt_const q z).sub ((hasDerivAt_id q).pow 2) using 1
    simp
  have hquot := hn.div_const (z - 1)
  have hlog := hquot.log harg
  have hmain := (hasDerivAt_A hq hq1).mul hlog
  have h := (hmain.sub_const (Real.log z)).sub
    (hasDerivAt_scaledD (by linarith : q ≠ -1))
  convert! h using 1
  · rw [scaledOuterPartialQ]
    field_simp [hnum, hden]
    ring

theorem zPlus_sq_q_lt {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    q ^ 2 < zPlus q := by
  rw [zPlus, pow_two]
  exact mul_lt_mul_of_pos_left
    ((q_lt_one_of_pos_le_qSoft hq hqs.le).trans (uPlus_spec hq hqs).1) hq

theorem zMinus_sq_q_lt {q : ℝ} (hq : 0 < q) (hqs : q ≤ qSoft) :
    q ^ 2 < zMinus q := by
  rw [zMinus, pow_two]
  exact mul_lt_mul_of_pos_left
    ((q_lt_one_of_pos_le_qSoft hq hqs).trans (one_lt_inv_q hq
      (q_lt_one_of_pos_le_qSoft hq hqs)) |>.trans (uMinus_spec hq hqs).1) hq

theorem scaledInnerPartialZ_zPlus_eq {q : ℝ} (hq : 0 < q)
    (hqs : q < qSoft) :
    scaledInnerPartialZ q (zPlus q) = innerPartialU q (uPlus q) / q := by
  have hu0 : uPlus q ≠ 0 :=
    ((show (0 : ℝ) < 1 by norm_num).trans (uPlus_spec hq hqs).1).ne'
  have huq : uPlus q - q ≠ 0 := by
    have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
    exact (sub_pos.mpr (hq1.trans (uPlus_spec hq hqs).1)).ne'
  have hqu : 1 - q * uPlus q ≠ 0 := by
    have hlt := (uPlus_spec hq hqs).2.1
    have := mul_lt_mul_of_pos_left hlt hq
    rw [mul_inv_cancel₀ hq.ne'] at this
    linarith
  rw [scaledInnerPartialZ, zPlus, innerPartialU, innerNumerator, exteriorB]
  field_simp [hq.ne', hu0, huq, hqu]
  ring

theorem scaledOuterPartialZ_zMinus_eq {q : ℝ} (hq : 0 < q)
    (hqs : q ≤ qSoft) :
    scaledOuterPartialZ q (zMinus q) = outerPartialU q (uMinus q) / q := by
  have hu0 : uMinus q ≠ 0 :=
    ((inv_pos.mpr hq).trans (uMinus_spec hq hqs).1).ne'
  have huq : uMinus q - q ≠ 0 := by
    have hq1 := q_lt_one_of_pos_le_qSoft hq hqs
    exact (sub_pos.mpr (hq1.trans (one_lt_inv_q hq hq1) |>.trans
      (uMinus_spec hq hqs).1)).ne'
  have hqu : q * uMinus q - 1 ≠ 0 := by
    have hlt := (uMinus_spec hq hqs).1
    have := mul_lt_mul_of_pos_left hlt hq
    rw [mul_inv_cancel₀ hq.ne'] at this
    linarith
  rw [scaledOuterPartialZ, zMinus, outerPartialU]
  field_simp [hq.ne', hu0, huq, hqu]
  ring

theorem hasDerivAt_zPlus {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    HasDerivAt zPlus (scaledZPlusSlope q) q := by
  have hz : HasDerivAt zPlus
      (uPlus q + q * uPlusSlopeFormula q) q := by
    have hu : HasDerivAt uPlus (uPlusSlope q) q := by
      simpa only [uPlusSlope] using! hasDerivAt_uPlus hq hqs
    rw [uPlusSlope_eq_formula hq hqs] at hu
    simpa only [zPlus, one_mul] using! (hasDerivAt_id q).mul hu
  have hzp0 := zPlus_pos hq hqs
  have hzq := zPlus_sq_q_lt hq hqs
  have hz1 := zPlus_lt_one hq hqs
  have hf : HasFDerivAt scaledInnerResidual
      (fderiv ℝ scaledInnerResidual (q, zPlus q)) (q, zPlus q) :=
    ((contDiffAt_scaledInnerResidual hq
      (q_lt_one_of_pos_le_qSoft hq hqs.le) hzp0 hzq hz1).differentiableAt
      (by simp)).hasFDerivAt
  have hx := hasDerivAt_scaledInnerResidual_left hq
    (q_lt_one_of_pos_le_qSoft hq hqs.le) hzq hz1
  have hy := hasDerivAt_scaledInnerResidual_right hzp0 hzq hz1
  have heq : (fun r : ℝ ↦ scaledInnerResidual (r, zPlus r)) =ᶠ[𝓝 q]
      fun _ ↦ scaledInnerResidual (q, zPlus q) := by
    filter_upwards [Ioi_mem_nhds hq, Iio_mem_nhds hqs] with r hr0 hrs
    rw [scaledInnerResidual_eq_scaledResidual (zPlus_lt_one hr0 hrs),
      scaledResidual_zPlus hr0 hrs,
      scaledInnerResidual_eq_scaledResidual hz1,
      scaledResidual_zPlus hq hqs]
  have hvertical : scaledInnerPartialZ q (zPlus q) ≠ 0 := by
    rw [scaledInnerPartialZ_zPlus_eq hq hqs]
    exact div_ne_zero (innerPartialU_uPlus_pos hq hqs).ne' hq.ne'
  have hslope' := implicit_derivative_eq hf hx hy hz rfl heq hvertical
  convert! hz using 1
  rw [scaledZPlusSlope, hslope']

theorem hasDerivAt_zMinus {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    HasDerivAt zMinus (scaledZMinusSlope q) q := by
  have hz : HasDerivAt zMinus
      (uMinus q + q * uMinusSlopeFormula q) q := by
    have hu : HasDerivAt uMinus (uMinusSlope q) q := by
      simpa only [uMinusSlope] using! hasDerivAt_uMinus hq hqs
    rw [uMinusSlope_eq_formula hq hqs] at hu
    simpa only [zMinus, one_mul] using! (hasDerivAt_id q).mul hu
  have hz1 := one_lt_zMinus hq hqs.le
  have hzq := zMinus_sq_q_lt hq hqs.le
  have hf : HasFDerivAt scaledOuterResidual
      (fderiv ℝ scaledOuterResidual (q, zMinus q)) (q, zMinus q) :=
    ((contDiffAt_scaledOuterResidual hq
      (q_lt_one_of_pos_le_qSoft hq hqs.le) hzq hz1).differentiableAt
      (by simp)).hasFDerivAt
  have hx := hasDerivAt_scaledOuterResidual_left hq
    (q_lt_one_of_pos_le_qSoft hq hqs.le) hzq hz1
  have hy := hasDerivAt_scaledOuterResidual_right hzq hz1
  have heq : (fun r : ℝ ↦ scaledOuterResidual (r, zMinus r)) =ᶠ[𝓝 q]
      fun _ ↦ scaledOuterResidual (q, zMinus q) := by
    filter_upwards [Ioi_mem_nhds hq, Iio_mem_nhds hqs] with r hr0 hrs
    rw [scaledOuterResidual_eq_scaledResidual (one_lt_zMinus hr0 hrs.le),
      scaledResidual_zMinus hr0 hrs.le,
      scaledOuterResidual_eq_scaledResidual hz1,
      scaledResidual_zMinus hq hqs.le]
  have hvertical : scaledOuterPartialZ q (zMinus q) ≠ 0 := by
    rw [scaledOuterPartialZ_zMinus_eq hq hqs.le]
    exact div_ne_zero (outerPartialU_uMinus_neg hq hqs.le).ne hq.ne'
  have hslope := implicit_derivative_eq hf hx hy hz rfl heq hvertical
  convert! hz using 1
  rw [scaledZMinusSlope, hslope]

theorem hasDerivAt_scaledH {q : ℝ} (hq : q ≠ -1) :
    HasDerivAt scaledH (scaledHprime q) q := by
  have hden : 1 + q ≠ 0 := by
    intro h
    apply hq
    linarith
  unfold scaledH scaledHprime
  have h := (hasDerivAt_const q (2 : ℝ)).div
    (((hasDerivAt_const q (1 : ℝ)).add (hasDerivAt_id q)).pow 2)
      (pow_ne_zero 2 hden)
  convert! h using 1
  simp only [Pi.pow_apply, Pi.add_apply, id_eq]
  field_simp [hden]
  ring

theorem hasDerivAt_scaledK {q : ℝ} (hq : q ≠ -1) :
    HasDerivAt scaledK (scaledKprime q) q := by
  have hden : 1 + q ≠ 0 := by
    intro h
    apply hq
    linarith
  unfold scaledK scaledKprime
  have hnum := (hasDerivAt_id q).pow 2 |>.const_mul 2
  have hdenD := ((hasDerivAt_const q (1 : ℝ)).add (hasDerivAt_id q)).pow 2
  have h := hnum.div hdenD (pow_ne_zero 2 hden)
  convert! h using 1
  simp only [Pi.pow_apply, Pi.add_apply, id_eq]
  field_simp [hden]
  ring

theorem LambdaDerivativeFormula_eq_scaled {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    LambdaDerivativeFormula q = scaledLambdaDerivativeFormula q := by
  have hevent : Lambda =ᶠ[𝓝 q]
      fun r ↦ scaledLambdaExpression r (zPlus r) (zMinus r) := by
    filter_upwards [Ioi_mem_nhds hq, Iio_mem_nhds hqs] with r hr0 hrs
    exact Lambda_eq_scaledLambdaExpression hr0 hrs
  have hzp := hasDerivAt_zPlus hq hqs
  have hzm := hasDerivAt_zMinus hq hqs
  have hh := hasDerivAt_scaledH (by linarith : q ≠ -1)
  have hk := hasDerivAt_scaledK (by linarith : q ≠ -1)
  have hdiff := hzm.sub hzp
  have hinvm := hasDerivAt_inv
    ((show (0 : ℝ) < 1 by norm_num).trans (one_lt_zMinus hq hqs.le)).ne' |>.comp q hzm
  have hinvp := hasDerivAt_inv (ne_of_gt (zPlus_pos hq hqs)) |>.comp q hzp
  have hscaled : HasDerivAt
      (fun r ↦ scaledLambdaExpression r (zPlus r) (zMinus r))
      (scaledLambdaDerivativeFormula q) q := by
    have hmain := hh.mul hdiff
    have hsmall := hk.mul (hinvm.sub hinvp)
    have hsum := hmain.add hsmall
    convert! hsum using 1
    funext r
    simp only [scaledLambdaExpression, scaledH, scaledK, Pi.add_apply,
      Pi.mul_apply, Pi.sub_apply, Function.comp_apply]
    ring
    unfold scaledLambdaDerivativeFormula
    simp only [Pi.sub_apply, Function.comp_apply]
    ring
  have hLambda : HasDerivAt Lambda (scaledLambdaDerivativeFormula q) q :=
    hscaled.congr_of_eventuallyEq hevent
  have horig := hasDerivAt_Lambda hq hqs
  rw [LambdaDerivative_eq_formula hq hqs] at horig
  exact horig.unique hLambda

end

end Erdos1038
