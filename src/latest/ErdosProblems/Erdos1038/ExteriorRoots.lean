import ErdosProblems.Erdos1038.OneCutElementary

/-!
# Exterior roots in the one-cut parametrization

This file formalizes the scalar exterior equation studied in Section 6 of
the manuscript.  We work with its residual `exteriorFunction`; its zero set
is exactly `exteriorEquation`.
-/

open Set Filter
open scoped Topology

namespace Erdos1038

noncomputable section

/-- The residual in the exterior crossing equation. -/
def exteriorFunction (q u : ℝ) : ℝ :=
  A q * Real.log ((u - q) / |1 - q * u|) - Real.log u

theorem exteriorEquation_iff_exteriorFunction_eq_zero {q u : ℝ} :
    exteriorEquation q u ↔ exteriorFunction q u = 0 := by
  rw [exteriorEquation, exteriorFunction, sub_eq_zero]

theorem q_mem_Ioo_of_pos_le_qSoft {q : ℝ} (hq : 0 < q) (hqs : q ≤ qSoft) :
    q ∈ Ioo (0 : ℝ) qCeiling :=
  ⟨hq, hqs.trans_lt qSoft_mem_Ioo.2⟩

theorem q_lt_one_of_pos_le_qSoft {q : ℝ} (hq : 0 < q) (hqs : q ≤ qSoft) : q < 1 :=
  mem_Ioo_zero_qCeiling_imp_lt_one (q_mem_Ioo_of_pos_le_qSoft hq hqs)

theorem A_pos_of_pos_le_qSoft {q : ℝ} (hq : 0 < q) (hqs : q ≤ qSoft) : 0 < A q :=
  A_pos_of_mem_Ioo (q_mem_Ioo_of_pos_le_qSoft hq hqs)

theorem A_lt_s_of_pos_lt_qSoft {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    A q < s q := by
  have hqdom : q ∈ Ioo (0 : ℝ) qCeiling :=
    q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hf : softFunction qSoft < softFunction q :=
    softFunction_strictAntiOn_Ioo_zero_qCeiling hqdom qSoft_mem_Ioo hqs
  exact (A_lt_s_iff_softFunction_pos hq
    (mem_Ioo_zero_qCeiling_imp_lt_one hqdom)).2 (by
      rw [softFunction_qSoft_eq_zero] at hf
      exact hf)

theorem A_le_s_of_pos_le_qSoft {q : ℝ} (hq : 0 < q) (hqs : q ≤ qSoft) :
    A q ≤ s q := by
  rcases hqs.eq_or_lt with rfl | hlt
  · exact A_qSoft_eq_s_qSoft.le
  · exact (A_lt_s_of_pos_lt_qSoft hq hlt).le

/-! ## Algebra and differentiation away from the pole -/

theorem abs_one_sub_q_mul_of_lt_inv {q u : ℝ} (hq : 0 < q) (hu : u < q⁻¹) :
    |1 - q * u| = 1 - q * u := by
  rw [abs_of_pos]
  have hmul := mul_lt_mul_of_pos_left hu hq
  rw [mul_inv_cancel₀ hq.ne'] at hmul
  linarith

theorem abs_one_sub_q_mul_of_inv_lt {q u : ℝ} (hq : 0 < q) (hu : q⁻¹ < u) :
    |1 - q * u| = q * u - 1 := by
  rw [abs_of_neg]
  · ring
  rw [sub_neg]
  have hmul := mul_lt_mul_of_pos_left hu hq
  rw [mul_inv_cancel₀ hq.ne'] at hmul
  linarith

theorem inv_q_pos {q : ℝ} (hq : 0 < q) : 0 < q⁻¹ := inv_pos.mpr hq

theorem one_lt_inv_q {q : ℝ} (hq : 0 < q) (hq1 : q < 1) : 1 < q⁻¹ := by
  exact (one_lt_inv₀ hq).2 hq1

theorem hasDerivAt_exteriorFunction_inner {q u : ℝ}
    (hq : 0 < q) (hu : 0 < u) (hqu_lower : q < u)
    (huq : u < q⁻¹) :
    HasDerivAt (exteriorFunction q)
      ((q * u ^ 2 - (1 + q ^ 2 - A q * (1 - q ^ 2)) * u + q) /
        (u * (u - q) * (1 - q * u))) u := by
  have hqu : 0 < 1 - q * u := by
    have hmul := mul_lt_mul_of_pos_left huq hq
    rw [mul_inv_cancel₀ hq.ne'] at hmul
    linarith
  have huqpos : 0 < u - q := sub_pos.mpr hqu_lower
  have habs_ne : |1 - q * u| ≠ 0 := (abs_pos.mpr hqu.ne').ne'
  have harg_pos : 0 < (u - q) / |1 - q * u| :=
    div_pos huqpos (abs_pos.mpr hqu.ne')
  have hnum : HasDerivAt (fun x : ℝ ↦ x - q) 1 u :=
    (hasDerivAt_id u).sub_const q
  have hlin : HasDerivAt (fun x : ℝ ↦ 1 - q * x) (-q) u := by
    simpa using! (hasDerivAt_const u (1 : ℝ)).sub
      ((hasDerivAt_id u).const_mul q)
  have habs : HasDerivAt (fun x : ℝ ↦ |1 - q * x|) (-q) u := by
    simpa [Function.comp_def] using! (hasDerivAt_abs_pos hqu).comp u hlin
  have hquot := hnum.div habs habs_ne
  have hlog := hquot.log harg_pos.ne'
  have hmain := hlog.const_mul (A q)
  have hres := hmain.sub (Real.hasDerivAt_log hu.ne')
  convert! hres using 1
  simp only [Pi.div_apply]
  rw [abs_of_pos hqu]
  field_simp [hu.ne', huqpos.ne', hqu.ne']
  ring

theorem hasDerivAt_exteriorFunction_outer {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (huq : q⁻¹ < u) :
    HasDerivAt (exteriorFunction q)
      (-A q * (1 - q ^ 2) / ((u - q) * (q * u - 1)) - 1 / u) u := by
  have hinvpos : 0 < q⁻¹ := inv_pos.mpr hq
  have hu : 0 < u := hinvpos.trans huq
  have hqu : 0 < q * u - 1 := by
    have hmul := mul_lt_mul_of_pos_left huq hq
    rw [mul_inv_cancel₀ hq.ne'] at hmul
    linarith
  have huqpos : 0 < u - q := by
    have hqinv : q < q⁻¹ :=
      hq1.trans (one_lt_inv_q hq hq1)
    linarith
  have habs_ne : |1 - q * u| ≠ 0 := by
    rw [abs_one_sub_q_mul_of_inv_lt hq huq]
    exact hqu.ne'
  have harg_pos : 0 < (u - q) / |1 - q * u| := by
    rw [abs_one_sub_q_mul_of_inv_lt hq huq]
    exact div_pos huqpos hqu
  have hnum : HasDerivAt (fun x : ℝ ↦ x - q) 1 u :=
    (hasDerivAt_id u).sub_const q
  have hlin : HasDerivAt (fun x : ℝ ↦ 1 - q * x) (-q) u := by
    simpa using! (hasDerivAt_const u (1 : ℝ)).sub
      ((hasDerivAt_id u).const_mul q)
  have habs : HasDerivAt (fun x : ℝ ↦ |1 - q * x|) q u := by
    simpa [Function.comp_def] using!
      (hasDerivAt_abs_neg (by linarith : 1 - q * u < 0)).comp u hlin
  have hquot := hnum.div habs habs_ne
  have hlog := hquot.log harg_pos.ne'
  have hmain := hlog.const_mul (A q)
  have hres := hmain.sub (Real.hasDerivAt_log hu.ne')
  convert! hres using 1
  simp only [Pi.div_apply]
  rw [abs_one_sub_q_mul_of_inv_lt hq huq]
  field_simp [hu.ne', huqpos.ne', hqu.ne']
  ring

theorem exteriorFunction_outer_deriv_neg {q u : ℝ}
    (hq : 0 < q) (hqs : q ≤ qSoft) (huq : q⁻¹ < u) :
    deriv (exteriorFunction q) u < 0 := by
  rw [(hasDerivAt_exteriorFunction_outer hq
    (q_lt_one_of_pos_le_qSoft hq hqs) huq).deriv]
  have hA : 0 < A q := A_pos_of_pos_le_qSoft hq hqs
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs
  have hfirst : -A q * (1 - q ^ 2) / ((u - q) * (q * u - 1)) < 0 := by
    have hqinv : q < q⁻¹ := hq1.trans (one_lt_inv_q hq hq1)
    have huqpos : 0 < u - q := by linarith
    have hqupos : 0 < q * u - 1 := by
      have hmul := mul_lt_mul_of_pos_left huq hq
      rw [mul_inv_cancel₀ hq.ne'] at hmul
      linarith
    have hden : 0 < (u - q) * (q * u - 1) := mul_pos huqpos hqupos
    have hnum : -A q * (1 - q ^ 2) < 0 :=
      mul_neg_of_neg_of_pos (neg_neg_of_pos hA) (by nlinarith)
    exact div_neg_of_neg_of_pos hnum hden
  have hu : 0 < u := (inv_pos.mpr hq).trans huq
  have hsecond : -(1 / u) < 0 := neg_neg_of_pos (one_div_pos.mpr hu)
  linarith

theorem exteriorFunction_continuousOn_outer {q : ℝ}
    (hq : 0 < q) (hqs : q ≤ qSoft) :
    ContinuousOn (exteriorFunction q) (Ioi q⁻¹) := by
  intro u hu
  exact (hasDerivAt_exteriorFunction_outer hq
    (q_lt_one_of_pos_le_qSoft hq hqs) hu).continuousAt.continuousWithinAt

theorem exteriorFunction_strictAntiOn_outer {q : ℝ}
    (hq : 0 < q) (hqs : q ≤ qSoft) :
    StrictAntiOn (exteriorFunction q) (Ioi q⁻¹) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi q⁻¹)
    (exteriorFunction_continuousOn_outer hq hqs)
  rw [interior_Ioi]
  intro u hu
  exact exteriorFunction_outer_deriv_neg hq hqs hu

/-! ## The unique critical point on the inner component -/

/-- The coefficient `B(q)` from equation (6.7). -/
def exteriorB (q : ℝ) : ℝ := 1 + q ^ 2 - A q * (1 - q ^ 2)

/-- The numerator of the inner derivative in equation (6.7). -/
def innerNumerator (q u : ℝ) : ℝ := q * u ^ 2 - exteriorB q * u + q

/-- The larger root of the reciprocal quadratic `innerNumerator`. -/
def innerCritical (q : ℝ) : ℝ :=
  (exteriorB q + Real.sqrt ((exteriorB q) ^ 2 - 4 * q ^ 2)) / (2 * q)

theorem exteriorB_gt_two_mul {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    2 * q < exteriorB q := by
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hAs : A q < s q := A_lt_s_of_pos_lt_qSoft hq hqs
  have hden : 1 + q ≠ 0 := by linarith
  have hsidentity : s q * (1 - q ^ 2) = (1 - q) ^ 2 := by
    rw [s]
    field_simp [hden]
    ring
  rw [exteriorB]
  have hd : 0 < 1 - q ^ 2 := by nlinarith
  nlinarith [mul_lt_mul_of_pos_right hAs hd]

theorem exteriorB_lt_two {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    exteriorB q < 2 := by
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hA : 0 < A q := A_pos_of_pos_le_qSoft hq hqs.le
  rw [exteriorB]
  have hd : 0 < 1 - q ^ 2 := by nlinarith
  nlinarith [mul_pos hA hd]

theorem innerDiscriminant_pos {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    0 < (exteriorB q) ^ 2 - 4 * q ^ 2 := by
  have hB := exteriorB_gt_two_mul hq hqs
  nlinarith [sq_pos_of_pos hq]

theorem innerCritical_gt_one {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    1 < innerCritical q := by
  have hB := exteriorB_gt_two_mul hq hqs
  have hsqrt : 0 < Real.sqrt ((exteriorB q) ^ 2 - 4 * q ^ 2) :=
    Real.sqrt_pos.2 (innerDiscriminant_pos hq hqs)
  rw [innerCritical, lt_div_iff₀ (by positivity : 0 < 2 * q)]
  nlinarith

theorem innerCritical_lt_inv {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    innerCritical q < q⁻¹ := by
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hA : 0 < A q := A_pos_of_pos_le_qSoft hq hqs.le
  have hd : 0 < 1 - q ^ 2 := by nlinarith
  have hB2 : exteriorB q < 2 := exteriorB_lt_two hq hqs
  have hsq : (exteriorB q) ^ 2 - 4 * q ^ 2 < (2 - exteriorB q) ^ 2 := by
    rw [exteriorB]
    nlinarith [mul_pos hA hd]
  have hsqrt : Real.sqrt ((exteriorB q) ^ 2 - 4 * q ^ 2) < 2 - exteriorB q :=
    (Real.sqrt_lt' (by linarith)).2 hsq
  rw [innerCritical, div_lt_iff₀ (by positivity : 0 < 2 * q)]
  field_simp [hq.ne']
  nlinarith

theorem innerNumerator_innerCritical {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    innerNumerator q (innerCritical q) = 0 := by
  have hdisc : 0 ≤ (exteriorB q) ^ 2 - 4 * q ^ 2 :=
    (innerDiscriminant_pos hq hqs).le
  have hsqrt := Real.sq_sqrt hdisc
  rw [innerNumerator, innerCritical]
  field_simp [hq.ne']
  ring_nf at hsqrt ⊢
  nlinarith

theorem innerCritical_ne_zero {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    innerCritical q ≠ 0 := (lt_trans (by norm_num) (innerCritical_gt_one hq hqs)).ne'

theorem exteriorB_eq_q_mul_critical_add_inv {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    exteriorB q = q * (innerCritical q + (innerCritical q)⁻¹) := by
  have hroot := innerNumerator_innerCritical hq hqs
  rw [innerNumerator] at hroot
  field_simp [innerCritical_ne_zero hq hqs]
  nlinarith

theorem innerNumerator_factor {q u : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    innerNumerator q u =
      q * (u - innerCritical q) * (u - (innerCritical q)⁻¹) := by
  rw [innerNumerator, exteriorB_eq_q_mul_critical_add_inv hq hqs]
  field_simp [innerCritical_ne_zero hq hqs]
  ring

theorem innerCritical_inv_lt_one {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    (innerCritical q)⁻¹ < 1 := by
  have hcpos : 0 < innerCritical q :=
    (by norm_num : (0 : ℝ) < 1).trans (innerCritical_gt_one hq hqs)
  exact (inv_lt_one₀ hcpos).2 (innerCritical_gt_one hq hqs)

theorem innerNumerator_neg_before_critical {q u : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) (hu1 : 1 < u) (huc : u < innerCritical q) :
    innerNumerator q u < 0 := by
  rw [innerNumerator_factor hq hqs]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hq (sub_neg.mpr huc))
    (sub_pos.mpr ((innerCritical_inv_lt_one hq hqs).trans hu1))

theorem innerNumerator_pos_after_critical {q u : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) (hcu : innerCritical q < u) :
    0 < innerNumerator q u := by
  rw [innerNumerator_factor hq hqs]
  exact mul_pos (mul_pos hq (sub_pos.mpr hcu))
    (sub_pos.mpr ((innerCritical_inv_lt_one hq hqs).trans
      ((innerCritical_gt_one hq hqs).trans hcu)))

theorem exteriorFunction_continuousOn_inner {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    ContinuousOn (exteriorFunction q) (Ioo q q⁻¹) := by
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  intro u hu
  exact (hasDerivAt_exteriorFunction_inner hq (hq.trans hu.1) hu.1 hu.2).continuousAt
    |>.continuousWithinAt

theorem exteriorFunction_inner_deriv_neg_before_critical {q u : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) (hu1 : 1 < u) (huc : u < innerCritical q) :
    deriv (exteriorFunction q) u < 0 := by
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have huq : u < q⁻¹ := huc.trans (innerCritical_lt_inv hq hqs)
  rw [(hasDerivAt_exteriorFunction_inner hq
    ((by norm_num : (0 : ℝ) < 1).trans hu1) (hq1.trans hu1) huq).deriv]
  change innerNumerator q u / (u * (u - q) * (1 - q * u)) < 0
  have hden : 0 < u * (u - q) * (1 - q * u) := by
    have hqu : 0 < 1 - q * u := by
      have hmul := mul_lt_mul_of_pos_left huq hq
      rw [mul_inv_cancel₀ hq.ne'] at hmul
      linarith
    exact mul_pos (mul_pos ((by norm_num : (0 : ℝ) < 1).trans hu1)
      (sub_pos.mpr (hq1.trans hu1))) hqu
  exact div_neg_of_neg_of_pos (innerNumerator_neg_before_critical hq hqs hu1 huc) hden

theorem exteriorFunction_inner_deriv_pos_after_critical {q u : ℝ}
    (hq : 0 < q) (hqs : q < qSoft)
    (hcu : innerCritical q < u) (huq : u < q⁻¹) :
    0 < deriv (exteriorFunction q) u := by
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hu1 : 1 < u := (innerCritical_gt_one hq hqs).trans hcu
  rw [(hasDerivAt_exteriorFunction_inner hq
    ((by norm_num : (0 : ℝ) < 1).trans hu1) (hq1.trans hu1) huq).deriv]
  change 0 < innerNumerator q u / (u * (u - q) * (1 - q * u))
  have hden : 0 < u * (u - q) * (1 - q * u) := by
    have hqu : 0 < 1 - q * u := by
      have hmul := mul_lt_mul_of_pos_left huq hq
      rw [mul_inv_cancel₀ hq.ne'] at hmul
      linarith
    exact mul_pos (mul_pos ((by norm_num : (0 : ℝ) < 1).trans hu1)
      (sub_pos.mpr (hq1.trans hu1))) hqu
  exact div_pos (innerNumerator_pos_after_critical hq hqs hcu) hden

theorem exteriorFunction_strictAntiOn_one_critical {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    StrictAntiOn (exteriorFunction q) (Icc 1 (innerCritical q)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 1 (innerCritical q))
  · exact (exteriorFunction_continuousOn_inner hq hqs).mono fun u hu ↦ by
      exact ⟨(q_lt_one_of_pos_le_qSoft hq hqs.le).trans_le hu.1,
        hu.2.trans_lt (innerCritical_lt_inv hq hqs)⟩
  · rw [interior_Icc]
    intro u hu
    exact exteriorFunction_inner_deriv_neg_before_critical hq hqs hu.1 hu.2

theorem exteriorFunction_strictMonoOn_critical_to {q b : ℝ}
    (hq : 0 < q) (hqs : q < qSoft)
    (hbq : b < q⁻¹) :
    StrictMonoOn (exteriorFunction q) (Icc (innerCritical q) b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (innerCritical q) b)
  · exact (exteriorFunction_continuousOn_inner hq hqs).mono fun u hu ↦ by
      exact ⟨((q_lt_one_of_pos_le_qSoft hq hqs.le).trans
        (innerCritical_gt_one hq hqs)).trans_le hu.1,
        hu.2.trans_lt hbq⟩
  · rw [interior_Icc]
    intro u hu
    exact exteriorFunction_inner_deriv_pos_after_critical hq hqs hu.1
      (hu.2.trans hbq)

theorem exteriorFunction_strictMonoOn_after_critical {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    StrictMonoOn (exteriorFunction q) (Ico (innerCritical q) q⁻¹) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico (innerCritical q) q⁻¹)
  · exact (exteriorFunction_continuousOn_inner hq hqs).mono fun u hu ↦ by
      exact ⟨((q_lt_one_of_pos_le_qSoft hq hqs.le).trans
        (innerCritical_gt_one hq hqs)).trans_le hu.1, hu.2⟩
  · rw [interior_Ico]
    intro u hu
    exact exteriorFunction_inner_deriv_pos_after_critical hq hqs hu.1 hu.2

theorem exteriorFunction_one {q : ℝ} (hq1 : q < 1) :
    exteriorFunction q 1 = 0 := by
  rw [exteriorFunction, abs_of_pos (by nlinarith : 0 < 1 - q * 1)]
  have hne : 1 - q ≠ 0 := by linarith
  field_simp [hne]
  simp

theorem exteriorFunction_innerCritical_neg {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    exteriorFunction q (innerCritical q) < 0 := by
  have hanti := exteriorFunction_strictAntiOn_one_critical hq hqs
    (by exact ⟨le_rfl, (innerCritical_gt_one hq hqs).le⟩)
    (by exact ⟨(innerCritical_gt_one hq hqs).le, le_rfl⟩)
    (innerCritical_gt_one hq hqs)
  rw [exteriorFunction_one (q_lt_one_of_pos_le_qSoft hq hqs.le)] at hanti
  exact hanti

theorem exists_inner_point_exteriorFunction_pos {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    ∃ u : ℝ, 1 < u ∧ u < q⁻¹ ∧ 0 < exteriorFunction q u := by
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hA : 0 < A q := A_pos_of_pos_le_qSoft hq hqs.le
  have hd : 0 < 1 - q ^ 2 := by nlinarith
  let C : ℝ := Real.exp (Real.log q⁻¹ / A q)
  have hC : 0 < C := Real.exp_pos _
  let e : ℝ := (1 - q ^ 2) / (2 * (q * C + 1))
  have hden : 0 < 2 * (q * C + 1) := by positivity
  have he : 0 < e := by
    dsimp [e]
    positivity
  have hden_two : (2 : ℝ) < 2 * (q * C + 1) := by
    nlinarith [mul_pos hq hC]
  have he_half : e < (1 - q ^ 2) / 2 := by
    dsimp [e]
    exact div_lt_div_of_pos_left hd (by norm_num) hden_two
  have he_q : e < 1 - q := by
    have hid : 1 - q ^ 2 = (1 - q) * (1 + q) := by ring
    rw [hid] at he_half
    nlinarith [mul_pos (sub_pos.mpr hq1) (sub_pos.mpr hq1)]
  let u : ℝ := (1 - e) / q
  have hu1 : 1 < u := by
    dsimp [u]
    rw [lt_div_iff₀ hq]
    linarith
  have huq : u < q⁻¹ := by
    dsimp [u]
    rw [div_eq_mul_inv]
    nlinarith [inv_pos.mpr hq]
  have hu : 0 < u := (by norm_num : (0 : ℝ) < 1).trans hu1
  have hinvpos : 0 < q⁻¹ := inv_pos.mpr hq
  have hqu : 1 - q * u = e := by
    dsimp [u]
    field_simp [hq.ne']
    ring
  have hu_sub : u - q = (1 - q ^ 2 - e) / q := by
    dsimp [u]
    field_simp [hq.ne']
    ring
  have hratio : C < (u - q) / |1 - q * u| := by
    rw [abs_one_sub_q_mul_of_lt_inv hq huq, hqu, hu_sub]
    rw [lt_div_iff₀ he, lt_div_iff₀ hq]
    dsimp [e]
    field_simp [hden.ne']
    nlinarith [mul_pos hq hC, mul_pos hC hd]
  have hratio_pos : 0 < (u - q) / |1 - q * u| := hC.trans hratio
  have hlogratio : Real.log C < Real.log ((u - q) / |1 - q * u|) :=
    Real.strictMonoOn_log hC hratio_pos hratio
  have hlogC : Real.log C = Real.log q⁻¹ / A q := by
    dsimp [C]
    rw [Real.log_exp]
  have hmain : Real.log q⁻¹ <
      A q * Real.log ((u - q) / |1 - q * u|) := by
    calc
      Real.log q⁻¹ = A q * (Real.log q⁻¹ / A q) := by field_simp [hA.ne']
      _ = A q * Real.log C := by rw [hlogC]
      _ < A q * Real.log ((u - q) / |1 - q * u|) :=
        mul_lt_mul_of_pos_left hlogratio hA
  have hlogu : Real.log u < Real.log q⁻¹ :=
    Real.strictMonoOn_log hu hinvpos huq
  refine ⟨u, hu1, huq, ?_⟩
  rw [exteriorFunction]
  linarith

/-! ## The nontrivial inner root and the `sInf` definition -/

theorem exists_inner_point_after_critical_pos {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    ∃ b : ℝ, innerCritical q < b ∧ b < q⁻¹ ∧ 0 < exteriorFunction q b := by
  obtain ⟨b, hb1, hbq, hbpos⟩ := exists_inner_point_exteriorFunction_pos hq hqs
  have hcb : innerCritical q < b := by
    by_contra hn
    have hbc : b ≤ innerCritical q := le_of_not_gt hn
    have hanti := exteriorFunction_strictAntiOn_one_critical hq hqs
      (by exact ⟨le_rfl, (innerCritical_gt_one hq hqs).le⟩)
      (by exact ⟨hb1.le, hbc⟩) hb1
    rw [exteriorFunction_one (q_lt_one_of_pos_le_qSoft hq hqs.le)] at hanti
    linarith
  exact ⟨b, hcb, hbq, hbpos⟩

theorem existsUnique_exteriorFunction_inner_root {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    ∃! u : ℝ, 1 < u ∧ u < q⁻¹ ∧ exteriorFunction q u = 0 := by
  obtain ⟨b, hcb, hbq, hbpos⟩ := exists_inner_point_after_critical_pos hq hqs
  have hcneg := exteriorFunction_innerCritical_neg hq hqs
  have hcont : ContinuousOn (exteriorFunction q) (Icc (innerCritical q) b) :=
    (exteriorFunction_continuousOn_inner hq hqs).mono fun u hu ↦ by
      exact ⟨((q_lt_one_of_pos_le_qSoft hq hqs.le).trans
        (innerCritical_gt_one hq hqs)).trans_le hu.1, hu.2.trans_lt hbq⟩
  have hzero : (0 : ℝ) ∈
      Icc (exteriorFunction q (innerCritical q)) (exteriorFunction q b) :=
    ⟨hcneg.le, hbpos.le⟩
  obtain ⟨u, hu, hu0⟩ := intermediate_value_Icc hcb.le hcont hzero
  have hu1 : 1 < u := (innerCritical_gt_one hq hqs).trans_le hu.1
  have huq : u < q⁻¹ := hu.2.trans_lt hbq
  refine ⟨u, ⟨hu1, huq, hu0⟩, ?_⟩
  intro v hv
  have hcv : innerCritical q < v := by
    by_contra hn
    have hvc : v ≤ innerCritical q := le_of_not_gt hn
    have hanti := exteriorFunction_strictAntiOn_one_critical hq hqs
      (by exact ⟨le_rfl, (innerCritical_gt_one hq hqs).le⟩)
      (by exact ⟨hv.1.le, hvc⟩) hv.1
    rw [exteriorFunction_one (q_lt_one_of_pos_le_qSoft hq hqs.le), hv.2.2] at hanti
    linarith
  exact (exteriorFunction_strictMonoOn_after_critical hq hqs).injOn
    ⟨hcv.le, hv.2.1⟩ ⟨hu.1, huq⟩ (hv.2.2.trans hu0.symm)

theorem existsUnique_exteriorEquation_inner {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    ∃! u : ℝ, 1 < u ∧ u < q⁻¹ ∧ exteriorEquation q u := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_exteriorFunction_inner_root hq hqs
  refine ⟨u, ⟨hu.1, hu.2.1,
    exteriorEquation_iff_exteriorFunction_eq_zero.2 hu.2.2⟩, ?_⟩
  intro v hv
  exact huniq v ⟨hv.1, hv.2.1,
    exteriorEquation_iff_exteriorFunction_eq_zero.1 hv.2.2⟩

theorem exteriorB_qSoft : exteriorB qSoft = 2 * qSoft := by
  have hq := qSoft_mem_Ioo.1
  have hq1 := mem_Ioo_zero_qCeiling_imp_lt_one qSoft_mem_Ioo
  have hden : 1 + qSoft ≠ 0 := by linarith
  rw [exteriorB, A_qSoft_eq_s_qSoft, s]
  field_simp [hden]
  ring

theorem innerNumerator_qSoft (u : ℝ) :
    innerNumerator qSoft u = qSoft * (u - 1) ^ 2 := by
  rw [innerNumerator, exteriorB_qSoft]
  ring

theorem uPlus_qSoft : uPlus qSoft = 1 := by
  simp [uPlus]

theorem exteriorEquation_qSoft_one : exteriorEquation qSoft 1 := by
  rw [exteriorEquation_iff_exteriorFunction_eq_zero]
  exact exteriorFunction_one (mem_Ioo_zero_qCeiling_imp_lt_one qSoft_mem_Ioo)

theorem exteriorEquation_qSoft_uPlus : exteriorEquation qSoft (uPlus qSoft) := by
  rw [uPlus_qSoft]
  exact exteriorEquation_qSoft_one

theorem uPlus_eq_inner_root {q r : ℝ}
    (hq : 0 < q) (hqs : q < qSoft)
    (hr : 1 < r ∧ r < q⁻¹ ∧ exteriorEquation q r) :
    uPlus q = r := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_exteriorEquation_inner hq hqs
  have hur : u = r := (huniq r hr).symm
  subst r
  have hset :
      {v : ℝ | 1 < v ∧ v < q⁻¹ ∧ exteriorEquation q v} = {u} := by
    ext v
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · exact huniq v
    · rintro rfl
      exact hu
  rw [uPlus, if_neg hqs.ne, hset, csInf_singleton]

theorem uPlus_spec {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    1 < uPlus q ∧ uPlus q < q⁻¹ ∧ exteriorEquation q (uPlus q) := by
  obtain ⟨r, hr, _⟩ := existsUnique_exteriorEquation_inner hq hqs
  rwa [uPlus_eq_inner_root hq hqs hr]

theorem exteriorEquation_inner_iff_eq_uPlus {q u : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) (hu1 : 1 < u) (huq : u < q⁻¹) :
    exteriorEquation q u ↔ u = uPlus q := by
  constructor
  · intro heq
    exact (uPlus_eq_inner_root hq hqs ⟨hu1, huq, heq⟩).symm
  · rintro rfl
    exact (uPlus_spec hq hqs).2.2

/-! ## Endpoint limits -/

theorem tendsto_outer_ratio_at_inv {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Tendsto (fun u : ℝ ↦ (u - q) / |1 - q * u|) (𝓝[>] (q⁻¹)) atTop := by
  have hU : Tendsto (fun u : ℝ ↦ u) (𝓝[>] (q⁻¹)) (𝓝 q⁻¹) :=
    tendsto_id.mono_left inf_le_left
  have hden0 : Tendsto (fun u : ℝ ↦ q * u - 1) (𝓝[>] (q⁻¹)) (𝓝 0) := by
    simpa [hq.ne'] using! (hU.const_mul q).sub_const 1
  have hdenpos : ∀ᶠ u : ℝ in 𝓝[>] (q⁻¹), 0 < q * u - 1 := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hmul := mul_lt_mul_of_pos_left hu hq
    rw [mul_inv_cancel₀ hq.ne'] at hmul
    linarith
  have hden : Tendsto (fun u : ℝ ↦ q * u - 1) (𝓝[>] (q⁻¹)) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hden0, hdenpos⟩
  have hnum : Tendsto (fun u : ℝ ↦ u - q) (𝓝[>] (q⁻¹)) (𝓝 (q⁻¹ - q)) :=
    hU.sub_const q
  have hnumpos : 0 < q⁻¹ - q := by
    have : q < q⁻¹ := hq1.trans (one_lt_inv_q hq hq1)
    linarith
  have hratio : Tendsto (fun u : ℝ ↦ (u - q) * (q * u - 1)⁻¹)
      (𝓝[>] (q⁻¹)) atTop :=
    hnum.pos_mul_atTop hnumpos hden.inv_tendsto_nhdsGT_zero
  refine hratio.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [abs_one_sub_q_mul_of_inv_lt hq hu, div_eq_mul_inv]

theorem tendsto_exteriorFunction_outer_at_inv {q : ℝ}
    (hq : 0 < q) (hqs : q ≤ qSoft) :
    Tendsto (exteriorFunction q) (𝓝[>] (q⁻¹)) atTop := by
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs
  have hA : 0 < A q := A_pos_of_pos_le_qSoft hq hqs
  have hlogratio : Tendsto
      (fun u : ℝ ↦ Real.log ((u - q) / |1 - q * u|)) (𝓝[>] (q⁻¹)) atTop :=
    Real.tendsto_log_atTop.comp (tendsto_outer_ratio_at_inv hq hq1)
  have hmain : Tendsto
      (fun u : ℝ ↦ A q * Real.log ((u - q) / |1 - q * u|))
      (𝓝[>] (q⁻¹)) atTop := hlogratio.const_mul_atTop hA
  have hU : Tendsto (fun u : ℝ ↦ u) (𝓝[>] (q⁻¹)) (𝓝 q⁻¹) :=
    tendsto_id.mono_left inf_le_left
  have hlogu : Tendsto (fun u : ℝ ↦ Real.log u) (𝓝[>] (q⁻¹))
      (𝓝 (Real.log q⁻¹)) := hU.log (inv_ne_zero hq.ne')
  simpa [exteriorFunction, sub_eq_add_neg] using! hmain.atTop_add hlogu.neg

theorem tendsto_inner_ratio_at_inv {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Tendsto (fun u : ℝ ↦ (u - q) / |1 - q * u|) (𝓝[<] (q⁻¹)) atTop := by
  have hU : Tendsto (fun u : ℝ ↦ u) (𝓝[<] (q⁻¹)) (𝓝 q⁻¹) :=
    tendsto_id.mono_left inf_le_left
  have hden0 : Tendsto (fun u : ℝ ↦ 1 - q * u) (𝓝[<] (q⁻¹)) (𝓝 0) := by
    simpa [hq.ne'] using! (hU.const_mul q).const_sub 1
  have hdenpos : ∀ᶠ u : ℝ in 𝓝[<] (q⁻¹), 0 < 1 - q * u := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hmul := mul_lt_mul_of_pos_left hu hq
    rw [mul_inv_cancel₀ hq.ne'] at hmul
    linarith
  have hden : Tendsto (fun u : ℝ ↦ 1 - q * u) (𝓝[<] (q⁻¹)) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hden0, hdenpos⟩
  have hnum : Tendsto (fun u : ℝ ↦ u - q) (𝓝[<] (q⁻¹)) (𝓝 (q⁻¹ - q)) :=
    hU.sub_const q
  have hnumpos : 0 < q⁻¹ - q := by
    have : q < q⁻¹ := hq1.trans (one_lt_inv_q hq hq1)
    linarith
  have hratio : Tendsto (fun u : ℝ ↦ (u - q) * (1 - q * u)⁻¹)
      (𝓝[<] (q⁻¹)) atTop :=
    hnum.pos_mul_atTop hnumpos hden.inv_tendsto_nhdsGT_zero
  refine hratio.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [abs_one_sub_q_mul_of_lt_inv hq hu, div_eq_mul_inv]

theorem tendsto_exteriorFunction_inner_at_inv {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    Tendsto (exteriorFunction q) (𝓝[<] (q⁻¹)) atTop := by
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hA : 0 < A q := A_pos_of_pos_le_qSoft hq hqs.le
  have hlogratio : Tendsto
      (fun u : ℝ ↦ Real.log ((u - q) / |1 - q * u|)) (𝓝[<] (q⁻¹)) atTop :=
    Real.tendsto_log_atTop.comp (tendsto_inner_ratio_at_inv hq hq1)
  have hmain : Tendsto
      (fun u : ℝ ↦ A q * Real.log ((u - q) / |1 - q * u|))
      (𝓝[<] (q⁻¹)) atTop := hlogratio.const_mul_atTop hA
  have hU : Tendsto (fun u : ℝ ↦ u) (𝓝[<] (q⁻¹)) (𝓝 q⁻¹) :=
    tendsto_id.mono_left inf_le_left
  have hlogu : Tendsto (fun u : ℝ ↦ Real.log u) (𝓝[<] (q⁻¹))
      (𝓝 (Real.log q⁻¹)) := hU.log (inv_ne_zero hq.ne')
  simpa [exteriorFunction, sub_eq_add_neg] using! hmain.atTop_add hlogu.neg

theorem tendsto_outer_ratio_atTop {q : ℝ} (hq : 0 < q) :
    Tendsto (fun u : ℝ ↦ (u - q) / |1 - q * u|) atTop (𝓝 q⁻¹) := by
  have hInv : Tendsto (fun u : ℝ ↦ u⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hnum : Tendsto (fun u : ℝ ↦ 1 - q * u⁻¹) atTop (𝓝 1) := by
    simpa using! (hInv.const_mul q).const_sub 1
  have hden : Tendsto (fun u : ℝ ↦ q - u⁻¹) atTop (𝓝 q) := by
    simpa using! hInv.const_sub q
  have hratio : Tendsto (fun u : ℝ ↦ (1 - q * u⁻¹) / (q - u⁻¹))
      atTop (𝓝 (1 / q)) := hnum.div hden hq.ne'
  have hratio' : Tendsto (fun u : ℝ ↦ (1 - q * u⁻¹) / (q - u⁻¹))
      atTop (𝓝 q⁻¹) := by simpa [one_div] using! hratio
  refine hratio'.congr' ?_
  filter_upwards [eventually_gt_atTop q⁻¹] with u hu
  have hu0 : u ≠ 0 := ((inv_pos.mpr hq).trans hu).ne'
  rw [abs_one_sub_q_mul_of_inv_lt hq hu]
  field_simp [hu0, hq.ne']

theorem tendsto_exteriorFunction_outer_atTop {q : ℝ}
    (hq : 0 < q) :
    Tendsto (exteriorFunction q) atTop atBot := by
  have hratio := tendsto_outer_ratio_atTop hq
  have hlogratio : Tendsto
      (fun u : ℝ ↦ Real.log ((u - q) / |1 - q * u|)) atTop
      (𝓝 (Real.log q⁻¹)) := hratio.log (inv_ne_zero hq.ne')
  have hmain : Tendsto
      (fun u : ℝ ↦ A q * Real.log ((u - q) / |1 - q * u|)) atTop
      (𝓝 (A q * Real.log q⁻¹)) := hlogratio.const_mul (A q)
  have hneglog : Tendsto (fun u : ℝ ↦ -Real.log u) atTop atBot :=
    tendsto_neg_atTop_atBot.comp Real.tendsto_log_atTop
  simpa [exteriorFunction, sub_eq_add_neg] using! hmain.add_atBot hneglog

/-! ## Explicit sign witnesses on the outer component -/

theorem exists_outer_point_exteriorFunction_pos {q : ℝ}
    (hq : 0 < q) (hqs : q ≤ qSoft) :
    ∃ u : ℝ, q⁻¹ < u ∧ 0 < exteriorFunction q u := by
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs
  have hA : 0 < A q := A_pos_of_pos_le_qSoft hq hqs
  have hd : 0 < 1 - q ^ 2 := by nlinarith
  let C : ℝ := Real.exp (Real.log (2 / q) / A q)
  have hC : 0 < C := Real.exp_pos _
  let e : ℝ := (1 - q ^ 2) / (2 * q * C + (1 - q ^ 2))
  have hden : 0 < 2 * q * C + (1 - q ^ 2) := by positivity
  have he : 0 < e := by
    dsimp [e]
    positivity
  have he1 : e < 1 := by
    dsimp [e]
    rw [div_lt_one hden]
    nlinarith [mul_pos hq hC]
  let u : ℝ := (1 + e) / q
  have huq : q⁻¹ < u := by
    dsimp [u]
    rw [div_eq_mul_inv]
    nlinarith [inv_pos.mpr hq]
  have hu_two : u < 2 / q := by
    dsimp [u]
    exact (div_lt_div_iff_of_pos_right hq).2 (by linarith)
  have hu : 0 < u := (inv_pos.mpr hq).trans huq
  have htwo : 0 < 2 / q := div_pos (by norm_num) hq
  have hqu : q * u - 1 = e := by
    dsimp [u]
    field_simp [hq.ne']
    ring
  have hu_sub : u - q = (1 - q ^ 2 + e) / q := by
    dsimp [u]
    field_simp [hq.ne']
    ring
  have hratio : C < (u - q) / |1 - q * u| := by
    rw [abs_one_sub_q_mul_of_inv_lt hq huq, hqu, hu_sub]
    rw [lt_div_iff₀ he]
    rw [lt_div_iff₀ hq]
    dsimp [e]
    field_simp [hden.ne']
    nlinarith [mul_pos hq hC, mul_pos hq hd, mul_pos hC hd]
  have hratio_pos : 0 < (u - q) / |1 - q * u| := hC.trans hratio
  have hlogratio : Real.log C < Real.log ((u - q) / |1 - q * u|) :=
    Real.strictMonoOn_log hC hratio_pos hratio
  have hlogC : Real.log C = Real.log (2 / q) / A q := by
    dsimp [C]
    rw [Real.log_exp]
  have hmain : Real.log (2 / q) <
      A q * Real.log ((u - q) / |1 - q * u|) := by
    calc
      Real.log (2 / q) = A q * (Real.log (2 / q) / A q) := by
        field_simp [hA.ne']
      _ = A q * Real.log C := by rw [hlogC]
      _ < A q * Real.log ((u - q) / |1 - q * u|) :=
        mul_lt_mul_of_pos_left hlogratio hA
  have hlogu : Real.log u < Real.log (2 / q) :=
    Real.strictMonoOn_log hu htwo hu_two
  refine ⟨u, huq, ?_⟩
  rw [exteriorFunction]
  linarith

theorem exists_outer_point_exteriorFunction_neg {q : ℝ}
    (hq : 0 < q) (hqs : q ≤ qSoft) :
    ∃ u : ℝ, q⁻¹ < u ∧ exteriorFunction q u < 0 := by
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs
  have hA : 0 < A q := A_pos_of_pos_le_qSoft hq hqs
  let C : ℝ := 2 / q
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hC1 : 1 < C := by
    dsimp [C]
    rw [lt_div_iff₀ hq]
    linarith
  have hlogC : 0 < Real.log C := Real.log_pos hC1
  let T : ℝ := A q * Real.log C + 1
  have hT : 0 < T := by
    dsimp [T]
    positivity
  let u : ℝ := C * Real.exp T
  have hexp1 : 1 < Real.exp T := Real.one_lt_exp_iff.2 hT
  have hCu : C < u := by
    dsimp [u]
    nlinarith [mul_pos hC (sub_pos.mpr hexp1)]
  have hinvC : q⁻¹ < C := by
    dsimp [C]
    rw [div_eq_mul_inv]
    nlinarith [inv_pos.mpr hq]
  have huq : q⁻¹ < u := hinvC.trans hCu
  have hu : 0 < u := hC.trans hCu
  have hqu : 0 < q * u - 1 := by
    have hmul := mul_lt_mul_of_pos_left huq hq
    rw [mul_inv_cancel₀ hq.ne'] at hmul
    linarith
  have huqpos : 0 < u - q := by
    have hqinv : q < q⁻¹ := hq1.trans (one_lt_inv_q hq hq1)
    linarith
  have hratio_pos : 0 < (u - q) / |1 - q * u| := by
    rw [abs_one_sub_q_mul_of_inv_lt hq huq]
    exact div_pos huqpos hqu
  have hratio : (u - q) / |1 - q * u| < C := by
    rw [abs_one_sub_q_mul_of_inv_lt hq huq]
    rw [div_lt_iff₀ hqu]
    dsimp [C] at hCu ⊢
    have hCu_mul : 2 < u * q := (div_lt_iff₀ hq).1 hCu
    rw [div_mul_eq_mul_div, lt_div_iff₀ hq]
    nlinarith [sq_pos_of_pos hq]
  have hlogratio : Real.log ((u - q) / |1 - q * u|) < Real.log C :=
    Real.strictMonoOn_log hratio_pos hC hratio
  have hlogu : Real.log u = Real.log C + T := by
    dsimp [u]
    rw [Real.log_mul hC.ne' (Real.exp_ne_zero T), Real.log_exp]
  refine ⟨u, huq, ?_⟩
  rw [exteriorFunction, hlogu]
  have hmul := mul_lt_mul_of_pos_left hlogratio hA
  dsimp [T]
  linarith

/-! ## The outer root and the `sInf` definition -/

theorem existsUnique_exteriorFunction_outer_root {q : ℝ}
    (hq : 0 < q) (hqs : q ≤ qSoft) :
    ∃! u : ℝ, q⁻¹ < u ∧ exteriorFunction q u = 0 := by
  obtain ⟨a, haq, ha⟩ := exists_outer_point_exteriorFunction_pos hq hqs
  obtain ⟨b, hbq, hb⟩ := exists_outer_point_exteriorFunction_neg hq hqs
  have hab : a < b := by
    by_contra hn
    have hba : b ≤ a := le_of_not_gt hn
    rcases hba.eq_or_lt with rfl | hba
    · linarith
    · have hanti := exteriorFunction_strictAntiOn_outer hq hqs hbq haq hba
      linarith
  have hcont : ContinuousOn (exteriorFunction q) (Icc a b) :=
    (exteriorFunction_continuousOn_outer hq hqs).mono fun u hu ↦ haq.trans_le hu.1
  have hzero : (0 : ℝ) ∈ Icc (exteriorFunction q b) (exteriorFunction q a) :=
    ⟨hb.le, ha.le⟩
  obtain ⟨u, huab, hu0⟩ := intermediate_value_Icc' hab.le hcont hzero
  have huq : q⁻¹ < u := haq.trans_le huab.1
  refine ⟨u, ⟨huq, hu0⟩, ?_⟩
  intro v hv
  exact ((exteriorFunction_strictAntiOn_outer hq hqs).injOn huq hv.1
    (hu0.trans hv.2.symm)).symm

theorem existsUnique_exteriorEquation_outer {q : ℝ}
    (hq : 0 < q) (hqs : q ≤ qSoft) :
    ∃! u : ℝ, q⁻¹ < u ∧ exteriorEquation q u := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_exteriorFunction_outer_root hq hqs
  refine ⟨u, ⟨hu.1, exteriorEquation_iff_exteriorFunction_eq_zero.2 hu.2⟩, ?_⟩
  intro v hv
  exact huniq v ⟨hv.1, exteriorEquation_iff_exteriorFunction_eq_zero.1 hv.2⟩

theorem uMinus_eq_outer_root {q r : ℝ}
    (hq : 0 < q) (hqs : q ≤ qSoft)
    (hr : q⁻¹ < r ∧ exteriorEquation q r) :
    uMinus q = r := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_exteriorEquation_outer hq hqs
  have hur : u = r := (huniq r hr).symm
  subst r
  have hset : {v : ℝ | q⁻¹ < v ∧ exteriorEquation q v} = {u} := by
    ext v
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · exact huniq v
    · rintro rfl
      exact hu
  rw [uMinus, hset, csInf_singleton]

theorem uMinus_spec {q : ℝ} (hq : 0 < q) (hqs : q ≤ qSoft) :
    q⁻¹ < uMinus q ∧ exteriorEquation q (uMinus q) := by
  obtain ⟨r, hr, _⟩ := existsUnique_exteriorEquation_outer hq hqs
  rwa [uMinus_eq_outer_root hq hqs hr]

theorem exteriorEquation_outer_iff_eq_uMinus {q u : ℝ}
    (hq : 0 < q) (hqs : q ≤ qSoft) (hu : q⁻¹ < u) :
    exteriorEquation q u ↔ u = uMinus q := by
  constructor
  · intro heq
    exact (uMinus_eq_outer_root hq hqs ⟨hu, heq⟩).symm
  · rintro rfl
    exact (uMinus_spec hq hqs).2

end

end Erdos1038
