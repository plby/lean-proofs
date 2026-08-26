import ErdosProblems.Erdos1038.ExteriorRoots
import ErdosProblems.Erdos1038.SoftEdgeCertificate

/-!
# Regularity and minimization of the one-cut length

The absolute value in `exteriorFunction` is resolved separately on its two
components.  This gives smooth two-variable residuals to which the implicit
function theorem can be applied.
-/

open Set Filter
open scoped Topology ContDiff

namespace Erdos1038

noncomputable section

/-- Smooth residual on `1 < u < q⁻¹`. -/
def innerResidual (p : ℝ × ℝ) : ℝ :=
  A p.1 * Real.log ((p.2 - p.1) / (1 - p.1 * p.2)) - Real.log p.2

/-- Smooth residual on `q⁻¹ < u`. -/
def outerResidual (p : ℝ × ℝ) : ℝ :=
  A p.1 * Real.log ((p.2 - p.1) / (p.1 * p.2 - 1)) - Real.log p.2

theorem innerResidual_eq_exteriorFunction {q u : ℝ}
    (hq : 0 < q) (huq : u < q⁻¹) :
    innerResidual (q, u) = exteriorFunction q u := by
  rw [innerResidual, exteriorFunction, abs_one_sub_q_mul_of_lt_inv hq huq]

theorem outerResidual_eq_exteriorFunction {q u : ℝ}
    (hq : 0 < q) (huq : q⁻¹ < u) :
    outerResidual (q, u) = exteriorFunction q u := by
  rw [outerResidual, exteriorFunction, abs_one_sub_q_mul_of_inv_lt hq huq]

theorem contDiffAt_H {q : ℝ} (hq : q ≠ -1) : ContDiffAt ℝ ⊤ H q := by
  unfold H
  have hden : (1 + q) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro h
    apply hq
    linarith
  exact (contDiffAt_const.mul contDiffAt_id).div
    ((contDiffAt_const.add contDiffAt_id).pow 2) hden

theorem contDiffAt_A {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ContDiffAt ℝ ⊤ A q := by
  have hq0 : q ≠ 0 := hq.ne'
  have hqneg : q ≠ -1 := by linarith
  have hH : H q ≠ 0 := (H_pos hq).ne'
  have hlog : Real.log q ≠ 0 := log_q_ne_zero hq hq1
  unfold A
  exact ((contDiffAt_H hqneg).log hH).div (contDiffAt_id.log hq0) hlog

theorem contDiffAt_innerResidual {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hu : 0 < u)
    (hqu : q < u) (huq : u < q⁻¹) :
    ContDiffAt ℝ ⊤ innerResidual (q, u) := by
  have hden : 1 - q * u ≠ 0 := by
    have hmul := mul_lt_mul_of_pos_left huq hq
    rw [mul_inv_cancel₀ hq.ne'] at hmul
    linarith
  have hnum : u - q ≠ 0 := (sub_pos.mpr hqu).ne'
  have harg : (u - q) / (1 - q * u) ≠ 0 := div_ne_zero hnum hden
  have hA : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ ↦ A p.1) (q, u) :=
    (contDiffAt_A hq hq1).comp (q, u) contDiffAt_fst
  have hnumcd : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ ↦ p.2 - p.1) (q, u) :=
    contDiffAt_snd.sub contDiffAt_fst
  have hdencd : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ ↦ 1 - p.1 * p.2) (q, u) :=
    contDiffAt_const.sub (contDiffAt_fst.mul contDiffAt_snd)
  have hlogarg : ContDiffAt ℝ ⊤
      (fun p : ℝ × ℝ ↦ Real.log ((p.2 - p.1) / (1 - p.1 * p.2))) (q, u) :=
    (hnumcd.div hdencd hden).log harg
  have hlogu : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ ↦ Real.log p.2) (q, u) :=
    contDiffAt_snd.log hu.ne'
  exact hA.mul hlogarg |>.sub hlogu

theorem contDiffAt_outerResidual {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (huq : q⁻¹ < u) :
    ContDiffAt ℝ ⊤ outerResidual (q, u) := by
  have hu : 0 < u := (inv_pos.mpr hq).trans huq
  have hden : q * u - 1 ≠ 0 := by
    have hmul := mul_lt_mul_of_pos_left huq hq
    rw [mul_inv_cancel₀ hq.ne'] at hmul
    linarith
  have hqinv : q < q⁻¹ := hq1.trans (one_lt_inv_q hq hq1)
  have hnum : u - q ≠ 0 := (sub_pos.mpr (hqinv.trans huq)).ne'
  have harg : (u - q) / (q * u - 1) ≠ 0 := div_ne_zero hnum hden
  have hA : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ ↦ A p.1) (q, u) :=
    (contDiffAt_A hq hq1).comp (q, u) contDiffAt_fst
  have hnumcd : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ ↦ p.2 - p.1) (q, u) :=
    contDiffAt_snd.sub contDiffAt_fst
  have hdencd : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ ↦ p.1 * p.2 - 1) (q, u) :=
    (contDiffAt_fst.mul contDiffAt_snd).sub contDiffAt_const
  have hlogarg : ContDiffAt ℝ ⊤
      (fun p : ℝ × ℝ ↦ Real.log ((p.2 - p.1) / (p.1 * p.2 - 1))) (q, u) :=
    (hnumcd.div hdencd hden).log harg
  have hlogu : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ ↦ Real.log p.2) (q, u) :=
    contDiffAt_snd.log hu.ne'
  exact hA.mul hlogarg |>.sub hlogu

/-! ## A scalar implicit-function package -/

/-- Scalar implicit-function hypotheses, with the current mathlib interface below. -/
structure ScalarImplicitData (f : ℝ × ℝ → ℝ) (f' : ℝ × ℝ →L[ℝ] ℝ)
    (u : ℝ × ℝ) : Prop where
  hasFDerivAt : HasFDerivAt f f' u
  contDiffAt : ContDiffAt ℝ ⊤ f u
  bijective : Function.Bijective (f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ))
  ne_zero : (⊤ : ℕ∞ω) ≠ 0

namespace ScalarImplicitData

variable {f : ℝ × ℝ → ℝ} {f' : ℝ × ℝ →L[ℝ] ℝ} {u : ℝ × ℝ}

theorem invertible (h : ScalarImplicitData f f' u) :
    ((fderiv ℝ f u).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible := by
  rw [h.hasFDerivAt.fderiv]
  exact ⟨ContinuousLinearEquiv.ofBijective _
    (LinearMap.ker_eq_bot.mpr h.bijective.1)
    (LinearMap.range_eq_top.mpr h.bijective.2), rfl⟩

noncomputable def implicitFunction (h : ScalarImplicitData f f' u) : ℝ → ℝ :=
  h.contDiffAt.implicitFunction h.ne_zero h.invertible

theorem eventually_implicitFunction_apply_eq (h : ScalarImplicitData f f' u) :
    ∀ᶠ v in 𝓝 u, f v = f u ↔ h.implicitFunction v.1 = v.2 :=
  h.contDiffAt.eventually_apply_eq_iff_implicitFunction h.ne_zero h.invertible

theorem contDiffAt_implicitFunction (h : ScalarImplicitData f f' u) :
    ContDiffAt ℝ ⊤ h.implicitFunction u.1 :=
  h.contDiffAt.contDiffAt_implicitFunction h.ne_zero h.invertible

theorem apply_implicitFunction (h : ScalarImplicitData f f' u) :
    ∀ᶠ x in 𝓝 u.1, f (x, h.implicitFunction x) = f u :=
  h.contDiffAt.eventually_apply_implicitFunction h.ne_zero h.invertible

end ScalarImplicitData

theorem isContDiffImplicitAt_of_slice_deriv
    {f : ℝ × ℝ → ℝ} {q u Fu : ℝ}
    (hf : ContDiffAt ℝ ⊤ f (q, u))
    (hslice : HasDerivAt (fun v : ℝ ↦ f (q, v)) Fu u)
    (hFu : Fu ≠ 0) :
    ScalarImplicitData f (fderiv ℝ f (q, u)) (q, u) := by
  have hfd : HasFDerivAt f (fderiv ℝ f (q, u)) (q, u) :=
    (hf.differentiableAt (by simp)).hasFDerivAt
  have hembed : HasDerivAt (fun v : ℝ ↦ (q, v)) (0, 1) u :=
    (hasDerivAt_const u q).prodMk (hasDerivAt_id u)
  have hslice' : HasDerivAt (fun v : ℝ ↦ f (q, v))
      ((fderiv ℝ f (q, u)) (0, 1)) u := by
    convert! hfd.comp_hasDerivAt u hembed using 1
  have heval : (fderiv ℝ f (q, u)) (0, 1) = Fu := hslice'.unique hslice
  let L : ℝ →L[ℝ] ℝ :=
    (fderiv ℝ f (q, u)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)
  have hL (x : ℝ) : L x = x * Fu := by
    calc
      L x = (fderiv ℝ f (q, u)) (0, x) := by
        simp [L, ContinuousLinearMap.inr_apply]
      _ = (fderiv ℝ f (q, u)) (x • (0, 1)) := by
        congr 1
        ext <;> simp
      _ = x • (fderiv ℝ f (q, u)) (0, 1) :=
        (fderiv ℝ f (q, u)).map_smul x (0, 1)
      _ = x * Fu := by rw [heval]; simp [smul_eq_mul]
  refine ⟨hfd, hf, ?_, by simp⟩
  constructor
  · intro x y hxy
    rw [hL, hL] at hxy
    exact mul_right_cancel₀ hFu hxy
  · intro y
    refine ⟨y / Fu, ?_⟩
    rw [hL]
    exact div_mul_cancel₀ y hFu

/-! ## Nonvanishing vertical derivatives at the two roots -/

def innerPartialU (q u : ℝ) : ℝ :=
  innerNumerator q u / (u * (u - q) * (1 - q * u))

def outerPartialU (q u : ℝ) : ℝ :=
  -A q * (1 - q ^ 2) / ((u - q) * (q * u - 1)) - 1 / u

def innerPartialQ (q u : ℝ) : ℝ := deriv (fun r : ℝ ↦ innerResidual (r, u)) q

def outerPartialQ (q u : ℝ) : ℝ := deriv (fun r : ℝ ↦ outerResidual (r, u)) q

theorem hasDerivAt_innerResidual_right {q u : ℝ}
    (hq : 0 < q) (hu : 0 < u) (hqu : q < u) (huq : u < q⁻¹) :
    HasDerivAt (fun v : ℝ ↦ innerResidual (q, v)) (innerPartialU q u) u := by
  have hext := hasDerivAt_exteriorFunction_inner hq hu hqu huq
  have heq : (fun v : ℝ ↦ innerResidual (q, v)) =ᶠ[𝓝 u] exteriorFunction q := by
    filter_upwards [Iio_mem_nhds huq] with v hv
    exact innerResidual_eq_exteriorFunction hq hv
  exact hext.congr_of_eventuallyEq heq

theorem hasDerivAt_outerResidual_right {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (huq : q⁻¹ < u) :
    HasDerivAt (fun v : ℝ ↦ outerResidual (q, v)) (outerPartialU q u) u := by
  have hext := hasDerivAt_exteriorFunction_outer hq hq1 huq
  have heq : (fun v : ℝ ↦ outerResidual (q, v)) =ᶠ[𝓝 u] exteriorFunction q := by
    filter_upwards [Ioi_mem_nhds huq] with v hv
    exact outerResidual_eq_exteriorFunction hq hv
  exact hext.congr_of_eventuallyEq heq

theorem innerCritical_lt_uPlus {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    innerCritical q < uPlus q := by
  have hup := uPlus_spec hq hqs
  by_contra hn
  have hle : uPlus q ≤ innerCritical q := le_of_not_gt hn
  have hanti := exteriorFunction_strictAntiOn_one_critical hq hqs
    (by exact ⟨le_rfl, (innerCritical_gt_one hq hqs).le⟩)
    (by exact ⟨hup.1.le, hle⟩) hup.1
  rw [exteriorFunction_one (q_lt_one_of_pos_le_qSoft hq hqs.le)] at hanti
  have hzero := exteriorEquation_iff_exteriorFunction_eq_zero.1 hup.2.2
  linarith

theorem innerPartialU_uPlus_pos {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    0 < innerPartialU q (uPlus q) := by
  have hup := uPlus_spec hq hqs
  have hderiv := exteriorFunction_inner_deriv_pos_after_critical hq hqs
    (innerCritical_lt_uPlus hq hqs) hup.2.1
  rw [(hasDerivAt_exteriorFunction_inner hq
    ((by norm_num : (0 : ℝ) < 1).trans hup.1)
    ((q_lt_one_of_pos_le_qSoft hq hqs.le).trans hup.1) hup.2.1).deriv] at hderiv
  exact hderiv

theorem outerPartialU_uMinus_neg {q : ℝ} (hq : 0 < q) (hqs : q ≤ qSoft) :
    outerPartialU q (uMinus q) < 0 := by
  have hum := uMinus_spec hq hqs
  have hderiv := exteriorFunction_outer_deriv_neg hq hqs hum.1
  rw [(hasDerivAt_exteriorFunction_outer hq
    (q_lt_one_of_pos_le_qSoft hq hqs) hum.1).deriv] at hderiv
  exact hderiv

theorem innerImplicitData {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    ScalarImplicitData innerResidual
      (fderiv ℝ innerResidual (q, uPlus q)) (q, uPlus q) := by
  have hup := uPlus_spec hq hqs
  apply isContDiffImplicitAt_of_slice_deriv
  · exact contDiffAt_innerResidual hq (q_lt_one_of_pos_le_qSoft hq hqs.le)
      ((by norm_num : (0 : ℝ) < 1).trans hup.1)
      ((q_lt_one_of_pos_le_qSoft hq hqs.le).trans hup.1) hup.2.1
  · exact hasDerivAt_innerResidual_right hq
      ((by norm_num : (0 : ℝ) < 1).trans hup.1)
      ((q_lt_one_of_pos_le_qSoft hq hqs.le).trans hup.1) hup.2.1
  · exact (innerPartialU_uPlus_pos hq hqs).ne'

theorem outerImplicitData {q : ℝ} (hq : 0 < q) (hqs : q ≤ qSoft) :
    ScalarImplicitData outerResidual
      (fderiv ℝ outerResidual (q, uMinus q)) (q, uMinus q) := by
  have hum := uMinus_spec hq hqs
  apply isContDiffImplicitAt_of_slice_deriv
  · exact contDiffAt_outerResidual hq (q_lt_one_of_pos_le_qSoft hq hqs) hum.1
  · exact hasDerivAt_outerResidual_right hq (q_lt_one_of_pos_le_qSoft hq hqs) hum.1
  · exact (outerPartialU_uMinus_neg hq hqs).ne

/-! ## Identification of the local implicit functions with the global branches -/

theorem uPlus_eventuallyEq_implicitFunction {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    uPlus =ᶠ[𝓝 q] (innerImplicitData hq hqs).implicitFunction := by
  let h := innerImplicitData hq hqs
  let φ : ℝ → ℝ := h.implicitFunction
  have hup := uPlus_spec hq hqs
  have hbase : innerResidual (q, uPlus q) = 0 := by
    rw [innerResidual_eq_exteriorFunction hq hup.2.1]
    exact exteriorEquation_iff_exteriorFunction_eq_zero.1 hup.2.2
  have hφq : φ q = uPlus q := by
    exact h.eventually_implicitFunction_apply_eq.self_of_nhds.mp rfl
  have hφcont : ContinuousAt φ q := h.contDiffAt_implicitFunction.continuousAt
  have hφgt : ∀ᶠ r in 𝓝 q, 1 < φ r := by
    apply hφcont.eventually
    rw [hφq]
    exact Ioi_mem_nhds hup.1
  have hqmul : q * uPlus q < 1 := by
    have hmul := mul_lt_mul_of_pos_left hup.2.1 hq
    rw [mul_inv_cancel₀ hq.ne'] at hmul
    exact hmul
  have hmulcont : ContinuousAt (fun r : ℝ ↦ r * φ r) q :=
    continuousAt_id.mul hφcont
  have hmul : ∀ᶠ r in 𝓝 q, r * φ r < 1 := by
    have hnh : Iio (1 : ℝ) ∈ 𝓝 (q * φ q) := by
      rw [hφq]
      exact Iio_mem_nhds hqmul
    exact hmulcont.eventually hnh
  have heq : ∀ᶠ r in 𝓝 q, innerResidual (r, φ r) = 0 := by
    filter_upwards [h.apply_implicitFunction] with r hr
    rwa [hbase] at hr
  filter_upwards [Ioi_mem_nhds hq, Iio_mem_nhds hqs, hφgt, hmul, heq] with
    r hr0 hrs hφ1 hrmul hres
  have hφinv : φ r < r⁻¹ := by
    rw [← one_div]
    rw [lt_div_iff₀ hr0]
    nlinarith
  have hext : exteriorFunction r (φ r) = 0 := by
    rw [← innerResidual_eq_exteriorFunction hr0 hφinv]
    exact hres
  have hroot : exteriorEquation r (φ r) :=
    exteriorEquation_iff_exteriorFunction_eq_zero.2 hext
  exact (exteriorEquation_inner_iff_eq_uPlus hr0 hrs hφ1 hφinv).1 hroot |>.symm

theorem uMinus_eventuallyEq_implicitFunction {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    uMinus =ᶠ[𝓝 q] (outerImplicitData hq hqs.le).implicitFunction := by
  let h := outerImplicitData hq hqs.le
  let φ : ℝ → ℝ := h.implicitFunction
  have hum := uMinus_spec hq hqs.le
  have hbase : outerResidual (q, uMinus q) = 0 := by
    rw [outerResidual_eq_exteriorFunction hq hum.1]
    exact exteriorEquation_iff_exteriorFunction_eq_zero.1 hum.2
  have hφq : φ q = uMinus q := by
    exact h.eventually_implicitFunction_apply_eq.self_of_nhds.mp rfl
  have hφcont : ContinuousAt φ q := h.contDiffAt_implicitFunction.continuousAt
  have hqmul : 1 < q * uMinus q := by
    have hmul := mul_lt_mul_of_pos_left hum.1 hq
    rw [mul_inv_cancel₀ hq.ne'] at hmul
    exact hmul
  have hmulcont : ContinuousAt (fun r : ℝ ↦ r * φ r) q :=
    continuousAt_id.mul hφcont
  have hmul : ∀ᶠ r in 𝓝 q, 1 < r * φ r := by
    have hnh : Ioi (1 : ℝ) ∈ 𝓝 (q * φ q) := by
      rw [hφq]
      exact Ioi_mem_nhds hqmul
    exact hmulcont.eventually hnh
  have heq : ∀ᶠ r in 𝓝 q, outerResidual (r, φ r) = 0 := by
    filter_upwards [h.apply_implicitFunction] with r hr
    rwa [hbase] at hr
  filter_upwards [Ioi_mem_nhds hq, Iio_mem_nhds hqs, hmul, heq] with
    r hr0 hrs hrmul hres
  have hinvφ : r⁻¹ < φ r := by
    rw [← one_div]
    rw [div_lt_iff₀ hr0]
    nlinarith
  have hext : exteriorFunction r (φ r) = 0 := by
    rw [← outerResidual_eq_exteriorFunction hr0 hinvφ]
    exact hres
  have hroot : exteriorEquation r (φ r) :=
    exteriorEquation_iff_exteriorFunction_eq_zero.2 hext
  exact (exteriorEquation_outer_iff_eq_uMinus hr0 hrs.le hinvφ).1 hroot |>.symm

theorem differentiableAt_uPlus {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    DifferentiableAt ℝ uPlus q := by
  let h := innerImplicitData hq hqs
  have hdiff : DifferentiableAt ℝ h.implicitFunction q :=
    h.contDiffAt_implicitFunction.differentiableAt (by simp)
  exact hdiff.congr_of_eventuallyEq (uPlus_eventuallyEq_implicitFunction hq hqs)

theorem differentiableAt_uMinus {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    DifferentiableAt ℝ uMinus q := by
  let h := outerImplicitData hq hqs.le
  have hdiff : DifferentiableAt ℝ h.implicitFunction q :=
    h.contDiffAt_implicitFunction.differentiableAt (by simp)
  exact hdiff.congr_of_eventuallyEq (uMinus_eventuallyEq_implicitFunction hq hqs)

theorem continuousAt_uPlus {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    ContinuousAt uPlus q := (differentiableAt_uPlus hq hqs).continuousAt

theorem continuousAt_uMinus {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    ContinuousAt uMinus q := (differentiableAt_uMinus hq hqs).continuousAt

/-! ## Implicit derivative formulas -/

theorem implicit_derivative_eq
    {f : ℝ × ℝ → ℝ} {g : ℝ → ℝ} {f' : ℝ × ℝ →L[ℝ] ℝ}
    {q u Fq Fu g' : ℝ}
    (hf : HasFDerivAt f f' (q, u))
    (hqx : HasDerivAt (fun r : ℝ ↦ f (r, u)) Fq q)
    (huy : HasDerivAt (fun v : ℝ ↦ f (q, v)) Fu u)
    (hg : HasDerivAt g g' q) (hgu : g q = u)
    (heq : (fun r : ℝ ↦ f (r, g r)) =ᶠ[𝓝 q] fun _ ↦ f (q, u))
    (hFu : Fu ≠ 0) :
    g' = -Fq / Fu := by
  have hxembed : HasDerivAt (fun r : ℝ ↦ (r, u)) (1, 0) q :=
    (hasDerivAt_id q).prodMk (hasDerivAt_const q u)
  have hyembed : HasDerivAt (fun v : ℝ ↦ (q, v)) (0, 1) u :=
    (hasDerivAt_const u q).prodMk (hasDerivAt_id u)
  have hqx' : HasDerivAt (fun r : ℝ ↦ f (r, u)) (f' (1, 0)) q := by
    convert! hf.comp_hasDerivAt q hxembed using 1
  have huy' : HasDerivAt (fun v : ℝ ↦ f (q, v)) (f' (0, 1)) u := by
    convert! hf.comp_hasDerivAt u hyembed using 1
  have hfx : f' (1, 0) = Fq := hqx'.unique hqx
  have hfy : f' (0, 1) = Fu := huy'.unique huy
  have hpair : HasDerivAt (fun r : ℝ ↦ (r, g r)) (1, g') q :=
    (hasDerivAt_id q).prodMk hg
  have hcomp : HasDerivAt (fun r : ℝ ↦ f (r, g r)) (f' (1, g')) q := by
    convert! hf.comp_hasDerivAt_of_eq q hpair (by simp [hgu]) using 1
  have hconst : HasDerivAt (fun r : ℝ ↦ f (r, g r)) 0 q :=
    (hasDerivAt_const q (f (q, u))).congr_of_eventuallyEq heq
  have htotal : f' (1, g') = 0 := hcomp.unique hconst
  have hsplit : f' (1, g') = Fq + g' * Fu := by
    calc
      f' (1, g') = f' ((1, 0) + g' • (0, 1)) := by
        congr 1
        ext <;> simp [smul_eq_mul]
      _ = f' (1, 0) + g' • f' (0, 1) := by rw [map_add, map_smul]
      _ = Fq + g' * Fu := by rw [hfx, hfy]; simp [smul_eq_mul]
  rw [hsplit] at htotal
  apply (eq_div_iff hFu).2
  nlinarith

theorem hasDerivAt_innerResidual_left {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hu : 0 < u)
    (hqu : q < u) (huq : u < q⁻¹) :
    HasDerivAt (fun r : ℝ ↦ innerResidual (r, u)) (innerPartialQ q u) q := by
  have hcd : ContDiffAt ℝ ⊤ (fun r : ℝ ↦ innerResidual (r, u)) q :=
    (contDiffAt_innerResidual hq hq1 hu hqu huq).comp q
      (contDiffAt_id.prodMk contDiffAt_const)
  exact hcd.differentiableAt (by simp) |>.hasDerivAt

theorem hasDerivAt_outerResidual_left {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (huq : q⁻¹ < u) :
    HasDerivAt (fun r : ℝ ↦ outerResidual (r, u)) (outerPartialQ q u) q := by
  have hcd : ContDiffAt ℝ ⊤ (fun r : ℝ ↦ outerResidual (r, u)) q :=
    (contDiffAt_outerResidual hq hq1 huq).comp q
      (contDiffAt_id.prodMk contDiffAt_const)
  exact hcd.differentiableAt (by simp) |>.hasDerivAt

theorem innerResidual_uPlus_eventually_zero {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    ∀ᶠ r in 𝓝 q, innerResidual (r, uPlus r) = 0 := by
  filter_upwards [Ioi_mem_nhds hq, Iio_mem_nhds hqs] with r hr hrs
  have hur := uPlus_spec hr hrs
  rw [innerResidual_eq_exteriorFunction hr hur.2.1]
  exact exteriorEquation_iff_exteriorFunction_eq_zero.1 hur.2.2

theorem outerResidual_uMinus_eventually_zero {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    ∀ᶠ r in 𝓝 q, outerResidual (r, uMinus r) = 0 := by
  filter_upwards [Ioi_mem_nhds hq, Iio_mem_nhds hqs] with r hr hrs
  have hur := uMinus_spec hr hrs.le
  rw [outerResidual_eq_exteriorFunction hr hur.1]
  exact exteriorEquation_iff_exteriorFunction_eq_zero.1 hur.2

theorem hasDerivAt_uPlus {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    HasDerivAt uPlus
      (-innerPartialQ q (uPlus q) / innerPartialU q (uPlus q)) q := by
  have hup := uPlus_spec hq hqs
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hu : 0 < uPlus q := (by norm_num : (0 : ℝ) < 1).trans hup.1
  have hqu : q < uPlus q := hq1.trans hup.1
  have hf : HasFDerivAt innerResidual (fderiv ℝ innerResidual (q, uPlus q))
      (q, uPlus q) :=
    ((contDiffAt_innerResidual hq hq1 hu hqu hup.2.1).differentiableAt (by simp)).hasFDerivAt
  have hqx := hasDerivAt_innerResidual_left hq hq1 hu hqu hup.2.1
  have huy := hasDerivAt_innerResidual_right hq hu hqu hup.2.1
  have hg := (differentiableAt_uPlus hq hqs).hasDerivAt
  have hbase : innerResidual (q, uPlus q) = 0 :=
    (innerResidual_uPlus_eventually_zero hq hqs).self_of_nhds
  have heq : (fun r : ℝ ↦ innerResidual (r, uPlus r)) =ᶠ[𝓝 q]
      fun _ ↦ innerResidual (q, uPlus q) := by
    filter_upwards [innerResidual_uPlus_eventually_zero hq hqs] with r hr
    rw [hr, hbase]
  have hderiv := implicit_derivative_eq hf hqx huy hg rfl heq
    (innerPartialU_uPlus_pos hq hqs).ne'
  rwa [hderiv] at hg

theorem hasDerivAt_uMinus {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    HasDerivAt uMinus
      (-outerPartialQ q (uMinus q) / outerPartialU q (uMinus q)) q := by
  have hum := uMinus_spec hq hqs.le
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hf : HasFDerivAt outerResidual (fderiv ℝ outerResidual (q, uMinus q))
      (q, uMinus q) :=
    ((contDiffAt_outerResidual hq hq1 hum.1).differentiableAt (by simp)).hasFDerivAt
  have hqx := hasDerivAt_outerResidual_left hq hq1 hum.1
  have huy := hasDerivAt_outerResidual_right hq hq1 hum.1
  have hg := (differentiableAt_uMinus hq hqs).hasDerivAt
  have hbase : outerResidual (q, uMinus q) = 0 :=
    (outerResidual_uMinus_eventually_zero hq hqs).self_of_nhds
  have heq : (fun r : ℝ ↦ outerResidual (r, uMinus r)) =ᶠ[𝓝 q]
      fun _ ↦ outerResidual (q, uMinus q) := by
    filter_upwards [outerResidual_uMinus_eventually_zero hq hqs] with r hr
    rw [hr, hbase]
  have hderiv := implicit_derivative_eq hf hqx huy hg rfl heq
    (outerPartialU_uMinus_neg hq hqs.le).ne
  rwa [hderiv] at hg

/-! ## Derivative of the length -/

def Hprime (q : ℝ) : ℝ := 2 * (1 - q) / (1 + q) ^ 3

def reciprocalSum (u : ℝ) : ℝ := u + u⁻¹

def uPlusSlope (q : ℝ) : ℝ :=
  -innerPartialQ q (uPlus q) / innerPartialU q (uPlus q)

def uMinusSlope (q : ℝ) : ℝ :=
  -outerPartialQ q (uMinus q) / outerPartialU q (uMinus q)

def LambdaDerivative (q : ℝ) : ℝ :=
  Hprime q * (reciprocalSum (uMinus q) - reciprocalSum (uPlus q)) +
    H q * ((1 - (uMinus q)⁻¹ ^ 2) * uMinusSlope q -
      (1 - (uPlus q)⁻¹ ^ 2) * uPlusSlope q)

theorem hasDerivAt_H {q : ℝ} (hq : q ≠ -1) : HasDerivAt H (Hprime q) q := by
  have hden : 1 + q ≠ 0 := by
    intro h
    apply hq
    linarith
  have hadd : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 q := by
    simpa using! (hasDerivAt_const q (1 : ℝ)).add (hasDerivAt_id q)
  have hpow : HasDerivAt (fun x : ℝ ↦ (1 + x) ^ 2) (2 * (1 + q)) q := by
    convert! hadd.pow 2 using 1
    all_goals ring
  have hnum : HasDerivAt (fun x : ℝ ↦ 2 * x) 2 q := by
    simpa using! (hasDerivAt_id q).const_mul 2
  unfold H Hprime
  convert! hnum.div hpow (pow_ne_zero 2 hden) using 1
  field_simp [hden]
  ring

def Aprime (q : ℝ) : ℝ :=
  ((Hprime q / H q) * Real.log q - Real.log (H q) * (1 / q)) /
    (Real.log q) ^ 2

def innerPartialQFormula (q u : ℝ) : ℝ :=
  Aprime q * Real.log ((u - q) / (1 - q * u)) +
    A q * (u ^ 2 - 1) / ((u - q) * (1 - q * u))

def outerPartialQFormula (q u : ℝ) : ℝ :=
  Aprime q * Real.log ((u - q) / (q * u - 1)) +
    A q * (1 - u ^ 2) / ((u - q) * (q * u - 1))

theorem hasDerivAt_A {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasDerivAt A (Aprime q) q := by
  have hH : H q ≠ 0 := (H_pos hq).ne'
  have hlogq : Real.log q ≠ 0 := log_q_ne_zero hq hq1
  have hlogH := (hasDerivAt_H (by linarith : q ≠ -1)).log hH
  have hlog := Real.hasDerivAt_log hq.ne'
  unfold A Aprime
  convert! hlogH.div hlog hlogq using 1
  ring

theorem hasDerivAt_innerResidual_left_formula {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hqu : q < u) (huq : u < q⁻¹) :
    HasDerivAt (fun r : ℝ ↦ innerResidual (r, u))
      (innerPartialQFormula q u) q := by
  have hdenpos : 0 < 1 - q * u := by
    have hmul := mul_lt_mul_of_pos_left huq hq
    rw [mul_inv_cancel₀ hq.ne'] at hmul
    linarith
  have hnumpos : 0 < u - q := sub_pos.mpr hqu
  have hnum : HasDerivAt (fun r : ℝ ↦ u - r) (-1) q := by
    simpa using! (hasDerivAt_const q u).sub (hasDerivAt_id q)
  have hden : HasDerivAt (fun r : ℝ ↦ 1 - r * u) (-u) q := by
    simpa using! (hasDerivAt_const q (1 : ℝ)).sub ((hasDerivAt_id q).mul_const u)
  have hquot := hnum.div hden hdenpos.ne'
  have harg : (u - q) / (1 - q * u) ≠ 0 :=
    div_ne_zero hnumpos.ne' hdenpos.ne'
  have hlog := hquot.log harg
  have hmain := (hasDerivAt_A hq hq1).mul hlog
  have hres := hmain.sub (hasDerivAt_const q (Real.log u))
  convert! hres using 1
  simp only [Pi.div_apply]
  rw [innerPartialQFormula]
  field_simp [hnumpos.ne', hdenpos.ne']
  ring

theorem innerPartialQ_eq_formula {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hu : 0 < u)
    (hqu : q < u) (huq : u < q⁻¹) :
    innerPartialQ q u = innerPartialQFormula q u :=
  (hasDerivAt_innerResidual_left hq hq1 hu hqu huq).unique
    (hasDerivAt_innerResidual_left_formula hq hq1 hqu huq)

theorem hasDerivAt_outerResidual_left_formula {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (huq : q⁻¹ < u) :
    HasDerivAt (fun r : ℝ ↦ outerResidual (r, u))
      (outerPartialQFormula q u) q := by
  have hdenpos : 0 < q * u - 1 := by
    have hmul := mul_lt_mul_of_pos_left huq hq
    rw [mul_inv_cancel₀ hq.ne'] at hmul
    linarith
  have hqinv : q < q⁻¹ := hq1.trans (one_lt_inv_q hq hq1)
  have hnumpos : 0 < u - q := sub_pos.mpr (hqinv.trans huq)
  have hnum : HasDerivAt (fun r : ℝ ↦ u - r) (-1) q := by
    simpa using! (hasDerivAt_const q u).sub (hasDerivAt_id q)
  have hden : HasDerivAt (fun r : ℝ ↦ r * u - 1) u q := by
    simpa using! ((hasDerivAt_id q).mul_const u).sub_const 1
  have hquot := hnum.div hden hdenpos.ne'
  have harg : (u - q) / (q * u - 1) ≠ 0 :=
    div_ne_zero hnumpos.ne' hdenpos.ne'
  have hlog := hquot.log harg
  have hmain := (hasDerivAt_A hq hq1).mul hlog
  have hres := hmain.sub (hasDerivAt_const q (Real.log u))
  convert! hres using 1
  simp only [Pi.div_apply]
  rw [outerPartialQFormula]
  field_simp [hnumpos.ne', hdenpos.ne']
  ring

theorem outerPartialQ_eq_formula {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (huq : q⁻¹ < u) :
    outerPartialQ q u = outerPartialQFormula q u :=
  (hasDerivAt_outerResidual_left hq hq1 huq).unique
    (hasDerivAt_outerResidual_left_formula hq hq1 huq)

def uPlusSlopeFormula (q : ℝ) : ℝ :=
  -innerPartialQFormula q (uPlus q) / innerPartialU q (uPlus q)

def uMinusSlopeFormula (q : ℝ) : ℝ :=
  -outerPartialQFormula q (uMinus q) / outerPartialU q (uMinus q)

def LambdaDerivativeFormula (q : ℝ) : ℝ :=
  Hprime q * (reciprocalSum (uMinus q) - reciprocalSum (uPlus q)) +
    H q * ((1 - (uMinus q)⁻¹ ^ 2) * uMinusSlopeFormula q -
      (1 - (uPlus q)⁻¹ ^ 2) * uPlusSlopeFormula q)

theorem uPlusSlope_eq_formula {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    uPlusSlope q = uPlusSlopeFormula q := by
  have hup := uPlus_spec hq hqs
  rw [uPlusSlope, uPlusSlopeFormula,
    innerPartialQ_eq_formula hq (q_lt_one_of_pos_le_qSoft hq hqs.le)
      ((by norm_num : (0 : ℝ) < 1).trans hup.1)
      ((q_lt_one_of_pos_le_qSoft hq hqs.le).trans hup.1) hup.2.1]

theorem uMinusSlope_eq_formula {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    uMinusSlope q = uMinusSlopeFormula q := by
  have hum := uMinus_spec hq hqs.le
  rw [uMinusSlope, uMinusSlopeFormula,
    outerPartialQ_eq_formula hq (q_lt_one_of_pos_le_qSoft hq hqs.le) hum.1]

theorem LambdaDerivative_eq_formula {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    LambdaDerivative q = LambdaDerivativeFormula q := by
  rw [LambdaDerivative, LambdaDerivativeFormula,
    uPlusSlope_eq_formula hq hqs, uMinusSlope_eq_formula hq hqs]

/-! ## The stable scaled-root chart used by the interval certificate -/

def zPlus (q : ℝ) : ℝ := q * uPlus q

def zMinus (q : ℝ) : ℝ := q * uMinus q

def scaledLambdaExpression (q zp zm : ℝ) : ℝ :=
  2 * (zm - zp) / (1 + q) ^ 2 +
    2 * q ^ 2 / (1 + q) ^ 2 * (zm⁻¹ - zp⁻¹)

def scaledD (q : ℝ) : ℝ := Real.log (2 / (1 + q) ^ 2)

def scaledResidual (q z : ℝ) : ℝ :=
  A q * Real.log ((z - q ^ 2) / |1 - z|) - Real.log z - scaledD q

theorem A_mul_log_q {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    A q * Real.log q = Real.log (H q) := by
  rw [A]
  field_simp [log_q_ne_zero hq hq1]

theorem scaledD_eq_log_H_sub_log_q {q : ℝ} (hq : 0 < q) :
    scaledD q = Real.log (H q) - Real.log q := by
  have hq0 : q ≠ 0 := hq.ne'
  have hH0 : H q ≠ 0 := (H_pos hq).ne'
  have hratio : 2 / (1 + q) ^ 2 = H q / q := by
    rw [H]
    field_simp [hq0]
  rw [scaledD, hratio, Real.log_div hH0 hq0]

theorem scaledResidual_mul_eq_exteriorFunction {q u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hu : 0 < u)
    (hqu : q < u) (hpole : q * u ≠ 1) :
    scaledResidual q (q * u) = exteriorFunction q u := by
  have habs : |1 - q * u| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hpole.symm)
  have hratio : 0 < (u - q) / |1 - q * u| :=
    div_pos (sub_pos.mpr hqu) (abs_pos.mpr (sub_ne_zero.mpr hpole.symm))
  have hfactor : (q * u - q ^ 2) / |1 - q * u| =
      q * ((u - q) / |1 - q * u|) := by
    field_simp [habs]
  rw [scaledResidual, exteriorFunction, scaledD_eq_log_H_sub_log_q hq,
    hfactor, Real.log_mul hq.ne' hratio.ne', Real.log_mul hq.ne' hu.ne']
  rw [mul_add, A_mul_log_q hq hq1]
  ring

theorem zPlus_pos {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    0 < zPlus q := by
  rw [zPlus]
  exact mul_pos hq ((by norm_num : (0 : ℝ) < 1).trans (uPlus_spec hq hqs).1)

theorem zPlus_lt_one {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    zPlus q < 1 := by
  rw [zPlus]
  have hmul := mul_lt_mul_of_pos_left (uPlus_spec hq hqs).2.1 hq
  rw [mul_inv_cancel₀ hq.ne'] at hmul
  exact hmul

theorem one_lt_zMinus {q : ℝ} (hq : 0 < q) (hqs : q ≤ qSoft) :
    1 < zMinus q := by
  rw [zMinus]
  have hmul := mul_lt_mul_of_pos_left (uMinus_spec hq hqs).1 hq
  rw [mul_inv_cancel₀ hq.ne'] at hmul
  exact hmul

theorem scaledResidual_zPlus {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    scaledResidual q (zPlus q) = 0 := by
  have hup := uPlus_spec hq hqs
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hpole : q * uPlus q ≠ 1 := by
    intro heq
    have hz := zPlus_lt_one hq hqs
    rw [zPlus, heq] at hz
    exact (lt_irrefl 1) hz
  rw [zPlus, scaledResidual_mul_eq_exteriorFunction hq hq1
    ((by norm_num : (0 : ℝ) < 1).trans hup.1) (hq1.trans hup.1)
    hpole]
  exact exteriorEquation_iff_exteriorFunction_eq_zero.1 hup.2.2

theorem scaledResidual_zMinus {q : ℝ} (hq : 0 < q) (hqs : q ≤ qSoft) :
    scaledResidual q (zMinus q) = 0 := by
  have hum := uMinus_spec hq hqs
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs
  have hpole : q * uMinus q ≠ 1 := by
    intro heq
    have hz := one_lt_zMinus hq hqs
    rw [zMinus, heq] at hz
    exact (lt_irrefl 1) hz
  rw [zMinus, scaledResidual_mul_eq_exteriorFunction hq hq1
    ((inv_pos.mpr hq).trans hum.1)
    (hq1.trans (one_lt_inv_q hq hq1) |>.trans hum.1)
    hpole]
  exact exteriorEquation_iff_exteriorFunction_eq_zero.1 hum.2

theorem Lambda_eq_scaledLambdaExpression {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    Lambda q = scaledLambdaExpression q (zPlus q) (zMinus q) := by
  have hup0 : uPlus q ≠ 0 :=
    ((by norm_num : (0 : ℝ) < 1).trans (uPlus_spec hq hqs).1).ne'
  have hum0 : uMinus q ≠ 0 :=
    ((inv_pos.mpr hq).trans (uMinus_spec hq hqs.le).1).ne'
  have hden : 1 + q ≠ 0 := by linarith
  rw [Lambda, scaledLambdaExpression, zPlus, zMinus, H]
  field_simp [hq.ne', hup0, hum0, hden]
  ring

theorem hasDerivAt_reciprocalSum {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt reciprocalSum (1 - u⁻¹ ^ 2) u := by
  unfold reciprocalSum
  convert! (hasDerivAt_id u).add (hasDerivAt_inv hu) using 1
  field_simp [hu]
  ring

theorem hasDerivAt_reciprocalSum_uPlus {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    HasDerivAt (fun r : ℝ ↦ reciprocalSum (uPlus r))
      ((1 - (uPlus q)⁻¹ ^ 2) * uPlusSlope q) q := by
  have hup := uPlus_spec hq hqs
  have hcomp := (hasDerivAt_reciprocalSum
    ((lt_trans (by norm_num) hup.1).ne')).comp q (hasDerivAt_uPlus hq hqs)
  simpa [uPlusSlope, Function.comp_def] using! hcomp

theorem hasDerivAt_reciprocalSum_uMinus {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    HasDerivAt (fun r : ℝ ↦ reciprocalSum (uMinus r))
      ((1 - (uMinus q)⁻¹ ^ 2) * uMinusSlope q) q := by
  have hum := uMinus_spec hq hqs.le
  have hu : 0 < uMinus q := (inv_pos.mpr hq).trans hum.1
  have hcomp := (hasDerivAt_reciprocalSum hu.ne').comp q (hasDerivAt_uMinus hq hqs)
  simpa [uMinusSlope, Function.comp_def] using! hcomp

theorem hasDerivAt_Lambda {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    HasDerivAt Lambda (LambdaDerivative q) q := by
  have hH := hasDerivAt_H (by linarith : q ≠ -1)
  have hm := hasDerivAt_reciprocalSum_uMinus hq hqs
  have hp := hasDerivAt_reciprocalSum_uPlus hq hqs
  have hdiff := hm.sub hp
  have hprod := hH.mul hdiff
  convert! hprod using 1
  funext r
  simp only [Lambda, reciprocalSum, Pi.mul_apply, Pi.sub_apply]
  ring

theorem Lambda_deriv {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    deriv Lambda q = LambdaDerivative q := (hasDerivAt_Lambda hq hqs).deriv

theorem differentiableAt_Lambda {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    DifferentiableAt ℝ Lambda q := (hasDerivAt_Lambda hq hqs).differentiableAt

theorem continuousAt_Lambda {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    ContinuousAt Lambda q := (hasDerivAt_Lambda hq hqs).continuousAt

theorem continuousOn_Lambda_Ioo : ContinuousOn Lambda (Ioo (0 : ℝ) qSoft) := by
  intro q hq
  exact (continuousAt_Lambda hq.1 hq.2).continuousWithinAt

/-! ## Analytic reduction of the global minimization certificate -/

theorem Lambda_strictAntiOn_Ioc_of_deriv_neg {c : ℝ}
    (hcs : c < qSoft)
    (hneg : ∀ q ∈ Ioo (0 : ℝ) c, deriv Lambda q < 0) :
    StrictAntiOn Lambda (Ioc (0 : ℝ) c) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 c)
  · intro q hq
    exact (continuousAt_Lambda hq.1 (hq.2.trans_lt hcs)).continuousWithinAt
  · rw [interior_Ioc]
    exact hneg

theorem Lambda_strictMonoOn_Icc_of_deriv_pos {c b : ℝ}
    (hc0 : 0 < c) (hbs : b < qSoft)
    (hpos : ∀ q ∈ Ioo c qSoft, 0 < deriv Lambda q) :
    StrictMonoOn Lambda (Icc c b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc c b)
  · intro q hq
    exact (continuousAt_Lambda (hc0.trans_le hq.1) (hq.2.trans_lt hbs)).continuousWithinAt
  · rw [interior_Icc]
    intro q hq
    exact hpos q ⟨hq.1, hq.2.trans hbs⟩

theorem lambda_lt_of_ne_of_deriv_sign {c q : ℝ}
    (hc0 : 0 < c) (hcs : c < qSoft)
    (hq : q ∈ Ioc (0 : ℝ) qSoft) (hqc : q ≠ c)
    (hneg : ∀ r ∈ Ioo (0 : ℝ) c, deriv Lambda r < 0)
    (hpos : ∀ r ∈ Ioo c qSoft, 0 < deriv Lambda r)
    (hend : Lambda c < Lambda qSoft) :
    Lambda c < Lambda q := by
  rcases lt_or_gt_of_ne hqc with hqclt | hcqlt
  · exact Lambda_strictAntiOn_Ioc_of_deriv_neg hcs hneg
      ⟨hq.1, hqclt.le⟩ ⟨hc0, le_rfl⟩ hqclt
  · rcases hq.2.eq_or_lt with rfl | hqsoft
    · exact hend
    · exact Lambda_strictMonoOn_Icc_of_deriv_pos hc0 hqsoft hpos
        ⟨le_rfl, hcqlt.le⟩ ⟨hcqlt.le, le_rfl⟩ hcqlt

theorem unique_lambda_minimizer_of_deriv_sign {c : ℝ}
    (hc0 : 0 < c) (hcs : c < qSoft)
    (hneg : ∀ q ∈ Ioo (0 : ℝ) c, deriv Lambda q < 0)
    (hpos : ∀ q ∈ Ioo c qSoft, 0 < deriv Lambda q)
    (hend : Lambda c < Lambda qSoft) :
    (∃! q : ℝ, IsLambdaMinimizer q) ∧ IsLambdaMinimizer qStar ∧ qStar = c := by
  have hcmin : IsLambdaMinimizer c := by
    refine ⟨⟨hc0, hcs.le⟩, ?_⟩
    intro q hq
    rcases eq_or_ne q c with rfl | hne
    · exact le_rfl
    · exact (lambda_lt_of_ne_of_deriv_sign hc0 hcs hq hne hneg hpos hend).le
  have huniq : ∀ q : ℝ, IsLambdaMinimizer q → q = c := by
    intro q hq
    by_contra hne
    have hstrict := lambda_lt_of_ne_of_deriv_sign hc0 hcs hq.1 hne hneg hpos hend
    exact (not_lt_of_ge (hq.2 c hcmin.1)) hstrict
  have hex : ∃! q : ℝ, IsLambdaMinimizer q := ⟨c, hcmin, huniq⟩
  have hset : {q : ℝ | IsLambdaMinimizer q} = {c} := by
    ext q
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · exact huniq q
    · rintro rfl
      exact hcmin
  have hqstar : qStar = c := by
    rw [qStar, hset, csInf_singleton]
  exact ⟨hex, hqstar.symm ▸ hcmin, hqstar⟩

/-! ## Exact decimal targets and the certificate interface -/

def qStarLowerRat : Rat := 25715536866527 / 1000000000000000

def qStarUpperRat : Rat := 25715536866528 / 1000000000000000

def lambdaLowerRat : Rat := 1834430475762661 / 1000000000000000

def lambdaUpperRat : Rat := 1834430475762662 / 1000000000000000

theorem qStar_decimal_interval_nonempty :
    (qStarLowerRat : ℝ) < (qStarUpperRat : ℝ) := by
  norm_num [qStarLowerRat, qStarUpperRat]

theorem lambda_decimal_interval_nonempty :
    (lambdaLowerRat : ℝ) < (lambdaUpperRat : ℝ) := by
  norm_num [lambdaLowerRat, lambdaUpperRat]

theorem qStar_candidate_interval_in_domain :
    (0 : ℝ) < (qStarLowerRat : ℝ) ∧ (qStarUpperRat : ℝ) < qSoft := by
  constructor
  · norm_num [qStarLowerRat]
  · exact (by
      norm_num [qStarUpperRat, qSoftLowerRat] :
        (qStarUpperRat : ℝ) < (qSoftLowerRat : ℝ)).trans qSoftLower_lt_qSoft

/--
This theorem records the exact remaining kernel-level leaves of the one-cut
interval certificate.  Its conclusion is precisely the minimizer and decimal
part of `MainTheorem`.  In particular, the hypotheses mention the explicit
function `LambdaDerivative`, not an opaque numerical oracle.
-/
theorem oneCut_global_certificate_reduction {c : ℝ}
    (hcbox : (qStarLowerRat : ℝ) < c ∧ c < (qStarUpperRat : ℝ))
    (hneg : ∀ q ∈ Ioo (0 : ℝ) c, LambdaDerivativeFormula q < 0)
    (hpos : ∀ q ∈ Ioo c qSoft, 0 < LambdaDerivativeFormula q)
    (hend : Lambda c < Lambda qSoft)
    (hLbox : (lambdaLowerRat : ℝ) < Lambda c ∧
      Lambda c < (lambdaUpperRat : ℝ)) :
    (∃! q : ℝ, IsLambdaMinimizer q) ∧
      IsLambdaMinimizer qStar ∧
      (25715536866527 / 10 ^ 15 : ℝ) < qStar ∧
      qStar < (25715536866528 / 10 ^ 15 : ℝ) ∧
      (1834430475762661 / 10 ^ 15 : ℝ) < L ∧
      L < (1834430475762662 / 10 ^ 15 : ℝ) := by
  have hc0 : 0 < c := qStar_candidate_interval_in_domain.1.trans hcbox.1
  have hcs : c < qSoft :=
    hcbox.2.trans qStar_candidate_interval_in_domain.2
  have hneg' : ∀ q ∈ Ioo (0 : ℝ) c, deriv Lambda q < 0 := by
    intro q hq
    rw [Lambda_deriv hq.1 (hq.2.trans hcs)]
    rw [LambdaDerivative_eq_formula hq.1 (hq.2.trans hcs)]
    exact hneg q hq
  have hpos' : ∀ q ∈ Ioo c qSoft, 0 < deriv Lambda q := by
    intro q hq
    rw [Lambda_deriv (hc0.trans hq.1) hq.2]
    rw [LambdaDerivative_eq_formula (hc0.trans hq.1) hq.2]
    exact hpos q hq
  obtain ⟨hex, hmin, hqstar⟩ :=
    unique_lambda_minimizer_of_deriv_sign hc0 hcs hneg' hpos' hend
  have hqlo : (25715536866527 / 10 ^ 15 : ℝ) < qStar := by
    rw [hqstar]
    have heq : (25715536866527 / 10 ^ 15 : ℝ) = (qStarLowerRat : ℝ) := by
      norm_num [qStarLowerRat]
    rw [heq]
    exact hcbox.1
  have hqhi : qStar < (25715536866528 / 10 ^ 15 : ℝ) := by
    rw [hqstar]
    have heq : (25715536866528 / 10 ^ 15 : ℝ) = (qStarUpperRat : ℝ) := by
      norm_num [qStarUpperRat]
    rw [heq]
    exact hcbox.2
  have hL : L = Lambda c := by rw [L, hqstar]
  have hLlo : (1834430475762661 / 10 ^ 15 : ℝ) < L := by
    rw [hL]
    have heq : (1834430475762661 / 10 ^ 15 : ℝ) = (lambdaLowerRat : ℝ) := by
      norm_num [lambdaLowerRat]
    rw [heq]
    exact hLbox.1
  have hLhi : L < (1834430475762662 / 10 ^ 15 : ℝ) := by
    rw [hL]
    have heq : (1834430475762662 / 10 ^ 15 : ℝ) = (lambdaUpperRat : ℝ) := by
      norm_num [lambdaUpperRat]
    rw [heq]
    exact hLbox.2
  exact ⟨hex, hmin, hqlo, hqhi, hLlo, hLhi⟩

end

end Erdos1038
