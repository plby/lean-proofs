/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSum
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionRadiusTwelve
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville

/-!
# High derivatives of a zero-regularized logarithmic derivative

This file makes the fixed-disk regular factor available to the Erdos 48
zero detector and applies Cauchy's estimate to its logarithmic derivative.
The factorization argument is the proved one used by the pinned
BoundedGaps development; it is reproduced task-locally because its regular
factor is deliberately private there.
-/

open Filter Function Metric Set
open scoped Topology

namespace BoundedGaps.Maynard

noncomputable section

private noncomputable def selectedDivisor
    (f : ℂ -> ℂ) (c : ℂ) (R : ℝ) : Function.locallyFinsuppWithin
      (closedBall c (2 * R)) ℤ :=
  MeromorphicOn.divisor f (closedBall c (2 * R))

private noncomputable def selectedZeroProduct
    (f : ℂ -> ℂ) (c : ℂ) (R : ℝ) : ℂ -> ℂ :=
  ∏ᶠ rho : ℂ, (fun z => z - rho) ^ selectedDivisor f c R rho

private noncomputable def selectedRawFactor
    (f : ℂ -> ℂ) (c : ℂ) (R : ℝ) : ℂ -> ℂ :=
  (selectedZeroProduct f c R)⁻¹ * f

private noncomputable def selectedRegularFactor
    (f : ℂ -> ℂ) (c : ℂ) (R : ℝ) : ℂ -> ℂ :=
  toMeromorphicNFOn (selectedRawFactor f c R)
    (closedBall c (4 * R))

private theorem selectedDivisor_support_finite
    (f : ℂ -> ℂ) (c : ℂ) (R : ℝ) :
    (selectedDivisor f c R).support.Finite :=
  (selectedDivisor f c R).finiteSupport (isCompact_closedBall c (2 * R))

private theorem analyticOrderAt_ne_top_on_closedBall
    {f : ℂ -> ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    {z : ℂ} (hz : z ∈ closedBall c R) :
    analyticOrderAt f z ≠ ⊤ := by
  have hc_mem : c ∈ closedBall c R := mem_closedBall_self hR
  apply hf.analyticOrderAt_ne_top_of_isPreconnected
    (convex_closedBall c R).isPreconnected hc_mem hz
  rw [(hf c hc_mem).analyticOrderAt_eq_zero.mpr hc]
  exact WithTop.zero_ne_top

private theorem selectedDivisor_apply_eq_order
    {f : ℂ -> ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    {z : ℂ} (hz : z ∈ closedBall c (2 * R)) :
    selectedDivisor f c R z = (analyticOrderNatAt f z : ℤ) := by
  have hf_inner : AnalyticOnNhd ℂ f (closedBall c (2 * R)) :=
    hf.mono (closedBall_subset_closedBall (by linarith))
  have hfinite := analyticOrderAt_ne_top_on_closedBall (by positivity)
    hf_inner hc hz
  rw [selectedDivisor, MeromorphicOn.AnalyticOnNhd.divisor_apply hf_inner hz,
    ← Nat.cast_analyticOrderNatAt hfinite, ENat.map_coe, WithTop.untop₀_coe]

private theorem selectedDivisor_nonneg
    {f : ℂ -> ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) :
    0 ≤ selectedDivisor f c R := by
  exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg
    (hf.mono (closedBall_subset_closedBall (by linarith)))

private theorem meromorphic_selectedZeroProduct
    (f : ℂ -> ℂ) (c : ℂ) (R : ℝ) :
    Meromorphic (selectedZeroProduct f c R) := by
  simpa [selectedZeroProduct] using
    (Function.FactorizedRational.meromorphicNFOn_univ
      (selectedDivisor f c R)).meromorphicOn

private theorem meromorphicOn_selectedRawFactor
    {f : ℂ -> ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) :
    MeromorphicOn (selectedRawFactor f c R) (closedBall c (4 * R)) := by
  exact (meromorphic_selectedZeroProduct f c R).meromorphicOn.inv.mul
    hf.meromorphicOn

private theorem meromorphicOrderAt_selectedRawFactor
    {f : ℂ -> ℂ} {c z : ℂ} {R : ℝ}
    (hfz : AnalyticAt ℂ f z) :
    meromorphicOrderAt (selectedRawFactor f c R) z =
      -(selectedDivisor f c R z : WithTop ℤ) +
        (analyticOrderAt f z).map (↑) := by
  rw [selectedRawFactor,
    meromorphicOrderAt_mul
      ((meromorphic_selectedZeroProduct f c R z).inv) hfz.meromorphicAt,
    meromorphicOrderAt_inv,
    selectedZeroProduct,
    Function.FactorizedRational.meromorphicOrderAt_eq
      (selectedDivisor f c R) (selectedDivisor_support_finite f c R),
    hfz.meromorphicOrderAt_eq]

private theorem meromorphicOrderAt_selectedRawFactor_eq_zero
    {f : ℂ -> ℂ} {c z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hz : z ∈ closedBall c (2 * R)) :
    meromorphicOrderAt (selectedRawFactor f c R) z = 0 := by
  have hz_outer : z ∈ closedBall c (4 * R) :=
    closedBall_subset_closedBall (by linarith) hz
  have hfinite := analyticOrderAt_ne_top_on_closedBall (by positivity) hf hc hz_outer
  rw [meromorphicOrderAt_selectedRawFactor (hf z hz_outer),
    selectedDivisor_apply_eq_order hR hf hc hz,
    ← Nat.cast_analyticOrderNatAt hfinite, ENat.map_coe]
  simp

private theorem meromorphicOrderAt_selectedRawFactor_nonneg
    {f : ℂ -> ℂ} {c z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hz : z ∈ closedBall c (4 * R)) :
    0 ≤ meromorphicOrderAt (selectedRawFactor f c R) z := by
  by_cases hz_inner : z ∈ closedBall c (2 * R)
  · rw [meromorphicOrderAt_selectedRawFactor_eq_zero hR hf hc hz_inner]
  · have hfinite := analyticOrderAt_ne_top_on_closedBall (by positivity) hf hc hz
    rw [meromorphicOrderAt_selectedRawFactor (hf z hz),
      selectedDivisor, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz_inner,
      ← Nat.cast_analyticOrderNatAt hfinite, ENat.map_coe]
    simp only [WithTop.coe_zero, neg_zero, zero_add]
    exact_mod_cast Nat.zero_le (analyticOrderNatAt f z)

private theorem analyticOnNhd_selectedRegularFactor
    {f : ℂ -> ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0) :
    AnalyticOnNhd ℂ (selectedRegularFactor f c R) (closedBall c (4 * R)) := by
  intro z hz
  have hraw := meromorphicOn_selectedRawFactor hf
  have hnf := meromorphicNFOn_toMeromorphicNFOn
    (selectedRawFactor f c R) (closedBall c (4 * R)) hz
  unfold selectedRegularFactor
  rw [← hnf.meromorphicOrderAt_nonneg_iff_analyticAt,
    meromorphicOrderAt_toMeromorphicNFOn hraw hz]
  exact meromorphicOrderAt_selectedRawFactor_nonneg hR hf hc hz

private theorem selectedRegularFactor_ne_zero
    {f : ℂ -> ℂ} {c z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hz : z ∈ closedBall c (2 * R)) :
    selectedRegularFactor f c R z ≠ 0 := by
  have hz_outer : z ∈ closedBall c (4 * R) :=
    closedBall_subset_closedBall (by linarith) hz
  have hraw := meromorphicOn_selectedRawFactor hf
  have hnf := meromorphicNFOn_toMeromorphicNFOn
    (selectedRawFactor f c R) (closedBall c (4 * R)) hz_outer
  unfold selectedRegularFactor
  rw [← hnf.meromorphicOrderAt_eq_zero_iff,
    meromorphicOrderAt_toMeromorphicNFOn hraw hz_outer]
  exact meromorphicOrderAt_selectedRawFactor_eq_zero hR hf hc hz

private theorem selectedZeroProduct_ne_zero_of_divisor_eq_zero
    {f : ℂ -> ℂ} {c z : ℂ} {R : ℝ}
    (hz : selectedDivisor f c R z = 0) :
    selectedZeroProduct f c R z ≠ 0 := by
  simpa [selectedZeroProduct] using
    (Function.FactorizedRational.ne_zero (d := selectedDivisor f c R) hz)

private theorem selectedRegularFactor_eq_raw
    {f : ℂ -> ℂ} {c z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R)))
    (hz : z ∈ closedBall c (4 * R))
    (hPz : selectedZeroProduct f c R z ≠ 0) :
    selectedRegularFactor f c R z = selectedRawFactor f c R z := by
  have hraw := meromorphicOn_selectedRawFactor hf
  have hP_analytic : AnalyticAt ℂ (selectedZeroProduct f c R) z := by
    unfold selectedZeroProduct
    exact Function.FactorizedRational.analyticAt
      (selectedDivisor_nonneg hR hf z)
  have hraw_nf : MeromorphicNFAt (selectedRawFactor f c R) z := by
    apply AnalyticAt.meromorphicNFAt
    unfold selectedRawFactor
    exact (hP_analytic.inv hPz).mul (hf z hz)
  rw [selectedRegularFactor,
    toMeromorphicNFOn_eq_toMeromorphicNFAt hraw hz,
    toMeromorphicNFAt_eq_self.2 hraw_nf]

private theorem selectedDivisor_apply_center_eq_zero
    {f : ℂ -> ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0) :
    selectedDivisor f c R c = 0 := by
  rw [selectedDivisor_apply_eq_order hR hf hc (by simp [hR.le])]
  have horder := (hf c (by simp [hR.le])).analyticOrderAt_eq_zero.mpr hc
  simp [analyticOrderNatAt, horder]

private theorem selectedDivisor_apply_eq_zero_of_ne_zero
    {f : ℂ -> ℂ} {c z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hz : z ∈ closedBall c (2 * R)) (hfz : f z ≠ 0) :
    selectedDivisor f c R z = 0 := by
  rw [selectedDivisor_apply_eq_order hR hf hc hz]
  have hz_outer : z ∈ closedBall c (4 * R) :=
    closedBall_subset_closedBall (by linarith) hz
  have horder := (hf z hz_outer).analyticOrderAt_eq_zero.mpr hfz
  simp [analyticOrderNatAt, horder]

private theorem norm_selectedZeroProduct_center_le_sphere
    {f : ℂ -> ℂ} {c w : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hw : w ∈ sphere c (4 * R)) :
    ‖selectedZeroProduct f c R c‖ ≤ ‖selectedZeroProduct f c R w‖ := by
  let D := selectedDivisor f c R
  have hD : D.support.Finite := selectedDivisor_support_finite f c R
  have hmul (x : ℂ) : (fun rho => (x - rho) ^ D rho).mulSupport ⊆ hD.toFinset := by
    intro rho hrho
    apply hD.mem_toFinset.mpr
    intro hzero
    simp [hzero] at hrho
  rw [selectedZeroProduct, Function.FactorizedRational.finprod_eq_fun hD]
  change ‖∏ᶠ rho : ℂ, (c - rho) ^ D rho‖ ≤
    ‖∏ᶠ rho : ℂ, (w - rho) ^ D rho‖
  rw [finprod_eq_prod_of_mulSupport_subset _ (hmul c),
    finprod_eq_prod_of_mulSupport_subset _ (hmul w), norm_prod, norm_prod]
  apply Finset.prod_le_prod
  · intro rho hrho
    exact norm_nonneg _
  · intro rho hrho
    have hrho_support : rho ∈ D.support := hD.mem_toFinset.mp hrho
    have hrho_inner : rho ∈ closedBall c (2 * R) := D.supportWithinDomain hrho_support
    have hrho_dist : dist rho c ≤ 2 * R := mem_closedBall.mp hrho_inner
    have hbase : ‖c - rho‖ ≤ ‖w - rho‖ := by
      have htriangle := dist_triangle w rho c
      rw [mem_sphere] at hw
      rw [hw] at htriangle
      calc
        ‖c - rho‖ = dist rho c := by
          rw [dist_eq_norm]
          simpa only [neg_sub] using (norm_neg (c - rho)).symm
        _ ≤ 2 * R := hrho_dist
        _ ≤ dist w rho := by linarith [htriangle, hrho_dist]
        _ = ‖w - rho‖ := dist_eq_norm w rho
    rw [selectedDivisor_apply_eq_order hR hf hc hrho_inner]
    simp only [zpow_natCast, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hbase _

private theorem norm_selectedRegularFactor_le_on_outer_sphere
    {f : ℂ -> ℂ} {c w : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hbound : ∀ z ∈ sphere c (4 * R),
      ‖f z‖ ≤ Real.exp M * ‖f c‖)
    (hw : w ∈ sphere c (4 * R)) :
    ‖selectedRegularFactor f c R w‖ ≤
      Real.exp M * ‖selectedRegularFactor f c R c‖ := by
  have hc_outer : c ∈ closedBall c (4 * R) := by simp [hR.le]
  have hw_outer : w ∈ closedBall c (4 * R) := sphere_subset_closedBall hw
  have hw_not_inner : w ∉ closedBall c (2 * R) := by
    intro hw_inner
    have hw_dist := mem_sphere.mp hw
    have hw_inner_dist := mem_closedBall.mp hw_inner
    linarith
  have hDc := selectedDivisor_apply_center_eq_zero hR hf hc
  have hDw : selectedDivisor f c R w = 0 := by
    unfold selectedDivisor
    exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hw_not_inner
  have hPc := selectedZeroProduct_ne_zero_of_divisor_eq_zero hDc
  have hPw := selectedZeroProduct_ne_zero_of_divisor_eq_zero hDw
  rw [selectedRegularFactor_eq_raw hR hf hw_outer hPw,
    selectedRegularFactor_eq_raw hR hf hc_outer hPc]
  simp only [selectedRawFactor, Pi.mul_apply, Pi.inv_apply, norm_mul, norm_inv]
  have hPnorm := norm_selectedZeroProduct_center_le_sphere hR hf hc hw
  have hPinv : ‖selectedZeroProduct f c R w‖⁻¹ ≤
      ‖selectedZeroProduct f c R c‖⁻¹ := by
    exact (inv_le_inv₀ (norm_pos_iff.mpr hPw) (norm_pos_iff.mpr hPc)).2 hPnorm
  calc
    ‖selectedZeroProduct f c R w‖⁻¹ * ‖f w‖
        ≤ ‖selectedZeroProduct f c R w‖⁻¹ *
            (Real.exp M * ‖f c‖) :=
      mul_le_mul_of_nonneg_left (hbound w hw) (inv_nonneg.mpr (norm_nonneg _))
    _ ≤ ‖selectedZeroProduct f c R c‖⁻¹ *
          (Real.exp M * ‖f c‖) :=
      mul_le_mul_of_nonneg_right hPinv (mul_nonneg (Real.exp_pos M).le (norm_nonneg _))
    _ = Real.exp M *
          (‖selectedZeroProduct f c R c‖⁻¹ * ‖f c‖) := by ring

private theorem norm_selectedRegularFactor_le_on_outer_closedBall
    {f : ℂ -> ℂ} {c z : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hbound : ∀ w ∈ sphere c (4 * R),
      ‖f w‖ ≤ Real.exp M * ‖f c‖)
    (hz : z ∈ closedBall c (4 * R)) :
    ‖selectedRegularFactor f c R z‖ ≤
      Real.exp M * ‖selectedRegularFactor f c R c‖ := by
  have h4R : 4 * R ≠ 0 := by positivity
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    ((analyticOnNhd_selectedRegularFactor hR hf hc).differentiableOn.diffContOnCl_ball
      (by rfl))
  · intro w hw
    apply norm_selectedRegularFactor_le_on_outer_sphere hR hf hc hbound
    simpa [frontier_ball c h4R] using hw
  · simpa [closure_ball c h4R] using hz

private theorem norm_logDeriv_selectedRegularFactor_le
    {f : ℂ -> ℂ} {c s : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hbound : ∀ z ∈ sphere c (4 * R), ‖f z‖ ≤ Real.exp M * ‖f c‖)
    (hs : s ∈ closedBall c R) :
    ‖logDeriv (selectedRegularFactor f c R) s‖ ≤ 16 * M / R := by
  let G := selectedRegularFactor f c R
  have hG : AnalyticOnNhd ℂ G (closedBall c (4 * R)) :=
    analyticOnNhd_selectedRegularFactor hR hf hc
  have hGne {z : ℂ} (hz : z ∈ closedBall c (2 * R)) : G z ≠ 0 :=
    selectedRegularFactor_ne_zero hR hf hc hz
  have hlogDiff : DifferentiableOn ℂ (logDeriv G) (ball c (2 * R)) := by
    intro z hz
    have hz' : z ∈ closedBall c (2 * R) := mem_closedBall.mpr (mem_ball.mp hz).le
    have hz'' : z ∈ closedBall c (4 * R) :=
      closedBall_subset_closedBall (by linarith) hz'
    exact (by
      simpa [logDeriv] using ((hG z hz'').deriv.div (hG z hz'') (hGne hz'))
      : AnalyticAt ℂ (logDeriv G) z).differentiableAt.differentiableWithinAt
  obtain ⟨H, hHc, hH⟩ := hlogDiff.isExactOn_ball.with_val_at c 0
  have hHDiff : DifferentiableOn ℂ H (ball c (2 * R)) :=
    fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
  have hc_ball : c ∈ ball c (2 * R) := mem_ball_self (by positivity)
  have hGDiff : DifferentiableOn ℂ G (ball c (2 * R)) := by
    intro z hz
    exact (hG z (closedBall_subset_closedBall (by linarith)
      (mem_closedBall.mpr (mem_ball.mp hz).le))).differentiableAt.differentiableWithinAt
  have hEDiff : DifferentiableOn ℂ (Complex.exp ∘ H) (ball c (2 * R)) := by
    intro z hz
    exact (Complex.differentiableAt_exp.comp z
      (hH z hz).differentiableAt).differentiableWithinAt
  have hlogEq : EqOn (logDeriv (Complex.exp ∘ H)) (logDeriv G) (ball c (2 * R)) := by
    intro z hz
    rw [logDeriv_comp Complex.differentiableAt_exp (hH z hz).differentiableAt]
    simp only [logDeriv_apply, (Complex.hasDerivAt_exp _).deriv,
      div_self (Complex.exp_ne_zero _), one_mul, (hH z hz).deriv]
  obtain ⟨a, ha, hEq⟩ := (logDeriv_eqOn_iff hEDiff hGDiff isOpen_ball
    (convex_ball c (2 * R)).isPreconnected (fun z hz => hGne
      (mem_closedBall.mpr (mem_ball.mp hz).le))
    (fun z _ => Complex.exp_ne_zero (H z))).mp hlogEq
  have hGc : G c ≠ 0 := hGne (by simp [hR.le])
  have ha_eq : a = (G c)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa [hHc, smul_eq_mul] using (hEq hc_ball).symm
  have hHre {z : ℂ} (hz : z ∈ ball c (2 * R)) : (H z).re ≤ M := by
    have hz_outer : z ∈ closedBall c (4 * R) :=
      closedBall_subset_closedBall (by linarith)
        (mem_closedBall.mpr (mem_ball.mp hz).le)
    have hmax := norm_selectedRegularFactor_le_on_outer_closedBall hR hf hc hbound hz_outer
    have hexp : ‖Complex.exp (H z)‖ ≤ Real.exp M := by
      change ‖(Complex.exp ∘ H) z‖ ≤ Real.exp M
      rw [hEq hz, ha_eq]
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv]
      calc
        ‖G c‖⁻¹ * ‖G z‖ ≤ ‖G c‖⁻¹ * (Real.exp M * ‖G c‖) :=
          mul_le_mul_of_nonneg_left hmax (inv_nonneg.mpr (norm_nonneg _))
        _ = Real.exp M := by field_simp
    rw [Complex.norm_exp] at hexp
    exact Real.exp_le_exp.mp hexp
  have hHbound {w : ℂ} (hw : w ∈ sphere s (R / 2)) : ‖H w‖ ≤ 6 * M := by
    have hws : dist w s = R / 2 := mem_sphere.mp hw
    have hsc : dist s c ≤ R := by simpa [dist_comm] using mem_closedBall.mp hs
    have hwc : ‖w - c‖ ≤ 3 * R / 2 := by
      rw [← dist_eq_norm]
      linarith [dist_triangle w s c]
    have huc : w - c ∈ ball (0 : ℂ) (2 * R) := by
      rw [mem_ball_zero_iff]
      linarith
    have hBC := Complex.borelCaratheodory_zero hM (f := fun u => H (c + u)) (R := 2 * R)
      (by
        intro u hu
        have hcu : c + u ∈ ball c (2 * R) := by
          simpa [mem_ball, dist_eq_norm] using hu
        exact ((hH (c + u) hcu).differentiableAt.comp u
          (by fun_prop)).differentiableWithinAt)
      (by
        intro u hu
        have hcu : c + u ∈ ball c (2 * R) := by
          simpa [mem_ball, dist_eq_norm] using hu
        exact hHre hcu)
      (by positivity) huc (by simpa using hHc)
    have hden : 0 < 2 * R - ‖w - c‖ := by linarith
    calc
      ‖H w‖ = ‖H (c + (w - c))‖ := by ring_nf
      _ ≤ 2 * M * ‖w - c‖ / (2 * R - ‖w - c‖) := hBC
      _ ≤ 6 * M := by
        rw [div_le_iff₀ hden]
        nlinarith [mul_nonneg hM.le (norm_nonneg (w - c))]
  have hclosure : closedBall s (R / 2) ⊆ ball c (2 * R) := by
    intro w hw
    have hws : dist w s ≤ R / 2 := mem_closedBall.mp hw
    have hsc : dist s c ≤ R := by simpa [dist_comm] using mem_closedBall.mp hs
    exact mem_ball.mpr (by linarith [dist_triangle w s c])
  have hCauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by positivity : 0 < R / 2)
    (hHDiff.diffContOnCl_ball hclosure)
    (fun w hw => hHbound hw)
  rw [(hH s (hclosure (mem_closedBall_self (by positivity)))).deriv] at hCauchy
  calc
    ‖logDeriv G s‖ ≤ 6 * M / (R / 2) := hCauchy
    _ ≤ 16 * M / R := by
      field_simp
      nlinarith

private theorem logDeriv_factorizedRational_eq_finsum
    {D : ℂ -> ℤ} (hD : D.support.Finite) {s : ℂ} (hs : D s = 0) :
    logDeriv (∏ᶠ rho : ℂ, (fun z => z - rho) ^ D rho) s =
      ∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho) := by
  have hmul : (fun rho : ℂ => (fun z : ℂ => z - rho) ^ D rho).mulSupport ⊆
      hD.toFinset := by
    rw [Function.FactorizedRational.mulSupport]
    exact hD.coe_toFinset.ge
  rw [finprod_eq_prod_of_mulSupport_subset _ hmul]
  have hprod : (∏ rho ∈ hD.toFinset, (fun z : ℂ => z - rho) ^ D rho) =
      fun z => ∏ rho ∈ hD.toFinset, (z - rho) ^ D rho := by ext z; simp
  rw [hprod, logDeriv_prod]
  · rw [finsum_eq_sum_of_support_subset]
    · apply Finset.sum_congr rfl
      intro rho _
      rw [logDeriv_fun_zpow (by fun_prop)]
      simp [logDeriv_apply, div_eq_mul_inv]
    · intro rho hrho
      apply hD.mem_toFinset.mpr
      intro hzero
      simp [hzero] at hrho
  · intro rho hrho
    have hrho := Function.mem_support.mp (hD.mem_toFinset.mp hrho)
    exact zpow_ne_zero _ (sub_ne_zero.mpr (fun h => hrho (h ▸ hs)))
  · intro rho hrho
    have hrho := Function.mem_support.mp (hD.mem_toFinset.mp hrho)
    exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z - rho) s).zpow
      (.inl (sub_ne_zero.mpr (fun h => hrho (h ▸ hs))))

private theorem logDeriv_selectedRegularFactor_eq_sub_finsum
    {f : ℂ -> ℂ} {c s : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R))) (hc : f c ≠ 0)
    (hs : s ∈ closedBall c R) (hfs : f s ≠ 0) :
    logDeriv (selectedRegularFactor f c R) s = logDeriv f s -
      ∑ᶠ rho : ℂ, ((selectedDivisor f c R rho : ℤ) : ℂ) / (s - rho) := by
  have hs_inner : s ∈ closedBall c (2 * R) :=
    closedBall_subset_closedBall (by linarith) hs
  have hs_outer : s ∈ closedBall c (4 * R) :=
    closedBall_subset_closedBall (by linarith) hs
  have hDs := selectedDivisor_apply_eq_zero_of_ne_zero hR hf hc hs_inner hfs
  have hPs := selectedZeroProduct_ne_zero_of_divisor_eq_zero hDs
  have hPa : AnalyticAt ℂ (selectedZeroProduct f c R) s := by
    unfold selectedZeroProduct
    exact Function.FactorizedRational.analyticAt (selectedDivisor_nonneg hR hf s)
  have hrawa : AnalyticAt ℂ (selectedRawFactor f c R) s := by
    unfold selectedRawFactor
    exact (hPa.inv hPs).mul (hf s hs_outer)
  have hraw := meromorphicOn_selectedRawFactor hf
  have heq : selectedRegularFactor f c R =ᶠ[nhds s] selectedRawFactor f c R := by
    simpa [selectedRegularFactor, toMeromorphicNFAt_eq_self.2 hrawa.meromorphicNFAt] using
      toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hraw hs_outer
  have hlogeq : logDeriv (selectedRegularFactor f c R) s =
      logDeriv (selectedRawFactor f c R) s := by
    simp only [logDeriv_apply]
    rw [heq.deriv_eq, heq.self_of_nhds]
  rw [hlogeq]
  have hrawfun : selectedRawFactor f c R =
      fun z => f z / selectedZeroProduct f c R z := by
    funext z
    simp [selectedRawFactor, div_eq_mul_inv, mul_comm]
  rw [hrawfun, logDeriv_div s hfs hPs (hf s hs_outer).differentiableAt
    hPa.differentiableAt]
  rw [selectedZeroProduct, logDeriv_factorizedRational_eq_finsum
    (selectedDivisor_support_finite f c R) hDs]


/-- The fixed-disk construction simultaneously supplies the analytic,
zero-free regular factor, its exact logarithmic-derivative identity, and the
uniform bound required by Cauchy's derivative estimate. -/
theorem exists_regularizedLogDeriv_data_erdos48
    {f : ℂ → ℂ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (closedBall c (4 * R)))
    (hc : f c ≠ 0)
    (hbound : ∀ z ∈ sphere c (4 * R),
      ‖f z‖ ≤ Real.exp M * ‖f c‖) :
    ∃ G : ℂ → ℂ,
      AnalyticOnNhd ℂ G (closedBall c (4 * R)) ∧
      (∀ z ∈ closedBall c (2 * R), G z ≠ 0) ∧
      (∀ s ∈ closedBall c R, f s ≠ 0 →
        logDeriv G s = logDeriv f s -
          ∑ᶠ rho : ℂ,
            ((MeromorphicOn.divisor f (closedBall c (2 * R))) rho : ℂ) /
              (s - rho)) ∧
      (∀ s ∈ closedBall c R,
        ‖logDeriv G s‖ ≤ 16 * M / R) := by
  let G := selectedRegularFactor f c R
  refine ⟨G, analyticOnNhd_selectedRegularFactor hR hf hc, ?_, ?_, ?_⟩
  · intro z hz
    exact selectedRegularFactor_ne_zero hR hf hc hz
  · intro s hs hfs
    exact logDeriv_selectedRegularFactor_eq_sub_finsum hR hf hc hs hfs
  · intro s hs
    exact norm_logDeriv_selectedRegularFactor_le hR hM hf hc hbound hs

/-- Cauchy's estimate for the logarithmic derivative of a regular factor.
The smaller closed disk is required to lie in the region where both the
factor is zero-free and its logarithmic derivative has the displayed
uniform bound. -/
theorem norm_iteratedDeriv_logDeriv_le_of_regularized_data
    {G : ℂ → ℂ} {c z : ℂ} {R r C : ℝ}
    (hR : 0 < R) (hr : 0 < r)
    (hG : AnalyticOnNhd ℂ G (closedBall c (4 * R)))
    (hGne : ∀ w ∈ closedBall c (2 * R), G w ≠ 0)
    (hsub : closedBall z r ⊆ closedBall c R)
    (hbound : ∀ w ∈ closedBall c R, ‖logDeriv G w‖ ≤ C)
    (k : ℕ) :
    ‖iteratedDeriv k (logDeriv G) z‖ ≤
      k.factorial * C / r ^ k := by
  have hlog : AnalyticOnNhd ℂ (logDeriv G) (closedBall z r) := by
    intro w hw
    have hwR : w ∈ closedBall c R := hsub hw
    have hw2R : w ∈ closedBall c (2 * R) :=
      closedBall_subset_closedBall (by linarith) hwR
    have hw4R : w ∈ closedBall c (4 * R) :=
      closedBall_subset_closedBall (by linarith) hwR
    simpa [logDeriv] using
      ((hG w hw4R).deriv.div (hG w hw4R) (hGne w hw2R))
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      k hr (hlog.differentiableOn.diffContOnCl_ball (by rfl))
  intro w hw
  exact hbound w (hsub (Metric.sphere_subset_closedBall hw))

end

end BoundedGaps.Maynard
