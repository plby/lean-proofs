import ErdosProblems.Erdos1038.CircleAbelBoundary

/-!
# Fourier evaluation of the centered two-arc deficit

The interior Abel kernel is evaluated by its absolutely convergent cosine
series.  Dominated convergence then passes to the boundary logarithmic
kernel on the product of two centered arcs.
-/

set_option warningAsError false

open Metric Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Erdos1038

noncomputable section

local notation "AngleCircle" => AddCircle (2 * Real.pi)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private lemma ae_angleCircle_prod_ne :
    ∀ᵐ p : AngleCircle × AngleCircle ∂(volume.prod volume),
      p.1 ≠ p.2 := by
  have hmeas : MeasurableSet
      {p : AngleCircle × AngleCircle | p.1 ≠ p.2} := by
    exact (isClosed_eq continuous_fst continuous_snd).isOpen_compl.measurableSet
  rw [Measure.ae_prod_iff_ae_ae
    hmeas]
  filter_upwards with x
  have hnull := volume_angleCircle_singleton_zero x
  rw [measure_eq_zero_iff_ae_notMem] at hnull
  filter_upwards [hnull] with y hy
  simpa only [mem_singleton_iff, ne_comm] using! hy

private lemma integrableOn_circleLogDeficitAt_prod_closedBalls
    (Q R : ℝ) :
    IntegrableOn
      (Function.uncurry circleLogDeficitAt)
      (closedBall (0 : AngleCircle) Q ×ˢ
        closedBall (0 : AngleCircle) R)
      (volume.prod volume) := by
  let S : Set (AngleCircle × AngleCircle) :=
    closedBall (0 : AngleCircle) Q ×ˢ closedBall (0 : AngleCircle) R
  have hmeas : Measurable (Function.uncurry circleLogDeficitAt) := by
    unfold circleLogDeficitAt
    fun_prop
  have hnonneg : 0 ≤ᵐ[(volume.prod volume).restrict S]
      Function.uncurry circleLogDeficitAt :=
    Filter.Eventually.of_forall fun p ↦ circleLogDeficitAt_nonneg p.1 p.2
  have hfinite :
      (∫⁻ p in S,
        ENNReal.ofReal (Function.uncurry circleLogDeficitAt p)
        ∂(volume.prod volume)) ≠ ∞ := by
    change circleSetLogDeficit
      (closedBall (0 : AngleCircle) Q)
      (closedBall (0 : AngleCircle) R) ≠ ∞
    rw [show circleSetLogDeficit
        (closedBall (0 : AngleCircle) Q)
        (closedBall (0 : AngleCircle) R) =
          circleLogTwoArcEnergy Q R 0 by
      simpa only [AddCircle.coe_zero] using!
        circleSetLogDeficit_closedBalls_zero Q R 0]
    exact circleLogTwoArcEnergy_ne_top Q R 0
  exact (lintegral_ofReal_ne_top_iff_integrable
    hmeas.aestronglyMeasurable hnonneg).mp hfinite

/-- Exact product-set integral of the interior Abel kernel. -/
theorem setIntegral_circleAbelLogKernelOn_eq_arcEnergy
    {rho : ℝ} (hrho : |rho| < 1)
    {Q R : ℝ} (hQ0 : 0 ≤ Q) (hQpi : Q ≤ Real.pi)
    (hR0 : 0 ≤ R) (hRpi : R ≤ Real.pi)
    (hQne : Q ≠ 0) (hRne : R ≠ 0) :
    (∫ p in closedBall (0 : AngleCircle) Q ×ˢ
          closedBall (0 : AngleCircle) R,
        circleAbelLogKernelOn rho p.1 p.2
        ∂(volume.prod volume)) =
      4 * Q * R * circleAbelArcEnergy rho Q R := by
  have hcompact : IsCompact
      (closedBall (0 : AngleCircle) Q ×ˢ
        closedBall (0 : AngleCircle) R) :=
    isClosed_closedBall.isCompact.prod isClosed_closedBall.isCompact
  have hint : IntegrableOn
      (Function.uncurry (circleAbelLogKernelOn rho))
      (closedBall (0 : AngleCircle) Q ×ˢ
        closedBall (0 : AngleCircle) R)
      (volume.prod volume) :=
    (continuous_circleAbelLogKernelOn hrho).continuousOn.integrableOn_compact
      hcompact
  change (∫ p in closedBall (0 : AngleCircle) Q ×ˢ
        closedBall (0 : AngleCircle) R,
      Function.uncurry (circleAbelLogKernelOn rho) p
      ∂(volume.prod volume)) = _
  rw [setIntegral_prod _ hint]
  rw [integral_centeredClosedBall_eq_interval hQ0 hQpi]
  calc
    (∫ theta : ℝ in -Q..Q,
        ∫ y in closedBall (0 : AngleCircle) R,
          circleAbelLogKernelOn rho (theta : AngleCircle) y) =
        ∫ theta : ℝ in -Q..Q,
          ∫ phi : ℝ in -R..R,
            circleAbelLogKernel rho (theta - phi) := by
      apply intervalIntegral.integral_congr
      intro theta _htheta
      change (∫ y in closedBall (0 : AngleCircle) R,
          circleAbelLogKernelOn rho (theta : AngleCircle) y) =
        ∫ phi : ℝ in -R..R,
          circleAbelLogKernel rho (theta - phi)
      rw [integral_centeredClosedBall_eq_interval hR0 hRpi]
      apply intervalIntegral.integral_congr
      intro phi _hphi
      exact circleAbelLogKernelOn_coe_coe rho theta phi
    _ = 4 * Q * R * circleAbelArcEnergy rho Q R :=
      iteratedIntegral_circleAbelLogKernel_eq_arcEnergy hrho hQne hRne

private lemma integrableOn_logTwo_add_circleDeficit
    (Q R : ℝ) :
    IntegrableOn
      (fun p : AngleCircle × AngleCircle ↦
        Real.log 2 + circleLogDeficitAt p.1 p.2)
      (closedBall (0 : AngleCircle) Q ×ˢ
        closedBall (0 : AngleCircle) R)
      (volume.prod volume) := by
  exact (integrableOn_const (C := Real.log 2)).add
    (integrableOn_circleLogDeficitAt_prod_closedBalls Q R)

/-- The centered product integral of the boundary logarithmic kernel is
the boundary value of the Abel/Fourier series. -/
theorem setIntegral_circleAbelLogKernelOn_one_eq_arcEnergy
    {Q R : ℝ} (hQ : 0 < Q) (hQpi : Q ≤ Real.pi)
    (hR : 0 < R) (hRpi : R ≤ Real.pi) :
    (∫ p in closedBall (0 : AngleCircle) Q ×ˢ
          closedBall (0 : AngleCircle) R,
        circleAbelLogKernelOn 1 p.1 p.2
        ∂(volume.prod volume)) =
      4 * Q * R * circleArcEnergy Q R := by
  let S : Set (AngleCircle × AngleCircle) :=
    closedBall (0 : AngleCircle) Q ×ˢ closedBall (0 : AngleCircle) R
  let mu : Measure (AngleCircle × AngleCircle) :=
    (volume.prod volume).restrict S
  have hdiag : ∀ᵐ p ∂mu, p.1 ≠ p.2 :=
    ae_angleCircle_prod_ne.filter_mono ae_restrict_le
  have hnear : Ioi (1 / 2 : ℝ) ∈ nhdsWithin 1 (Iio 1) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
  have hDCT : Tendsto
      (fun rho : ℝ ↦ ∫ p, circleAbelLogKernelOn rho p.1 p.2 ∂mu)
      (nhdsWithin 1 (Iio 1))
      (nhds (∫ p, circleAbelLogKernelOn 1 p.1 p.2 ∂mu)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun p : AngleCircle × AngleCircle ↦
        Real.log 2 + circleLogDeficitAt p.1 p.2)
    · exact Filter.Eventually.of_forall fun rho ↦
        (measurable_circleAbelLogKernelOn rho).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin, hnear] with rho hrhoUpper hrhoLower
      filter_upwards [hdiag] with p hp
      rw [Real.norm_eq_abs]
      exact abs_circleAbelLogKernelOn_le_log_two_add_deficit
        hrhoLower.le hrhoUpper.le hp
    · exact integrableOn_logTwo_add_circleDeficit Q R
    · filter_upwards [hdiag] with p hp
      exact tendsto_circleAbelLogKernelOn_one hp
  have hInterior : ∀ᶠ rho in nhdsWithin 1 (Iio 1),
      (∫ p, circleAbelLogKernelOn rho p.1 p.2 ∂mu) =
        4 * Q * R * circleAbelArcEnergy rho Q R := by
    filter_upwards [self_mem_nhdsWithin, hnear] with rho hrho hrhoLower
    change (∫ p in S,
        circleAbelLogKernelOn rho p.1 p.2
        ∂(volume.prod volume)) = _
    exact setIntegral_circleAbelLogKernelOn_eq_arcEnergy
      (by
        change rho < 1 at hrho
        change 1 / 2 < rho at hrhoLower
        rw [abs_lt]
        constructor <;> linarith)
      hQ.le hQpi hR.le hRpi hQ.ne' hR.ne'
  have hFourier : Tendsto
      (fun rho : ℝ ↦ 4 * Q * R * circleAbelArcEnergy rho Q R)
      (nhdsWithin 1 (Iio 1))
      (nhds (4 * Q * R * circleArcEnergy Q R)) :=
    (tendsto_circleAbelArcEnergy_one hQ hR).const_mul (4 * Q * R)
  have hDCT' : Tendsto
      (fun rho : ℝ ↦ 4 * Q * R * circleAbelArcEnergy rho Q R)
      (nhdsWithin 1 (Iio 1))
      (nhds (∫ p, circleAbelLogKernelOn 1 p.1 p.2 ∂mu)) :=
    hDCT.congr' hInterior
  change (∫ p, circleAbelLogKernelOn 1 p.1 p.2 ∂mu) = _
  exact tendsto_nhds_unique hDCT' hFourier

private lemma setIntegral_circleLogDeficitAt_eq_twoArcEnergy_toReal
    (Q R : ℝ) :
    (∫ p in closedBall (0 : AngleCircle) Q ×ˢ
          closedBall (0 : AngleCircle) R,
        circleLogDeficitAt p.1 p.2 ∂(volume.prod volume)) =
      (circleLogTwoArcEnergy Q R 0).toReal := by
  let S : Set (AngleCircle × AngleCircle) :=
    closedBall (0 : AngleCircle) Q ×ˢ closedBall (0 : AngleCircle) R
  have hint := integrableOn_circleLogDeficitAt_prod_closedBalls Q R
  have hnonneg : 0 ≤ᵐ[(volume.prod volume).restrict S]
      Function.uncurry circleLogDeficitAt :=
    Filter.Eventually.of_forall fun p ↦ circleLogDeficitAt_nonneg p.1 p.2
  have hofReal : ENNReal.ofReal
      (∫ p in S, Function.uncurry circleLogDeficitAt p
        ∂(volume.prod volume)) =
      circleLogTwoArcEnergy Q R 0 := by
    calc
      ENNReal.ofReal
          (∫ p in S, Function.uncurry circleLogDeficitAt p
            ∂(volume.prod volume)) =
          ∫⁻ p in S,
            ENNReal.ofReal (Function.uncurry circleLogDeficitAt p)
            ∂(volume.prod volume) :=
        ofReal_integral_eq_lintegral_ofReal hint hnonneg
      _ = circleSetLogDeficit
          (closedBall (0 : AngleCircle) Q)
          (closedBall (0 : AngleCircle) R) := rfl
      _ = circleLogTwoArcEnergy Q R 0 := by
        simpa only [AddCircle.coe_zero] using!
          circleSetLogDeficit_closedBalls_zero Q R 0
  have hintegralNonneg : 0 ≤
      ∫ p in S, Function.uncurry circleLogDeficitAt p
        ∂(volume.prod volume) :=
    integral_nonneg_of_ae hnonneg
  have hreal := congrArg ENNReal.toReal hofReal
  rw [ENNReal.toReal_ofReal hintegralNonneg] at hreal
  exact hreal

private lemma setIntegral_logTwo_eq_four_mul
    {Q R : ℝ} (hQ0 : 0 ≤ Q) (hQpi : Q ≤ Real.pi)
    (hR0 : 0 ≤ R) (hRpi : R ≤ Real.pi) :
    (∫ _p in closedBall (0 : AngleCircle) Q ×ˢ
          closedBall (0 : AngleCircle) R,
        Real.log 2 ∂(volume.prod volume)) =
      4 * Q * R * Real.log 2 := by
  have hint : IntegrableOn
      (fun _p : AngleCircle × AngleCircle ↦ Real.log 2)
      (closedBall (0 : AngleCircle) Q ×ˢ
        closedBall (0 : AngleCircle) R)
      (volume.prod volume) := integrableOn_const
  rw [setIntegral_prod _ hint]
  have hinner : (∫ _y in closedBall (0 : AngleCircle) R,
      Real.log 2) = 2 * R * Real.log 2 := by
    rw [integral_centeredClosedBall_eq_interval hR0 hRpi,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hinner]
  rw [integral_centeredClosedBall_eq_interval hQ0 hQpi,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Exact Fourier evaluation of the centered two-arc logarithmic deficit. -/
theorem circleLogTwoArcEnergy_zero_toReal_eq_arcEnergy
    {Q R : ℝ} (hQ : 0 < Q) (hQpi : Q ≤ Real.pi)
    (hR : 0 < R) (hRpi : R ≤ Real.pi) :
    (circleLogTwoArcEnergy Q R 0).toReal =
      4 * Q * R * (Real.log 2 - circleArcEnergy Q R) := by
  let S : Set (AngleCircle × AngleCircle) :=
    closedBall (0 : AngleCircle) Q ×ˢ closedBall (0 : AngleCircle) R
  have hdiag : ∀ᵐ p ∂(volume.prod volume).restrict S, p.1 ≠ p.2 :=
    ae_angleCircle_prod_ne.filter_mono ae_restrict_le
  have hboundary :=
    setIntegral_circleAbelLogKernelOn_one_eq_arcEnergy hQ hQpi hR hRpi
  have hcongr :
      (∫ p in S, circleAbelLogKernelOn 1 p.1 p.2
          ∂(volume.prod volume)) =
        ∫ p in S,
          (Real.log 2 - circleLogDeficitAt p.1 p.2)
          ∂(volume.prod volume) := by
    apply integral_congr_ae
    filter_upwards [hdiag] with p hp
    exact circleAbelLogKernelOn_one_eq_log_two_sub_deficit hp
  have hconst : IntegrableOn
      (fun _p : AngleCircle × AngleCircle ↦ Real.log 2) S
      (volume.prod volume) := integrableOn_const
  have hdeficit := integrableOn_circleLogDeficitAt_prod_closedBalls Q R
  have hdecomp :
      (∫ p in S, (Real.log 2 - circleLogDeficitAt p.1 p.2)
        ∂(volume.prod volume)) =
        4 * Q * R * Real.log 2 -
          (circleLogTwoArcEnergy Q R 0).toReal := by
    change IntegrableOn (Function.uncurry circleLogDeficitAt) S
      (volume.prod volume) at hdeficit
    change (∫ p in S,
        (fun _p : AngleCircle × AngleCircle ↦ Real.log 2) p -
          Function.uncurry circleLogDeficitAt p
          ∂(volume.prod volume)) = _
    have hdefEval :
        (∫ p in S, Function.uncurry circleLogDeficitAt p
          ∂(volume.prod volume)) =
          (circleLogTwoArcEnergy Q R 0).toReal := by
      change (∫ p in closedBall (0 : AngleCircle) Q ×ˢ
          closedBall (0 : AngleCircle) R,
        circleLogDeficitAt p.1 p.2 ∂(volume.prod volume)) = _
      exact setIntegral_circleLogDeficitAt_eq_twoArcEnergy_toReal Q R
    rw [integral_sub hconst hdeficit,
      setIntegral_logTwo_eq_four_mul hQ.le hQpi hR.le hRpi,
      hdefEval]
  rw [hcongr, hdecomp] at hboundary
  linarith

end

end Erdos1038
