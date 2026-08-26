import ErdosProblems.Erdos1038.PlatformResidualMaterialBoundaryKernel

/-!
# Boundary convergence of the residual material Abel representation

This file records dominated convergence for the smooth derivative terms in
the finite-jump Abel logarithmic representation.
-/

set_option warningAsError false

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

omit [LinearOrder iota] in
/-- The smooth derivative integral in one residual block converges to its
boundary-kernel counterpart along the canonical Abel radii. -/
theorem tendsto_integral_deriv_mul_platformHalfCircleAbelLogDifference_canonical
    (C : ResidualConfiguration iota) (k : ℝ) {a : ℝ}
    (ha : 0 < a) (ha2 : a < 2) (i : iota)
    {theta left right : ℝ} (htheta : theta ∈ Ioo 0 Real.pi)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    Tendsto
      (fun n ↦ ∫ phi in left..right,
        deriv (platformResidualMaterialSmoothBlock C k a i) phi *
          platformHalfCircleAbelLogDifference
            (canonicalAbelParameter n) theta phi)
      atTop
      (𝓝 (∫ phi in left..right,
        deriv (platformResidualMaterialSmoothBlock C k a i) phi *
          platformHalfCircleBoundaryLogDifference theta phi)) := by
  let D := platformResidualMaterialSmoothBlockDerivativeBound C k a i
  let F : ℕ → ℝ → ℝ := fun n phi ↦
    deriv (platformResidualMaterialSmoothBlock C k a i) phi *
      platformHalfCircleAbelLogDifference
        (canonicalAbelParameter n) theta phi
  let f : ℝ → ℝ := fun phi ↦
    deriv (platformResidualMaterialSmoothBlock C k a i) phi *
      platformHalfCircleBoundaryLogDifference theta phi
  let bound : ℝ → ℝ := fun phi ↦
    D * (Real.sin phi *
      platformHalfCircleBoundaryLogDifference theta phi)
  have hthetaIcc : theta ∈ Icc (0 : ℝ) Real.pi :=
    ⟨htheta.1.le, htheta.2.le⟩
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact platformResidualMaterialSmoothBlockDerivativeBound_nonneg
      C k ha ha2 i
  have hderivCont : Continuous
      (fun phi : ℝ ↦ deriv
        (platformResidualMaterialSmoothBlock C k a i) phi) := by
    have hd : Continuous (platformAngularDistance a) := by
      unfold platformAngularDistance
      fun_prop
    have hdne (phi : ℝ) : platformAngularDistance a phi ≠ 0 :=
      (ha.trans_le (platformAngularDistance_ge_all ha2.le phi)).ne'
    rw [show (fun phi : ℝ ↦ deriv
        (platformResidualMaterialSmoothBlock C k a i) phi) =
      fun phi ↦ platformRadius a * Real.sin phi *
        (k * Real.sqrt (2 * a) * C.location i /
          platformAngularDistance a phi ^ 2 - (k + 1)) by
        funext phi
        exact deriv_platformResidualMaterialSmoothBlock_eq_sin_mul
          C k ha ha2 i phi]
    exact (continuous_const.mul Real.continuous_sin).mul
      ((continuous_const.div (hd.pow 2)
        (fun phi ↦ pow_ne_zero 2 (hdne phi))).sub continuous_const)
  have hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (F n)
      (volume.restrict (uIoc left right)) := by
    apply Filter.Eventually.of_forall
    intro n
    apply Continuous.aestronglyMeasurable
    dsimp only [F]
    exact hderivCont.mul
      (continuous_platformHalfCircleAbelLogDifference
        (canonicalAbelParameter_isInteriorApproach.1 n) theta)
  have hbound : ∀ᶠ n in atTop, ∀ᵐ phi ∂volume,
      phi ∈ uIoc left right → ‖F n phi‖ ≤ bound phi := by
    apply Filter.Eventually.of_forall
    intro n
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) theta]
      with phi hne
    intro hphi
    rw [uIoc_of_le hle] at hphi
    have hphiIcc : phi ∈ Icc (0 : ℝ) Real.pi :=
      ⟨hleft.trans hphi.1.le, hphi.2.trans hright⟩
    have hsin : 0 ≤ Real.sin phi :=
      Real.sin_nonneg_of_nonneg_of_le_pi hphiIcc.1 hphiIcc.2
    have hderiv := abs_deriv_platformResidualMaterialSmoothBlock_le_sin
      C k ha ha2 i hphiIcc
    have hboundaryNonneg :=
      platformHalfCircleBoundaryLogDifference_nonneg
        hthetaIcc hphiIcc hne.symm
    by_cases hn : n = 0
    · subst n
      dsimp only [F, bound]
      simp only [canonicalAbelParameter, Nat.cast_zero, zero_add, zero_div,
        platformHalfCircleAbelLogDifference_rho_zero, mul_zero, norm_zero]
      exact mul_nonneg hD (mul_nonneg hsin hboundaryNonneg)
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hrhopos : 0 < canonicalAbelParameter n := by
        unfold canonicalAbelParameter
        positivity
      have hrholt : canonicalAbelParameter n < 1 := by
        have habs := canonicalAbelParameter_isInteriorApproach.1 n
        rw [abs_of_pos hrhopos] at habs
        exact habs
      have hkernel :=
        platformHalfCircleAbelLogDifference_nonneg_le_boundary
          hrhopos hrholt hthetaIcc hphiIcc hne.symm
      dsimp only [F, bound, D]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hkernel.1]
      calc
        |deriv (platformResidualMaterialSmoothBlock C k a i) phi| *
            platformHalfCircleAbelLogDifference
              (canonicalAbelParameter n) theta phi ≤
          (platformResidualMaterialSmoothBlockDerivativeBound C k a i *
            Real.sin phi) *
            platformHalfCircleAbelLogDifference
              (canonicalAbelParameter n) theta phi := by
                exact mul_le_mul_of_nonneg_right hderiv hkernel.1
        _ ≤ platformResidualMaterialSmoothBlockDerivativeBound C k a i *
            (Real.sin phi *
              platformHalfCircleBoundaryLogDifference theta phi) := by
                nlinarith [mul_le_mul_of_nonneg_left hkernel.2 hsin,
                  mul_nonneg hD hsin]
  have hboundIntegrable : IntervalIntegrable bound volume left right := by
    have hfull : IntervalIntegrable bound volume 0 Real.pi := by
      dsimp only [bound]
      exact (intervalIntegrable_sin_mul_platformHalfCircleBoundaryLogDifference
        theta 0 Real.pi).const_mul D
    apply hfull.mono_set
    rw [uIcc_of_le hle, uIcc_of_le Real.pi_pos.le]
    exact Icc_subset_Icc hleft hright
  have hlimit : ∀ᵐ phi ∂volume, phi ∈ uIoc left right →
      Tendsto (fun n ↦ F n phi) atTop (𝓝 (f phi)) := by
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) theta]
      with phi hne
    intro hphi
    rw [uIoc_of_le hle] at hphi
    have hphiIcc : phi ∈ Icc (0 : ℝ) Real.pi :=
      ⟨hleft.trans hphi.1.le, hphi.2.trans hright⟩
    dsimp only [F, f]
    exact tendsto_const_nhds.mul
      (tendsto_platformHalfCircleAbelLogDifference_canonical
        hthetaIcc hphiIcc hne.symm)
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    bound hmeas hbound hboundIntegrable hlimit

/-- Away from the finite set of residual block endpoints, the complete
canonical Abel logarithmic representation converges to its boundary form. -/
theorem tendsto_platformResidualMaterialAbelLogRepresentation_canonical
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) {theta : ℝ}
    (htheta : theta ∈ Ioo 0 Real.pi)
    (hleftNe : ∀ i, theta ≠
      platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
    (hrightNe : ∀ i, theta ≠
      platformResidualBlockRight C k a hk ha ha2 hthreshold i) :
    Tendsto
      (fun n ↦ platformResidualMaterialAbelLogRepresentation C k a
        hk ha ha2 hthreshold (canonicalAbelParameter n) theta)
      atTop
      (𝓝 (platformResidualMaterialBoundaryLogRepresentation C k a
        hk ha ha2 hthreshold theta)) := by
  classical
  have hthetaIcc : theta ∈ Icc (0 : ℝ) Real.pi :=
    ⟨htheta.1.le, htheta.2.le⟩
  unfold platformResidualMaterialAbelLogRepresentation
    platformResidualMaterialBoundaryLogRepresentation
  apply tendsto_finsetSum
  intro i _hi
  let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold i
  let right := platformResidualBlockRight C k a hk ha ha2 hthreshold i
  let G := platformResidualMaterialSmoothBlock C k a i
  have hleftMem : left ∈ Icc (0 : ℝ) Real.pi := by
    dsimp only [left]
    exact platformResidualBlockLeft_mem_Icc
      C k a hk ha ha2 hthreshold i
  have hrightMem : right ∈ Icc (0 : ℝ) Real.pi := by
    dsimp only [right]
    exact platformResidualBlockRight_mem_Icc
      C k a hk ha ha2 hthreshold i
  have hleftRight : left ≤ right :=
    (platformResidualBlockLeft_lt_right C k a hk ha ha2
      hthreshold i).le
  have hrightK : Tendsto
      (fun n ↦ platformHalfCircleAbelLogDifference
        (canonicalAbelParameter n) theta right)
      atTop (𝓝 (platformHalfCircleBoundaryLogDifference theta right)) := by
    exact tendsto_platformHalfCircleAbelLogDifference_canonical
      hthetaIcc hrightMem (by
        dsimp only [right]
        exact hrightNe i)
  have hleftK : Tendsto
      (fun n ↦ platformHalfCircleAbelLogDifference
        (canonicalAbelParameter n) theta left)
      atTop (𝓝 (platformHalfCircleBoundaryLogDifference theta left)) := by
    exact tendsto_platformHalfCircleAbelLogDifference_canonical
      hthetaIcc hleftMem (by
        dsimp only [left]
        exact hleftNe i)
  have hintegral : Tendsto
      (fun n ↦ ∫ phi in left..right,
        deriv G phi * platformHalfCircleAbelLogDifference
          (canonicalAbelParameter n) theta phi)
      atTop
      (𝓝 (∫ phi in left..right,
        deriv G phi * platformHalfCircleBoundaryLogDifference theta phi)) := by
    dsimp only [G]
    exact
      tendsto_integral_deriv_mul_platformHalfCircleAbelLogDifference_canonical
        C k ha ha2 i htheta hleftMem.1 hleftRight hrightMem.2
  dsimp only [left, right, G] at hrightK hleftK hintegral ⊢
  exact tendsto_const_nhds.mul
    (((tendsto_const_nhds.mul hrightK).sub
      (tendsto_const_nhds.mul hleftK)).sub hintegral)

end

end Erdos1038
