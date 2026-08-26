import ErdosProblems.Erdos1038.PlatformResidualMaterialAbelEndpoint
import ErdosProblems.Erdos1038.PlatformAdjointAbelExteriorLimit
import ErdosProblems.Erdos1038.PlatformReferenceDirectionalRootLimits

/-!
# Concrete material Fourier data at the exterior crossings

The cosine coefficients used by the endpoint-corrected Abel argument are
those of the density-weighted residual material field.  This file identifies
their unregularized exterior value with the continuum material resolvents.
With the reciprocal-slope adjoint weights, that value is exactly the
material velocity of the width between the two continuum crossings.
-/

set_option warningAsError false
set_option maxHeartbeats 800000

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- One target block of the canonical quantile can equivalently be
integrated in its local mass coordinate or its angular coordinate. -/
theorem weight_mul_integral_platformResidualBlockReferenceIntegrand_eq_angular
    (C : ResidualConfiguration iota) (i : iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc a 2)) :
    C.weight i *
        (∫ t in (0 : ℝ)..1,
          platformResidualBlockReferenceIntegrand C i
            k a hk ha ha2 hthreshold F t) =
      (1 / Real.pi) *
        ∫ theta in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
            platformResidualBlockRight C k a hk ha ha2 hthreshold i,
          platformAngularDensity k a theta *
            F (platformAngularDistance a theta) := by
  rw [weight_mul_integral_platformResidualBlockReferenceIntegrand]
  let G := platformReferenceQuantileIntegrand k a
    hk ha ha2 hthreshold F
  let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold i
  let right := platformResidualBlockRight C k a hk ha ha2 hthreshold i
  have hG : Continuous G :=
    continuous_platformReferenceQuantileIntegrand
      k a hk ha ha2 hthreshold F hF
  have hderivative : ∀ theta ∈ uIcc left right,
      HasDerivAt (platformReferenceCumulative k a)
        ((1 / Real.pi) * platformAngularDensity k a theta) theta :=
    fun theta _ ↦ hasDerivAt_platformReferenceCumulative k ha ha2.le
  have hderivativeContinuous : ContinuousOn
      (fun theta ↦ (1 / Real.pi) * platformAngularDensity k a theta)
      (uIcc left right) := by
    exact (continuous_const.mul
      (by
        unfold platformAngularDensity platformDensityCoefficient
        have hd : Continuous (platformAngularDistance a) := by
          unfold platformAngularDistance
          fun_prop
        apply Continuous.sub continuous_const
        apply Continuous.div continuous_const hd
        intro theta
        have hge := platformAngularDistance_ge_all ha2.le theta
        exact (ha.trans_le hge).ne')).continuousOn
  have hsubstitution := intervalIntegral.integral_comp_mul_deriv
    (a := left) (b := right)
    (f := platformReferenceCumulative k a)
    (f' := fun theta ↦ (1 / Real.pi) * platformAngularDensity k a theta)
    (g := G) hderivative hderivativeContinuous hG
  have hleftCumulative :
      platformReferenceCumulative k a left =
        orderedResidualLeftMass C i := by
    dsimp only [left, platformResidualBlockLeft]
    exact platformReferenceCumulative_cut
      k a hk ha ha2 hthreshold _
  have hrightCumulative :
      platformReferenceCumulative k a right =
        orderedResidualRightMass C i := by
    dsimp only [right, platformResidualBlockRight]
    exact platformReferenceCumulative_cut
      k a hk ha ha2 hthreshold _
  rw [hleftCumulative, hrightCumulative] at hsubstitution
  have hleftMem := platformResidualBlockLeft_mem_Icc
    C k a hk ha ha2 hthreshold i
  have hrightMem := platformResidualBlockRight_mem_Icc
    C k a hk ha ha2 hthreshold i
  have hleftRight : left < right := by
    exact platformResidualBlockLeft_lt_right
      C k a hk ha ha2 hthreshold i
  have hcompose (theta : ℝ) (htheta : theta ∈ uIcc left right) :
      G (platformReferenceCumulative k a theta) =
        F (platformAngularDistance a theta) := by
    rw [uIcc_of_le hleftRight.le] at htheta
    have hthetaFull : theta ∈ Icc (0 : ℝ) Real.pi :=
      ⟨hleftMem.1.trans htheta.1, htheta.2.trans hrightMem.2⟩
    have hcumulative := platformReferenceCumulative_mem_Icc
      hk ha ha2 hthreshold hthetaFull
    dsimp only [G, platformReferenceQuantileIntegrand]
    rw [projIcc_of_mem zero_le_one hcumulative]
    change F (platformReferenceQuantile k a hk ha ha2 hthreshold
      (platformReferenceCumulativeMap k a hk ha ha2 hthreshold
        ⟨theta, hthetaFull⟩)) = _
    rw [platformReferenceQuantile_cumulativeMap]
  calc
    (∫ u in orderedResidualLeftMass C i..orderedResidualRightMass C i,
        platformReferenceQuantileIntegrand k a
          hk ha ha2 hthreshold F u) =
        ∫ theta in left..right,
          (G ∘ platformReferenceCumulative k a) theta *
            ((1 / Real.pi) * platformAngularDensity k a theta) := by
      simpa only [G] using! hsubstitution.symm
    _ = ∫ theta in left..right,
          (1 / Real.pi) *
            (platformAngularDensity k a theta *
              F (platformAngularDistance a theta)) := by
      apply intervalIntegral.integral_congr
      intro theta htheta
      change G (platformReferenceCumulative k a theta) *
          ((1 / Real.pi) * platformAngularDensity k a theta) = _
      rw [hcompose theta htheta]
      ring
    _ = (1 / Real.pi) *
        ∫ theta in left..right,
          platformAngularDensity k a theta *
            F (platformAngularDistance a theta) := by
      rw [intervalIntegral.integral_const_mul]

private theorem integral_indicator_Ioc_over_platform
    {g : ℝ → ℝ} {left right : ℝ}
    (hleft : 0 ≤ left) (hlr : left ≤ right) (hright : right ≤ Real.pi) :
    (∫ theta in (0 : ℝ)..Real.pi,
        (Ioc left right).indicator g theta) =
      ∫ theta in left..right, g theta := by
  rw [intervalIntegral.integral_of_le Real.pi_pos.le,
    intervalIntegral.integral_of_le hlr,
    integral_indicator measurableSet_Ioc]
  have hsubset : Ioc left right ⊆ Ioc 0 Real.pi := by
    intro theta htheta
    exact ⟨hleft.trans_lt htheta.1, htheta.2.trans hright⟩
  rw [Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr hsubset]

/-- The continuum material resolvent is the angular integral of the
piecewise material field, in the normalization used by the Lagrange
weights. -/
theorem platformReferenceExteriorPotentialMaterialVelocityLimit_eq_materialFieldIntegral
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hxa : x < a) :
    platformReferenceExteriorPotentialMaterialVelocityLimit C k a
        hk ha ha2 hthreshold x =
      (1 / k) * (1 / Real.pi) *
        ∫ theta in (0 : ℝ)..Real.pi,
          platformResidualMaterialField C k a hk ha ha2 hthreshold theta /
            (platformAngularDistance a theta - x) := by
  classical
  let base : iota → ℝ → ℝ := fun i theta ↦
    platformAngularDensity k a theta *
      (C.location i - platformAngularDistance a theta) /
        (platformAngularDistance a theta - x)
  have hbaseContinuous (i : iota) : Continuous (base i) := by
    dsimp only [base]
    have hd : Continuous (platformAngularDistance a) := by
      unfold platformAngularDistance
      fun_prop
    have hden (theta : ℝ) : platformAngularDistance a theta - x ≠ 0 := by
      exact (platformAngularDistance_sub_pos_all hxa ha2.le theta).ne'
    have hDensity : Continuous (platformAngularDensity k a) := by
      unfold platformAngularDensity platformDensityCoefficient
      apply Continuous.sub continuous_const
      apply Continuous.div continuous_const hd
      intro theta
      exact (ha.trans_le (platformAngularDistance_ge_all ha2.le theta)).ne'
    exact (hDensity.mul (continuous_const.sub hd)).div
      (hd.sub continuous_const) hden
  have htermIntegrable (i : iota) : IntervalIntegrable
      ((Ioc
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i)).indicator
        (base i)) volume 0 Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le]
    have hbase : IntegrableOn (base i) (Ioc (0 : ℝ) Real.pi) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le]
      exact (hbaseContinuous i).intervalIntegrable 0 Real.pi
    exact hbase.indicator measurableSet_Ioc
  have hfield :
      (fun theta ↦
        platformResidualMaterialField C k a hk ha ha2 hthreshold theta /
          (platformAngularDistance a theta - x)) =
        fun theta ↦ ∑ i,
          (Ioc
            (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
            (platformResidualBlockRight C k a hk ha ha2 hthreshold i)).indicator
            (base i) theta := by
    funext theta
    unfold platformResidualMaterialField
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases htheta : theta ∈ Ioc
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i)
    · rw [indicator_of_mem htheta, indicator_of_mem htheta]
    · rw [indicator_of_notMem htheta, indicator_of_notMem htheta,
        zero_div]
  have hsumIntegral :
      (∫ theta in (0 : ℝ)..Real.pi,
          ∑ i,
            (Ioc
              (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
              (platformResidualBlockRight C k a hk ha ha2 hthreshold i)).indicator
              (base i) theta) =
        ∑ i, ∫ theta in (0 : ℝ)..Real.pi,
          (Ioc
            (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
            (platformResidualBlockRight C k a hk ha ha2 hthreshold i)).indicator
            (base i) theta := by
    simpa only [Finset.sum_apply] using!
      intervalIntegral.integral_finsetSum (s := Finset.univ)
        (fun i _hi ↦ htermIntegrable i)
  have hblockIntegral (i : iota) :
      (∫ theta in (0 : ℝ)..Real.pi,
          (Ioc
            (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
            (platformResidualBlockRight C k a hk ha ha2 hthreshold i)).indicator
            (base i) theta) =
        ∫ theta in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
            platformResidualBlockRight C k a hk ha ha2 hthreshold i,
          base i theta := by
    exact integral_indicator_Ioc_over_platform
      (platformResidualBlockLeft_mem_Icc
        C k a hk ha ha2 hthreshold i).1
      (platformResidualBlockLeft_lt_right
        C k a hk ha ha2 hthreshold i).le
      (platformResidualBlockRight_mem_Icc
        C k a hk ha ha2 hthreshold i).2
  unfold platformReferenceExteriorPotentialMaterialVelocityLimit
    platformReferenceBlockObservableLimit
  calc
    (∑ i, residualLagrangeAlpha C k i *
        (∫ t in (0 : ℝ)..1,
          platformResidualBlockReferenceIntegrand C i
            k a hk ha ha2 hthreshold
              (fun d ↦ (C.location i - d) / (d - x)) t)) =
        ∑ i, (1 / k) *
          (C.weight i *
            (∫ t in (0 : ℝ)..1,
              platformResidualBlockReferenceIntegrand C i
                k a hk ha ha2 hthreshold
                  (fun d ↦ (C.location i - d) / (d - x)) t)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      unfold residualLagrangeAlpha
      ring
    _ = ∑ i, (1 / k) * ((1 / Real.pi) *
          ∫ theta in
            platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
              platformResidualBlockRight C k a hk ha ha2 hthreshold i,
            base i theta) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [weight_mul_integral_platformResidualBlockReferenceIntegrand_eq_angular
        C i k a hk ha ha2 hthreshold]
      · congr 3
        funext theta
        dsimp only [base]
        ring
      · exact (continuousOn_const.sub continuousOn_id).div
          (continuousOn_id.sub continuousOn_const) fun d hd ↦
            (sub_pos.mpr (hxa.trans_le hd.1)).ne'
    _ = (1 / k) * (1 / Real.pi) *
          ∑ i, ∫ theta in
            platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
              platformResidualBlockRight C k a hk ha ha2 hthreshold i,
            base i theta := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ = (1 / k) * (1 / Real.pi) *
        ∫ theta in (0 : ℝ)..Real.pi,
          platformResidualMaterialField C k a hk ha ha2 hthreshold theta /
            (platformAngularDistance a theta - x) := by
      rw [hfield, hsumIntegral]
      congr 2
      funext i
      exact (hblockIntegral i).symm

/-- The full positive-frequency sequence at angular position zero. -/
def platformAbelZeroSequence
    (coefficient : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else 2 * coefficient n

@[simp] theorem platformAbelZeroSequence_zero
    (coefficient : ℕ → ℝ) :
    platformAbelZeroSequence coefficient 0 = 0 := by
  simp [platformAbelZeroSequence]

@[simp] theorem platformAbelZeroSequence_of_pos
    (coefficient : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    platformAbelZeroSequence coefficient n = 2 * coefficient n := by
  simp [platformAbelZeroSequence, Nat.ne_of_gt hn]

/-- The parity-split Abel cosine series at zero is the ordinary full
positive-frequency power series. -/
theorem platformAbelCosineSeries_zero_eq_tsum_zeroSequence
    {coefficient : ℕ → ℝ} {lambda coefficientBound : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient coefficientBound)
    (f0 : ℝ) :
    platformAbelCosineSeries f0 coefficient lambda 0 =
      f0 + ∑' n : ℕ,
        platformAbelZeroSequence coefficient n * lambda ^ n := by
  let term : ℕ → ℝ := fun n ↦
    platformAbelZeroSequence coefficient n * lambda ^ n
  have hEvenBase : Summable (fun m : ℕ ↦
      2 * (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1)))) :=
    (summable_platformAbelEvenCoefficient hlambda hbound).mul_left 2
  have hEvenShift : Summable (fun m : ℕ ↦ term (2 * (m + 1))) := by
    exact hEvenBase.congr (fun m ↦ by
      dsimp only [term]
      rw [platformAbelZeroSequence_of_pos coefficient (by omega)]
      ring)
  have hEven : Summable (fun m : ℕ ↦ term (2 * m)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.add_eq, Nat.add_comm] using! hEvenShift
  have hOddBase : Summable (fun m : ℕ ↦
      2 * (lambda ^ (2 * m + 1) * coefficient (2 * m + 1))) :=
    (summable_platformAbelOddCoefficient hlambda hbound).mul_left 2
  have hOdd : Summable (fun m : ℕ ↦ term (2 * m + 1)) := by
    exact hOddBase.congr (fun m ↦ by
      dsimp only [term]
      rw [platformAbelZeroSequence_of_pos coefficient (by omega)]
      ring)
  have hEvenTsum :
      (∑' m : ℕ, term (2 * m)) =
        ∑' m : ℕ,
          2 * (lambda ^ (2 * (m + 1)) *
            coefficient (2 * (m + 1))) := by
    rw [hEven.tsum_eq_zero_add]
    dsimp only [term]
    rw [Nat.mul_zero, platformAbelZeroSequence_zero, pow_zero,
      mul_one, zero_add]
    apply tsum_congr
    intro m
    rw [platformAbelZeroSequence_of_pos coefficient (by omega)]
    ring
  have hOddTsum :
      (∑' m : ℕ, term (2 * m + 1)) =
        ∑' m : ℕ,
          2 * (lambda ^ (2 * m + 1) * coefficient (2 * m + 1)) := by
    apply tsum_congr
    intro m
    dsimp only [term]
    rw [platformAbelZeroSequence_of_pos coefficient (by omega)]
    ring
  have hsplit :
      (∑' m : ℕ, term (2 * m)) +
          (∑' m : ℕ, term (2 * m + 1)) =
        ∑' n : ℕ, term n :=
    tsum_even_add_odd hEven hOdd
  rw [platformAbelCosineSeries, ← hsplit, hEvenTsum, hOddTsum]
  simp only [platformAbelEvenCosineTerm, platformAbelOddCosineTerm,
    mul_zero, Real.cos_zero, mul_one]
  ring

private def residualZeroPoissonTerm
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (rho : ℝ) (n : ℕ) (theta : ℝ) : ℝ :=
  platformResidualMaterialField C k a hk ha ha2 hthreshold theta *
    (2 * rho ^ (n + 1) *
      Real.cos (((n + 1 : ℕ) : ℝ) * theta))

private def residualZeroPoissonBound
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (rho : ℝ) (n : ℕ) (theta : ℝ) : ℝ :=
  2 * |rho| ^ (n + 1) *
    |platformResidualMaterialField C k a hk ha ha2 hthreshold theta|

private theorem hasSum_integral_residualZeroPoissonTerm
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {rho : ℝ} (hrho : |rho| < 1) :
    HasSum
      (fun n ↦ ∫ theta in 0..Real.pi,
        residualZeroPoissonTerm C k a hk ha ha2 hthreshold
          rho n theta)
      (∫ theta in 0..Real.pi,
        platformResidualMaterialField C k a hk ha ha2 hthreshold theta *
          (platformPoissonKernel rho theta - 1)) := by
  let F := platformResidualMaterialField C k a hk ha ha2 hthreshold
  let term := residualZeroPoissonTerm C k a hk ha ha2 hthreshold rho
  let bound := residualZeroPoissonBound C k a hk ha ha2 hthreshold rho
  have hF : IntervalIntegrable F volume 0 Real.pi :=
    intervalIntegrable_platformResidualMaterialField
      C k a hk ha ha2 hthreshold
  have hFmeas : Measurable F :=
    measurable_platformResidualMaterialField C k a hk ha ha2 hthreshold
  have htermMeas (n : ℕ) : AEStronglyMeasurable (term n)
      (volume.restrict (uIoc (0 : ℝ) Real.pi)) := by
    apply Measurable.aestronglyMeasurable
    change Measurable (fun theta ↦
      F theta *
        (2 * rho ^ (n + 1) *
          Real.cos (((n + 1 : ℕ) : ℝ) * theta)))
    exact hFmeas.mul (by fun_prop)
  have hboundPoint (n : ℕ) : ∀ᵐ theta ∂volume,
      theta ∈ uIoc (0 : ℝ) Real.pi →
        ‖term n theta‖ ≤ bound n theta := by
    filter_upwards with theta
    intro _htheta
    dsimp only [term, bound, residualZeroPoissonTerm,
      residualZeroPoissonBound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      |platformResidualMaterialField C k a hk ha ha2 hthreshold theta| *
          (2 * |rho| ^ (n + 1) *
            |Real.cos (((n + 1 : ℕ) : ℝ) * theta)|) ≤
          |platformResidualMaterialField C k a hk ha ha2 hthreshold theta| *
            (2 * |rho| ^ (n + 1) * 1) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (Real.abs_cos_le_one
                    (((n + 1 : ℕ) : ℝ) * theta))
                  (mul_nonneg (by norm_num)
                    (pow_nonneg (abs_nonneg rho) (n + 1))))
                (abs_nonneg _)
      _ = 2 * |rho| ^ (n + 1) *
          |platformResidualMaterialField C k a hk ha ha2 hthreshold theta| := by
            ring
  have hgeom : Summable (fun n : ℕ ↦ |rho| ^ (n + 1)) := by
    exact (summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one (abs_nonneg rho) hrho)
  have hboundSummable : ∀ᵐ theta ∂volume,
      theta ∈ uIoc (0 : ℝ) Real.pi → Summable (fun n ↦ bound n theta) := by
    filter_upwards with theta
    intro _htheta
    dsimp only [bound, residualZeroPoissonBound]
    have hs := hgeom.mul_right
      (2 * |platformResidualMaterialField C k a hk ha ha2 hthreshold theta|)
    exact hs.congr (fun n ↦ by ring)
  have hboundTsum : (fun theta ↦ ∑' n, bound n theta) =
      fun theta ↦
        (2 * ∑' n : ℕ, |rho| ^ (n + 1)) * |F theta| := by
    funext theta
    dsimp only [bound, residualZeroPoissonBound, F]
    rw [show (∑' n : ℕ,
        2 * |rho| ^ (n + 1) *
          |platformResidualMaterialField C k a hk ha ha2 hthreshold theta|) =
        (∑' n : ℕ, |rho| ^ (n + 1)) *
          (2 * |platformResidualMaterialField C k a hk ha ha2 hthreshold theta|) by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro n
      ring]
    ring
  have hboundIntegrable : IntervalIntegrable
      (fun theta ↦ ∑' n, bound n theta) volume 0 Real.pi := by
    rw [hboundTsum]
    exact hF.abs.const_mul (2 * ∑' n : ℕ, |rho| ^ (n + 1))
  have htermHasSum : ∀ᵐ theta ∂volume,
      theta ∈ uIoc (0 : ℝ) Real.pi →
        HasSum (fun n ↦ term n theta)
          (F theta * (platformPoissonKernel rho theta - 1)) := by
    filter_upwards with theta
    intro _htheta
    let base : ℕ → ℝ := fun n ↦
      2 * rho ^ (n + 1) *
        Real.cos (((n + 1 : ℕ) : ℝ) * theta)
    have hbase : Summable base := by
      apply Summable.of_norm_bounded (hgeom.mul_left 2)
      intro n
      calc
        ‖base n‖ = 2 * |rho| ^ (n + 1) *
            |Real.cos (((n + 1 : ℕ) : ℝ) * theta)| := by
              simp only [base, Real.norm_eq_abs, abs_mul, abs_pow,
                abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ 2 * |rho| ^ (n + 1) := by
              exact mul_le_of_le_one_right
                (mul_nonneg (by norm_num)
                  (pow_nonneg (abs_nonneg rho) (n + 1)))
                (Real.abs_cos_le_one
                  (((n + 1 : ℕ) : ℝ) * theta))
    have hkernel := platformPoissonKernel_eq_one_add_two_tsum hrho theta
    have hbaseTsum : ∑' n, base n =
        platformPoissonKernel rho theta - 1 := by
      dsimp only [base]
      rw [show (∑' n : ℕ,
          2 * rho ^ (n + 1) *
            Real.cos (((n + 1 : ℕ) : ℝ) * theta)) =
          2 * ∑' n : ℕ,
            rho ^ (n + 1) *
              Real.cos (((n + 1 : ℕ) : ℝ) * theta) by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        ring]
      linarith
    have hscaled := hbase.hasSum.mul_left (F theta)
    rw [hbaseTsum] at hscaled
    exact HasSum.congr_fun hscaled (fun _n ↦ rfl)
  exact intervalIntegral.hasSum_integral_of_dominated_convergence
    bound htermMeas hboundPoint hboundSummable hboundIntegrable htermHasSum

/-- The Abel cosine series of the concrete material Fourier coefficients,
evaluated at zero, is its ordinary Poisson convolution. -/
theorem platformResidualMaterialAbelCosineSeries_zero_eq_poissonIntegral
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    platformAbelCosineSeries
        (platformResidualMaterialMean C k a hk ha ha2 hthreshold)
        (platformResidualMaterialCosineCoefficient
          C k a hk ha ha2 hthreshold) rho 0 =
      (1 / Real.pi) *
        ∫ theta in 0..Real.pi,
          platformResidualMaterialField C k a hk ha ha2 hthreshold theta *
            platformPoissonKernel rho theta := by
  let F := platformResidualMaterialField C k a hk ha ha2 hthreshold
  let coefficient := platformResidualMaterialCosineCoefficient
    C k a hk ha ha2 hthreshold
  let f0 := platformResidualMaterialMean C k a hk ha ha2 hthreshold
  let seq : ℕ → ℝ := fun n ↦
    platformAbelZeroSequence coefficient n * rho ^ n
  have hrhoAbs : |rho| < 1 := by
    rw [abs_of_nonneg hrho0]
    exact hrho1
  have hbound := platformResidualMaterialCosineCoefficient_bounded
    C k a hk ha ha2 hthreshold
  have hseries := hasSum_integral_residualZeroPoissonTerm
    C k a hk ha ha2 hthreshold hrhoAbs
  have hseriesScaled := hseries.mul_left (1 / Real.pi)
  have hterm (n : ℕ) :
      (1 / Real.pi) *
          (∫ theta in 0..Real.pi,
            residualZeroPoissonTerm C k a hk ha ha2 hthreshold
              rho n theta) = seq (n + 1) := by
    have hintegrand :
        (fun theta ↦
          residualZeroPoissonTerm C k a hk ha ha2 hthreshold
            rho n theta) =
        fun theta ↦
          (2 * rho ^ (n + 1)) *
            (F theta * Real.cos (((n + 1 : ℕ) : ℝ) * theta)) := by
      funext theta
      dsimp only [residualZeroPoissonTerm, F]
      ring
    rw [hintegrand, intervalIntegral.integral_const_mul]
    dsimp only [seq]
    rw [platformAbelZeroSequence_of_pos coefficient (by omega)]
    dsimp only [coefficient, platformResidualMaterialCosineCoefficient]
    ring
  have hshift : HasSum (fun n ↦ seq (n + 1))
      ((1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          F theta * (platformPoissonKernel rho theta - 1))) := by
    exact HasSum.congr_fun hseriesScaled (fun n ↦ (hterm n).symm)
  have hseqSummable : Summable seq := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.add_comm] using! hshift.summable
  have hseqTsum : ∑' n, seq n =
      (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          F theta * (platformPoissonKernel rho theta - 1)) := by
    rw [hseqSummable.tsum_eq_zero_add]
    have hzero : seq 0 = 0 := by
      simp [seq]
    rw [hzero, zero_add]
    simpa only [Nat.add_comm] using! hshift.tsum_eq
  have hzeroSeries := platformAbelCosineSeries_zero_eq_tsum_zeroSequence
    hrhoAbs hbound f0
  change platformAbelCosineSeries f0 coefficient rho 0 = _
  rw [hzeroSeries]
  change f0 + ∑' n, seq n = _
  rw [hseqTsum]
  have hF : IntervalIntegrable F volume 0 Real.pi :=
    intervalIntegrable_platformResidualMaterialField
      C k a hk ha ha2 hthreshold
  have hP : Continuous (fun theta ↦ platformPoissonKernel rho theta) := by
    unfold platformPoissonKernel
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro theta
      exact (platformPoissonKernel_den_pos hrho0 hrho1).ne'
  have hdiff : IntervalIntegrable
      (fun theta ↦ F theta * (platformPoissonKernel rho theta - 1))
      volume 0 Real.pi :=
    hF.mul_continuousOn (hP.sub continuous_const).continuousOn
  have hsumIntegral :
      (∫ theta in 0..Real.pi,
        F theta * platformPoissonKernel rho theta) =
      (∫ theta in 0..Real.pi, F theta) +
        ∫ theta in 0..Real.pi,
          F theta * (platformPoissonKernel rho theta - 1) := by
    rw [← intervalIntegral.integral_add hF hdiff]
    apply intervalIntegral.integral_congr
    intro theta _htheta
    ring
  dsimp only [f0, platformResidualMaterialMean]
  rw [hsumIntegral]
  ring

private theorem tsum_crossing_split
    (aMinus aPlus : ℝ) (coefficient powerMinus powerPlus : ℕ → ℝ)
    (hminus : Summable (fun n ↦ coefficient n * powerMinus n))
    (hplus : Summable (fun n ↦ coefficient n * powerPlus n)) :
    (∑' n, coefficient n *
        (-2 * (aMinus * powerMinus n + aPlus * powerPlus n))) =
      -2 * aMinus * ∑' n, coefficient n * powerMinus n +
        -2 * aPlus * ∑' n, coefficient n * powerPlus n := by
  calc
    (∑' n, coefficient n *
        (-2 * (aMinus * powerMinus n + aPlus * powerPlus n))) =
        ∑' n, (
          (-2 * aMinus) * (coefficient n * powerMinus n) +
            (-2 * aPlus) * (coefficient n * powerPlus n)) := by
      apply tsum_congr
      intro n
      ring
    _ = (∑' n, (-2 * aMinus) * (coefficient n * powerMinus n)) +
          ∑' n, (-2 * aPlus) * (coefficient n * powerPlus n) := by
      rw [(hminus.mul_left _).tsum_add (hplus.mul_left _)]
    _ = _ := by
      rw [tsum_mul_left, tsum_mul_left]

/-- For every bounded coefficient sequence, the exterior coefficient value
is the corresponding linear combination of its two Poisson evaluations. -/
theorem platformBoundaryExteriorVariation_eq_abelCosineSeries_zero
    {a xMinus xPlus sigmaMinus sigmaPlus f0 : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    {coefficient : ℕ → ℝ} {coefficientBound : ℝ}
    (hbound : RealSequenceBoundedBy coefficient coefficientBound) :
    platformBoundaryExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 coefficient =
      -(sigmaMinus / platformCrossingScale a xMinus) *
          platformAbelCosineSeries f0 coefficient
            (platformRho a xMinus) 0 -
        (sigmaPlus / platformCrossingScale a xPlus) *
          platformAbelCosineSeries f0 coefficient
            (platformRho a xPlus) 0 := by
  have hrhoMinus := platformRho_mem_Ioo hxMinus ha2
  have hrhoPlus := platformRho_mem_Ioo hxPlus ha2
  have hrhoMinusAbs : |platformRho a xMinus| < 1 := by
    rw [abs_of_pos hrhoMinus.1]
    exact hrhoMinus.2
  have hrhoPlusAbs : |platformRho a xPlus| < 1 := by
    rw [abs_of_pos hrhoPlus.1]
    exact hrhoPlus.2
  have hEvenMinus : Summable (fun m : ℕ ↦
      coefficient (2 * (m + 1)) *
        platformRho a xMinus ^ (2 * (m + 1))) :=
    (summable_platformAbelEvenCoefficient hrhoMinusAbs hbound).congr
      (fun m ↦ by ring)
  have hEvenPlus : Summable (fun m : ℕ ↦
      coefficient (2 * (m + 1)) *
        platformRho a xPlus ^ (2 * (m + 1))) :=
    (summable_platformAbelEvenCoefficient hrhoPlusAbs hbound).congr
      (fun m ↦ by ring)
  have hOddMinus : Summable (fun m : ℕ ↦
      coefficient (2 * m + 1) *
        platformRho a xMinus ^ (2 * m + 1)) :=
    (summable_platformAbelOddCoefficient hrhoMinusAbs hbound).congr
      (fun m ↦ by ring)
  have hOddPlus : Summable (fun m : ℕ ↦
      coefficient (2 * m + 1) *
        platformRho a xPlus ^ (2 * m + 1)) :=
    (summable_platformAbelOddCoefficient hrhoPlusAbs hbound).congr
      (fun m ↦ by ring)
  have hEvenSeriesMinus :
      (∑' m, platformAbelEvenCosineTerm coefficient
          (platformRho a xMinus) m 0) =
        2 * ∑' m, coefficient (2 * (m + 1)) *
          platformRho a xMinus ^ (2 * (m + 1)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    simp only [platformAbelEvenCosineTerm, mul_zero,
      Real.cos_zero, mul_one]
    ring
  have hEvenSeriesPlus :
      (∑' m, platformAbelEvenCosineTerm coefficient
          (platformRho a xPlus) m 0) =
        2 * ∑' m, coefficient (2 * (m + 1)) *
          platformRho a xPlus ^ (2 * (m + 1)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    simp only [platformAbelEvenCosineTerm, mul_zero,
      Real.cos_zero, mul_one]
    ring
  have hOddSeriesMinus :
      (∑' m, platformAbelOddCosineTerm coefficient
          (platformRho a xMinus) m 0) =
        2 * ∑' m, coefficient (2 * m + 1) *
          platformRho a xMinus ^ (2 * m + 1) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    simp only [platformAbelOddCosineTerm, mul_zero,
      Real.cos_zero, mul_one]
    ring
  have hOddSeriesPlus :
      (∑' m, platformAbelOddCosineTerm coefficient
          (platformRho a xPlus) m 0) =
        2 * ∑' m, coefficient (2 * m + 1) *
          platformRho a xPlus ^ (2 * m + 1) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    simp only [platformAbelOddCosineTerm, mul_zero,
      Real.cos_zero, mul_one]
    ring
  have hAbelMinus :
      platformAbelCosineSeries f0 coefficient
          (platformRho a xMinus) 0 =
        f0 +
          2 * ∑' m, coefficient (2 * (m + 1)) *
            platformRho a xMinus ^ (2 * (m + 1)) +
          2 * ∑' m, coefficient (2 * m + 1) *
            platformRho a xMinus ^ (2 * m + 1) := by
    unfold platformAbelCosineSeries
    rw [hEvenSeriesMinus, hOddSeriesMinus]
  have hAbelPlus :
      platformAbelCosineSeries f0 coefficient
          (platformRho a xPlus) 0 =
        f0 +
          2 * ∑' m, coefficient (2 * (m + 1)) *
            platformRho a xPlus ^ (2 * (m + 1)) +
          2 * ∑' m, coefficient (2 * m + 1) *
            platformRho a xPlus ^ (2 * m + 1) := by
    unfold platformAbelCosineSeries
    rw [hEvenSeriesPlus, hOddSeriesPlus]
  unfold platformBoundaryExteriorVariation platformAbelExteriorSeriesValue
  simp only [one_pow, one_mul]
  rw [endpointAdjointGamma_eq_crossingScales hxMinus hxPlus ha2]
  simp_rw [endpointExteriorCosCoefficient_eq_crossingScales
    hxMinus hxPlus ha2]
  rw [tsum_crossing_split
      (sigmaMinus / platformCrossingScale a xMinus)
      (sigmaPlus / platformCrossingScale a xPlus)
      (fun m ↦ coefficient (2 * (m + 1)))
      (fun m ↦ platformRho a xMinus ^ (2 * (m + 1)))
      (fun m ↦ platformRho a xPlus ^ (2 * (m + 1)))
      hEvenMinus hEvenPlus,
    tsum_crossing_split
      (sigmaMinus / platformCrossingScale a xMinus)
      (sigmaPlus / platformCrossingScale a xPlus)
      (fun m ↦ coefficient (2 * m + 1))
      (fun m ↦ platformRho a xMinus ^ (2 * m + 1))
      (fun m ↦ platformRho a xPlus ^ (2 * m + 1))
      hOddMinus hOddPlus]
  rw [hAbelMinus, hAbelPlus]
  ring

/-- The concrete Poisson evaluation at one exterior point is the continuum
material numerator, including the `k` and crossing-scale normalizations. -/
theorem platformResidualMaterialAbelCosineSeries_zero_eq_materialVelocity
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hxa : x < a) :
    platformAbelCosineSeries
        (platformResidualMaterialMean C k a hk ha ha2 hthreshold)
        (platformResidualMaterialCosineCoefficient
          C k a hk ha ha2 hthreshold)
        (platformRho a x) 0 =
      platformCrossingScale a x * k *
        platformReferenceExteriorPotentialMaterialVelocityLimit
          C k a hk ha ha2 hthreshold x := by
  have hrho := platformRho_mem_Ioo hxa ha2
  rw [platformResidualMaterialAbelCosineSeries_zero_eq_poissonIntegral
    C k a hk ha ha2 hthreshold hrho.1.le hrho.2]
  rw [platformReferenceExteriorPotentialMaterialVelocityLimit_eq_materialFieldIntegral
    C k a hk ha ha2 hthreshold hxa]
  let F := platformResidualMaterialField C k a hk ha ha2 hthreshold
  have hintegral :
      (∫ theta in 0..Real.pi,
        F theta * platformPoissonKernel (platformRho a x) theta) =
      platformCrossingScale a x *
        ∫ theta in 0..Real.pi,
          F theta / (platformAngularDistance a theta - x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro theta htheta
    rw [uIcc_of_le Real.pi_pos.le] at htheta
    have hpoisson := platformCrossingScale_div_distance_eq_poisson
      hxa ha2 htheta
    change F theta * platformPoissonKernel (platformRho a x) theta =
      platformCrossingScale a x *
        (F theta / (platformAngularDistance a theta - x))
    rw [← hpoisson]
    ring
  rw [hintegral]
  have hk0 : k ≠ 0 := (zero_lt_one.trans_le hk).ne'
  field_simp [hk0]
  ring

/-- The concrete material boundary functional is the adjoint-weighted sum
of the two continuum material numerators. -/
theorem platformBoundaryExteriorVariation_material_eq_resolvents
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) :
    platformBoundaryExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus
        (platformResidualMaterialMean C k a hk ha ha2 hthreshold)
        (platformResidualMaterialCosineCoefficient
          C k a hk ha ha2 hthreshold) =
      -sigmaMinus * k *
          platformReferenceExteriorPotentialMaterialVelocityLimit
            C k a hk ha ha2 hthreshold xMinus -
        sigmaPlus * k *
          platformReferenceExteriorPotentialMaterialVelocityLimit
            C k a hk ha ha2 hthreshold xPlus := by
  rw [platformBoundaryExteriorVariation_eq_abelCosineSeries_zero
    hxMinus hxPlus ha2
    (platformResidualMaterialCosineCoefficient_bounded
      C k a hk ha ha2 hthreshold)]
  rw [platformResidualMaterialAbelCosineSeries_zero_eq_materialVelocity
      C k a hk ha ha2 hthreshold hxMinus,
    platformResidualMaterialAbelCosineSeries_zero_eq_materialVelocity
      C k a hk ha ha2 hthreshold hxPlus]
  have hscaleMinus : platformCrossingScale a xMinus ≠ 0 :=
    (platformCrossingScale_pos hxMinus ha2).ne'
  have hscalePlus : platformCrossingScale a xPlus ≠ 0 :=
    (platformCrossingScale_pos hxPlus ha2).ne'
  field_simp [hscaleMinus, hscalePlus]

/-- Canonical adjoint mass at the negative-slope crossing. -/
def platformReferenceNegativeCrossingAdjointWeight
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (xMinus : ℝ) : ℝ :=
  -1 / (k * platformReferenceExteriorPotentialXDerivativeLimit
    C k a hk ha ha2 hthreshold xMinus)

/-- Canonical adjoint mass at the positive-slope crossing. -/
def platformReferencePositiveCrossingAdjointWeight
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (xPlus : ℝ) : ℝ :=
  1 / (k * platformReferenceExteriorPotentialXDerivativeLimit
    C k a hk ha ha2 hthreshold xPlus)

/-- With the reciprocal-slope adjoint weights, the concrete material Abel
boundary value is exactly the implicit velocity of the crossing width. -/
theorem platformBoundaryExteriorVariation_material_eq_crossingWidthMaterialVelocity
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xMinus xPlus : ℝ} (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hminusDerivative : platformReferenceExteriorPotentialXDerivativeLimit
      C k a hk ha ha2 hthreshold xMinus ≠ 0)
    (hplusDerivative : platformReferenceExteriorPotentialXDerivativeLimit
      C k a hk ha ha2 hthreshold xPlus ≠ 0) :
    platformBoundaryExteriorVariation a xMinus xPlus
        (platformReferenceNegativeCrossingAdjointWeight
          C k a hk ha ha2 hthreshold xMinus)
        (platformReferencePositiveCrossingAdjointWeight
          C k a hk ha ha2 hthreshold xPlus)
        (platformResidualMaterialMean C k a hk ha ha2 hthreshold)
        (platformResidualMaterialCosineCoefficient
          C k a hk ha ha2 hthreshold) =
      platformReferenceCrossingWidthMaterialVelocity C k a
        hk ha ha2 hthreshold xMinus xPlus := by
  rw [platformBoundaryExteriorVariation_material_eq_resolvents
    C k a hk ha ha2 hthreshold hxMinus hxPlus]
  unfold platformReferenceNegativeCrossingAdjointWeight
    platformReferencePositiveCrossingAdjointWeight
    platformReferenceCrossingWidthMaterialVelocity
  have hk0 : k ≠ 0 := (zero_lt_one.trans_le hk).ne'
  field_simp [hk0, hminusDerivative, hplusDerivative]
  ring

end

end Erdos1038
