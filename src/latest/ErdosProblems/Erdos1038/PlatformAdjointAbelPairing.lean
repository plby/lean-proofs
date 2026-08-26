import ErdosProblems.Erdos1038.PlatformAdjointAbelHilbert

/-!
# The infinite interior Abel adjoint pairing

The compact-uniform Hilbert estimates permit termwise integration against
the endpoint adjoint density.  Consequently the actual interval integral
of the infinite Abel Hilbert series is the sum of the exact mode pairings.
-/

set_option warningAsError false

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

private def platformAdjointIntervalCompact : TopologicalSpace.Compacts ℝ :=
  ⟨uIcc (0 : ℝ) Real.pi, isCompact_uIcc⟩

def endpointAdjointDensityContinuousMap
    (sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ)
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1) : C(ℝ, ℝ) where
  toFun := endpointAdjointAngularDensity
    sigmaMinus sigmaPlus rhoMinus rhoPlus
  continuous_toFun :=
    continuous_endpointAdjointAngularDensity hm0 hm1 hp0 hp1

def endpointAdjointAbelEvenIntegrandTerm
    (sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ)
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    (r : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) : C(ℝ, ℝ) :=
  endpointAdjointDensityContinuousMap sigmaMinus sigmaPlus
      rhoMinus rhoPlus hm0 hm1 hp0 hp1 *
    platformAbelEvenHilbertContinuousTerm r coefficient lambda m

def endpointAdjointAbelOddIntegrandTerm
    (sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ)
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    (r : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) : C(ℝ, ℝ) :=
  endpointAdjointDensityContinuousMap sigmaMinus sigmaPlus
      rhoMinus rhoPlus hm0 hm1 hp0 hp1 *
    platformAbelOddHilbertContinuousTerm r coefficient lambda m

def endpointAdjointAbelIntegrandTerm
    (sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ)
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    (r : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) :
    ℕ ⊕ ℕ → C(ℝ, ℝ)
  | Sum.inl m => endpointAdjointAbelEvenIntegrandTerm
      sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
        r coefficient lambda m
  | Sum.inr m => endpointAdjointAbelOddIntegrandTerm
      sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
        r coefficient lambda m

private lemma endpointAdjointAbelEvenIntegrandTerm_norm_restrict_le
    {sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    (r : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) :
    ‖(endpointAdjointAbelEvenIntegrandTerm
        sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
          r coefficient lambda m).restrict platformAdjointIntervalCompact‖ ≤
      ‖(endpointAdjointDensityContinuousMap sigmaMinus sigmaPlus
          rhoMinus rhoPlus hm0 hm1 hp0 hp1).restrict
            platformAdjointIntervalCompact‖ *
        ‖(platformAbelEvenHilbertContinuousTerm
          r coefficient lambda m).restrict platformAdjointIntervalCompact‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro theta
  have hdensity :
      |endpointAdjointAngularDensity sigmaMinus sigmaPlus
          rhoMinus rhoPlus theta.1| ≤
        ‖(endpointAdjointDensityContinuousMap sigmaMinus sigmaPlus
          rhoMinus rhoPlus hm0 hm1 hp0 hp1).restrict
            platformAdjointIntervalCompact‖ := by
    simpa only [endpointAdjointDensityContinuousMap,
      ContinuousMap.restrict_apply, Real.norm_eq_abs] using!
      ((endpointAdjointDensityContinuousMap sigmaMinus sigmaPlus
        rhoMinus rhoPlus hm0 hm1 hp0 hp1).restrict
          platformAdjointIntervalCompact).norm_coe_le_norm theta
  have hterm :
      |platformAbelEvenHilbertTerm r coefficient lambda m theta.1| ≤
        ‖(platformAbelEvenHilbertContinuousTerm
          r coefficient lambda m).restrict platformAdjointIntervalCompact‖ := by
    simpa only [platformAbelEvenHilbertContinuousTerm,
      ContinuousMap.restrict_apply, Real.norm_eq_abs] using!
      ((platformAbelEvenHilbertContinuousTerm
        r coefficient lambda m).restrict
          platformAdjointIntervalCompact).norm_coe_le_norm theta
  change
    |endpointAdjointAngularDensity sigmaMinus sigmaPlus
        rhoMinus rhoPlus theta.1 *
      platformAbelEvenHilbertTerm r coefficient lambda m theta.1| ≤ _
  rw [abs_mul]
  exact mul_le_mul hdensity hterm (abs_nonneg _) (norm_nonneg _)

private lemma endpointAdjointAbelOddIntegrandTerm_norm_restrict_le
    {sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    (r : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) :
    ‖(endpointAdjointAbelOddIntegrandTerm
        sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
          r coefficient lambda m).restrict platformAdjointIntervalCompact‖ ≤
      ‖(endpointAdjointDensityContinuousMap sigmaMinus sigmaPlus
          rhoMinus rhoPlus hm0 hm1 hp0 hp1).restrict
            platformAdjointIntervalCompact‖ *
        ‖(platformAbelOddHilbertContinuousTerm
          r coefficient lambda m).restrict platformAdjointIntervalCompact‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro theta
  have hdensity :
      |endpointAdjointAngularDensity sigmaMinus sigmaPlus
          rhoMinus rhoPlus theta.1| ≤
        ‖(endpointAdjointDensityContinuousMap sigmaMinus sigmaPlus
          rhoMinus rhoPlus hm0 hm1 hp0 hp1).restrict
            platformAdjointIntervalCompact‖ := by
    simpa only [endpointAdjointDensityContinuousMap,
      ContinuousMap.restrict_apply, Real.norm_eq_abs] using!
      ((endpointAdjointDensityContinuousMap sigmaMinus sigmaPlus
        rhoMinus rhoPlus hm0 hm1 hp0 hp1).restrict
          platformAdjointIntervalCompact).norm_coe_le_norm theta
  have hterm :
      |platformAbelOddHilbertTerm r coefficient lambda m theta.1| ≤
        ‖(platformAbelOddHilbertContinuousTerm
          r coefficient lambda m).restrict platformAdjointIntervalCompact‖ := by
    simpa only [platformAbelOddHilbertContinuousTerm,
      ContinuousMap.restrict_apply, Real.norm_eq_abs] using!
      ((platformAbelOddHilbertContinuousTerm
        r coefficient lambda m).restrict
          platformAdjointIntervalCompact).norm_coe_le_norm theta
  change
    |endpointAdjointAngularDensity sigmaMinus sigmaPlus
        rhoMinus rhoPlus theta.1 *
      platformAbelOddHilbertTerm r coefficient lambda m theta.1| ≤ _
  rw [abs_mul]
  exact mul_le_mul hdensity hterm (abs_nonneg _) (norm_nonneg _)

theorem summable_endpointAdjointAbelEvenIntegrandTerm_restrict_norm
    {sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) (r : ℝ) :
    Summable (fun m : ℕ ↦
      ‖(endpointAdjointAbelEvenIntegrandTerm
        sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
          r coefficient lambda m).restrict platformAdjointIntervalCompact‖) := by
  have hmajor :=
    (summable_platformAbelEvenHilbertContinuousTerm_restrict_norm
      hlambda hbound r platformAdjointIntervalCompact).mul_left
        ‖(endpointAdjointDensityContinuousMap sigmaMinus sigmaPlus
          rhoMinus rhoPlus hm0 hm1 hp0 hp1).restrict
            platformAdjointIntervalCompact‖
  apply Summable.of_norm_bounded hmajor
  intro m
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact endpointAdjointAbelEvenIntegrandTerm_norm_restrict_le
    hm0 hm1 hp0 hp1 r coefficient lambda m

theorem summable_endpointAdjointAbelOddIntegrandTerm_restrict_norm
    {sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) (r : ℝ) :
    Summable (fun m : ℕ ↦
      ‖(endpointAdjointAbelOddIntegrandTerm
        sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
          r coefficient lambda m).restrict platformAdjointIntervalCompact‖) := by
  have hmajor :=
    (summable_platformAbelOddHilbertContinuousTerm_restrict_norm
      hlambda hbound r platformAdjointIntervalCompact).mul_left
        ‖(endpointAdjointDensityContinuousMap sigmaMinus sigmaPlus
          rhoMinus rhoPlus hm0 hm1 hp0 hp1).restrict
            platformAdjointIntervalCompact‖
  apply Summable.of_norm_bounded hmajor
  intro m
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact endpointAdjointAbelOddIntegrandTerm_norm_restrict_le
    hm0 hm1 hp0 hp1 r coefficient lambda m

theorem summable_endpointAdjointAbelIntegrandTerm_restrict_norm
    {sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) (r : ℝ) :
    Summable (fun i : ℕ ⊕ ℕ ↦
      ‖(endpointAdjointAbelIntegrandTerm
        sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
          r coefficient lambda i).restrict platformAdjointIntervalCompact‖) := by
  apply Summable.sum _
  · exact summable_endpointAdjointAbelEvenIntegrandTerm_restrict_norm
      hm0 hm1 hp0 hp1 hlambda hbound r
  · exact summable_endpointAdjointAbelOddIntegrandTerm_restrict_norm
      hm0 hm1 hp0 hp1 hlambda hbound r

set_option maxHeartbeats 1000000 in
theorem tsum_endpointAdjointAbelIntegrandTerm_apply
    {sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C)
    (r theta : ℝ) :
    (∑' i : ℕ ⊕ ℕ,
      endpointAdjointAbelIntegrandTerm
        sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
          r coefficient lambda i theta) =
      endpointAdjointAngularDensity sigmaMinus sigmaPlus
          rhoMinus rhoPlus theta *
        platformAbelHilbertSeries r coefficient lambda theta := by
  let d : ℝ := endpointAdjointAngularDensity sigmaMinus sigmaPlus
    rhoMinus rhoPlus theta
  let e : ℕ → ℝ := fun m ↦
    platformAbelEvenHilbertTerm r coefficient lambda m theta
  let o : ℕ → ℝ := fun m ↦
    platformAbelOddHilbertTerm r coefficient lambda m theta
  have he : Summable e := by
    simpa only [e] using!
      summable_platformAbelEvenHilbertTerm hlambda hbound r theta
  have ho : Summable o := by
    simpa only [o] using!
      summable_platformAbelOddHilbertTerm hlambda hbound r theta
  have hcombined (i : ℕ ⊕ ℕ) :
      endpointAdjointAbelIntegrandTerm
        sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
          r coefficient lambda i theta =
        Sum.elim (fun m ↦ d * e m) (fun m ↦ d * o m) i := by
    cases i <;> rfl
  have hsplit :
      (∑' i : ℕ ⊕ ℕ,
        Sum.elim (fun m ↦ d * e m) (fun m ↦ d * o m) i) =
        d * (∑' m : ℕ, e m) + d * ∑' m : ℕ, o m := by
    have hsum : HasSum
        (fun i : ℕ ⊕ ℕ ↦
          Sum.elim (fun m ↦ d * e m) (fun m ↦ d * o m) i)
        (d * (∑' m : ℕ, e m) + d * ∑' m : ℕ, o m) := by
      exact (he.hasSum.mul_left d).sum (ho.hasSum.mul_left d)
    exact hsum.tsum_eq
  calc
    (∑' i : ℕ ⊕ ℕ,
        endpointAdjointAbelIntegrandTerm
          sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
            r coefficient lambda i theta) =
        ∑' i : ℕ ⊕ ℕ,
          Sum.elim (fun m ↦ d * e m) (fun m ↦ d * o m) i := by
      apply tsum_congr
      exact hcombined
    _ = d * (∑' m : ℕ, e m) + d * ∑' m : ℕ, o m := hsplit
    _ = d * ((∑' m : ℕ, e m) + ∑' m : ℕ, o m) := by
      rw [mul_add]
    _ = endpointAdjointAngularDensity sigmaMinus sigmaPlus
          rhoMinus rhoPlus theta *
        platformAbelHilbertSeries r coefficient lambda theta := by
      simp only [d, e, o, platformAbelHilbertSeries]

theorem integral_endpointAdjointDensity_mul_platformAbelHilbertSeries_eq_tsum
    {sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) (r : ℝ) :
    (∫ theta in 0..Real.pi,
      endpointAdjointAngularDensity sigmaMinus sigmaPlus
          rhoMinus rhoPlus theta *
        platformAbelHilbertSeries r coefficient lambda theta) =
      ∑' i : ℕ ⊕ ℕ,
        ∫ theta in 0..Real.pi,
          endpointAdjointAbelIntegrandTerm
            sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
              r coefficient lambda i theta := by
  have hnorm := summable_endpointAdjointAbelIntegrandTerm_restrict_norm
    (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
      hm0 hm1 hp0 hp1 hlambda hbound r
  have hnorm' : Summable (fun i : ℕ ⊕ ℕ ↦
      ‖(endpointAdjointAbelIntegrandTerm
        sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
          r coefficient lambda i).restrict
        (⟨uIcc (0 : ℝ) Real.pi, isCompact_uIcc⟩ :
          TopologicalSpace.Compacts ℝ)‖) := by
    simpa only [platformAdjointIntervalCompact] using! hnorm
  have hswap :=
    intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
      (a := (0 : ℝ)) (b := Real.pi)
      (f := endpointAdjointAbelIntegrandTerm
        sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
          r coefficient lambda) hnorm'
  calc
    (∫ theta in 0..Real.pi,
        endpointAdjointAngularDensity sigmaMinus sigmaPlus
            rhoMinus rhoPlus theta *
          platformAbelHilbertSeries r coefficient lambda theta) =
        ∫ theta in 0..Real.pi,
          ∑' i : ℕ ⊕ ℕ,
            endpointAdjointAbelIntegrandTerm
              sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
                r coefficient lambda i theta := by
      apply intervalIntegral.integral_congr
      intro theta _htheta
      exact (tsum_endpointAdjointAbelIntegrandTerm_apply
        (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
          hm0 hm1 hp0 hp1 hlambda hbound r theta).symm
    _ = _ := hswap.symm

theorem one_div_pi_mul_integral_endpointAdjointAbelEvenIntegrandTerm
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAbelEvenIntegrandTerm
            sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
              r coefficient lambda m theta) =
      (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) *
        endpointAdjointEvenCosCoefficient
          r sigmaMinus sigmaPlus rhoMinus rhoPlus m := by
  let c : ℝ := lambda ^ (2 * (m + 1)) *
    coefficient (2 * (m + 1))
  have hpoint :
      (fun theta : ℝ ↦
        endpointAdjointAbelEvenIntegrandTerm
          sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
            r coefficient lambda m theta) =
      fun theta ↦ (c * (2 / r)) *
        (endpointAdjointAngularDensity sigmaMinus sigmaPlus
            rhoMinus rhoPlus theta *
          (-oddSecondKindAngularMode (m + 1) theta)) := by
    funext theta
    change endpointAdjointAngularDensity sigmaMinus sigmaPlus
        rhoMinus rhoPlus theta *
          platformAbelEvenHilbertTerm
            r coefficient lambda m theta = _
    unfold platformAbelEvenHilbertTerm c
    ring
  rw [hpoint, intervalIntegral.integral_const_mul]
  have hpair := finiteHilbert_evenMode_adjointPairing
    (r := r) (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
      hm0 hm1 hp0 hp1 m
  calc
    (1 / Real.pi) *
        ((c * (2 / r)) *
          (∫ theta in 0..Real.pi,
            endpointAdjointAngularDensity sigmaMinus sigmaPlus
                rhoMinus rhoPlus theta *
              (-oddSecondKindAngularMode (m + 1) theta))) =
      c * ((2 / r) * (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity sigmaMinus sigmaPlus
              rhoMinus rhoPlus theta *
            (-oddSecondKindAngularMode (m + 1) theta))) := by ring
    _ = c * endpointAdjointEvenCosCoefficient
        r sigmaMinus sigmaPlus rhoMinus rhoPlus m := by rw [hpair]
    _ = _ := by rfl

theorem one_div_pi_mul_integral_endpointAdjointAbelOddIntegrandTerm
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAbelOddIntegrandTerm
            sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
              r coefficient lambda m theta) =
      (lambda ^ (2 * m + 1) * coefficient (2 * m + 1)) *
        endpointAdjointOddCosCoefficient
          r sigmaMinus sigmaPlus rhoMinus rhoPlus m := by
  let c : ℝ := lambda ^ (2 * m + 1) * coefficient (2 * m + 1)
  have hpoint :
      (fun theta : ℝ ↦
        endpointAdjointAbelOddIntegrandTerm
          sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
            r coefficient lambda m theta) =
      fun theta ↦ (c * (2 / r)) *
        (endpointAdjointAngularDensity sigmaMinus sigmaPlus
            rhoMinus rhoPlus theta *
          (-evenSecondKindAngularMode m theta)) := by
    funext theta
    change endpointAdjointAngularDensity sigmaMinus sigmaPlus
        rhoMinus rhoPlus theta *
          platformAbelOddHilbertTerm
            r coefficient lambda m theta = _
    unfold platformAbelOddHilbertTerm c
    ring
  rw [hpoint, intervalIntegral.integral_const_mul]
  have hpair := finiteHilbert_oddMode_adjointPairing
    (r := r) (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
      hm0 hm1 hp0 hp1 m
  calc
    (1 / Real.pi) *
        ((c * (2 / r)) *
          (∫ theta in 0..Real.pi,
            endpointAdjointAngularDensity sigmaMinus sigmaPlus
                rhoMinus rhoPlus theta *
              (-evenSecondKindAngularMode m theta))) =
      c * ((2 / r) * (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity sigmaMinus sigmaPlus
              rhoMinus rhoPlus theta *
            (-evenSecondKindAngularMode m theta))) := by ring
    _ = c * endpointAdjointOddCosCoefficient
        r sigmaMinus sigmaPlus rhoMinus rhoPlus m := by rw [hpair]
    _ = _ := by rfl

/-- The exact Abel sum of the adjoint mode coefficients. -/
def platformAbelAdjointPairingSeries
    (r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ)
    (coefficient : ℕ → ℝ) (lambda : ℝ) : ℝ :=
  (∑' m : ℕ,
    (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) *
      endpointAdjointEvenCosCoefficient
        r sigmaMinus sigmaPlus rhoMinus rhoPlus m) +
  ∑' m : ℕ,
    (lambda ^ (2 * m + 1) * coefficient (2 * m + 1)) *
      endpointAdjointOddCosCoefficient
        r sigmaMinus sigmaPlus rhoMinus rhoPlus m

private theorem summable_one_div_pi_mul_integral_evenIntegrand
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) :
    Summable (fun m : ℕ ↦
      (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAbelEvenIntegrandTerm
            sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
              r coefficient lambda m theta)) := by
  have hnorm :=
    summable_endpointAdjointAbelEvenIntegrandTerm_restrict_norm
      (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
        hm0 hm1 hp0 hp1 hlambda hbound r
  have hnorm' : Summable (fun m : ℕ ↦
      ‖(endpointAdjointAbelEvenIntegrandTerm
        sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
          r coefficient lambda m).restrict
        (⟨uIcc (0 : ℝ) Real.pi, isCompact_uIcc⟩ :
          TopologicalSpace.Compacts ℝ)‖) := by
    simpa only [platformAdjointIntervalCompact] using! hnorm
  exact (intervalIntegral.hasSum_intervalIntegral_of_summable_norm
    hnorm').summable.mul_left (1 / Real.pi)

private theorem summable_one_div_pi_mul_integral_oddIntegrand
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) :
    Summable (fun m : ℕ ↦
      (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAbelOddIntegrandTerm
            sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
              r coefficient lambda m theta)) := by
  have hnorm :=
    summable_endpointAdjointAbelOddIntegrandTerm_restrict_norm
      (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
        hm0 hm1 hp0 hp1 hlambda hbound r
  have hnorm' : Summable (fun m : ℕ ↦
      ‖(endpointAdjointAbelOddIntegrandTerm
        sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
          r coefficient lambda m).restrict
        (⟨uIcc (0 : ℝ) Real.pi, isCompact_uIcc⟩ :
          TopologicalSpace.Compacts ℝ)‖) := by
    simpa only [platformAdjointIntervalCompact] using! hnorm
  exact (intervalIntegral.hasSum_intervalIntegral_of_summable_norm
    hnorm').summable.mul_left (1 / Real.pi)

set_option maxHeartbeats 1000000 in
theorem one_div_pi_mul_integral_endpointAdjointDensity_mul_abelHilbertSeries
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity sigmaMinus sigmaPlus
              rhoMinus rhoPlus theta *
            platformAbelHilbertSeries r coefficient lambda theta) =
      platformAbelAdjointPairingSeries r sigmaMinus sigmaPlus
        rhoMinus rhoPlus coefficient lambda := by
  have hintegral :=
    integral_endpointAdjointDensity_mul_platformAbelHilbertSeries_eq_tsum
      (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
        hm0 hm1 hp0 hp1 hlambda hbound r
  have heven := summable_one_div_pi_mul_integral_evenIntegrand
    (r := r) (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
      hm0 hm1 hp0 hp1 hlambda hbound
  have hodd := summable_one_div_pi_mul_integral_oddIntegrand
    (r := r) (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
      hm0 hm1 hp0 hp1 hlambda hbound
  let evenIntegral : ℕ → ℝ := fun m ↦
    (1 / Real.pi) *
      (∫ theta in 0..Real.pi,
        endpointAdjointAbelEvenIntegrandTerm
          sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
            r coefficient lambda m theta)
  let oddIntegral : ℕ → ℝ := fun m ↦
    (1 / Real.pi) *
      (∫ theta in 0..Real.pi,
        endpointAdjointAbelOddIntegrandTerm
          sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
            r coefficient lambda m theta)
  have heven' : Summable evenIntegral := by
    simpa only [evenIntegral] using! heven
  have hodd' : Summable oddIntegral := by
    simpa only [oddIntegral] using! hodd
  have hsplit :
      (∑' i : ℕ ⊕ ℕ,
        Sum.elim evenIntegral oddIntegral i) =
        (∑' m : ℕ, evenIntegral m) + ∑' m : ℕ, oddIntegral m := by
    have hsum : HasSum (fun i : ℕ ⊕ ℕ ↦
        Sum.elim evenIntegral oddIntegral i)
        ((∑' m : ℕ, evenIntegral m) + ∑' m : ℕ, oddIntegral m) :=
      heven'.hasSum.sum hodd'.hasSum
    exact hsum.tsum_eq
  rw [hintegral]
  calc
    (1 / Real.pi) *
        (∑' i : ℕ ⊕ ℕ,
          ∫ theta in 0..Real.pi,
            endpointAdjointAbelIntegrandTerm
              sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
                r coefficient lambda i theta) =
      ∑' i : ℕ ⊕ ℕ,
        (1 / Real.pi) *
          (∫ theta in 0..Real.pi,
            endpointAdjointAbelIntegrandTerm
              sigmaMinus sigmaPlus rhoMinus rhoPlus hm0 hm1 hp0 hp1
                r coefficient lambda i theta) := by
      rw [tsum_mul_left]
    _ = ∑' i : ℕ ⊕ ℕ, Sum.elim evenIntegral oddIntegral i := by
      apply tsum_congr
      intro i
      cases i <;> rfl
    _ = (∑' m : ℕ, evenIntegral m) +
        ∑' m : ℕ, oddIntegral m := hsplit
    _ = platformAbelAdjointPairingSeries r sigmaMinus sigmaPlus
        rhoMinus rhoPlus coefficient lambda := by
      unfold platformAbelAdjointPairingSeries
      congr 1
      · apply tsum_congr
        intro m
        exact one_div_pi_mul_integral_endpointAdjointAbelEvenIntegrandTerm
          hm0 hm1 hp0 hp1 coefficient lambda m
      · apply tsum_congr
        intro m
        exact one_div_pi_mul_integral_endpointAdjointAbelOddIntegrandTerm
          hm0 hm1 hp0 hp1 coefficient lambda m

/-- The interior Abel pairing identity with the actual platform density. -/
theorem one_div_pi_mul_integral_platformAdjointDensity_mul_abelHilbertSeries
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelHilbertSeries (platformRadius a)
              coefficient lambda theta) =
      platformAbelAdjointPairingSeries (platformRadius a)
        sigmaMinus sigmaPlus (platformRho a xMinus)
          (platformRho a xPlus) coefficient lambda := by
  have hrhoMinus := platformRho_mem_Ioo hxMinus ha2
  have hrhoPlus := platformRho_mem_Ioo hxPlus ha2
  have hIntegral :
      (∫ theta in 0..Real.pi,
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformAbelHilbertSeries (platformRadius a)
            coefficient lambda theta) =
        ∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity sigmaMinus sigmaPlus
              (platformRho a xMinus) (platformRho a xPlus) theta *
            platformAbelHilbertSeries (platformRadius a)
              coefficient lambda theta := by
    apply intervalIntegral.integral_congr
    intro theta htheta
    rw [uIcc_of_le Real.pi_pos.le] at htheta
    change platformAngularAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformAbelHilbertSeries (platformRadius a)
            coefficient lambda theta =
      endpointAdjointAngularDensity sigmaMinus sigmaPlus
          (platformRho a xMinus) (platformRho a xPlus) theta *
        platformAbelHilbertSeries (platformRadius a)
          coefficient lambda theta
    rw [endpointAdjointAngularDensity_platformRho_eq
      hxMinus hxPlus ha2 htheta]
  rw [hIntegral]
  exact one_div_pi_mul_integral_endpointAdjointDensity_mul_abelHilbertSeries
    hrhoMinus.1.le hrhoMinus.2 hrhoPlus.1.le hrhoPlus.2 hlambda hbound

theorem summable_platformAbelEvenAdjointPairingTerm
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) :
    Summable (fun m : ℕ ↦
      (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) *
        endpointAdjointEvenCosCoefficient
          r sigmaMinus sigmaPlus rhoMinus rhoPlus m) := by
  exact (summable_one_div_pi_mul_integral_evenIntegrand
    (r := r) (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
      hm0 hm1 hp0 hp1 hlambda hbound).congr fun m ↦
        one_div_pi_mul_integral_endpointAdjointAbelEvenIntegrandTerm
          hm0 hm1 hp0 hp1 coefficient lambda m

theorem summable_platformAbelOddAdjointPairingTerm
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) :
    Summable (fun m : ℕ ↦
      (lambda ^ (2 * m + 1) * coefficient (2 * m + 1)) *
        endpointAdjointOddCosCoefficient
          r sigmaMinus sigmaPlus rhoMinus rhoPlus m) := by
  exact (summable_one_div_pi_mul_integral_oddIntegrand
    (r := r) (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
      hm0 hm1 hp0 hp1 hlambda hbound).congr fun m ↦
        one_div_pi_mul_integral_endpointAdjointAbelOddIntegrandTerm
          hm0 hm1 hp0 hp1 coefficient lambda m

theorem one_div_pi_mul_integral_endpointAdjointDensity_finiteAbelTransform_eq_range_sums
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    (coefficient : ℕ → ℝ) (lambda : ℝ) (N : ℕ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity sigmaMinus sigmaPlus
              rhoMinus rhoPlus theta *
            platformAbelFiniteHilbertTransform
              r coefficient lambda N theta) =
      (∑ m ∈ Finset.range N,
        (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) *
          endpointAdjointEvenCosCoefficient
            r sigmaMinus sigmaPlus rhoMinus rhoPlus m) +
      ∑ m ∈ Finset.range N,
        (lambda ^ (2 * m + 1) * coefficient (2 * m + 1)) *
          endpointAdjointOddCosCoefficient
            r sigmaMinus sigmaPlus rhoMinus rhoPlus m := by
  have hfinite :=
    one_div_pi_mul_integral_endpointAdjointDensity_finiteTransform
      (r := r) (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
        hm0 hm1 hp0 hp1
        (fun m : Fin N ↦ m.1) (fun m : Fin N ↦ m.1)
        (platformAbelEvenCoefficient coefficient lambda)
        (platformAbelOddCoefficient coefficient lambda)
  have heven :
      (∑ m : Fin N,
        platformAbelEvenCoefficient coefficient lambda m *
          endpointAdjointEvenCosCoefficient
            r sigmaMinus sigmaPlus rhoMinus rhoPlus m.1) =
      ∑ m ∈ Finset.range N,
        (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) *
          endpointAdjointEvenCosCoefficient
            r sigmaMinus sigmaPlus rhoMinus rhoPlus m := by
    simpa only [platformAbelEvenCoefficient] using!
      Fin.sum_univ_eq_sum_range
        (fun m : ℕ ↦
          (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) *
            endpointAdjointEvenCosCoefficient
              r sigmaMinus sigmaPlus rhoMinus rhoPlus m) N
  have hodd :
      (∑ m : Fin N,
        platformAbelOddCoefficient coefficient lambda m *
          endpointAdjointOddCosCoefficient
            r sigmaMinus sigmaPlus rhoMinus rhoPlus m.1) =
      ∑ m ∈ Finset.range N,
        (lambda ^ (2 * m + 1) * coefficient (2 * m + 1)) *
          endpointAdjointOddCosCoefficient
            r sigmaMinus sigmaPlus rhoMinus rhoPlus m := by
    simpa only [platformAbelOddCoefficient] using!
      Fin.sum_univ_eq_sum_range
        (fun m : ℕ ↦
          (lambda ^ (2 * m + 1) * coefficient (2 * m + 1)) *
            endpointAdjointOddCosCoefficient
              r sigmaMinus sigmaPlus rhoMinus rhoPlus m) N
  unfold platformAbelFiniteHilbertTransform
  rw [hfinite, heven, hodd]

theorem tendsto_one_div_pi_mul_integral_endpointAdjointDensity_finiteAbelTransform
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) :
    Tendsto
      (fun N ↦ (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity sigmaMinus sigmaPlus
              rhoMinus rhoPlus theta *
            platformAbelFiniteHilbertTransform
              r coefficient lambda N theta))
      atTop
      (nhds (platformAbelAdjointPairingSeries r sigmaMinus sigmaPlus
        rhoMinus rhoPlus coefficient lambda)) := by
  have heven :=
    (summable_platformAbelEvenAdjointPairingTerm
      (r := r) (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
        hm0 hm1 hp0 hp1 hlambda hbound).hasSum.tendsto_sum_nat
  have hodd :=
    (summable_platformAbelOddAdjointPairingTerm
      (r := r) (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
        hm0 hm1 hp0 hp1 hlambda hbound).hasSum.tendsto_sum_nat
  have hsum := heven.add hodd
  unfold platformAbelAdjointPairingSeries
  apply hsum.congr'
  exact Eventually.of_forall fun N ↦
    (one_div_pi_mul_integral_endpointAdjointDensity_finiteAbelTransform_eq_range_sums
      hm0 hm1 hp0 hp1 coefficient lambda N).symm

end

end Erdos1038
