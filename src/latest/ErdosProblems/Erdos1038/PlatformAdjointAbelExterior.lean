import ErdosProblems.Erdos1038.PlatformAdjointAbelPairing

/-!
# Passage of the platform exterior variation to the interior Abel series

The paired finite cosine polynomials converge under each nonsingular
crossing integral.  A compact-uniform majorant supplied by the absolutely
summable cosine terms gives the result directly by dominated convergence.
-/

set_option warningAsError false

open Filter MeasureTheory Set
open scoped BigOperators Topology Interval

namespace Erdos1038

noncomputable section

lemma platformAngularDistance_ge_all
    {a : ℝ} (ha2 : a ≤ 2) (theta : ℝ) :
    a ≤ platformAngularDistance a theta := by
  have hr : 0 ≤ platformRadius a := by
    unfold platformRadius
    linarith
  have hcos := Real.cos_le_one theta
  unfold platformAngularDistance platformCenter platformRadius
  nlinarith

lemma platformAngularDistance_sub_pos_all
    {a x : ℝ} (hx : x < a) (ha2 : a ≤ 2) (theta : ℝ) :
    0 < platformAngularDistance a theta - x :=
  sub_pos.mpr (hx.trans_le (platformAngularDistance_ge_all ha2 theta))

/-- The actual two-crossing exterior variation of the infinite interior
Abel cosine series. -/
def platformAbelExteriorVariation
    (a xMinus xPlus sigmaMinus sigmaPlus f0 : ℝ)
    (coefficient : ℕ → ℝ) (lambda : ℝ) : ℝ :=
  -sigmaMinus * (1 / Real.pi) *
      (∫ theta in 0..Real.pi,
        platformAbelCosineSeries f0 coefficient lambda theta /
          (platformAngularDistance a theta - xMinus)) -
    sigmaPlus * (1 / Real.pi) *
      (∫ theta in 0..Real.pi,
        platformAbelCosineSeries f0 coefficient lambda theta /
          (platformAngularDistance a theta - xPlus))

private def abelExteriorIntervalCompact : TopologicalSpace.Compacts ℝ :=
  ⟨uIcc (0 : ℝ) Real.pi, isCompact_uIcc⟩

private lemma continuous_platformAbelFiniteCosinePolynomial
    (f0 : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (N : ℕ) :
    Continuous (platformAbelFiniteCosinePolynomial
      f0 coefficient lambda N) := by
  unfold platformAbelFiniteCosinePolynomial
    finiteEndpointCosinePolynomial platformAbelEvenCoefficient
    platformAbelOddCoefficient
  fun_prop

private lemma continuous_platformAbelFiniteCosinePolynomial_div_distance
    {a x : ℝ} (hx : x < a) (ha2 : a ≤ 2)
    (f0 : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (N : ℕ) :
    Continuous (fun theta : ℝ ↦
      platformAbelFiniteCosinePolynomial f0 coefficient lambda N theta /
        (platformAngularDistance a theta - x)) := by
  apply Continuous.div
  · exact continuous_platformAbelFiniteCosinePolynomial
      f0 coefficient lambda N
  · unfold platformAngularDistance
    fun_prop
  · intro theta
    exact (platformAngularDistance_sub_pos_all hx ha2 theta).ne'

/-- Each nonsingular crossing integral commutes with the paired interior
Abel limit. -/
theorem tendsto_integral_platformAbelFiniteCosinePolynomial_div_distance
    {a x : ℝ} (hx : x < a) (ha2 : a ≤ 2)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C)
    (f0 : ℝ) :
    Tendsto
      (fun N ↦ ∫ theta in 0..Real.pi,
        platformAbelFiniteCosinePolynomial f0 coefficient lambda N theta /
          (platformAngularDistance a theta - x))
      atTop
      (nhds (∫ theta in 0..Real.pi,
        platformAbelCosineSeries f0 coefficient lambda theta /
          (platformAngularDistance a theta - x))) := by
  let evenNorm : ℕ → ℝ := fun m ↦
    ‖(platformAbelEvenCosineContinuousTerm
      coefficient lambda m).restrict abelExteriorIntervalCompact‖
  let oddNorm : ℕ → ℝ := fun m ↦
    ‖(platformAbelOddCosineContinuousTerm
      coefficient lambda m).restrict abelExteriorIntervalCompact‖
  have heven : Summable evenNorm := by
    simpa only [evenNorm] using!
      summable_platformAbelEvenCosineContinuousTerm_restrict_norm
        hlambda hbound abelExteriorIntervalCompact
  have hodd : Summable oddNorm := by
    simpa only [oddNorm] using!
      summable_platformAbelOddCosineContinuousTerm_restrict_norm
        hlambda hbound abelExteriorIntervalCompact
  let B : ℝ := |f0| + (∑' m : ℕ, evenNorm m) + ∑' m : ℕ, oddNorm m
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hax : 0 < a - x := sub_pos.mpr hx
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := Real.pi)
    (F := fun N theta ↦
      platformAbelFiniteCosinePolynomial f0 coefficient lambda N theta /
        (platformAngularDistance a theta - x))
    (f := fun theta ↦
      platformAbelCosineSeries f0 coefficient lambda theta /
        (platformAngularDistance a theta - x))
    (fun _theta ↦ B / (a - x))
  · exact Eventually.of_forall fun N ↦
      (continuous_platformAbelFiniteCosinePolynomial_div_distance
        hx ha2 f0 coefficient lambda N).aestronglyMeasurable
  · exact Eventually.of_forall fun N ↦
      ae_of_all _ fun theta htheta ↦ by
        rw [uIoc_of_le Real.pi_pos.le] at htheta
        have hthetaIcc : theta ∈ Icc (0 : ℝ) Real.pi :=
          ⟨htheta.1.le, htheta.2⟩
        have hthetaCompact : theta ∈
            (abelExteriorIntervalCompact : Set ℝ) := by
          change theta ∈ uIcc (0 : ℝ) Real.pi
          rw [uIcc_of_le Real.pi_pos.le]
          exact hthetaIcc
        have hden : 0 < platformAngularDistance a theta - x :=
          platformAngularDistance_sub_pos_all hx ha2 theta
        have hdenLower : a - x ≤ platformAngularDistance a theta - x := by
          linarith [platformAngularDistance_ge_all ha2 theta]
        have heval (m : ℕ) :
            |platformAbelEvenCosineTerm
                coefficient lambda m theta| ≤ evenNorm m := by
          simpa only [evenNorm, abelExteriorIntervalCompact,
            platformAbelEvenCosineContinuousTerm,
            ContinuousMap.restrict_apply, Real.norm_eq_abs] using!
            ((platformAbelEvenCosineContinuousTerm
              coefficient lambda m).restrict
                abelExteriorIntervalCompact).norm_coe_le_norm
                  ⟨theta, hthetaCompact⟩
        have hoval (m : ℕ) :
            |platformAbelOddCosineTerm
                coefficient lambda m theta| ≤ oddNorm m := by
          simpa only [oddNorm, abelExteriorIntervalCompact,
            platformAbelOddCosineContinuousTerm,
            ContinuousMap.restrict_apply, Real.norm_eq_abs] using!
            ((platformAbelOddCosineContinuousTerm
              coefficient lambda m).restrict
                abelExteriorIntervalCompact).norm_coe_le_norm
                  ⟨theta, hthetaCompact⟩
        have hevenPartial :
            (∑ m ∈ Finset.range N,
              |platformAbelEvenCosineTerm
                coefficient lambda m theta|) ≤
              ∑' m : ℕ, evenNorm m := by
          calc
            (∑ m ∈ Finset.range N,
                |platformAbelEvenCosineTerm
                  coefficient lambda m theta|) ≤
                ∑ m ∈ Finset.range N, evenNorm m := by
              gcongr with m hm
              exact heval m
            _ ≤ ∑' m : ℕ, evenNorm m :=
              heven.sum_le_tsum (Finset.range N)
                (fun _m _hm ↦ norm_nonneg _)
        have hoddPartial :
            (∑ m ∈ Finset.range N,
              |platformAbelOddCosineTerm
                coefficient lambda m theta|) ≤
              ∑' m : ℕ, oddNorm m := by
          calc
            (∑ m ∈ Finset.range N,
                |platformAbelOddCosineTerm
                  coefficient lambda m theta|) ≤
                ∑ m ∈ Finset.range N, oddNorm m := by
              gcongr with m hm
              exact hoval m
            _ ≤ ∑' m : ℕ, oddNorm m :=
              hodd.sum_le_tsum (Finset.range N)
                (fun _m _hm ↦ norm_nonneg _)
        have hpoly :
            |platformAbelFiniteCosinePolynomial
                f0 coefficient lambda N theta| ≤ B := by
          rw [platformAbelFiniteCosinePolynomial_eq_range_sums]
          calc
            |f0 +
                (∑ m ∈ Finset.range N,
                  platformAbelEvenCosineTerm
                    coefficient lambda m theta) +
                ∑ m ∈ Finset.range N,
                  platformAbelOddCosineTerm
                    coefficient lambda m theta| ≤
              (|f0| +
                |∑ m ∈ Finset.range N,
                  platformAbelEvenCosineTerm
                    coefficient lambda m theta|) +
                |∑ m ∈ Finset.range N,
                  platformAbelOddCosineTerm
                    coefficient lambda m theta| := by
              exact (abs_add_le _ _).trans
                (add_le_add (abs_add_le _ _) le_rfl)
            _ ≤ |f0| +
                (∑ m ∈ Finset.range N,
                  |platformAbelEvenCosineTerm
                    coefficient lambda m theta|) +
                ∑ m ∈ Finset.range N,
                  |platformAbelOddCosineTerm
                    coefficient lambda m theta| := by
              gcongr
              · exact Finset.abs_sum_le_sum_abs _ _
              · exact Finset.abs_sum_le_sum_abs _ _
            _ ≤ B := by
              dsimp [B]
              linarith
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
        exact div_le_div₀ hB hpoly hax hdenLower
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun theta _htheta ↦ by
      simpa only [div_eq_mul_inv] using!
        (tendsto_platformAbelFiniteCosinePolynomial
          hlambda hbound f0 theta).mul_const
            (platformAngularDistance a theta - x)⁻¹

/-- The finite two-crossing exterior variations converge to the actual
interior Abel exterior variation. -/
theorem tendsto_platformAbelFiniteExteriorVariation
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C)
    (f0 : ℝ) :
    Tendsto
      (fun N ↦ platformAbelFiniteExteriorVariation
        a xMinus xPlus sigmaMinus sigmaPlus
          f0 coefficient lambda N)
      atTop
      (nhds (platformAbelExteriorVariation
        a xMinus xPlus sigmaMinus sigmaPlus
          f0 coefficient lambda)) := by
  have hminus :=
    tendsto_integral_platformAbelFiniteCosinePolynomial_div_distance
      hxMinus ha2.le hlambda hbound f0
  have hplus :=
    tendsto_integral_platformAbelFiniteCosinePolynomial_div_distance
      hxPlus ha2.le hlambda hbound f0
  have hscaledMinus := hminus.const_mul
    (-sigmaMinus * (1 / Real.pi))
  have hscaledPlus := hplus.const_mul
    (sigmaPlus * (1 / Real.pi))
  have hsub := hscaledMinus.sub hscaledPlus
  simpa only [platformAbelFiniteExteriorVariation,
    finitePlatformExteriorVariation,
    platformAbelExteriorVariation] using! hsub

end

end Erdos1038
