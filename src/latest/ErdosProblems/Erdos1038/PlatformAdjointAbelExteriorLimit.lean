import ErdosProblems.Erdos1038.PlatformAdjointAbelBoundary
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Automatic exterior Abel boundary limit

The two crossing radii lie strictly inside the unit disk.  Consequently
the exterior variation has an absolutely convergent coefficient formula
even at the Abel boundary.  This file makes that boundary value explicit
and proves that every interior Abel approach converges to it for an
arbitrary bounded coefficient sequence.
-/

set_option warningAsError false

open Filter
open scoped Topology

namespace Erdos1038

noncomputable section

/-- Absolutely convergent coefficient form of the exterior variation. -/
def platformAbelExteriorSeriesValue
    (a xMinus xPlus sigmaMinus sigmaPlus f0 : ℝ)
    (coefficient : ℕ → ℝ) (lambda : ℝ) : ℝ :=
  -endpointAdjointGamma (platformRadius a)
      sigmaMinus sigmaPlus (platformRho a xMinus) (platformRho a xPlus) * f0 +
    ∑' m : ℕ,
      (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) *
        endpointExteriorCosCoefficient (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) (2 * (m + 1)) +
    ∑' m : ℕ,
      (lambda ^ (2 * m + 1) * coefficient (2 * m + 1)) *
        endpointExteriorCosCoefficient (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) (2 * m + 1)

/-- The unregularized exterior coefficient value at `lambda = 1`. -/
def platformBoundaryExteriorVariation
    (a xMinus xPlus sigmaMinus sigmaPlus f0 : ℝ)
    (coefficient : ℕ → ℝ) : ℝ :=
  platformAbelExteriorSeriesValue a xMinus xPlus
    sigmaMinus sigmaPlus f0 coefficient 1

private lemma abs_mul_platformRho_lt_one
    {a x lambda : ℝ} (hx : x < a) (ha2 : a < 2)
    (hlambda : |lambda| ≤ 1) :
    |lambda * platformRho a x| < 1 := by
  have hrho := platformRho_mem_Ioo hx ha2
  rw [abs_mul, abs_of_nonneg hrho.1.le]
  calc
    |lambda| * platformRho a x ≤ 1 * platformRho a x :=
      mul_le_mul_of_nonneg_right hlambda hrho.1.le
    _ < 1 := by simpa using! hrho.2

lemma summable_platformAbelExteriorEvenTerm
    {a xMinus xPlus sigmaMinus sigmaPlus lambda : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    (hlambda : |lambda| ≤ 1) :
    Summable (fun m : ℕ ↦
      (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) *
        endpointExteriorCosCoefficient (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) (2 * (m + 1))) := by
  have hm := (summable_platformAbelEvenCoefficient
    (abs_mul_platformRho_lt_one hxMinus ha2 hlambda) hbound).mul_left
      (-2 * (sigmaMinus / platformCrossingScale a xMinus))
  have hp := (summable_platformAbelEvenCoefficient
    (abs_mul_platformRho_lt_one hxPlus ha2 hlambda) hbound).mul_left
      (-2 * (sigmaPlus / platformCrossingScale a xPlus))
  apply (hm.add hp).congr
  intro m
  rw [endpointExteriorCosCoefficient_eq_crossingScales
    hxMinus hxPlus ha2]
  simp only [mul_pow]
  ring

lemma summable_platformAbelExteriorOddTerm
    {a xMinus xPlus sigmaMinus sigmaPlus lambda : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    (hlambda : |lambda| ≤ 1) :
    Summable (fun m : ℕ ↦
      (lambda ^ (2 * m + 1) * coefficient (2 * m + 1)) *
        endpointExteriorCosCoefficient (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) (2 * m + 1)) := by
  have hm := (summable_platformAbelOddCoefficient
    (abs_mul_platformRho_lt_one hxMinus ha2 hlambda) hbound).mul_left
      (-2 * (sigmaMinus / platformCrossingScale a xMinus))
  have hp := (summable_platformAbelOddCoefficient
    (abs_mul_platformRho_lt_one hxPlus ha2 hlambda) hbound).mul_left
      (-2 * (sigmaPlus / platformCrossingScale a xPlus))
  apply (hm.add hp).congr
  intro m
  rw [endpointExteriorCosCoefficient_eq_crossingScales
    hxMinus hxPlus ha2]
  simp only [mul_pow]
  ring

theorem platformAbelExteriorVariation_eq_seriesValue
    {a xMinus xPlus sigmaMinus sigmaPlus lambda : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) (f0 : ℝ) :
    platformAbelExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 coefficient lambda =
      platformAbelExteriorSeriesValue a xMinus xPlus
        sigmaMinus sigmaPlus f0 coefficient lambda := by
  have hactual := tendsto_platformAbelFiniteExteriorVariation
    (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
    hxMinus hxPlus ha2 hlambda hbound f0
  have heven := (summable_platformAbelExteriorEvenTerm
    (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
    hxMinus hxPlus ha2 hbound hlambda.le).hasSum.tendsto_sum_nat
  have hodd := (summable_platformAbelExteriorOddTerm
    (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
    hxMinus hxPlus ha2 hbound hlambda.le).hasSum.tendsto_sum_nat
  have hconst : Tendsto (fun _N : ℕ ↦
      -endpointAdjointGamma (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) * f0) atTop
      (nhds (-endpointAdjointGamma (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) * f0)) := tendsto_const_nhds
  have hseries := (hconst.add heven).add hodd
  apply tendsto_nhds_unique hactual
  apply hseries.congr'
  filter_upwards with N
  symm
  rw [platformAbelFiniteExteriorVariation]
  rw [finitePlatformExteriorVariation_eq_finiteEndpointExteriorVariation
    hxMinus hxPlus ha2]
  unfold finiteEndpointExteriorVariation
  simp only [platformAbelEvenCoefficient, platformAbelOddCoefficient]
  have hevenFin :
      (∑ i : Fin N,
        lambda ^ (2 * (i.1 + 1)) * coefficient (2 * (i.1 + 1)) *
          endpointExteriorCosCoefficient (platformRadius a)
            sigmaMinus sigmaPlus (platformRho a xMinus)
              (platformRho a xPlus) (2 * (i.1 + 1))) =
        ∑ i ∈ Finset.range N,
          lambda ^ (2 * (i + 1)) * coefficient (2 * (i + 1)) *
            endpointExteriorCosCoefficient (platformRadius a)
              sigmaMinus sigmaPlus (platformRho a xMinus)
                (platformRho a xPlus) (2 * (i + 1)) :=
    Fin.sum_univ_eq_sum_range
      (fun i : ℕ ↦
        lambda ^ (2 * (i + 1)) * coefficient (2 * (i + 1)) *
          endpointExteriorCosCoefficient (platformRadius a)
            sigmaMinus sigmaPlus (platformRho a xMinus)
              (platformRho a xPlus) (2 * (i + 1))) N
  have hoddFin :
      (∑ i : Fin N,
        lambda ^ (2 * i.1 + 1) * coefficient (2 * i.1 + 1) *
          endpointExteriorCosCoefficient (platformRadius a)
            sigmaMinus sigmaPlus (platformRho a xMinus)
              (platformRho a xPlus) (2 * i.1 + 1)) =
        ∑ i ∈ Finset.range N,
          lambda ^ (2 * i + 1) * coefficient (2 * i + 1) *
            endpointExteriorCosCoefficient (platformRadius a)
              sigmaMinus sigmaPlus (platformRho a xMinus)
                (platformRho a xPlus) (2 * i + 1) :=
    Fin.sum_univ_eq_sum_range
      (fun i : ℕ ↦
        lambda ^ (2 * i + 1) * coefficient (2 * i + 1) *
          endpointExteriorCosCoefficient (platformRadius a)
            sigmaMinus sigmaPlus (platformRho a xMinus)
              (platformRho a xPlus) (2 * i + 1)) N
  rw [hevenFin, hoddFin]

private lemma tendsto_platformAbelExteriorEvenSeries
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    {lambda : ℕ → ℝ} (hlambda : InteriorAbelApproach lambda) :
    Tendsto (fun n ↦ ∑' m : ℕ,
      (lambda n ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) *
        endpointExteriorCosCoefficient (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) (2 * (m + 1)))
      atTop (nhds (∑' m : ℕ,
        coefficient (2 * (m + 1)) *
          endpointExteriorCosCoefficient (platformRadius a)
            sigmaMinus sigmaPlus (platformRho a xMinus)
              (platformRho a xPlus) (2 * (m + 1)))) := by
  let boundaryTerm : ℕ → ℝ := fun m ↦
    coefficient (2 * (m + 1)) *
      endpointExteriorCosCoefficient (platformRadius a)
        sigmaMinus sigmaPlus (platformRho a xMinus)
          (platformRho a xPlus) (2 * (m + 1))
  have hsum : Summable (fun m ↦ ‖boundaryTerm m‖) :=
    by simpa only [boundaryTerm, one_pow, one_mul] using!
      (summable_platformAbelExteriorEvenTerm
      (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
      hxMinus hxPlus ha2 hbound (by norm_num : |(1 : ℝ)| ≤ 1)).norm
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro m
    have hpow := (hlambda.2.pow (2 * (m + 1)))
    have ht := hpow.mul_const (coefficient (2 * (m + 1)) *
        endpointExteriorCosCoefficient (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) (2 * (m + 1)))
    rw [show (fun n ↦
        lambda n ^ (2 * (m + 1)) * coefficient (2 * (m + 1)) *
          endpointExteriorCosCoefficient (platformRadius a)
            sigmaMinus sigmaPlus (platformRho a xMinus)
              (platformRho a xPlus) (2 * (m + 1))) =
        (fun n ↦ lambda n ^ (2 * (m + 1)) *
          (coefficient (2 * (m + 1)) *
            endpointExteriorCosCoefficient (platformRadius a)
              sigmaMinus sigmaPlus (platformRho a xMinus)
                (platformRho a xPlus) (2 * (m + 1)))) by
      funext n
      ring]
    simpa only [one_pow, one_mul] using! ht
  · exact Eventually.of_forall fun n m ↦ by
      rw [mul_assoc, norm_mul]
      have hpow : ‖lambda n ^ (2 * (m + 1))‖ ≤ 1 := by
        rw [norm_pow, Real.norm_eq_abs]
        exact pow_le_one₀ (abs_nonneg _) (hlambda.1 n).le
      rw [show ‖coefficient (2 * (m + 1)) *
          endpointExteriorCosCoefficient (platformRadius a)
            sigmaMinus sigmaPlus (platformRho a xMinus)
              (platformRho a xPlus) (2 * (m + 1))‖ =
        ‖boundaryTerm m‖ by rfl]
      exact mul_le_of_le_one_left (norm_nonneg _) hpow

private lemma tendsto_platformAbelExteriorOddSeries
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    {lambda : ℕ → ℝ} (hlambda : InteriorAbelApproach lambda) :
    Tendsto (fun n ↦ ∑' m : ℕ,
      (lambda n ^ (2 * m + 1) * coefficient (2 * m + 1)) *
        endpointExteriorCosCoefficient (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) (2 * m + 1))
      atTop (nhds (∑' m : ℕ,
        coefficient (2 * m + 1) *
          endpointExteriorCosCoefficient (platformRadius a)
            sigmaMinus sigmaPlus (platformRho a xMinus)
              (platformRho a xPlus) (2 * m + 1))) := by
  let boundaryTerm : ℕ → ℝ := fun m ↦
    coefficient (2 * m + 1) *
      endpointExteriorCosCoefficient (platformRadius a)
        sigmaMinus sigmaPlus (platformRho a xMinus)
          (platformRho a xPlus) (2 * m + 1)
  have hsum : Summable (fun m ↦ ‖boundaryTerm m‖) :=
    by simpa only [boundaryTerm, one_pow, one_mul] using!
      (summable_platformAbelExteriorOddTerm
      (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
      hxMinus hxPlus ha2 hbound (by norm_num : |(1 : ℝ)| ≤ 1)).norm
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro m
    have hpow := hlambda.2.pow (2 * m + 1)
    have ht := hpow.mul_const (coefficient (2 * m + 1) *
        endpointExteriorCosCoefficient (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) (2 * m + 1))
    rw [show (fun n ↦
        lambda n ^ (2 * m + 1) * coefficient (2 * m + 1) *
          endpointExteriorCosCoefficient (platformRadius a)
            sigmaMinus sigmaPlus (platformRho a xMinus)
              (platformRho a xPlus) (2 * m + 1)) =
        (fun n ↦ lambda n ^ (2 * m + 1) *
          (coefficient (2 * m + 1) *
            endpointExteriorCosCoefficient (platformRadius a)
              sigmaMinus sigmaPlus (platformRho a xMinus)
                (platformRho a xPlus) (2 * m + 1))) by
      funext n
      ring]
    simpa only [one_pow, one_mul] using! ht
  · exact Eventually.of_forall fun n m ↦ by
      rw [mul_assoc, norm_mul]
      have hpow : ‖lambda n ^ (2 * m + 1)‖ ≤ 1 := by
        rw [norm_pow, Real.norm_eq_abs]
        exact pow_le_one₀ (abs_nonneg _) (hlambda.1 n).le
      rw [show ‖coefficient (2 * m + 1) *
          endpointExteriorCosCoefficient (platformRadius a)
            sigmaMinus sigmaPlus (platformRho a xMinus)
              (platformRho a xPlus) (2 * m + 1)‖ =
        ‖boundaryTerm m‖ by rfl]
      exact mul_le_of_le_one_left (norm_nonneg _) hpow

/-- Exterior convergence is automatic for every bounded coefficient
sequence; no regularity of the underlying material velocity is needed. -/
theorem tendsto_platformAbelExteriorVariation_boundary
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C) (f0 : ℝ)
    {lambda : ℕ → ℝ} (hlambda : InteriorAbelApproach lambda) :
    Tendsto
      (fun n ↦ platformAbelExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 coefficient (lambda n))
      atTop (nhds (platformBoundaryExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 coefficient)) := by
  have heven := tendsto_platformAbelExteriorEvenSeries
    (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
    hxMinus hxPlus ha2 hbound hlambda
  have hodd := tendsto_platformAbelExteriorOddSeries
    (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
    hxMinus hxPlus ha2 hbound hlambda
  have hconst : Tendsto (fun _n : ℕ ↦
      -endpointAdjointGamma (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) * f0) atTop
      (nhds (-endpointAdjointGamma (platformRadius a)
          sigmaMinus sigmaPlus (platformRho a xMinus)
            (platformRho a xPlus) * f0)) := tendsto_const_nhds
  have hseries := (hconst.add heven).add hodd
  simp only [platformBoundaryExteriorVariation,
    platformAbelExteriorSeriesValue, one_pow, one_mul]
  apply hseries.congr'
  filter_upwards with n
  rw [platformAbelExteriorVariation_eq_seriesValue
    hxMinus hxPlus ha2 (hlambda.1 n) hbound f0]
  rfl

end

end Erdos1038
