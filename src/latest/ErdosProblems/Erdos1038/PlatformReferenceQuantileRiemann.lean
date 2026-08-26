import ErdosProblems.Erdos1038.PlatformReferenceQuantileContinuity
import ErdosProblems.Erdos1038.UniformLeftRiemann
import ErdosProblems.Erdos1038.NormalizedResidualPlatformCanonicalStrict
import Mathlib.Topology.Order.ProjIcc

/-!
# Canonical platform samples as blockwise uniform left sums

The product refinement divides each atomic target block into equal
reference-mass subcells.  This file identifies those samples exactly with
uniform left-grid evaluations of the continuous platform quantile.  It is
the concrete bridge from `UniformLeftRiemann` to all canonical reference
moments and logarithmic potentials.
-/

set_option warningAsError false

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- Affine parametrization of the probability block belonging to one
target atom. -/
def platformResidualBlockMassParameter
    (C : ResidualConfiguration iota) (i : iota)
    (t : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨orderedResidualLeftMass C i + C.weight i * t,
    by
      constructor
      · exact add_nonneg (orderedResidualLeftMass_mem_Icc C i).1
          (mul_nonneg (C.weight_pos i).le t.property.1)
      · have hmul : C.weight i * (t : ℝ) ≤ C.weight i := by
          simpa only [mul_one] using!
            mul_le_mul_of_nonneg_left t.property.2 (C.weight_pos i).le
        calc
          orderedResidualLeftMass C i + C.weight i * (t : ℝ) ≤
              orderedResidualLeftMass C i + C.weight i :=
            by linarith
          _ = orderedResidualRightMass C i :=
            (orderedResidualRightMass_eq_left_add_weight C i).symm
          _ ≤ 1 := (orderedResidualRightMass_mem_Icc C i).2⟩

theorem continuous_platformResidualBlockMassParameter
    (C : ResidualConfiguration iota) (i : iota) :
    Continuous (platformResidualBlockMassParameter C i) := by
  apply Continuous.subtype_mk
  fun_prop

/-- An arbitrary scalar observable of the platform reference quantile,
restricted to one target block and extended continuously to all real grid
parameters by projection onto `[0,1]`. -/
def platformResidualBlockReferenceIntegrand
    (C : ResidualConfiguration iota) (i : iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  F (platformReferenceQuantile k a hk ha ha2 hthreshold
    (platformResidualBlockMassParameter C i
      (projIcc 0 1 zero_le_one t)))

theorem continuous_platformResidualBlockReferenceIntegrand
    (C : ResidualConfiguration iota) (i : iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc a 2)) :
    Continuous (platformResidualBlockReferenceIntegrand C i
      k a hk ha ha2 hthreshold F) := by
  have hmass : Continuous (fun t : ℝ ↦
      platformResidualBlockMassParameter C i
        (projIcc 0 1 zero_le_one t)) :=
    (continuous_platformResidualBlockMassParameter C i).comp
      continuous_projIcc
  have hquantile : Continuous (fun t : ℝ ↦
      platformReferenceQuantile k a hk ha ha2 hthreshold
        (platformResidualBlockMassParameter C i
          (projIcc 0 1 zero_le_one t))) :=
    (continuous_platformReferenceQuantile k a hk ha ha2 hthreshold).comp hmass
  exact hF.comp_continuous hquantile fun t ↦
    platformReferenceQuantile_mem_Icc
      k a hk ha ha2 hthreshold
      (platformResidualBlockMassParameter C i
        (projIcc 0 1 zero_le_one t))

lemma residualRefinementFraction_eq_uniformLeftGridPoint
    (n : ℕ) (j : Fin (n + 1)) :
    residualRefinementFraction n j =
      uniformLeftGridPoint (n + 1) j := by
  rfl

lemma platformResidualRefinementMass_eq_blockParameter
    (C : ResidualConfiguration iota) (n : ℕ)
    (p : iota × Fin (n + 1)) :
    platformResidualRefinementMass C n p =
      platformResidualBlockMassParameter C p.1
        ⟨residualRefinementFraction n p.2,
          (residualRefinementFraction_mem_Ico n p.2).1,
          (residualRefinementFraction_mem_Ico n p.2).2.le⟩ := by
  rfl

lemma platformResidualRefinementReference_eq_quantile
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ)
    (p : iota × Fin (n + 1)) :
    platformResidualRefinementReference C k a
        hk ha ha2 hthreshold n p =
      platformReferenceQuantile k a hk ha ha2 hthreshold
        (platformResidualBlockMassParameter C p.1
          ⟨residualRefinementFraction n p.2,
            (residualRefinementFraction_mem_Ico n p.2).1,
            (residualRefinementFraction_mem_Ico n p.2).2.le⟩) := by
  rfl

lemma platformResidualBlockReferenceIntegrand_uniformLeftGridPoint
    (C : ResidualConfiguration iota) (i : iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : ℝ → ℝ) (n : ℕ) (j : Fin (n + 1)) :
    platformResidualBlockReferenceIntegrand C i
        k a hk ha ha2 hthreshold F
        (uniformLeftGridPoint (n + 1) j) =
      F (platformResidualRefinementReference C k a
        hk ha ha2 hthreshold n (i, j)) := by
  unfold platformResidualBlockReferenceIntegrand
  rw [projIcc_of_mem]
  · have hgrid := uniformLeftGridPoint_mem_Icc
      (Nat.succ_pos n) j.isLt.le
    have hsub :
        (⟨uniformLeftGridPoint (n + 1) j, hgrid⟩ : Icc (0 : ℝ) 1) =
          ⟨residualRefinementFraction n j,
            (residualRefinementFraction_mem_Ico n j).1,
            (residualRefinementFraction_mem_Ico n j).2.le⟩ := by
      apply Subtype.ext
      exact (residualRefinementFraction_eq_uniformLeftGridPoint n j).symm
    rw [hsub]
    exact congrArg F
      (platformResidualRefinementReference_eq_quantile
        C k a hk ha ha2 hthreshold n (i, j)).symm
  · exact uniformLeftGridPoint_mem_Icc (Nat.succ_pos n) j.isLt.le

/-- The average of an observable over one refined target block is exactly
the uniform left Riemann sum of its continuous block pullback. -/
theorem uniformLeftRiemannSum_platformResidualBlockReferenceIntegrand
    (C : ResidualConfiguration iota) (i : iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : ℝ → ℝ) (n : ℕ) :
    uniformLeftRiemannSum
        (platformResidualBlockReferenceIntegrand C i
          k a hk ha ha2 hthreshold F) (n + 1) =
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ j : Fin (n + 1),
          F (platformResidualRefinementReference C k a
            hk ha ha2 hthreshold n (i, j)) := by
  unfold uniformLeftRiemannSum
  congr 1
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < n + 1 := Finset.mem_range.mp hj
  rw [dif_pos hjlt]
  simpa only using!
    platformResidualBlockReferenceIntegrand_uniformLeftGridPoint
      C i k a hk ha ha2 hthreshold F n ⟨j, hjlt⟩

/-- The actual average on one canonical target block converges to the
integral of the observable pulled back along the continuous reference
quantile. -/
theorem tendsto_platformResidualBlockReferenceAverage
    (C : ResidualConfiguration iota) (i : iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc a 2)) :
    Tendsto
      (fun n ↦ (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ j : Fin (n + 1),
          F (platformResidualRefinementReference C k a
            hk ha ha2 hthreshold n (i, j)))
      atTop
      (nhds (∫ t in (0 : ℝ)..1,
        platformResidualBlockReferenceIntegrand C i
          k a hk ha ha2 hthreshold F t)) := by
  have hcont := continuous_platformResidualBlockReferenceIntegrand
    C i k a hk ha ha2 hthreshold F hF
  have hriemann := tendsto_uniformLeftRiemannSum
    (platformResidualBlockReferenceIntegrand C i
      k a hk ha ha2 hthreshold F) hcont.continuousOn
  apply hriemann.congr'
  filter_upwards with n
  exact uniformLeftRiemannSum_platformResidualBlockReferenceIntegrand
    C i k a hk ha ha2 hthreshold F n

/-- Canonical weighted sums of a block-dependent continuous observable
converge to the corresponding finite sum of block integrals. -/
theorem tendsto_sum_platformResidualRefinementAlpha_mul_blockObservable
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : iota → ℝ → ℝ) (hF : ∀ i, ContinuousOn (F i) (Icc a 2)) :
    Tendsto
      (fun n ↦ ∑ p,
        platformResidualRefinementAlpha C k n p *
          F p.1 (platformResidualRefinementReference C k a
            hk ha ha2 hthreshold n p))
      atTop
      (nhds (∑ i, residualLagrangeAlpha C k i *
        (∫ t in (0 : ℝ)..1,
          platformResidualBlockReferenceIntegrand C i
            k a hk ha ha2 hthreshold (F i) t))) := by
  have hsum : Tendsto
      (fun n ↦ ∑ i, residualLagrangeAlpha C k i *
        ((1 / ((n + 1 : ℕ) : ℝ)) *
          ∑ j : Fin (n + 1),
            F i (platformResidualRefinementReference C k a
              hk ha ha2 hthreshold n (i, j))))
      atTop
      (nhds (∑ i, residualLagrangeAlpha C k i *
        (∫ t in (0 : ℝ)..1,
          platformResidualBlockReferenceIntegrand C i
            k a hk ha ha2 hthreshold (F i) t))) := by
    apply tendsto_finsetSum Finset.univ
    intro i _hi
    exact (tendsto_platformResidualBlockReferenceAverage
      C i k a hk ha ha2 hthreshold (F i) (hF i)).const_mul
        (residualLagrangeAlpha C k i)
  apply hsum.congr'
  filter_upwards with n
  symm
  exact sum_platformResidualRefinementAlpha_mul C k n
    (fun p ↦ F p.1 (platformResidualRefinementReference C k a
      hk ha ha2 hthreshold n p))

/-- Block-independent specialization. -/
theorem tendsto_sum_platformResidualRefinementAlpha_mul_observable
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc a 2)) :
    Tendsto
      (fun n ↦ ∑ p,
        platformResidualRefinementAlpha C k n p *
          F (platformResidualRefinementReference C k a
            hk ha ha2 hthreshold n p))
      atTop
      (nhds (∑ i, residualLagrangeAlpha C k i *
        (∫ t in (0 : ℝ)..1,
          platformResidualBlockReferenceIntegrand C i
            k a hk ha ha2 hthreshold F t))) := by
  simpa only using!
    tendsto_sum_platformResidualRefinementAlpha_mul_blockObservable
      C k a hk ha ha2 hthreshold (fun _i ↦ F) (fun _i ↦ hF)

end

end Erdos1038
