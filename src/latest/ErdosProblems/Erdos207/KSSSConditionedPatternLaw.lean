/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPatternStoppedLaw
import ErdosProblems.Erdos207.KSSSInitialGraphLaw
import ErdosProblems.Erdos207.GraphDistributionConditioning

/-! # One conditioned law carrying all initial bands and the working-graph product bound -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem ksssPatternFailureCoefficient_ge_one
    (q N levels patterns inner : ℕ) (hN : 1 ≤ N) :
    1 ≤ ksssPatternFailureCoefficient q N levels patterns inner := by
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast (one_le_pow₀ hN : 1 ≤ N ^ 2)
  have hrest : 0 ≤ 2 * (levels : ℝ) * N + 2 * (levels : ℝ) * patterns +
      4 * (q + 1 : ℝ) ^ 2 * (N + 1 : ℝ) ^ 6 + (inner : ℝ) * (N : ℝ) ^ 5 := by positivity
  have hextra : 0 ≤ (q + 1 : ℝ) ^ 2 * (N : ℝ) ^ 3 := by positivity
  dsimp only [ksssPatternFailureCoefficient]
  nlinarith only [hN2, hrest, hextra]

theorem KSSSPatternStoppedLawData.exists_conditioned_graph_law
    {I J V : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (H : SimpleGraph V) (S₀ : GreedyStateOn V) (sets : I → Finset V)
    (patterns : J → SimpleGraph V) (i₀ : I)
    (D : KSSSPatternStoppedLawData F (initialResidualPairs H) q n b B k t a E A S₀ sets patterns i₀)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hambient : ∀ T ∈ S₀.available,
      tripleEdgeFinset T ⊆ graphEdges (graphDifference (SimpleGraph.completeGraph V) H))
    (hratio : (Fintype.card V : ℝ) / 6 ≤ A / E)
    (hEupper : E ≤ (Fintype.card V : ℝ) ^ 2) (hEquadratic : (Fintype.card V : ℝ) ^ 2 ≤ 16 * E)
    (hsmall : ksssPatternFailureCoefficient q (Fintype.card V) (Fintype.card I) (Fintype.card J)
      (Fintype.card {i : I // i ≠ i₀}) * (1 / 2 : ℝ) ^ t < 1 / 2) :
    ∃ law : FiniteLaw (GreedyStateOn V),
      law.SupportedOn (fun S ↦ GreedyInvariant F S ∧ GreedyContainedIn S₀.available S ∧ S.chosen.card = n ∧
        KSSSOnTrajectories F S q (ksssResidualPairs (initialResidualPairs H) S) a E A
          ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B n ∧
        CrudeStateBounds F S q (dyadicCrudeThresholds V t k) ∧
        AllUncoveredNeighborBands sets (initialResidualPairs H) E t (ksssPowerErrorExponent b B) B n S ∧
        AllProperPatternBands sets patterns q a E t (ksssPowerErrorExponent b B) B n S) ∧
      IsInitialGraphProductBound law (fun S ↦ S.chosen)
        (graphDifference (SimpleGraph.completeGraph V) H) (Real.toNNReal (ksssEdgeDensity E n))
        (2 * ksssInitialGraphProductConstant q coeff)
        (Real.toNNReal (ksssPatternFailureCoefficient q (Fintype.card V) (Fintype.card I) (Fintype.card J)
          (Fintype.card {i : I // i ≠ i₀})) * (1 / 2 : ℝ≥0) ^ t) := by
  let raw := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) D.active S₀
  let Good := fun w : FiniteLaw.TimedState (GreedyStateOn V) n ↦ D.active w.1.1 w.2
  let c := ksssPatternFailureCoefficient q (Fintype.card V) (Fintype.card I) (Fintype.card J)
    (Fintype.card {i : I // i ≠ i₀})
  let error := Real.toNNReal c * (1 / 2 : ℝ≥0) ^ t
  have hc : 1 ≤ c := ksssPatternFailureCoefficient_ge_one _ _ _ _ _ P.ambient_pos
  have hc0 : 0 ≤ c := by linarith only [hc]
  have herrorEq : (error : ℝ) = c * (1 / 2 : ℝ) ^ t := by
    simp only [error, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat, Real.coe_toNNReal _ hc0]
  have herrSmall : error < 1 / 2 := by
    rw [← NNReal.coe_lt_coe]
    simpa only [herrorEq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hsmall
  have hfailure : raw.probability (fun w ↦ ¬ Good w) ≤ error := by
    rw [← NNReal.coe_le_coe, herrorEq]
    exact D.failure
  have hhalf : 1 / 2 ≤ raw.probability Good := by
    have h := hfailure
    rw [raw.probability_not] at h
    calc
      (1 / 2 : ℝ≥0) = 1 - (1 / 2 : ℝ≥0) := eq_tsub_of_add_eq (by norm_num)
      _ ≤ 1 - error := tsub_le_tsub_left herrSmall.le _
      _ ≤ _ := tsub_le_iff_tsub_le.mp h
  have hGood : 0 < raw.probability Good := (by norm_num : (0 : ℝ≥0) < 1 / 2).trans_le hhalf
  have herrLower : (1 / 2 : ℝ≥0) ^ t ≤ error := by
    have hcNN : (1 : ℝ≥0) ≤ Real.toNNReal c := by
      rw [← NNReal.coe_le_coe, NNReal.coe_one, Real.coe_toNNReal _ hc0]
      exact hc
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcNN (by positivity : (0 : ℝ≥0) ≤ (1 / 2 : ℝ≥0) ^ t)
  have hgraph := P.initial_graph_product_bound H S₀ D.active D.coupled hInv₀ hchosen₀ hambient hratio
    hEupper hEquadratic error herrLower (herrSmall.trans (by norm_num)) hfailure
  have hconditioned := hgraph.conditionOn_half Good hGood hhalf
  have hactiveSupport := raw.conditionOn_supported Good hGood
  have hstateSupport := D.support.conditionOn hGood
  have hterminal := (FiniteLaw.timedStoppedProcessLaw_supported_terminal n (fun _ ↦ greedyKernel F)
    D.active S₀).conditionOn hGood
  refine ⟨(raw.conditionOn Good hGood).map Prod.snd, ?_, hconditioned.map Prod.snd⟩
  refine FiniteLaw.SupportedOn.map (L := raw.conditionOn Good hGood)
    (P := fun w : FiniteLaw.TimedState (GreedyStateOn V) n ↦ GreedyInvariant F w.2 ∧
      GreedyContainedIn S₀.available w.2 ∧ w.2.chosen.card = n ∧
      KSSSOnTrajectories F w.2 q (ksssResidualPairs (initialResidualPairs H) w.2) a E A
        ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B n ∧
      CrudeStateBounds F w.2 q (dyadicCrudeThresholds V t k) ∧
      AllUncoveredNeighborBands sets (initialResidualPairs H) E t (ksssPowerErrorExponent b B) B n w.2 ∧
      AllProperPatternBands sets patterns q a E t (ksssPowerErrorExponent b B) B n w.2)
    ?_ Prod.snd (fun _ h ↦ h)
  intro w hw
  have ha := hactiveSupport w hw
  have hs := hstateSupport w hw
  have htime := (hterminal w hw).resolve_right (not_not_intro ha)
  have hcoupled := D.coupled w.1.1 w.2 ha
  refine ⟨hs.1.1, hs.1.2, hs.2.trans htime, ?_, hcoupled.2.2.1, ?_, ?_⟩
  · simpa only [htime] using hcoupled.2.1
  · simpa only [htime] using D.degree w.1.1 w.2 ha
  · simpa only [htime] using D.pattern w.1.1 w.2 ha

end

end Erdos207
