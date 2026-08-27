/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternTypicalityArithmetic
import ErdosProblems.Erdos207.KSSSPatternBandsFailure
import ErdosProblems.Erdos207.BoundedPatternIndex
import ErdosProblems.Erdos207.UncoveredNeighborBandFailure
import ErdosProblems.Erdos207.UncoveredNeighborGraph

/-! # The initial degree and proper-pattern bands imply exact iteration-typicality -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem patternUncovered_of_le_graphDifference
    {V : Type*} [Fintype V] [DecidableEq V]
    {Q G : SimpleGraph V} {S : GreedyStateOn V}
    (hQ : Q ≤ graphDifference G (coveredGraph S.chosen)) : PatternUncovered Q S := by
  intro e he hc
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hQadj : Q.Adj u v := by simpa only [mem_graphEdges_iff, SimpleGraph.mem_edgeSet] using he
    exact (hQ hQadj).2.2 (by simpa only [SimpleGraph.mem_edgeSet] using hc)

theorem initial_bands_isIterationTypical
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (H : SimpleGraph V) (S : GreedyStateOn V)
    (q b B t h : ℕ) (a coeff : ℕ → ℝ) (E time : ℝ)
    (ht : 1 ≤ t) (hb : 1 ≤ b) (hh : h ≤ t)
    (htime : 0 ≤ time) (hclock : time ≤ E)
    (hfloor : 1 / (t : ℝ) ^ b ≤ ksssEdgeDensity E time)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hexp : Real.exp (∑ d ∈ ksssOrders q, coeff d) ≤ t)
    (hU : ∀ i, (W.U i).Nonempty)
    (hsize : ∀ i, (t : ℝ) ^ (b * h + h ^ 2 + 2) ≤ ((W.U i).card : ℝ))
    (hdegree : AllUncoveredNeighborBands W.U (initialResidualPairs H) E t
      (ksssPowerErrorExponent b B) B time S)
    (hpatterns : AllProperPatternBands W.U
      (fun Q : WorkingGraphPattern (graphDifference (SimpleGraph.completeGraph V) H) h ↦ Q.1.1)
      q a E t (ksssPowerErrorExponent b B) B time S) :
    IsIterationTypical W 0
      (graphDifference (graphDifference (SimpleGraph.completeGraph V) H) (coveredGraph S.chosen))
      S.available (Real.toNNReal (ksssEdgeDensity E time))
      (Real.toNNReal (Real.exp (-ksssPoissonExponent (ksssOrders q) a time)))
      (17 / (t : ℝ≥0)) h := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  have hp : 0 < ksssEdgeDensity E time := (by positivity : (0 : ℝ) < 1 / (t : ℝ) ^ b).trans_le hfloor
  have hdegree' : ∀ i v,
      WithinMultiplicativeError (17 / (t : ℝ≥0))
        ((neighborsIn (graphDifference (graphDifference (SimpleGraph.completeGraph V) H)
          (coveredGraph S.chosen)) (W.U i) v).card : ℝ≥0)
        (Real.toNNReal (ksssEdgeDensity E time) * (W.U i).card) := by
    intro i v
    apply (withinMultiplicativeError_iff_abs _ _ _).mpr
    simp only [NNReal.coe_natCast, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat,
      Real.coe_toNNReal _ hp.le]
    have hbound := (hdegree i v).trans
      (uncoveredNeighborErrorEnvelope_relative_upper E (W.U i).card t time b B
        (Nat.cast_nonneg _) htpos hfloor)
    rw [uncoveredNeighbors_initialResidualPairs_eq_graph_neighbors] at hbound
    simp only [uncoveredNeighborTarget] at hbound
    calc
      _ = |((neighborsIn (graphDifference (graphDifference (SimpleGraph.completeGraph V) H)
          (coveredGraph S.chosen)) (W.U i) v).card : ℝ) - (W.U i).card * ksssEdgeDensity E time| := by rw [mul_comm]
      _ ≤ (16 / (t : ℝ)) * ((W.U i).card * ksssEdgeDensity E time) := hbound
      _ ≤ (17 / (t : ℝ)) * (ksssEdgeDensity E time * (W.U i).card) := by
        rw [mul_comm (ksssEdgeDensity E time)]
        gcongr <;> norm_num
  refine ⟨fun i _ ↦ ⟨fun v _ ↦ hdegree' i.castSucc v, fun v _ ↦ hdegree' i.succ v⟩, ?_⟩
  intro i _ iStar _ Q hQG _ hQh
  let Q' : WorkingGraphPattern (graphDifference (SimpleGraph.completeGraph V) H) h :=
    ⟨⟨Q, hQh⟩, hQG.trans (graphDifference_le_left _ _)⟩
  let f := ksssPatternTrajectory (ksssOrders q) a E (W.U iStar).card
    (graphSupportFinset Q).card (graphEdges Q).card time
  have hf : 0 < f := ksssPatternTrajectory_pos _ _ _ _ _ _ _
    (by exact_mod_cast card_pos.mpr (hU iStar)) hp
  have hm : (graphEdges Q).card ≤ h ^ 2 :=
    (card_graphEdges_le_graphSupportFinset_sq Q).trans (Nat.pow_le_pow_left hQh 2)
  have hpow : b * (graphSupportFinset Q).card + (graphEdges Q).card + 2 ≤ b * h + h ^ 2 + 2 := by
    have hmul := Nat.mul_le_mul_left b hQh
    omega
  have hendpoint : ((graphSupportFinset Q).card : ℝ) ≤ (1 / (t : ℝ)) * f :=
    pattern_endpoint_power_budget (W.U iStar).card f t (graphSupportFinset Q).card
      (b * (graphSupportFinset Q).card + (graphEdges Q).card) htR (by exact_mod_cast hQh.trans hh)
      ((pow_le_pow_right₀ htR hpow).trans (hsize iStar))
      (ksssPatternTrajectory_power_lower _ _ coeff _ _ _ _ _ _ _ (Nat.cast_nonneg _) htpos
        htime hclock ha hab hexp hfloor)
  have hband : |((properPatternExtensions S.available Q (W.U iStar)).card : ℝ) / f - 1| ≤
      relativePatternEnvelope E t (ksssPowerErrorExponent b B) B time :=
    hpatterns iStar Q' (patternUncovered_of_le_graphDifference hQG)
  have hpower : (t : ℝ) ≤ (t : ℝ) ^ b := by
    simpa only [pow_one] using pow_le_pow_right₀ htR hb
  have hz : relativePatternEnvelope E t (ksssPowerErrorExponent b B) B time ≤ 16 / (t : ℝ) :=
    (relativePatternEnvelope_terminal_bound E t time b B htpos hfloor).trans
      (div_le_div_of_nonneg_left (by norm_num) htpos hpower)
  have hfull := full_pattern_error_of_proper_relative_band S.available Q (W.U iStar)
    f (16 / t) (1 / t) hf (hband.trans hz) hendpoint
  apply (withinMultiplicativeError_iff_abs _ _ _).mpr
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_ofNat,
    Real.coe_toNNReal _ hp.le, Real.coe_toNNReal _ (Real.exp_pos _).le]
  have hfEq := ksssPatternTrajectory_eq_multiplicative_target (ksssOrders q) a E
    (W.U iStar).card time (graphSupportFinset Q).card (graphEdges Q).card
  change f = _ at hfEq
  rw [← hfEq]
  convert hfull using 1 <;> ring

end

end Erdos207
