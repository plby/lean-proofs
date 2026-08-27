/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRegularizedSparseData
import ErdosProblems.Erdos207.SourceRegularizedPrecision

/-! # Actual integer regularization gaps supply every sparse initial-data field -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem source_regularized_sparse_process_data_of_integer_gap
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I]
    (G : SimpleGraph V) (available : TripleSystemOn V) (e : I ↪ TripleOn V)
    (hencode : univ.map e = available) (q b B k t Rmin c : ℕ)
    (Lstar : ℕ → Finset (Finset I)) (p tau C : ℝ≥0)
    (huniform : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, E.card = j - 2)
    (havoid : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j,
      ∀ D ∈ (Ico 4 j).biUnion Lstar, ¬ D ⊆ E)
    (hpacking : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, IsPackingOn (E.map e))
    (htri : ∀ T ∈ available, tripleEdgeFinset T ⊆ graphEdges G)
    (hEpos : 0 < (graphEdges G).card) (hN : 1 ≤ Fintype.card V)
    (hp : 0 < p) (hp1 : p ≤ 1) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hreg : ∀ edge ∈ graphEdges G,
      |((available.filter fun T ↦ edge ∈ tripleEdgeFinset T).card : ℝ) -
        (p : ℝ) ^ 2 * tau * Fintype.card V / 4| ≤
          (1 / (24 * (t : ℝ) ^ ksssPowerErrorExponent b B)) * ((p : ℝ) ^ 2 * tau * Fintype.card V / 4))
    (hgap : ∀ j ∈ Icc 4 q, finiteHypergraphDegreeGap (Lstar j) ≤ 8192 * t)
    (ht : 49152 ≤ t) (hbinomial : 2 ^ q ≤ t) (horder : q ≤ t)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ Fintype.card V)
    (hEdgeFloor : (Fintype.card V : ℝ) ^ 2 / (t : ℝ) ^ b ≤ (graphEdges G).card)
    (hRatioFloor : (Fintype.card V : ℝ) / (t : ℝ) ^ b ≤
      (p : ℝ) ^ 2 * tau * Fintype.card V / 24)
    (hC : 1 ≤ C) (hsmall : C * t * p ≤ tau)
    (hdegree : ∀ d ∈ ksssOrders q, (finiteHypergraphMaxDegree (Lstar (d + 3)) : ℝ≥0) ≤
      9 * t * C * (p ^ 3 * Fintype.card V) ^ d)
    (hcoeff : KSSSPowerCoefficientBounds q (fun d ↦ 9 * 24 ^ d) B t)
    (henvelope : 4 * q ≤ B)
    (hpair : ksssPairDriftCoefficient q (fun d ↦ 9 * 24 ^ d) +
      ksssPairTaylorCoefficient (ksssOrders q) (fun d ↦ 9 * 24 ^ d) ≤ 3 * (B : ℝ))
    (hconfiguration : ∀ i : CrudeOrderIndex q 4,
      ksssIndexedConfigurationDriftCoefficient q (fun d ↦ 9 * 24 ^ d) i +
        ksssConfigurationTaylorCoefficient (ksssOrders q) (fun d ↦ 9 * 24 ^ d)
          (i.order - 3) i.chosen ≤ 3 * (B : ℝ) / 2)
    (hcb : 2 * c ≤ b) :
    let F := regularizedForbiddenUnion e q Lstar
    let E : ℝ := (graphEdges G).card
    let A : ℝ := available.card
    let S : GreedyStateOn V := ⟨∅, available⟩
    let horizon := ksssDensityHorizon E (1 / (t : ℝ) ^ c)
    KSSSPowerParameters F q horizon b B k t Rmin
      (regularizedTrajectoryCoefficient Lstar A) (fun d ↦ 9 * 24 ^ d) E A ∧
      GreedyInvariant F S ∧
      KSSSInitialRegularity F S q (graphPairFamily G)
        (regularizedTrajectoryCoefficient Lstar A) E A (1 / (6 * (t : ℝ) ^ ksssPowerErrorExponent b B)) ∧
      (∀ D ∈ F, D ⊆ available) ∧
      (∀ i : ℕ, i ≤ horizon → 1 / (t : ℝ) ^ c ≤ ksssEdgeDensity E i) ∧
      E / A ≤ 24 / ((p : ℝ) ^ 2 * tau * Fintype.card V) ∧
      ksssEdgeDensity E horizon ≤ 2 / (t : ℝ) ^ c := by
  dsimp only
  let theta : ℝ := 1 / (24 * (t : ℝ) ^ ksssPowerErrorExponent b B)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hprecision := source_regularized_precision t b B ht1
  have hnPos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have htarget : (0 : ℝ) < (p : ℝ) ^ 2 * tau * Fintype.card V / 4 := by positivity
  have hpairData := regularized_graph_pair_initial_bounds G
    ({chosen := ∅, available := available} : GreedyStateOn V)
    ((p : ℝ) ^ 2 * tau * Fintype.card V / 4) theta htri hEpos htarget
    hprecision.1.le hprecision.2.1 hreg
  have hratio : (Fintype.card V : ℝ) / (t : ℝ) ^ b ≤
      (available.card : ℝ) / (graphEdges G).card := by
    apply hRatioFloor.trans
    calc
      (p : ℝ) ^ 2 * tau * Fintype.card V / 24 =
          ((p : ℝ) ^ 2 * tau * Fintype.card V / 4) / 6 := by ring
      _ ≤ _ := hpairData.2.1
  have hscaleR : (t : ℝ) ^ ksssPowerDenominatorExponent q b B k Rmin ≤ Fintype.card V := by
    exact_mod_cast hscale
  have hgapReal : ∀ j ∈ Icc 4 q, (finiteHypergraphDegreeGap (Lstar j) : ℝ) ≤
      (4 * theta) * ((available.card : ℝ) / (graphEdges G).card) ^ (j - 3) := by
    intro j hj
    have hj4 := (mem_Icc.mp hj).1
    have hfixed : (finiteHypergraphDegreeGap (Lstar j) : ℝ) ≤ 8192 * (t : ℝ) := by
      exact_mod_cast hgap j hj
    exact hfixed.trans (source_regularized_gap_budget q b B k Rmin (j - 3)
      (Fintype.card V) t ((available.card : ℝ) / (graphEdges G).card)
      (by exact_mod_cast ht) (by omega) hscaleR hratio).2
  have hStoppingMass := source_regularized_stopping_mass q b B k Rmin c (Fintype.card V) t
    (graphEdges G).card (by exact_mod_cast (show 3 ≤ t by omega)) (by omega) hscaleR hEdgeFloor
  have hdata := source_regularized_sparse_process_data G available e hencode q b B k t Rmin c Lstar
    p tau C theta huniform havoid hpacking htri hEpos hN hp hp1 htau htau1
    hprecision.1.le hprecision.2.1 hreg hgapReal (by omega) hbinomial horder hscale
    hEdgeFloor hRatioFloor hC hsmall hdegree hcoeff henvelope hpair hconfiguration hcb hStoppingMass
  simpa only [theta, hprecision.2.2] using hdata

end

end Erdos207
