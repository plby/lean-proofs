/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizedKSSSPowerParameters
import ErdosProblems.Erdos207.RegularizedPairAverage
import ErdosProblems.Erdos207.SourceUniformCoefficient
import ErdosProblems.Erdos207.KSSSJointHorizon
import ErdosProblems.Erdos207.CrossScaleRegularizationScalars
import ErdosProblems.Erdos207.BoundedPatternIndex

/-! # Assemble actual regularized data at the shorter sparse-process horizon -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem source_regularized_sparse_process_data
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I]
    (G : SimpleGraph V) (available : TripleSystemOn V) (e : I ↪ TripleOn V)
    (hencode : univ.map e = available) (q b B k t Rmin c : ℕ)
    (Lstar : ℕ → Finset (Finset I)) (p tau C : ℝ≥0) (theta : ℝ)
    (huniform : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, E.card = j - 2)
    (havoid : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j,
      ∀ D ∈ (Ico 4 j).biUnion Lstar, ¬ D ⊆ E)
    (hpacking : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, IsPackingOn (E.map e))
    (htri : ∀ T ∈ available, tripleEdgeFinset T ⊆ graphEdges G)
    (hEpos : 0 < (graphEdges G).card) (hN : 1 ≤ Fintype.card V)
    (hp : 0 < p) (hp1 : p ≤ 1) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1 / 2)
    (hreg : ∀ edge ∈ graphEdges G,
      |((available.filter fun T ↦ edge ∈ tripleEdgeFinset T).card : ℝ) -
        (p : ℝ) ^ 2 * tau * Fintype.card V / 4| ≤
          theta * ((p : ℝ) ^ 2 * tau * Fintype.card V / 4))
    (hgap : ∀ j ∈ Icc 4 q, (finiteHypergraphDegreeGap (Lstar j) : ℝ) ≤
      (4 * theta) * ((available.card : ℝ) / (graphEdges G).card) ^ (j - 3))
    (ht : 32 ≤ t) (hbinomial : 2 ^ q ≤ t) (horder : q ≤ t)
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
    (hcb : 2 * c ≤ b) (hStoppingMass : 3 * (t : ℝ) ^ c ≤ (graphEdges G).card) :
    let F := regularizedForbiddenUnion e q Lstar
    let E : ℝ := (graphEdges G).card
    let A : ℝ := available.card
    let S : GreedyStateOn V := ⟨∅, available⟩
    let horizon := ksssDensityHorizon E (1 / (t : ℝ) ^ c)
    KSSSPowerParameters F q horizon b B k t Rmin
      (regularizedTrajectoryCoefficient Lstar A) (fun d ↦ 9 * 24 ^ d) E A ∧
      GreedyInvariant F S ∧
      KSSSInitialRegularity F S q (graphPairFamily G)
        (regularizedTrajectoryCoefficient Lstar A) E A (4 * theta) ∧
      (∀ D ∈ F, D ⊆ available) ∧
      (∀ i : ℕ, i ≤ horizon → 1 / (t : ℝ) ^ c ≤ ksssEdgeDensity E i) ∧
      E / A ≤ 24 / ((p : ℝ) ^ 2 * tau * Fintype.card V) ∧
      ksssEdgeDensity E horizon ≤ 2 / (t : ℝ) ^ c := by
  dsimp only
  let S : GreedyStateOn V := ⟨∅, available⟩
  let A : ℝ := available.card
  let E : ℝ := (graphEdges G).card
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have htNN : (1 : ℝ≥0) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hnPos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hE : 0 < E := by
    dsimp only [E]
    exact_mod_cast hEpos
  have htarget : (0 : ℝ) < (p : ℝ) ^ 2 * tau * Fintype.card V / 4 := by positivity
  have hpairData := regularized_graph_pair_initial_bounds G S
    ((p : ℝ) ^ 2 * tau * Fintype.card V / 4) theta htri hEpos htarget htheta htheta1 hreg
  have hA : 0 < A := hpairData.1
  have hratio : (p : ℝ) ^ 2 * tau * Fintype.card V / 24 ≤ A / E := by
    convert hpairData.2.1 using 1; ring
  have hratioUpper : A / E ≤ (Fintype.card V : ℝ) := by
    have hpR : (p : ℝ) ≤ 1 := by exact_mod_cast hp1
    have htauR : (tau : ℝ) ≤ 1 := by exact_mod_cast htau1
    have hscaleSmall : (p : ℝ) ^ 2 * tau * Fintype.card V ≤ (Fintype.card V : ℝ) := by
      calc
        (p : ℝ) ^ 2 * tau * Fintype.card V ≤ 1 ^ 2 * 1 * Fintype.card V := by
          gcongr
        _ = _ := by ring
    have hb := hpairData.2.2.1
    change A / E ≤ ((p : ℝ) ^ 2 * tau * Fintype.card V / 4) / 2 at hb
    linarith only [hb, hscaleSmall, hnPos]
  have hdegree' : ∀ d ∈ ksssOrders q,
      (finiteHypergraphMaxDegree (Lstar (d + 3)) : ℝ) ≤ (9 * 24 ^ d) * (A / E) ^ d := by
    intro d hd
    have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
    let ratio : ℝ≥0 := ⟨A / E, (div_pos hA hE).le⟩
    have hr : p ^ 2 * tau * Fintype.card V / 24 ≤ ratio := by exact_mod_cast hratio
    have hh := (hdegree d hd).trans
      (source_regularized_degree_scale_bound_uniform d t p tau (Fintype.card V) C ratio
        hd1 htNN hC hsmall hr)
    exact_mod_cast hh
  have hEupper : E ≤ (Fintype.card V : ℝ) ^ 2 := by
    dsimp only [E]
    exact_mod_cast (card_le_univ (graphEdges G)).trans (card_sym2_le_square V)
  have hparams := regularized_ksss_power_parameters e q b B k t Rmin Lstar huniform havoid hpacking
    A E (fun d ↦ 9 * 24 ^ d) hA hE hN ht hbinomial horder hscale hEupper hEdgeFloor
    (hRatioFloor.trans hratio) hratioUpper hdegree' hcoeff henvelope hpair hconfiguration
  have hshort := hparams.earlier_density_horizon (c := c) (by omega)
  refine ⟨hshort.1, regularizedForbiddenUnion_initial_invariant e q Lstar huniform available,
    regularized_initial_regularity e q Lstar huniform S (graphPairFamily G) A E (4 * theta) hA
      (by rw [hencode]) hpairData.2.2.2 hgap, ?_, hshort.2, ?_, ?_⟩
  · intro D hD
    obtain ⟨D0, _, rfl⟩ := mem_image.mp hD
    rw [← hencode]
    exact map_subset_map.mpr (subset_univ D0)
  · have hb := one_div_le_one_div_of_le (by positivity : (0 : ℝ) <
        (p : ℝ) ^ 2 * tau * Fintype.card V / 24) hratio
    simpa only [one_div_div] using hb
  · exact ksssDensityHorizon_survival_upper E t c hE ht1 hStoppingMass

end

end Erdos207
