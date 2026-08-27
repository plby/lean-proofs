/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRegularizedGapData
import ErdosProblems.Erdos207.CurrentAuxiliaryEncoding

/-! # Actual regularized sparse data on the current vertex subtype -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem source_regularized_current_sparse_process_data
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I]
    (G : SimpleGraph V) (U : Finset V) (hG : GraphSupportedOn G (U : Set V)) (available : TripleSystemOn V) (e : I ↪ TripleOn V)
    (hencode : univ.map e = available) (hsupport : ∀ i, (e i).1 ⊆ U) (q b B k t Rmin c : ℕ)
    (Lstar : ℕ → Finset (Finset I)) (p tau C : ℝ≥0)
    (huniform : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, E.card = j - 2)
    (havoid : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j,
      ∀ D ∈ (Ico 4 j).biUnion Lstar, ¬ D ⊆ E)
    (hpacking : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, IsPackingOn (E.map e))
    (htri : ∀ T ∈ available, tripleEdgeFinset T ⊆ graphEdges G)
    (hEpos : 0 < (graphEdges G).card) (hN : 1 ≤ U.card)
    (hp : 0 < p) (hp1 : p ≤ 1) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hreg : ∀ edge ∈ graphEdges G,
      |((available.filter fun T ↦ edge ∈ tripleEdgeFinset T).card : ℝ) -
        (p : ℝ) ^ 2 * tau * U.card / 4| ≤
          (1 / (24 * (t : ℝ) ^ ksssPowerErrorExponent b B)) * ((p : ℝ) ^ 2 * tau * U.card / 4))
    (hgap : ∀ j ∈ Icc 4 q, finiteHypergraphDegreeGap (Lstar j) ≤ 8192 * t)
    (ht : 49152 ≤ t) (hbinomial : 2 ^ q ≤ t) (horder : q ≤ t)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ U.card)
    (hEdgeFloor : (U.card : ℝ) ^ 2 / (t : ℝ) ^ b ≤ (graphEdges G).card)
    (hRatioFloor : (U.card : ℝ) / (t : ℝ) ^ b ≤
      (p : ℝ) ^ 2 * tau * U.card / 24)
    (hC : 1 ≤ C) (hsmall : C * t * p ≤ tau)
    (hdegree : ∀ d ∈ ksssOrders q, (finiteHypergraphMaxDegree (Lstar (d + 3)) : ℝ≥0) ≤
      9 * t * C * (p ^ 3 * U.card) ^ d)
    (hcoeff : KSSSPowerCoefficientBounds q (fun d ↦ 9 * 24 ^ d) B t)
    (henvelope : 4 * q ≤ B)
    (hpair : ksssPairDriftCoefficient q (fun d ↦ 9 * 24 ^ d) +
      ksssPairTaylorCoefficient (ksssOrders q) (fun d ↦ 9 * 24 ^ d) ≤ 3 * (B : ℝ))
    (hconfiguration : ∀ i : CrudeOrderIndex q 4,
      ksssIndexedConfigurationDriftCoefficient q (fun d ↦ 9 * 24 ^ d) i +
        ksssConfigurationTaylorCoefficient (ksssOrders q) (fun d ↦ 9 * 24 ^ d)
          (i.order - 3) i.chosen ≤ 3 * (B : ℝ) / 2)
    (hcb : 2 * c ≤ b) :
    let elocal := restrictTripleIndexEmbedding U e hsupport
    let F := regularizedForbiddenUnion elocal q Lstar
    let E : ℝ := (graphEdges G).card
    let A : ℝ := available.card
    let S : GreedyStateOn U := ⟨∅, restrictTripleSystemTo U available⟩
    let horizon := ksssDensityHorizon E (1 / (t : ℝ) ^ c)
    KSSSPowerParameters F q horizon b B k t Rmin
      (regularizedTrajectoryCoefficient Lstar A) (fun d ↦ 9 * 24 ^ d) E A ∧
      GreedyInvariant F S ∧
      KSSSInitialRegularity F S q (graphPairFamily (G.induce (U : Set V)))
        (regularizedTrajectoryCoefficient Lstar A) E A (1 / (6 * (t : ℝ) ^ ksssPowerErrorExponent b B)) ∧
      (∀ D ∈ F, D ⊆ restrictTripleSystemTo U available) ∧
      (∀ i : ℕ, i ≤ horizon → 1 / (t : ℝ) ^ c ≤ ksssEdgeDensity E i) ∧
      E / A ≤ 24 / ((p : ℝ) ^ 2 * tau * U.card) ∧
      ksssEdgeDensity E horizon ≤ 2 / (t : ℝ) ^ c := by
  dsimp only
  let elocal := restrictTripleIndexEmbedding U e hsupport
  let availableLocal := restrictTripleSystemTo U available
  have hASupport : ∀ T ∈ available, T.1 ⊆ U := by
    intro T hT
    rw [← hencode] at hT
    obtain ⟨i, _, rfl⟩ := mem_map.mp hT
    exact hsupport i
  have hAcard := card_restrictTripleSystemTo U available hASupport
  have hGcard := card_graphEdges_induce G U hG
  have hencoding := restrictTripleIndexEmbedding_univ U e available hencode hsupport
  have hpackingLocal : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, IsPackingOn (E.map elocal) := by
    intro j hj E hE
    exact (restrictTripleIndexEmbedding_packing U e hsupport E).mpr (hpacking j hj E hE)
  have htriLocal := restricted_triangle_edges_induce G U available htri
  have hregLocal := restricted_triangle_pair_regularity G U available
    ((p : ℝ) ^ 2 * tau * U.card / 4) (1 / (24 * (t : ℝ) ^ ksssPowerErrorExponent b B))
    hASupport hreg
  have hdata := source_regularized_sparse_process_data_of_integer_gap (V := U)
    (G.induce (U : Set V)) availableLocal elocal hencoding q b B k t Rmin c Lstar p tau C
    huniform havoid hpackingLocal htriLocal
    (by simpa only [hGcard] using hEpos)
    (by simpa only [Fintype.card_coe] using hN) hp hp1 htau htau1
    (by
      intro edge hedge
      simp only [Fintype.card_coe]
      apply hregLocal edge
      revert hedge
      refine Sym2.inductionOn edge (fun x y hxy ↦ ?_)
      have hadj : (G.induce (U : Set V)).Adj x y := mem_graphEdges_iff.mp hxy
      exact mem_graphEdges_iff.mpr hadj) hgap ht hbinomial horder
    (by simpa only [Fintype.card_coe] using hscale)
    (by simpa only [Fintype.card_coe, hGcard] using hEdgeFloor)
    (by simpa only [Fintype.card_coe] using hRatioFloor)
    hC hsmall (by simpa only [Fintype.card_coe] using hdegree)
    hcoeff henvelope hpair hconfiguration hcb
  simpa only [availableLocal, elocal, hAcard, hGcard, Fintype.card_coe] using hdata

end

end Erdos207
