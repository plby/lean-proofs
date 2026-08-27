/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRegularizedCurrentData
import ErdosProblems.Erdos207.PreparedAuxiliaryRegularization
import ErdosProblems.Erdos207.FixedEnvelopeCurrentGeometry

/-! # Actual frozen prepared families supply the current sparse-process data -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem sourceAuxiliaryDegreeGood.regularized_degree_bound
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {current : Fin (ell + 1)} {q t : ℕ}
    {F : ℕ → ForbiddenFamilyOn V} {available old : Omega → TripleSystemOn V}
    {p C : ℝ≥0} {y : ℕ → ℝ≥0} {omega : Omega}
    (hgood : sourceAuxiliaryDegreeGood W current q t F available old p y omega)
    (Lstar : ℕ → Finset (Finset {T // T ∈ available omega}))
    (hmax : ∀ j ∈ Icc 4 q, finiteHypergraphMaxDegree (Lstar j) ≤
      9 * finiteHypergraphMaxDegree (finiteHypergraphOnSubset (available omega)
        (localForbiddenConfigurations ((Icc 4 q).biUnion F) (available omega) (old omega) j)))
    (hC : ∀ j ∈ Icc 4 q,
      (∑ j' ∈ Icc j q, sourceNibbleMomentCoefficient current.val j' 2 * y j') ≤ C) :
    ∀ d ∈ ksssOrders q, (finiteHypergraphMaxDegree (Lstar (d + 3)) : ℝ≥0) ≤
      9 * t * C * (p ^ 3 * (W.U current).card) ^ d := by
  intro d hd
  have hdb := mem_Icc.mp hd
  have hj : d + 3 ∈ Icc 4 q := mem_Icc.mpr ⟨by omega, by omega⟩
  have hmaxNN : (finiteHypergraphMaxDegree (Lstar (d + 3)) : ℝ≥0) ≤
      9 * finiteHypergraphMaxDegree (finiteHypergraphOnSubset (available omega)
        (localForbiddenConfigurations ((Icc 4 q).biUnion F) (available omega) (old omega) (d + 3))) := by
    exact_mod_cast hmax (d + 3) hj
  have hlocal := hgood (d + 3) hj
  have hconstant := hC (d + 3) hj
  simp only [Nat.add_sub_cancel, Vortex.prefix_terminalSize] at hlocal
  apply hmaxNN.trans
  calc
    _ ≤ 9 * (((t : ℝ≥0) * ∑ j' ∈ Icc (d + 3) q,
        sourceNibbleMomentCoefficient current.val j' 2 * y j') *
        (p ^ 3) ^ d * ((W.U current).card : ℝ≥0) ^ d) :=
      mul_le_mul_of_nonneg_left hlocal zero_le
    _ ≤ 9 * (((t : ℝ≥0) * C) * (p ^ 3) ^ d * ((W.U current).card : ℝ≥0) ^ d) := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

theorem frozen_prepared_current_sparse_data
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} (P : FiniteLaw Omega) (W : Vortex V ell) (current : Fin (ell + 1))
    (available old : Omega → TripleSystemOn V) [∀ omega, Nonempty {T // T ∈ available omega}]
    (F envelope : ℕ → ForbiddenFamilyOn V) (y z : ℕ → ℝ≥0)
    (q b B k t Rmin c decay : ℕ) (p tau C : ℝ≥0)
    (Lstar : ℕ → (omega : Omega) → Finset (Finset {T // T ∈ available omega}))
    (hsupport : ∀ omega T, T ∈ available omega → T.1 ⊆ W.U current)
    (hresult : ∀ j ∈ Icc 4 q,
      FixedRandomOrderResult P (W.prefix current)
        (fun omega ↦ Function.Embedding.subtype (fun T ↦ T ∈ available omega)) j (8192 * t)
        (fun omega ↦ finiteHypergraphOnSubset (available omega)
          (localForbiddenConfigurations ((Icc 4 q).biUnion F) (available omega) (old omega) j))
        (fun omega ↦ (Ico 4 j).biUnion (fun i ↦ Lstar i omega)) (F j)
        (terminalRandomConfigurations (W.prefix current) j)
        (y j) (z j) ((t : ℝ≥0) ^ 4) (1 / (t : ℝ≥0) ^ decay) (Lstar j) (envelope j))
    (hdegree : ∀ omega, sourceAuxiliaryDegreeGood W current q t F available old p y omega)
    (hCcoeff : ∀ j ∈ Icc 4 q,
      (∑ j' ∈ Icc j q, sourceNibbleMomentCoefficient current.val j' 2 * y j') ≤ C)
    (G : Omega → SimpleGraph V) (hG : ∀ omega, GraphSupportedOn (G omega) (W.U current : Set V))
    (htri : ∀ omega T, T ∈ available omega → tripleEdgeFinset T ⊆ graphEdges (G omega))
    (hEpos : ∀ omega, 0 < (graphEdges (G omega)).card) (hN : 1 ≤ (W.U current).card)
    (hp : 0 < p) (hp1 : p ≤ 1) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hreg : ∀ omega edge, edge ∈ graphEdges (G omega) →
      |((available omega |>.filter fun T ↦ edge ∈ tripleEdgeFinset T).card : ℝ) -
        (p : ℝ) ^ 2 * tau * (W.U current).card / 4| ≤
          (1 / (24 * (t : ℝ) ^ ksssPowerErrorExponent b B)) *
            ((p : ℝ) ^ 2 * tau * (W.U current).card / 4))
    (ht : 49152 ≤ t) (hbinomial : 2 ^ q ≤ t) (horder : q ≤ t)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ (W.U current).card)
    (hEdgeFloor : ∀ omega, ((W.U current).card : ℝ) ^ 2 / (t : ℝ) ^ b ≤ (graphEdges (G omega)).card)
    (hRatioFloor : ((W.U current).card : ℝ) / (t : ℝ) ^ b ≤
      (p : ℝ) ^ 2 * tau * (W.U current).card / 24)
    (hC : 1 ≤ C) (hsmall : C * t * p ≤ tau)
    (hcoeff : KSSSPowerCoefficientBounds q (fun d ↦ 9 * 24 ^ d) B t)
    (henvelope : 4 * q ≤ B)
    (hpair : ksssPairDriftCoefficient q (fun d ↦ 9 * 24 ^ d) +
      ksssPairTaylorCoefficient (ksssOrders q) (fun d ↦ 9 * 24 ^ d) ≤ 3 * (B : ℝ))
    (hconfiguration : ∀ i : CrudeOrderIndex q 4,
      ksssIndexedConfigurationDriftCoefficient q (fun d ↦ 9 * 24 ^ d) i +
        ksssConfigurationTaylorCoefficient (ksssOrders q) (fun d ↦ 9 * 24 ^ d)
          (i.order - 3) i.chosen ≤ 3 * (B : ℝ) / 2)
    (hcb : 2 * c ≤ b) :
    ∀ omega, (∀ j ∈ Icc 4 q, finiteHypergraphDegreeGap (Lstar j omega) ≤ 8192 * t) →
      let elocal := restrictTripleIndexEmbedding (W.U current)
        (Function.Embedding.subtype (fun T ↦ T ∈ available omega))
        (fun T ↦ hsupport omega T.val T.property)
      let J := regularizedForbiddenUnion elocal q (fun j ↦ Lstar j omega)
      let E : ℝ := (graphEdges (G omega)).card
      let A : ℝ := (available omega).card
      let S : GreedyStateOn (W.U current) := ⟨∅, restrictTripleSystemTo (W.U current) (available omega)⟩
      let horizon := ksssDensityHorizon E (1 / (t : ℝ) ^ c)
      KSSSPowerParameters J q horizon b B k t Rmin
        (regularizedTrajectoryCoefficient (fun j ↦ Lstar j omega) A) (fun d ↦ 9 * 24 ^ d) E A ∧
        GreedyInvariant J S ∧
        KSSSInitialRegularity J S q (graphPairFamily ((G omega).induce (W.U current : Set V)))
          (regularizedTrajectoryCoefficient (fun j ↦ Lstar j omega) A) E A
          (1 / (6 * (t : ℝ) ^ ksssPowerErrorExponent b B)) ∧
        (∀ D ∈ J, D ⊆ S.available) ∧
        (∀ i : ℕ, i ≤ horizon → 1 / (t : ℝ) ^ c ≤ ksssEdgeDensity E i) ∧
        E / A ≤ 24 / ((p : ℝ) ^ 2 * tau * (W.U current).card) ∧
        ksssEdgeDensity E horizon ≤ 2 / (t : ℝ) ^ c := by
  intro omega hgap
  have hFpacking : ∀ H ∈ (Icc 4 q).biUnion F, IsPackingOn H := by
    intro H hH
    obtain ⟨j, hj, hHj⟩ := mem_biUnion.mp hH
    exact ((hresult j hj).spread.uniform H (mem_union_left _ hHj)).2
  have hpacking : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j omega,
      IsPackingOn (E.map (Function.Embedding.subtype (fun T ↦ T ∈ available omega))) := by
    intro j hj
    apply (hresult j hj).decoded_packing omega
    intro E hE
    have hlocal := mem_image_of_mem
      (Finset.map (Function.Embedding.subtype (fun T ↦ T ∈ available omega))) hE
    rw [localForbiddenAuxiliary_decode] at hlocal
    exact localForbiddenConfigurations_packing ((Icc 4 q).biUnion F) (available omega)
      (old omega) j hFpacking _ hlocal
  exact source_regularized_current_sparse_process_data (G omega) (W.U current) (hG omega)
    (available omega) (Function.Embedding.subtype (fun T ↦ T ∈ available omega))
    (univ_map_subset_embedding (available omega)) (fun T ↦ hsupport omega T.val T.property)
    q b B k t Rmin c (fun j ↦ Lstar j omega) p tau C
    (fun j hj ↦ (hresult j hj).uniform omega)
    (fun j hj ↦ (hresult j hj).no_earlier_subset omega) hpacking
    (htri omega) (hEpos omega) hN hp hp1 htau htau1 (hreg omega) hgap
    ht hbinomial horder hscale (hEdgeFloor omega) hRatioFloor hC hsmall
    ((hdegree omega).regularized_degree_bound (fun j ↦ Lstar j omega)
      (fun j hj ↦ (hresult j hj).maximum omega) hCcoeff)
    hcoeff henvelope hpair hconfiguration hcb

end

end Erdos207
