/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FrozenPreparedSparseLaw
import ErdosProblems.Erdos207.ResidualSupportedSubtype

/-! # A positive prepared prior with the actual sparse mixed kernel in every fiber -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem exists_frozen_prepared_sparse_prior
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} (P : FiniteLaw Omega) (W : Vortex V ell) (current : Fin (ell + 1))
    (available initial later : Omega → TripleSystemOn V) [∀ omega, Nonempty {T // T ∈ available omega}]
    (F envelope : ℕ → ForbiddenFamilyOn V) (y z : ℕ → ℝ≥0)
    (q b B k t Rmin c gapDecay : ℕ) (p tau C : ℝ≥0)
    (Lstar : ℕ → (omega : Omega) → Finset (Finset {T // T ∈ available omega}))
    (hsupport : ∀ omega T, T ∈ available omega → T.1 ⊆ W.U current)
    (hresult : ∀ j ∈ Icc 4 q,
      FixedRandomOrderResult P (W.prefix current)
        (fun omega ↦ Function.Embedding.subtype (fun T ↦ T ∈ available omega)) j (8192 * t)
        (fun omega ↦ finiteHypergraphOnSubset (available omega)
          (localForbiddenConfigurations ((Icc 4 q).biUnion F) (available omega) (initial omega ∪ later omega) j))
        (fun omega ↦ (Ico 4 j).biUnion (fun i ↦ Lstar i omega)) (F j)
        (terminalRandomConfigurations (W.prefix current) j)
        (y j) (z j) ((t : ℝ≥0) ^ 4) (1 / (t : ℝ≥0) ^ gapDecay) (Lstar j) (envelope j))
    (hdegree : ∀ omega, sourceAuxiliaryDegreeGood W current q t F available (fun x ↦ initial x ∪ later x) p y omega)
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
    (hcb : 2 * c ≤ b)
    (baseGraph : SimpleGraph V) (reserve : Omega → Finset (Sym2 V)) (r Cprior beta : ℝ≥0)
    (hstrong : IsResidualReserveStronglyWellDistributed P W current baseGraph initial later reserve p r Cprior beta)
    (hCprior : 1 ≤ Cprior) (hnonempty : ∀ i, (W.U i).Nonempty)
    (hdisjoint : P.SupportedOn fun omega ↦ Disjoint (available omega) (initial omega ∪ later omega))
    (s R decay errorExponent zExponent : ℕ) (Z priorCoefficient : ℝ≥0)
    (hZ : 1 ≤ Z) (hz : ∀ j ∈ Icc 4 q, z j + 3 * (t : ℝ≥0) ^ 4 ≤ Z)
    (hZpower : Z ≤ (t : ℝ≥0) ^ zExponent)
    (hconstant : sourceCrudeUniformCoefficient current.val q (Icc 4 q).card 1 1 ≤ t)
    (hk : 2 * zExponent + 2 * q * (5 * b + 3) + 2 ≤ k)
    (hambient : Fintype.card V ≤ t ^ R) (hs : 6 * R + decay ≤ s)
    (herrorExponent : 6 * R + (6 * q * R) * s + decay ≤ errorExponent)
    (hbeta : beta ≤ priorCoefficient / (t : ℝ≥0) ^ errorExponent)
    (bandError delta : ℝ≥0) (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (herror : (1 / 2 : ℝ≥0) ^ t ≤ delta)
    (hbandError : 2 * (((W.U current).card : ℝ) ^ 2 +
      (q + 1 : ℝ) ^ 2 * ((W.U current).card : ℝ) ^ 3) * (1 / 2 : ℝ) ^ t ≤ bandError)
    (error : ℝ≥0)
    (hbudget : (((Icc 4 q).card : ℝ≥0) / (t : ℝ≥0) ^ gapDecay + bandError +
      sourceSparseCrudeFailure q s (Icc 4 q).card t decay Cprior priorCoefficient) / delta ≤ error)
    (herror1 : error < 1) :
    let J := fun omega ↦ regularizedForbiddenUnion
      (restrictTripleIndexEmbedding (W.U current)
        (Function.Embedding.subtype (fun T ↦ T ∈ available omega))
        (fun T ↦ hsupport omega T.val T.property)) q (fun j ↦ Lstar j omega)
    let E := fun omega ↦ ((graphEdges (G omega)).card : ℝ)
    let A := fun omega ↦ ((available omega).card : ℝ)
    let a := fun omega ↦ regularizedTrajectoryCoefficient (fun j ↦ Lstar j omega) (A omega)
    let Gap := fun omega ↦ ∀ j ∈ Icc 4 q, finiteHypergraphDegreeGap (Lstar j omega) ≤ 8192 * t
    let K := fun omega ↦ stoppedGreedyStateLaw (ksssDensityHorizon (E omega) (1 / (t : ℝ) ^ c)) (J omega)
      (fun i S ↦ Gap omega ∧ KSSSPowerActive (J omega)
        (graphPairFamily ((G omega).induce (W.U current : Set V))) q b B k t
          (a omega) (E omega) (A omega) i S)
      (⟨∅, restrictTripleSystemTo (W.U current) (available omega)⟩ : GreedyStateOn (W.U current))
    let Good := fun omega ↦ Gap omega ∧ IsGraphMixedProductBound (K omega)
      (fun S ↦ mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U current)) S.chosen)
      (G omega) (2 / (t : ℝ≥0) ^ c) (24 / (p ^ 2 * tau * (W.U current).card))
      (ksssSparseGraphProductConstant q (fun d ↦ 9 * 24 ^ d)) delta
    ∃ hpos : 0 < P.probability Good,
      1 - error ≤ P.probability Good ∧
      IsResidualReserveStronglyWellDistributed (P.conditionSubtype Good hpos) W current baseGraph
        (fun x ↦ initial x.val) (fun x ↦ later x.val) (fun x ↦ reserve x.val)
        p r (Cprior / (1 - error)) beta ∧
      ∀ x : {omega // Good omega}, Gap x.val ∧ IsGraphMixedProductBound (K x.val)
        (fun S ↦ mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U current)) S.chosen)
        (G x.val) (2 / (t : ℝ≥0) ^ c) (24 / (p ^ 2 * tau * (W.U current).card))
        (ksssSparseGraphProductConstant q (fun d ↦ 9 * 24 ^ d)) delta := by
  dsimp only
  let J := fun omega ↦ regularizedForbiddenUnion
    (restrictTripleIndexEmbedding (W.U current)
      (Function.Embedding.subtype (fun T ↦ T ∈ available omega))
      (fun T ↦ hsupport omega T.val T.property)) q (fun j ↦ Lstar j omega)
  let E := fun omega ↦ ((graphEdges (G omega)).card : ℝ)
  let A := fun omega ↦ ((available omega).card : ℝ)
  let a := fun omega ↦ regularizedTrajectoryCoefficient (fun j ↦ Lstar j omega) (A omega)
  let Gap := fun omega ↦ ∀ j ∈ Icc 4 q, finiteHypergraphDegreeGap (Lstar j omega) ≤ 8192 * t
  let K := fun omega ↦ stoppedGreedyStateLaw (ksssDensityHorizon (E omega) (1 / (t : ℝ) ^ c)) (J omega)
    (fun i S ↦ Gap omega ∧ KSSSPowerActive (J omega)
      (graphPairFamily ((G omega).induce (W.U current : Set V))) q b B k t
        (a omega) (E omega) (A omega) i S)
    (⟨∅, restrictTripleSystemTo (W.U current) (available omega)⟩ : GreedyStateOn (W.U current))
  let Good := fun omega ↦ Gap omega ∧ IsGraphMixedProductBound (K omega)
    (fun S ↦ mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U current)) S.chosen)
    (G omega) (2 / (t : ℝ≥0) ^ c) (24 / (p ^ 2 * tau * (W.U current).card))
    (ksssSparseGraphProductConstant q (fun d ↦ 9 * 24 ^ d)) delta
  have hfailure := frozen_prepared_sparse_law_failure_le P W current available initial later
    F envelope y z q b B k t Rmin c gapDecay p tau C Lstar hsupport hresult hdegree hCcoeff
    G hG htri hEpos hN hp hp1 htau htau1 hreg ht hbinomial horder hscale hEdgeFloor hRatioFloor
    hC hsmall hcoeff henvelope hpair hconfiguration hcb baseGraph Cprior beta hstrong.toResidual
    hCprior hnonempty hdisjoint s R decay errorExponent zExponent Z priorCoefficient hZ hz hZpower
    hconstant hk hambient hs herrorExponent hbeta bandError delta hdelta hdelta1 herror hbandError
  have hbad : P.probability (fun omega ↦ ¬ Good omega) ≤ error := hfailure.trans hbudget
  have hlower : 1 - error ≤ P.probability Good := by
    rw [P.probability_not Good] at hbad
    exact tsub_le_iff_tsub_le.mp hbad
  have hden : 0 < 1 - error := tsub_pos_iff_lt.mpr herror1
  have hpos : 0 < P.probability Good := hden.trans_le hlower
  refine ⟨hpos, hlower, ?_, fun x ↦ x.property⟩
  exact (hstrong.conditionSubtype Good hpos).mono
    (div_le_div_of_nonneg_left zero_le hden hlower) le_rfl

end

end Erdos207
