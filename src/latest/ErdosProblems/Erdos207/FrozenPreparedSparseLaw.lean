/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FrozenPreparedCurrentData
import ErdosProblems.Erdos207.SourceSparseJointGraphLaw
import ErdosProblems.Erdos207.CurrentVertexMixedLaw

/-! # The actual frozen preliminary process has the ambient sparse mixed law -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem frozen_prepared_sparse_law_failure_le
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
    (baseGraph : SimpleGraph V) (Cprior beta : ℝ≥0)
    (hstrong : IsResidualGraphStronglyWellDistributed P W current baseGraph initial later p Cprior beta)
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
      (q + 1 : ℝ) ^ 2 * ((W.U current).card : ℝ) ^ 3) * (1 / 2 : ℝ) ^ t ≤ bandError) :
    let J := fun omega ↦ regularizedForbiddenUnion
      (restrictTripleIndexEmbedding (W.U current)
        (Function.Embedding.subtype (fun T ↦ T ∈ available omega))
        (fun T ↦ hsupport omega T.val T.property)) q (fun j ↦ Lstar j omega)
    let E := fun omega ↦ ((graphEdges (G omega)).card : ℝ)
    let A := fun omega ↦ ((available omega).card : ℝ)
    let a := fun omega ↦ regularizedTrajectoryCoefficient (fun j ↦ Lstar j omega) (A omega)
    let Good := fun omega ↦ ∀ j ∈ Icc 4 q, finiteHypergraphDegreeGap (Lstar j omega) ≤ 8192 * t
    let K := fun omega ↦ stoppedGreedyStateLaw (ksssDensityHorizon (E omega) (1 / (t : ℝ) ^ c)) (J omega)
      (fun i S ↦ Good omega ∧ KSSSPowerActive (J omega)
        (graphPairFamily ((G omega).induce (W.U current : Set V))) q b B k t
          (a omega) (E omega) (A omega) i S)
      (⟨∅, restrictTripleSystemTo (W.U current) (available omega)⟩ : GreedyStateOn (W.U current))
    P.probability (fun omega ↦ ¬ (Good omega ∧ IsGraphMixedProductBound (K omega)
      (fun S ↦ mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U current)) S.chosen)
      (G omega) (2 / (t : ℝ≥0) ^ c) (24 / (p ^ 2 * tau * (W.U current).card))
      (ksssSparseGraphProductConstant q (fun d ↦ 9 * 24 ^ d)) delta)) ≤
      (((Icc 4 q).card : ℝ≥0) / (t : ℝ≥0) ^ gapDecay + bandError +
        sourceSparseCrudeFailure q s (Icc 4 q).card t decay Cprior priorCoefficient) / delta := by
  dsimp only
  let J := fun omega ↦ regularizedForbiddenUnion
    (restrictTripleIndexEmbedding (W.U current)
      (Function.Embedding.subtype (fun T ↦ T ∈ available omega))
      (fun T ↦ hsupport omega T.val T.property)) q (fun j ↦ Lstar j omega)
  let E := fun omega ↦ ((graphEdges (G omega)).card : ℝ)
  let A := fun omega ↦ ((available omega).card : ℝ)
  let a := fun omega ↦ regularizedTrajectoryCoefficient (fun j ↦ Lstar j omega) (A omega)
  let S₀ : Omega → GreedyStateOn (W.U current) :=
    fun omega ↦ ⟨∅, restrictTripleSystemTo (W.U current) (available omega)⟩
  let Glocal : Omega → SimpleGraph (W.U current) := fun omega ↦ (G omega).induce (W.U current : Set V)
  let horizon := fun omega ↦ ksssDensityHorizon (E omega) (1 / (t : ℝ) ^ c)
  let Good := fun omega ↦ ∀ j ∈ Icc 4 q, finiteHypergraphDegreeGap (Lstar j omega) ≤ 8192 * t
  let coeff : Omega → ℕ → ℝ := fun _ d ↦ 9 * 24 ^ d
  let eta : Omega → ℝ := fun _ ↦ 1 / (6 * (t : ℝ) ^ ksssPowerErrorExponent b B)
  let K := fun omega ↦ stoppedGreedyStateLaw (horizon omega) (J omega)
    (fun i S ↦ Good omega ∧ KSSSPowerActive (J omega) (graphPairFamily (Glocal omega))
      q b B k t (a omega) (E omega) (A omega) i S) (S₀ omega)
  have hdata := frozen_prepared_current_sparse_data P W current available
    (fun omega ↦ initial omega ∪ later omega) F envelope y z q b B k t Rmin c gapDecay p tau C
    Lstar hsupport hresult hdegree hCcoeff G hG htri hEpos hN hp hp1 htau htau1 hreg
    ht hbinomial horder hscale hEdgeFloor hRatioFloor hC hsmall hcoeff henvelope hpair hconfiguration hcb
  have hInv : ∀ omega, GreedyInvariant (J omega) (S₀ omega) := by
    intro omega
    exact regularizedForbiddenUnion_initial_invariant _ q (fun j ↦ Lstar j omega)
      (fun j hj ↦ (hresult j hj).uniform omega) (S₀ omega).available
  have hEcard : ∀ omega, ((graphEdges (Glocal omega)).card : ℝ) = E omega := by
    intro omega
    dsimp only [Glocal, E]
    rw [card_graphEdges_induce (G omega) (W.U current) (hG omega)]
  have htime : ∀ omega, horizon omega ≤ (W.U current).card ^ 2 := by
    intro omega
    apply (ksssDensityHorizon_power_bounds (E omega) t c (W.U current).card
      (by dsimp only [E]; exact_mod_cast hEpos omega) ?_
      (by exact_mod_cast (show 1 ≤ t by omega))).1
    rw [← hEcard omega]
    have hcard := (card_le_univ (graphEdges (Glocal omega))).trans
      (card_sym2_le_square (W.U current))
    simpa only [Fintype.card_coe, Nat.cast_pow] using
      (show ((graphEdges (Glocal omega)).card : ℝ) ≤ (Fintype.card (W.U current) : ℝ) ^ 2 by
        exact_mod_cast hcard)
  let Index := {j // j ∈ Icc 4 q}
  let : Fintype Index := Fintype.ofFinset (Icc 4 q) (fun _ ↦ Iff.rfl)
  have hIndexcard : Fintype.card Index = (Icc 4 q).card :=
    Fintype.card_of_subtype (Icc 4 q) (fun _ ↦ Iff.rfl)
  have hgeom := fixedRandomAllOrders_current_source_geometry P (W.prefix current)
    (fun omega ↦ Function.Embedding.subtype (fun T ↦ T ∈ available omega))
    (W.U current) q (fun _ ↦ 8192 * t)
    (fun j omega ↦ finiteHypergraphOnSubset (available omega)
      (localForbiddenConfigurations ((Icc 4 q).biUnion F) (available omega) (initial omega ∪ later omega) j))
    Lstar F (terminalRandomConfigurations (W.prefix current)) envelope y z
    (fun _ ↦ (t : ℝ≥0) ^ 4) (fun _ ↦ 1 / (t : ℝ≥0) ^ gapDecay)
    available (fun omega ↦ initial omega ∪ later omega)
    (fun omega T ↦ hsupport omega T.val T.property)
    (fun omega ↦ univ_map_subset_embedding (available omega))
    (fun j _ omega ↦ by rw [localForbiddenAuxiliary_decode]) hresult
  have hprior : P.SupportedOn (fun omega ↦
      Disjoint (mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U current)) (S₀ omega).available)
        (initial omega ∪ later omega) ∧
      ∀ D ∈ mapForbiddenFamily (Function.Embedding.subtype (fun v ↦ v ∈ W.U current)) (J omega),
        D ⊆ mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U current)) (S₀ omega).available ∧
        ∃ j : Index, ∃ H, H ∈ F j.val ∪ envelope j.val ∧ D ⊆ H ∧ H \ D ⊆ initial omega ∪ later omega) := by
    intro omega hmass
    dsimp only [S₀]
    rw [map_restrictTripleSystemTo (W.U current) (available omega) (hsupport omega)]
    refine ⟨hdisjoint omega hmass, ?_⟩
    intro D hD
    obtain ⟨hDA, j, hj, H, hH, hDH, hOld⟩ := hgeom omega D hD
    exact ⟨hDA, ⟨j, hj⟩, H, hH, hDH, hOld⟩
  have hinput : P.probability (fun omega ↦ ¬ Good omega) ≤
      ((Icc 4 q).card : ℝ≥0) / (t : ℝ≥0) ^ gapDecay := by
    have hfail := fixedRandomAllOrders_gap_failure P (W.prefix current)
      (fun omega ↦ Function.Embedding.subtype (fun T ↦ T ∈ available omega)) q
      (fun _ ↦ 8192 * t)
      (fun j omega ↦ finiteHypergraphOnSubset (available omega)
        (localForbiddenConfigurations ((Icc 4 q).biUnion F) (available omega) (initial omega ∪ later omega) j))
      Lstar F (terminalRandomConfigurations (W.prefix current)) envelope y z
      (fun _ ↦ (t : ℝ≥0) ^ 4) (fun _ ↦ 1 / (t : ℝ≥0) ^ gapDecay) hresult
    simpa only [Good, not_forall, not_le, exists_prop, sum_const, nsmul_eq_mul, mul_one_div] using hfail
  have hfailure := hstrong.source_sparse_joint_graph_law_failure_le
    (I := Index) hp1 hCprior hnonempty q b B k t Rmin c s R decay errorExponent zExponent
    horizon J Glocal a coeff E A eta S₀ Good (fun omega hgood ↦ (hdata omega hgood).1)
    (by omega) hscale htime hInv (fun _ ↦ rfl)
    (fun j ↦ F j.val ∪ envelope j.val) (fun j ↦ j.val)
    (fun j ↦ y j.val + (t : ℝ≥0) ^ 4) (fun j ↦ z j.val + 3 * (t : ℝ≥0) ^ 4)
    (fun j ↦ (hresult j.val j.property).spread)
    (fun j ↦ (mem_Icc.mp j.property).2)
    (fun i j hij ↦ by rw [hij]) hprior
    Z priorCoefficient hZ (fun j ↦ hz j.val j.property) hZpower
    (by simpa only [hIndexcard] using hconstant)
    hk hambient hs herrorExponent hbeta (fun omega _ ↦ hEcard omega)
    (fun omega _ ↦ restricted_triangle_edges_induce (G omega) (W.U current) (available omega) (htri omega))
    (fun omega hgood ↦ (hdata omega hgood).2.2.1)
    (fun omega hgood ↦ (hdata omega hgood).2.2.2.1)
    (fun _ _ ↦ by dsimp only [eta]; positivity) (fun _ _ ↦ le_rfl) hcb
    (fun omega hgood ↦ (hdata omega hgood).2.2.2.2.1)
    (((Icc 4 q).card : ℝ≥0) / (t : ℝ≥0) ^ gapDecay) bandError delta
    hdelta hdelta1 herror hinput hbandError
  apply le_trans ?_ (by simpa only [hIndexcard] using hfailure)
  apply P.probability_mono
  intro omega hbad hgood
  apply hbad
  refine ⟨hgood.1, ?_⟩
  have hmapped := hgood.2.of_current_vertices (W.U current)
    (fun S : GreedyStateOn (W.U current) ↦ S.chosen) (G omega) (hG omega)
  apply hmapped.mono_parameters ?_ ?_ le_rfl le_rfl
  · apply Real.toNNReal_le_iff_le_coe.mpr
    simpa only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_pow, NNReal.coe_natCast] using
      (hdata omega hgood.1).2.2.2.2.2.2
  · rw [← Real.toNNReal_div (by dsimp only [E]; positivity)]
    apply Real.toNNReal_le_iff_le_coe.mpr
    simpa only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast] using
      (hdata omega hgood.1).2.2.2.2.2.1

end

end Erdos207
