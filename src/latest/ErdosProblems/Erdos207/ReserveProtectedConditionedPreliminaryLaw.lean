/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryLaw
import ErdosProblems.Erdos207.OuterOnlyConditionedPreliminaryLaw

/-!
# Incidence-conditioned reserve-protected preliminary law

After the reserve-protected preliminary process reaches its active terminal
region, we condition once more on bounded residual internal incidence.  Both
the selected/non-sampled-crossing product law and the fact that the selected
triangles avoid the sampled reserve survive this conditioning.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_conditionedReserveProtectedPreliminaryLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (U : Finset V)
    (reserve : Finset (Sym2 V)) (A P : TripleSystemOn V)
    (hreserve : reserve ⊆ crossingEdges G U)
    (Kpair Kglobal Kinc Delta delta Icut Dcut M supply d : ℕ)
    (hDcut : 0 < Dcut) (hsupplyM : supply ≤ M)
    (h3supply : 3 * supply ≤ delta)
    (alpha eta epsilon : ℝ≥0)
    (hInv : GreedyInvariant F (relativePreliminaryInitialState P A))
    (hGleave : G ≤ leaveGraph P)
    (halive : ∀ e ∈ reserveProtectedOuterEdges G U reserve,
      PairAlive e.toFinset
        (relativePreliminaryInitialState P
          (reserveProtectedOuterAvailable G U reserve A)))
    (hsmall : 3 + Kpair < delta)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta Icut Dcut 0
        (relativePreliminaryInitialState P
          (reserveProtectedOuterAvailable G U reserve A)))
    (hupper : ∀ j S,
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta Icut Dcut j S →
      S.available.card ≤ M)
    (hselected : (n : ℝ≥0) * (Dcut : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - supply : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta Icut Dcut)
        (relativePreliminaryInitialState P
          (reserveProtectedOuterAvailable G U reserve A))).probability
        (fun z ↦ ¬ timedAggregateAveragePairBandActive F Kpair Kglobal
          Kinc Delta delta Icut Dcut z.1.1 z.2) ≤ epsilon)
    (hepsilon : epsilon < 1)
    (htail : residualOuterIncidenceTail V (internalOuterGraph G U) U
      (eta / (1 - epsilon)) (d + 1) < 1) :
    let S₀ := relativePreliminaryInitialState P
      (reserveProtectedOuterAvailable G U reserve A)
    let K₀ := supportedConditionedRelativePreliminaryKernel n F
      Kpair Kglobal Kinc Delta delta Icut Dcut S₀
    let added : FiniteLaw.TimedState (GreedyStateOn V) n →
        TripleSystemOn V := fun z ↦ z.2.chosen \ P
    let residual : FiniteLaw.TimedState (GreedyStateOn V) n →
        Finset (Sym2 V) := fun z ↦
      preliminaryResidualInternalEdges G U z.2.chosen
    let Good : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z ↦
      ∀ v : V,
        (outerIncidentEdges (internalOuterGraph G U) U v ∩
          residual z).card < d + 1
    ∃ hGood : 0 < K₀.probability Good,
      let K := K₀.conditionOn Good hGood
      K.SupportedOn Good ∧
        K.SupportedOn (fun z ↦ RelativeGreedyTrajectory F S₀ z.2) ∧
        (1 - residualOuterIncidenceTail V (internalOuterGraph G U) U
            (eta / (1 - epsilon)) (d + 1) ≤ K₀.probability Good) ∧
        (∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
          K.probability (fun z ↦ Q ⊆ added z ∧
            E ⊆ preliminaryResidualCrossingEdges G U (added z) \
              reserve) ≤
            (alpha / (1 - epsilon) /
                (1 - residualOuterIncidenceTail V
                  (internalOuterGraph G U) U (eta / (1 - epsilon))
                    (d + 1))) ^ Q.card *
              (eta / (1 - epsilon) /
                (1 - residualOuterIncidenceTail V
                  (internalOuterGraph G U) U (eta / (1 - epsilon))
                    (d + 1))) ^ E.card) ∧
        (∀ z, 0 < K.mass z →
          added z ⊆ reserveProtectedAvailable reserve A) ∧
        (∀ z, 0 < K.mass z → ∀ v : V,
          (scheduledEdgesAt
            (preliminaryResidualInternalEdges G U (P ∪ added z)) v).card
              ≤ d) := by
  dsimp only
  let Aprotected := reserveProtectedOuterAvailable G U reserve A
  let S₀ := relativePreliminaryInitialState P Aprotected
  let K₀ := supportedConditionedRelativePreliminaryKernel n F
    Kpair Kglobal Kinc Delta delta Icut Dcut S₀
  let added : FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := fun z ↦ z.2.chosen \ P
  let residual : FiniteLaw.TimedState (GreedyStateOn V) n →
      Finset (Sym2 V) := fun z ↦
    preliminaryResidualInternalEdges G U z.2.chosen
  let Gprotected := reserveProtectedOuterGraph G U reserve
  have houter :=
    supportedConditionedReserveProtectedPreliminaryKernel_outerProductLaw
      n F G U reserve A P Kpair Kglobal Kinc Delta delta Icut Dcut M
      supply hDcut hsupplyM h3supply alpha eta epsilon hInv hGleave
      halive hsmall hactive₀ hupper hselected hsurvived hinactive hepsilon
  have hready := houter.1
  have hmixedInternal : ∀ Q : TripleSystemOn V,
      ∀ E : Finset (Sym2 V),
      K₀.probability (fun z ↦ Q ⊆ added z ∧ E ⊆ residual z) ≤
        (alpha / (1 - epsilon)) ^ Q.card *
          (eta / (1 - epsilon)) ^ E.card := by
    intro Q E
    calc
      K₀.probability (fun z ↦ Q ⊆ added z ∧ E ⊆ residual z) ≤
          K₀.probability (fun z ↦ Q ⊆ added z ∧
            E ⊆ preliminaryResidualOuterEdges Gprotected U z.2.chosen) := by
        apply K₀.probability_mono
        intro z hz
        exact ⟨hz.1, hz.2.trans
          (preliminaryResidualInternalEdges_subset_protectedResidualOuter
            G U reserve z.2.chosen hreserve)⟩
      _ ≤ (alpha / (1 - epsilon)) ^ Q.card *
          (eta / (1 - epsilon)) ^ E.card := by
        simpa only [K₀, S₀, Aprotected, Gprotected, added] using
          houter.2 Q E
  obtain ⟨hGood, hGoodSupport, hlower, hproductInternal⟩ :=
    K₀.exists_conditionedOn_residualOuterIncidence
      (internalOuterGraph G U) U added residual
      (alpha / (1 - epsilon)) (eta / (1 - epsilon)) (d + 1)
      hmixedInternal htail
  let Good : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z ↦
    ∀ v : V,
      (outerIncidentEdges (internalOuterGraph G U) U v ∩
        residual z).card < d + 1
  let K := K₀.conditionOn Good hGood
  have htrajectory₀ : K₀.SupportedOn
      (fun z ↦ RelativeGreedyTrajectory F S₀ z.2) :=
    supportedConditionedRelativePreliminaryKernel_supported_trajectory
      n F Kpair Kglobal Kinc Delta delta Icut Dcut S₀
      (hInv.restrictAvailable
        (reserveProtectedOuterAvailable_subset G U reserve A)) hready
  have htrajectory : K.SupportedOn
      (fun z ↦ RelativeGreedyTrajectory F S₀ z.2) :=
    htrajectory₀.conditionOn hGood
  have hcross₀ :=
    supportedConditionedReserveProtectedPreliminaryKernel_productLaw
      n F G U reserve A P Kpair Kglobal Kinc Delta delta Icut Dcut M
      supply hDcut hsupplyM h3supply alpha eta epsilon hInv hGleave
      halive hsmall hactive₀ hupper hselected hsurvived hinactive hepsilon
  have hcrossRaw : ∀ Q : TripleSystemOn V,
      ∀ E : Finset (Sym2 V),
      K₀.probability (fun z ↦ Good z ∧ Q ⊆ added z ∧
        E ⊆ preliminaryResidualCrossingEdges G U (added z) \ reserve) ≤
          (alpha / (1 - epsilon)) ^ Q.card *
            (eta / (1 - epsilon)) ^ E.card := by
    intro Q E
    apply (K₀.probability_mono fun z hz ↦ ?_).trans
      (by simpa only [K₀, S₀, Aprotected] using hcross₀.2 Q E)
    refine ⟨hz.2.1, ?_⟩
    rw [preliminaryResidualCrossingEdges_sdiff_eq_of_le_leaveGraph
      hGleave]
    exact hz.2.2
  have hcrossConditioned := K₀.conditionOn_probability_mixedProduct_le
    Good added
      (fun z ↦ preliminaryResidualCrossingEdges G U (added z) \ reserve)
      (alpha / (1 - epsilon)) (eta / (1 - epsilon)) hGood hcrossRaw
  have hden : 0 < 1 - residualOuterIncidenceTail V
      (internalOuterGraph G U) U (eta / (1 - epsilon)) (d + 1) :=
    tsub_pos_iff_lt.mpr htail
  have halpha : alpha / (1 - epsilon) / K₀.probability Good ≤
      alpha / (1 - epsilon) /
        (1 - residualOuterIncidenceTail V (internalOuterGraph G U) U
          (eta / (1 - epsilon)) (d + 1)) :=
    div_le_div_of_nonneg_left zero_le hden hlower
  have heta : eta / (1 - epsilon) / K₀.probability Good ≤
      eta / (1 - epsilon) /
        (1 - residualOuterIncidenceTail V (internalOuterGraph G U) U
          (eta / (1 - epsilon)) (d + 1)) :=
    div_le_div_of_nonneg_left zero_le hden hlower
  refine ⟨hGood, hGoodSupport, htrajectory, hlower, ?_, ?_, ?_⟩
  · intro Q E
    exact (hcrossConditioned Q E).trans (by gcongr)
  · intro z hz
    have hnew := (htrajectory z hz).added_subset_available
    exact hnew.trans
      (reserveProtectedOuterAvailable_subset_reserveProtectedAvailable
        G U reserve A)
  · intro z hz v
    have hgood := hGoodSupport z hz v
    have hsched :
        (scheduledEdgesAt
          (preliminaryResidualInternalEdges G U z.2.chosen) v).card ≤ d :=
      Nat.lt_succ_iff.mp
        ((card_le_card
          (scheduledEdgesAt_preliminaryResidualInternalEdges_subset_internalOuterIncidence
            G U z.2.chosen v)).trans_lt (by
              simpa only [residual] using hgood))
    have hunion := (htrajectory z hz).initial_union_added
    have hunion' : P ∪ added z = z.2.chosen := by
      simpa only [S₀, relativePreliminaryInitialState_chosen, added] using
        hunion
    rw [hunion']
    exact hsched

end

end Erdos207
