/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OuterOnlyPreliminaryGeometry
import ErdosProblems.Erdos207.PreliminaryAugmentedReserveNumeric

/-!
# The conditioned outer-only preliminary law

The outer-only preliminary process is first conditioned on reaching its
terminal active region and then on leaving bounded internal residual degree.
The resulting law retains the selected-family product estimate.  Crossing
residual constraints cost no additional factor: forgetting such a constraint
only enlarges the event, so reserve density one is sufficient for the
augmented-reserve update.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The one-point empty law has the exact reserve-aware strong estimate when
the reserve density is one. -/
theorem reserveStronglyWellDistributed_pure_empty
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) :
    IsReserveStronglyWellDistributed (FiniteLaw.pure PUnit.unit) W k
      (fun _ : PUnit ↦ (∅ : TripleSystemOn V))
      (fun _ : PUnit ↦ (∅ : TripleSystemOn V))
      (fun _ : PUnit ↦ (∅ : Finset (Sym2 V))) 1 1 1 0 := by
  classical
  intro Ifix Dfix Efix Rfix _hdisjoint
  rw [FiniteLaw.probability_pure]
  by_cases hevent : ReserveStrongDistributionEvent
      (fun _ : PUnit ↦ (∅ : TripleSystemOn V))
      (fun _ : PUnit ↦ (∅ : TripleSystemOn V))
      (fun _ : PUnit ↦ (∅ : Finset (Sym2 V)))
      Ifix Dfix Efix Rfix PUnit.unit
  · have hIfix : Ifix = ∅ := subset_empty.mp hevent.1.1
    have hDfix : Dfix = ∅ := subset_empty.mp hevent.1.2.1
    have hRfix : Rfix = ∅ := subset_empty.mp hevent.2
    subst Ifix
    subst Dfix
    subst Rfix
    rw [if_pos hevent]
    simp
  · rw [if_neg hevent]
    exact bot_le

/-- Every edge scheduled from an internal residual family is counted by the
outer-incidence star of the graph consisting of all internal outer edges. -/
lemma scheduledEdgesAt_preliminaryResidualInternalEdges_subset_internalOuterIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (P : TripleSystemOn V) (v : V) :
    scheduledEdgesAt (preliminaryResidualInternalEdges G U P) v ⊆
      outerIncidentEdges (internalOuterGraph G U) U v ∩
        preliminaryResidualInternalEdges G U P := by
  intro e he
  have hs := mem_scheduledEdgesAt_iff.mp he
  refine mem_inter.mpr ⟨?_, hs.1⟩
  rw [outerIncidentEdges_internalOuterGraph]
  exact mem_scheduledEdgesAt_iff.mpr
    ⟨preliminaryResidualInternalEdges_subset_internalOuterEdges G U P hs.1,
      hs.2⟩

/-- Conditioning the outer-only preliminary law on bounded internal residual
incidence preserves a pure selected/internal-residual product estimate.  It
also supplies all geometric support facts needed by the subsequent internal
cover. -/
theorem exists_conditionedOuterOnlyPreliminaryLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (A P : TripleSystemOn V)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    {p etaTypical xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p etaTypical xi h)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h)
    (hgap : (((W.U i.succ).card + 2 : ℕ) : ℝ≥0) <
      (1 - xi) * (p ^ 2 * etaTypical * (W.U i.castSucc).card))
    (hInv : GreedyInvariant F (relativePreliminaryInitialState P A))
    (hGleave : G ≤ leaveGraph P)
    (Kpair Kglobal Kinc Delta delta Icut Dcut M supply d : ℕ)
    (hDcut : 0 < Dcut) (hsupplyM : supply ≤ M)
    (h3supply : 3 * supply ≤ delta)
    (alpha eta epsilon : ℝ≥0)
    (hsmall : 3 + Kpair < delta)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta Icut Dcut 0
        (relativePreliminaryInitialState P
          (outerOnlyAvailable (W.U i.succ) A)))
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
          (outerOnlyAvailable (W.U i.succ) A))).probability
        (fun z ↦ ¬ timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta Icut Dcut z.1.1 z.2) ≤ epsilon)
    (hepsilon : epsilon < 1)
    (htail : residualOuterIncidenceTail V
      (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
      (eta / (1 - epsilon)) (d + 1) < 1) :
    let S₀ := relativePreliminaryInitialState P
      (outerOnlyAvailable (W.U i.succ) A)
    let K₀ := supportedConditionedRelativePreliminaryKernel n F
      Kpair Kglobal Kinc Delta delta Icut Dcut S₀
    let added : FiniteLaw.TimedState (GreedyStateOn V) n →
        TripleSystemOn V := fun z ↦ z.2.chosen \ P
    let residual : FiniteLaw.TimedState (GreedyStateOn V) n →
        Finset (Sym2 V) := fun z ↦
      preliminaryResidualInternalEdges G (W.U i.succ) z.2.chosen
    let Good : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z ↦
      ∀ v : V,
        (outerIncidentEdges (internalOuterGraph G (W.U i.succ))
          (W.U i.succ) v ∩ residual z).card < d + 1
    ∃ hGood : 0 < K₀.probability Good,
      let K := K₀.conditionOn Good hGood
      K.SupportedOn Good ∧
        K.SupportedOn (fun z ↦ RelativeGreedyTrajectory F S₀ z.2) ∧
        (1 - residualOuterIncidenceTail V
            (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
            (eta / (1 - epsilon)) (d + 1) ≤ K₀.probability Good) ∧
        (∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
          K.probability (fun z ↦ Q ⊆ added z ∧ E ⊆ residual z) ≤
            (alpha / (1 - epsilon) /
                (1 - residualOuterIncidenceTail V
                  (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
                  (eta / (1 - epsilon)) (d + 1))) ^ Q.card *
              (eta / (1 - epsilon) /
                (1 - residualOuterIncidenceTail V
                  (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
                  (eta / (1 - epsilon)) (d + 1))) ^ E.card) ∧
        (∀ z, 0 < K.mass z → TrianglesDisjointFrom (W.U i.succ) (added z)) ∧
        (∀ z, 0 < K.mass z → ∀ v : V,
          (scheduledEdgesAt (residual z) v).card ≤ d) := by
  dsimp only
  let S₀ := relativePreliminaryInitialState P
    (outerOnlyAvailable (W.U i.succ) A)
  let K₀ := supportedConditionedRelativePreliminaryKernel n F
    Kpair Kglobal Kinc Delta delta Icut Dcut S₀
  let added : FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := fun z ↦ z.2.chosen \ P
  let residual : FiniteLaw.TimedState (GreedyStateOn V) n →
      Finset (Sym2 V) := fun z ↦
    preliminaryResidualInternalEdges G (W.U i.succ) z.2.chosen
  have hbase := supportedConditionedOuterOnlyPreliminaryKernel_internalProductLaw
    n F G A P i hstage htyp hGsupp hh hgap hInv hGleave
      Kpair Kglobal Kinc Delta delta Icut Dcut M supply hDcut hsupplyM
      h3supply alpha eta epsilon hsmall hactive₀ hupper hselected
      hsurvived hinactive hepsilon
  have hready := hbase.1
  have hmixed : ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
      K₀.probability (fun z ↦ Q ⊆ added z ∧ E ⊆ residual z) ≤
        (alpha / (1 - epsilon)) ^ Q.card *
          (eta / (1 - epsilon)) ^ E.card := by
    simpa only [K₀, S₀, added, residual] using hbase.2
  obtain ⟨hGood, hGoodSupport, hlower, hproduct⟩ :=
    K₀.exists_conditionedOn_residualOuterIncidence
      (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
      added residual (alpha / (1 - epsilon)) (eta / (1 - epsilon))
      (d + 1) hmixed htail
  refine ⟨hGood, hGoodSupport, ?_, hlower, hproduct, ?_, ?_⟩
  · exact (supportedConditionedRelativePreliminaryKernel_supported_trajectory
      n F Kpair Kglobal Kinc Delta delta Icut Dcut S₀
      (hInv.restrictAvailable (outerOnlyAvailable_subset _ _)) hready).conditionOn hGood
  · intro z hz
    have htrajectory :=
      (supportedConditionedRelativePreliminaryKernel_supported_trajectory
        n F Kpair Kglobal Kinc Delta delta Icut Dcut S₀
        (hInv.restrictAvailable (outerOnlyAvailable_subset _ _)) hready).conditionOn hGood z hz
    intro T hT
    exact (mem_outerOnlyAvailable_iff.mp
      (htrajectory.added_subset_available hT)).2
  · intro z hz v
    have hgood := hGoodSupport z hz v
    apply Nat.lt_succ_iff.mp
    exact (card_le_card
      (scheduledEdgesAt_preliminaryResidualInternalEdges_subset_internalOuterIncidence
        G (W.U i.succ) z.2.chosen v)).trans_lt (by
          simpa only [residual] using hgood)

end

end Erdos207
