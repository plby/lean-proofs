/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveProtectedConditionedPreliminaryLaw

/-!
# Total reserve-protected preliminary kernel

The active-conditioned preliminary kernel is conditioned a second time on
bounded residual internal incidence.  This file totalizes that second
conditioning, so it can be used as a state-dependent kernel in a joint law.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def reserveProtectedPreliminaryIncidenceGood
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} (G : SimpleGraph V) (U : Finset V) (d : ℕ)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n) : Prop :=
  ∀ v : V,
    (outerIncidentEdges (internalOuterGraph G U) U v ∩
      preliminaryResidualInternalEdges G U z.2.chosen).card < d + 1

/-- Use the incidence-conditioned law when its event has positive mass and
the already active-conditioned base law otherwise. -/
def reserveProtectedConditionedPreliminaryKernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (U : Finset V)
    (reserve : Finset (Sym2 V)) (A P : TripleSystemOn V)
    (Kpair Kglobal Kinc Delta delta Icut Dcut d : ℕ) :
    FiniteLaw (FiniteLaw.TimedState (GreedyStateOn V) n) := by
  classical
  let S₀ := relativePreliminaryInitialState P
    (reserveProtectedOuterAvailable G U reserve A)
  let K₀ := supportedConditionedRelativePreliminaryKernel n F
    Kpair Kglobal Kinc Delta delta Icut Dcut S₀
  let Good : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z ↦
    ∀ v : V, (outerIncidentEdges (internalOuterGraph G U) U v ∩
      preliminaryResidualInternalEdges G U z.2.chosen).card < d + 1
  if h : 0 < K₀.probability Good then
    exact K₀.conditionOn Good h
  else
    exact K₀

/-- Neither conditioning step changes the clock bound: the genuinely new
preliminary family has cardinality at most the process horizon. -/
theorem reserveProtectedConditionedPreliminaryKernel_supported_added_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (U : Finset V)
    (reserve : Finset (Sym2 V)) (A P : TripleSystemOn V)
    (Kpair Kglobal Kinc Delta delta Icut Dcut d : ℕ)
    (hInv : GreedyInvariant F (relativePreliminaryInitialState P A)) :
    (reserveProtectedConditionedPreliminaryKernel n F G U reserve A P
      Kpair Kglobal Kinc Delta delta Icut Dcut d).SupportedOn
        (fun z ↦ (z.2.chosen \ P).card ≤ n) := by
  classical
  let S₀ := relativePreliminaryInitialState P
    (reserveProtectedOuterAvailable G U reserve A)
  let K₀ := supportedConditionedRelativePreliminaryKernel n F
    Kpair Kglobal Kinc Delta delta Icut Dcut S₀
  let Good : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z ↦
    ∀ v : V, (outerIncidentEdges (internalOuterGraph G U) U v ∩
      preliminaryResidualInternalEdges G U z.2.chosen).card < d + 1
  have hInv₀ : GreedyInvariant F S₀ := by
    exact hInv.restrictAvailable
      (reserveProtectedOuterAvailable_subset G U reserve A)
  have hbase : K₀.SupportedOn (fun z ↦ (z.2.chosen \ P).card ≤ n) := by
    simpa only [K₀, S₀, relativePreliminaryInitialState_chosen] using
      supportedConditionedRelativePreliminaryKernel_supported_added_card_le
        n F Kpair Kglobal Kinc Delta delta Icut Dcut S₀ hInv₀
  by_cases hgood : 0 < K₀.probability Good
  · rw [reserveProtectedConditionedPreliminaryKernel, dif_pos hgood]
    exact hbase.conditionOn hgood
  · rw [reserveProtectedConditionedPreliminaryKernel, dif_neg hgood]
    exact hbase

/-- All conclusions of the two conditioning steps, now for the total kernel.
-/
theorem reserveProtectedConditionedPreliminaryKernel_spec
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
    let K := reserveProtectedConditionedPreliminaryKernel n F G U reserve
      A P Kpair Kglobal Kinc Delta delta Icut Dcut d
    let added : FiniteLaw.TimedState (GreedyStateOn V) n →
        TripleSystemOn V := fun z ↦ z.2.chosen \ P
    K.SupportedOn (fun z ↦ ∀ v : V,
        (outerIncidentEdges (internalOuterGraph G U) U v ∩
          preliminaryResidualInternalEdges G U z.2.chosen).card < d + 1) ∧
      K.SupportedOn (fun z ↦ RelativeGreedyTrajectory F S₀ z.2) ∧
      (∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
        K.probability (fun z ↦ Q ⊆ added z ∧
          E ⊆ preliminaryResidualCrossingEdges G U (added z) \ reserve) ≤
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
          (preliminaryResidualInternalEdges G U (P ∪ added z)) v).card ≤
            d) := by
  dsimp only
  let S₀ := relativePreliminaryInitialState P
    (reserveProtectedOuterAvailable G U reserve A)
  let K₀ := supportedConditionedRelativePreliminaryKernel n F
    Kpair Kglobal Kinc Delta delta Icut Dcut S₀
  let Good : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z ↦
    ∀ v : V, (outerIncidentEdges (internalOuterGraph G U) U v ∩
      preliminaryResidualInternalEdges G U z.2.chosen).card < d + 1
  let added : FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := fun z ↦ z.2.chosen \ P
  obtain ⟨hGood, hGoodSupport, htrajectory, _hlower, hproduct,
      hprotected, hincidence⟩ :=
    exists_conditionedReserveProtectedPreliminaryLaw n F G U reserve A P
      hreserve Kpair Kglobal Kinc Delta delta Icut Dcut M supply d
      hDcut hsupplyM h3supply alpha eta epsilon hInv hGleave halive
      hsmall hactive₀ hupper hselected hsurvived hinactive hepsilon htail
  have hGood' : 0 < K₀.probability Good := by
    simpa [K₀, S₀, Good,
      reserveProtectedPreliminaryIncidenceGood] using hGood
  rw [reserveProtectedConditionedPreliminaryKernel, dif_pos hGood']
  exact ⟨by simpa [K₀, S₀, Good,
      reserveProtectedPreliminaryIncidenceGood] using hGoodSupport,
    by simpa [K₀, S₀, Good,
      reserveProtectedPreliminaryIncidenceGood] using htrajectory,
    by simpa [K₀, S₀, Good, added,
      reserveProtectedPreliminaryIncidenceGood] using hproduct,
    by simpa [K₀, S₀, Good, added,
      reserveProtectedPreliminaryIncidenceGood] using hprotected,
    by simpa [K₀, S₀, Good, added,
      reserveProtectedPreliminaryIncidenceGood] using hincidence⟩

/-- The same total twice-conditioned preliminary kernel retains the stronger
mixed product law for every residual edge of the protected outer graph.  The
older specification above only exports crossing residual edges; internal
residual edges are also needed when the following internal phase is charged
jointly with the preliminary phase. -/
theorem reserveProtectedConditionedPreliminaryKernel_outerProduct
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
    let K := reserveProtectedConditionedPreliminaryKernel n F G U reserve
      A P Kpair Kglobal Kinc Delta delta Icut Dcut d
    let added : FiniteLaw.TimedState (GreedyStateOn V) n →
        TripleSystemOn V := fun z ↦ z.2.chosen \ P
    ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
      K.probability (fun z ↦ Q ⊆ added z ∧
        E ⊆ preliminaryResidualOuterEdges
          (reserveProtectedOuterGraph G U reserve) U z.2.chosen) ≤
        (alpha / (1 - epsilon) /
            (1 - residualOuterIncidenceTail V
              (internalOuterGraph G U) U (eta / (1 - epsilon))
                (d + 1))) ^ Q.card *
          (eta / (1 - epsilon) /
            (1 - residualOuterIncidenceTail V
              (internalOuterGraph G U) U (eta / (1 - epsilon))
                (d + 1))) ^ E.card := by
  dsimp only
  let S₀ := relativePreliminaryInitialState P
    (reserveProtectedOuterAvailable G U reserve A)
  let K₀ := supportedConditionedRelativePreliminaryKernel n F
    Kpair Kglobal Kinc Delta delta Icut Dcut S₀
  let Good : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z ↦
    ∀ v : V, (outerIncidentEdges (internalOuterGraph G U) U v ∩
      preliminaryResidualInternalEdges G U z.2.chosen).card < d + 1
  let added : FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := fun z ↦ z.2.chosen \ P
  obtain ⟨hGood, _hGoodSupport, _htrajectory, hlower, _hproduct,
      _hprotected, _hincidence⟩ :=
    exists_conditionedReserveProtectedPreliminaryLaw n F G U reserve A P
      hreserve Kpair Kglobal Kinc Delta delta Icut Dcut M supply d
      hDcut hsupplyM h3supply alpha eta epsilon hInv hGleave halive
      hsmall hactive₀ hupper hselected hsurvived hinactive hepsilon htail
  have houter :=
    supportedConditionedReserveProtectedPreliminaryKernel_outerProductLaw
      n F G U reserve A P Kpair Kglobal Kinc Delta delta Icut Dcut M
      supply hDcut hsupplyM h3supply alpha eta epsilon hInv hGleave
      halive hsmall hactive₀ hupper hselected hsurvived hinactive hepsilon
  have hGood' : 0 < K₀.probability Good := by
    simpa [K₀, S₀, Good, reserveProtectedPreliminaryIncidenceGood] using hGood
  have hraw : ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
      K₀.probability (fun z ↦ Good z ∧ Q ⊆ added z ∧
        E ⊆ preliminaryResidualOuterEdges
          (reserveProtectedOuterGraph G U reserve) U z.2.chosen) ≤
        (alpha / (1 - epsilon)) ^ Q.card *
          (eta / (1 - epsilon)) ^ E.card := by
    intro Q E
    calc
      K₀.probability (fun z ↦ Good z ∧ Q ⊆ added z ∧
          E ⊆ preliminaryResidualOuterEdges
            (reserveProtectedOuterGraph G U reserve) U z.2.chosen) ≤
          K₀.probability (fun z ↦ Q ⊆ added z ∧
            E ⊆ preliminaryResidualOuterEdges
              (reserveProtectedOuterGraph G U reserve) U z.2.chosen) := by
        apply K₀.probability_mono
        intro z hz
        exact ⟨hz.2.1, hz.2.2⟩
      _ ≤ (alpha / (1 - epsilon)) ^ Q.card *
          (eta / (1 - epsilon)) ^ E.card := by
        simpa only [K₀, S₀, added,
          relativePreliminaryInitialState_chosen] using houter.2 Q E
  have hconditioned := K₀.conditionOn_probability_mixedProduct_le
    Good added
      (fun z ↦ preliminaryResidualOuterEdges
        (reserveProtectedOuterGraph G U reserve) U z.2.chosen)
      (alpha / (1 - epsilon)) (eta / (1 - epsilon)) hGood' hraw
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
  rw [reserveProtectedConditionedPreliminaryKernel, dif_pos hGood']
  intro Q E
  exact (hconditioned Q E).trans (by gcongr)

end

end Erdos207
