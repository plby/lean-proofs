/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AggregatePreliminaryGreedyJointLaw
import ErdosProblems.Erdos207.FiniteConditioning

/-!
# Conditioning the preliminary greedy phase on full activity

The additive error in the unconditioned preliminary law is exactly the
probability that the stopped process has left its active region.  On the
active terminal event itself there is no additive loss: the residual
crossing edges agree with the activity-gated tracked edges.  Conditioning on
that event therefore gives a genuine product law.  The single reciprocal
normalizer is absorbed into the positive total number of prescribed
triangles and edges.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The selected/residual product estimate with the terminal active event
included in the event. -/
theorem timedAggregateAveragePairBand_probability_active_selected_residual_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H G : SimpleGraph V) (X : Finset V)
    (Kpair Kglobal Kinc Delta delta I D M k : ℕ)
    (hD : 0 < D) (hkM : k ≤ M) (h3k : 3 * k ≤ delta)
    (alpha eta : ℝ≥0) (S₀ : GreedyStateOn V)
    (hInv₀ : GreedyInvariant F S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hHG : Disjoint H G)
    (hsmall : 3 + Kpair < delta)
    (hchosen₀ : S₀.chosen = ∅)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D 0 S₀)
    (hupper : ∀ j S,
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D j S →
      S.available.card ≤ M)
    (hselected : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) :
    let active := timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    L.probability (fun z ↦ active z.1.1 z.2 ∧ Q ⊆ z.2.chosen ∧
        E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
      alpha ^ Q.card * eta ^ E.card := by
  classical
  dsimp only
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let Inv : GreedyStateOn V → Prop := fun S ↦
    GreedyInvariant F S ∧ OutsideLeavePairsAlive H X S
  let theta : ℝ≥0 :=
    ((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  have hInvStep : ∀ j, j < n → ∀ S, Inv S → active j S →
      (greedyKernel F S).SupportedOn Inv := by
    intro j _hj S hS hact
    have hout := greedyKernel_supported_outsideLeavePairsAlive_of_pairCutoff
      hS.2 hS.1 hact.1.1.2.2.1 hact.1.1.2.2.2.2 hsmall
    intro S' hmass
    exact ⟨greedyKernel_supported hS.1 S' hmass, hout S' hmass⟩
  have hfloorD : ∀ j S, active j S → D ≤ S.available.card := by
    intro j S hact
    exact hact.1.2.2
  have hsupply : ∀ j S, Inv S → active j S →
      ∀ e ∈ greedyUncoveredEdges (crossingEdges G X) S,
        3 * k ≤ (greedyChoicesCoveringEdge S e).card := by
    intro j S hS hact e he
    have hpre := hasPreliminaryEdgeSupply_of_outsideLeavePairsAlive
      hHG hS.2 hact.1.1.2.2.2.2
    exact h3k.trans (hpre e he)
  have hscalar : ∀ j S B, Inv S → active j S →
      B ⊆ greedyUncoveredEdges (crossingEdges G X) S →
      ((S.available.card - B.card * (3 * k) / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card := by
    intro j S B _hS hact _hB
    have hA : 0 < S.available.card := card_pos.mpr hact.1.1.1
    exact preliminary_survival_scalar S.available.card M k B.card
      hA (hupper j S hact) hkM
  by_cases hE : E ⊆ crossingEdges G X
  · have hQ : Disjoint Q S₀.chosen := by
      rw [hchosen₀]
      simp
    have hB : E ⊆ greedyUncoveredEdges (crossingEdges G X) S₀ := by
      rw [greedyUncoveredEdges_eq_self_of_chosen_eq_empty
        (crossingEdges G X) S₀ hchosen₀]
      exact hE
    have htracked : L.probability (fun z ↦
        Q ⊆ z.2.chosen ∧
          E ⊆ timedActiveTrackedUncoveredEdges active
            (crossingEdges G X) z) ≤
        alpha ^ Q.card * eta ^ E.card := by
      exact timedStoppedGreedyProcess_probability_selectedTrackedUncovered_le_product
        n F active (crossingEdges G X) Inv D (3 * k) hD theta alpha eta S₀
          ⟨hInv₀, houtside₀⟩ hactive₀ hInvStep hfloorD hsupply hscalar
          hselected Q E hQ hB (hsurvived Q)
    exact htracked.trans' <| by
      apply L.probability_mono
      intro z hz
      refine ⟨hz.2.1, ?_⟩
      have hact : active (z.1 : ℕ) z.2 := hz.1
      simpa only [timedActiveTrackedUncoveredEdges, if_pos hact,
        greedyUncoveredCrossingEdges_eq_preliminaryResidual] using hz.2.2
  · calc
      L.probability (fun z ↦ active z.1.1 z.2 ∧ Q ⊆ z.2.chosen ∧
          E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
          L.probability (fun _ ↦ False) := by
        apply L.probability_mono
        intro z hz
        exact hE (hz.2.2.trans
          (preliminaryResidualCrossingEdges_subset_crossingEdges
            G X z.2.chosen))
      _ = 0 := L.probability_false
      _ ≤ alpha ^ Q.card * eta ^ E.card := zero_le

/-- After conditioning on terminal activity, the preliminary family has a
pure product selected/residual law.  Each of the two bases absorbs the same
conditioning normalizer; this is deliberately a harmless overestimate when
both prescribed parts are nonempty. -/
theorem conditionedTimedAggregateAveragePairBand_probability_selected_residual_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H G : SimpleGraph V) (X : Finset V)
    (Kpair Kglobal Kinc Delta delta I D M k : ℕ)
    (hD : 0 < D) (hkM : k ≤ M) (h3k : 3 * k ≤ delta)
    (alpha eta : ℝ≥0) (S₀ : GreedyStateOn V)
    (hInv₀ : GreedyInvariant F S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hHG : Disjoint H G)
    (hsmall : 3 + Kpair < delta)
    (hchosen₀ : S₀.chosen = ∅)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D 0 S₀)
    (hupper : ∀ j S,
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D j S →
      S.available.card ≤ M)
    (hselected : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (hGood : 0 <
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D) S₀).probability
        (fun z ↦ timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D z.1.1 z.2))
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) :
    let active := timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    (L.conditionOn (fun z ↦ active z.1.1 z.2) hGood).probability
        (fun z ↦ Q ⊆ z.2.chosen ∧
          E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
      (alpha / L.probability (fun z ↦ active z.1.1 z.2)) ^ Q.card *
        (eta / L.probability (fun z ↦ active z.1.1 z.2)) ^ E.card := by
  classical
  dsimp only
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let Good : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ active z.1.1 z.2
  let Event : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ Q ⊆ z.2.chosen ∧
      E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen
  by_cases hempty : Q = ∅ ∧ E = ∅
  · rcases hempty with ⟨rfl, rfl⟩
    simpa only [card_empty, pow_zero, mul_one, one_mul] using
      (L.conditionOn Good hGood).probability_le_one Event
  · have hmass : 0 < Q.card + E.card := by
      rcases not_and_or.mp hempty with hQ | hE
      · exact Nat.add_pos_left (card_pos.mpr (nonempty_iff_ne_empty.mpr hQ)) _
      · exact Nat.add_pos_right _ (card_pos.mpr (nonempty_iff_ne_empty.mpr hE))
    have hprobOne : L.probability Good ≤ 1 := L.probability_le_one Good
    have hpow : (L.probability Good) ^ (Q.card + E.card) ≤
        L.probability Good :=
      pow_le_of_le_one zero_le hprobOne hmass.ne'
    have hraw : L.probability (fun z ↦ Good z ∧ Event z) ≤
        alpha ^ Q.card * eta ^ E.card := by
      simpa only [Good, Event, and_assoc] using
        timedAggregateAveragePairBand_probability_active_selected_residual_le
          n F H G X Kpair Kglobal Kinc Delta delta I D M k hD hkM h3k
          alpha eta S₀ hInv₀ houtside₀ hHG hsmall hchosen₀ hactive₀
          hupper hselected hsurvived Q E
    calc
      (L.conditionOn Good hGood).probability Event =
          L.probability (fun z ↦ Good z ∧ Event z) /
            L.probability Good := L.conditionOn_probability Good Event hGood
      _ ≤ (alpha ^ Q.card * eta ^ E.card) /
          L.probability Good := by gcongr
      _ ≤ (alpha ^ Q.card * eta ^ E.card) /
          (L.probability Good) ^ (Q.card + E.card) := by
        exact div_le_div_of_nonneg_left zero_le (pow_pos hGood _) hpow
      _ = (alpha / L.probability Good) ^ Q.card *
          (eta / L.probability Good) ^ E.card := by
        rw [pow_add, div_pow, div_pow]
        field_simp

/-- A uniform bound on the probability of stopping outside the active region
turns the preceding conditional estimate into a product law with the explicit
normalizer `1 - epsilon`.  The result also records both the support of the
conditioned law and the lower bound on the conditioning probability. -/
theorem exists_conditionedTimedAggregateAveragePairBand_productLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H G : SimpleGraph V) (X : Finset V)
    (Kpair Kglobal Kinc Delta delta I D M k : ℕ)
    (hD : 0 < D) (hkM : k ≤ M) (h3k : 3 * k ≤ delta)
    (alpha eta epsilon : ℝ≥0) (S₀ : GreedyStateOn V)
    (hInv₀ : GreedyInvariant F S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hHG : Disjoint H G)
    (hsmall : 3 + Kpair < delta)
    (hchosen₀ : S₀.chosen = ∅)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D 0 S₀)
    (hupper : ∀ j S,
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D j S →
      S.available.card ≤ M)
    (hselected : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D) S₀).probability
        (fun z ↦ ¬ timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D z.1.1 z.2) ≤ epsilon)
    (hepsilon : epsilon < 1) :
    let active := timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    let Good : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
      fun z ↦ active z.1.1 z.2
    ∃ hGood : 0 < L.probability Good,
      (∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
        (L.conditionOn Good hGood).probability
            (fun z ↦ Q ⊆ z.2.chosen ∧
              E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
          (alpha / (1 - epsilon)) ^ Q.card *
            (eta / (1 - epsilon)) ^ E.card) ∧
      (L.conditionOn Good hGood).SupportedOn Good ∧
      1 - epsilon ≤ L.probability Good := by
  classical
  dsimp only
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let Good : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ active z.1.1 z.2
  have hlower : 1 - epsilon ≤ L.probability Good := by
    rw [L.probability_not Good] at hinactive
    calc
      1 - epsilon ≤ 1 - (1 - L.probability Good) :=
        tsub_le_tsub_left hinactive 1
      _ = L.probability Good :=
        tsub_tsub_cancel_of_le (L.probability_le_one Good)
  have hGood : 0 < L.probability Good :=
    (tsub_pos_iff_lt.mpr hepsilon).trans_le hlower
  refine ⟨hGood, ?_, L.conditionOn_supported Good hGood, hlower⟩
  intro Q E
  have hraw :=
    conditionedTimedAggregateAveragePairBand_probability_selected_residual_le
      n F H G X Kpair Kglobal Kinc Delta delta I D M k hD hkM h3k
      alpha eta S₀ hInv₀ houtside₀ hHG hsmall hchosen₀ hactive₀ hupper
      hselected hsurvived hGood Q E
  have hden : 0 < 1 - epsilon := tsub_pos_iff_lt.mpr hepsilon
  have halpha : alpha / L.probability Good ≤ alpha / (1 - epsilon) := by
    exact div_le_div_of_nonneg_left zero_le hden hlower
  have heta : eta / L.probability Good ≤ eta / (1 - epsilon) := by
    exact div_le_div_of_nonneg_left zero_le hden hlower
  calc
    (L.conditionOn Good hGood).probability
        (fun z ↦ Q ⊆ z.2.chosen ∧
          E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
        (alpha / L.probability Good) ^ Q.card *
          (eta / L.probability Good) ^ E.card := by
      simpa only [L, Good, active] using hraw
    _ ≤ (alpha / (1 - epsilon)) ^ Q.card *
        (eta / (1 - epsilon)) ^ E.card := by
      gcongr

/-- Relative form of the active selected/residual estimate.  The preliminary
process may start from an old packing; only triangles newly selected beyond
that initial packing are charged.  The stage graph being contained in the
initial leave supplies the initially-uncovered crossing-edge condition. -/
theorem timedAggregateAveragePairBand_probability_active_newSelected_residual_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H G : SimpleGraph V) (X : Finset V)
    (Kpair Kglobal Kinc Delta delta I D M k : ℕ)
    (hD : 0 < D) (hkM : k ≤ M) (h3k : 3 * k ≤ delta)
    (alpha eta : ℝ≥0) (S₀ : GreedyStateOn V)
    (hInv₀ : GreedyInvariant F S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hHG : Disjoint H G)
    (hGleave : G ≤ leaveGraph S₀.chosen)
    (hsmall : 3 + Kpair < delta)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D 0 S₀)
    (hupper : ∀ j S,
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D j S →
      S.available.card ≤ M)
    (hselected : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) :
    let active := timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    L.probability (fun z ↦ active z.1.1 z.2 ∧
        Q ⊆ z.2.chosen \ S₀.chosen ∧
        E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
      alpha ^ Q.card * eta ^ E.card := by
  classical
  dsimp only
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let Inv : GreedyStateOn V → Prop := fun S ↦
    GreedyInvariant F S ∧ OutsideLeavePairsAlive H X S
  let theta : ℝ≥0 :=
    ((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  have hInvStep : ∀ j, j < n → ∀ S, Inv S → active j S →
      (greedyKernel F S).SupportedOn Inv := by
    intro j _hj S hS hact
    have hout := greedyKernel_supported_outsideLeavePairsAlive_of_pairCutoff
      hS.2 hS.1 hact.1.1.2.2.1 hact.1.1.2.2.2.2 hsmall
    intro S' hmass
    exact ⟨greedyKernel_supported hS.1 S' hmass, hout S' hmass⟩
  have hfloorD : ∀ j S, active j S → D ≤ S.available.card := by
    intro j S hact
    exact hact.1.2.2
  have hsupply : ∀ j S, Inv S → active j S →
      ∀ e ∈ greedyUncoveredEdges (crossingEdges G X) S,
        3 * k ≤ (greedyChoicesCoveringEdge S e).card := by
    intro j S hS hact e he
    have hpre := hasPreliminaryEdgeSupply_of_outsideLeavePairsAlive
      hHG hS.2 hact.1.1.2.2.2.2
    exact h3k.trans (hpre e he)
  have hscalar : ∀ j S B, Inv S → active j S →
      B ⊆ greedyUncoveredEdges (crossingEdges G X) S →
      ((S.available.card - B.card * (3 * k) / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card := by
    intro j S B _hS hact _hB
    have hA : 0 < S.available.card := card_pos.mpr hact.1.1.1
    exact preliminary_survival_scalar S.available.card M k B.card
      hA (hupper j S hact) hkM
  by_cases hQ : Disjoint Q S₀.chosen
  · by_cases hE : E ⊆ crossingEdges G X
    · have hB : E ⊆ greedyUncoveredEdges (crossingEdges G X) S₀ := by
        intro e he
        have heCross := hE he
        rw [greedyUncoveredEdges, mem_sdiff]
        refine ⟨heCross, ?_⟩
        induction e using Sym2.inductionOn with
        | _ u v =>
            have heGset : s(u, v) ∈ G.edgeSet :=
              (mem_crossingEdges_iff.mp heCross).1
            have hGadj : G.Adj u v := by
              change G.Adj u v at heGset
              exact heGset
            have hleave := leaveGraph_adj.mp (hGleave hGadj)
            intro hcovered
            exact hleave.2 (mem_graphEdges_iff.mp hcovered)
      have htracked : L.probability (fun z ↦
          Q ⊆ z.2.chosen ∧
            E ⊆ timedActiveTrackedUncoveredEdges active
              (crossingEdges G X) z) ≤
          alpha ^ Q.card * eta ^ E.card := by
        exact timedStoppedGreedyProcess_probability_selectedTrackedUncovered_le_product
          n F active (crossingEdges G X) Inv D (3 * k) hD theta alpha eta S₀
            ⟨hInv₀, houtside₀⟩ hactive₀ hInvStep hfloorD hsupply hscalar
            hselected Q E hQ hB (hsurvived Q)
      exact htracked.trans' <| by
        apply L.probability_mono
        intro z hz
        refine ⟨hz.2.1.trans sdiff_subset, ?_⟩
        have hact : active (z.1 : ℕ) z.2 := hz.1
        simpa only [timedActiveTrackedUncoveredEdges, if_pos hact,
          greedyUncoveredCrossingEdges_eq_preliminaryResidual] using hz.2.2
    · calc
        L.probability (fun z ↦ active z.1.1 z.2 ∧
            Q ⊆ z.2.chosen \ S₀.chosen ∧
            E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
            L.probability (fun _ ↦ False) := by
          apply L.probability_mono
          intro z hz
          exact hE (hz.2.2.trans
            (preliminaryResidualCrossingEdges_subset_crossingEdges
              G X z.2.chosen))
        _ = 0 := L.probability_false
        _ ≤ alpha ^ Q.card * eta ^ E.card := zero_le
  · have himpossible :
        ∀ z : FiniteLaw.TimedState (GreedyStateOn V) n,
        ¬(Q ⊆ z.2.chosen \ S₀.chosen) := by
      intro z hsub
      apply hQ
      rw [Finset.disjoint_left]
      intro T hTQ hT₀
      exact (mem_sdiff.mp (hsub hTQ)).2 hT₀
    calc
      L.probability (fun z ↦ active z.1.1 z.2 ∧
          Q ⊆ z.2.chosen \ S₀.chosen ∧
          E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
          L.probability (fun _ ↦ False) := by
        apply L.probability_mono
        intro z hz
        exact himpossible z hz.2.1
      _ = 0 := L.probability_false
      _ ≤ alpha ^ Q.card * eta ^ E.card := zero_le

/-- Conditioning the relative preliminary process on terminal activity gives
the pure product law for the newly selected family. -/
theorem conditionedTimedAggregateAveragePairBand_probability_newSelected_residual_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H G : SimpleGraph V) (X : Finset V)
    (Kpair Kglobal Kinc Delta delta I D M k : ℕ)
    (hD : 0 < D) (hkM : k ≤ M) (h3k : 3 * k ≤ delta)
    (alpha eta : ℝ≥0) (S₀ : GreedyStateOn V)
    (hInv₀ : GreedyInvariant F S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hHG : Disjoint H G)
    (hGleave : G ≤ leaveGraph S₀.chosen)
    (hsmall : 3 + Kpair < delta)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D 0 S₀)
    (hupper : ∀ j S,
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D j S →
      S.available.card ≤ M)
    (hselected : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (hGood : 0 <
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D) S₀).probability
        (fun z ↦ timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D z.1.1 z.2))
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) :
    let active := timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    (L.conditionOn (fun z ↦ active z.1.1 z.2) hGood).probability
        (fun z ↦ Q ⊆ z.2.chosen \ S₀.chosen ∧
          E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
      (alpha / L.probability (fun z ↦ active z.1.1 z.2)) ^ Q.card *
        (eta / L.probability (fun z ↦ active z.1.1 z.2)) ^ E.card := by
  classical
  dsimp only
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let Good : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ active z.1.1 z.2
  let Event : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ Q ⊆ z.2.chosen \ S₀.chosen ∧
      E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen
  by_cases hempty : Q = ∅ ∧ E = ∅
  · rcases hempty with ⟨rfl, rfl⟩
    simpa only [card_empty, pow_zero, mul_one, one_mul] using
      (L.conditionOn Good hGood).probability_le_one Event
  · have hmass : 0 < Q.card + E.card := by
      rcases not_and_or.mp hempty with hQ | hE
      · exact Nat.add_pos_left (card_pos.mpr (nonempty_iff_ne_empty.mpr hQ)) _
      · exact Nat.add_pos_right _ (card_pos.mpr (nonempty_iff_ne_empty.mpr hE))
    have hpow : (L.probability Good) ^ (Q.card + E.card) ≤
        L.probability Good :=
      pow_le_of_le_one zero_le (L.probability_le_one Good) hmass.ne'
    have hraw : L.probability (fun z ↦ Good z ∧ Event z) ≤
        alpha ^ Q.card * eta ^ E.card := by
      simpa only [Good, Event, and_assoc] using
        timedAggregateAveragePairBand_probability_active_newSelected_residual_le
          n F H G X Kpair Kglobal Kinc Delta delta I D M k hD hkM h3k
          alpha eta S₀ hInv₀ houtside₀ hHG hGleave hsmall hactive₀
          hupper hselected hsurvived Q E
    calc
      (L.conditionOn Good hGood).probability Event =
          L.probability (fun z ↦ Good z ∧ Event z) /
            L.probability Good := L.conditionOn_probability Good Event hGood
      _ ≤ (alpha ^ Q.card * eta ^ E.card) /
          L.probability Good := by gcongr
      _ ≤ (alpha ^ Q.card * eta ^ E.card) /
          (L.probability Good) ^ (Q.card + E.card) := by
        exact div_le_div_of_nonneg_left zero_le (pow_pos hGood _) hpow
      _ = (alpha / L.probability Good) ^ Q.card *
          (eta / L.probability Good) ^ E.card := by
        rw [pow_add, div_pow, div_pow]
        field_simp

/-- The relative preliminary law with an explicit uniform conditioning loss.
This is the stagewise form used by the vortex iteration: the input state may
already contain the accumulated packing, while the output variable records
only the newly chosen triples. -/
theorem exists_conditionedTimedAggregateAveragePairBand_newSelected_productLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H G : SimpleGraph V) (X : Finset V)
    (Kpair Kglobal Kinc Delta delta I D M k : ℕ)
    (hD : 0 < D) (hkM : k ≤ M) (h3k : 3 * k ≤ delta)
    (alpha eta epsilon : ℝ≥0) (S₀ : GreedyStateOn V)
    (hInv₀ : GreedyInvariant F S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hHG : Disjoint H G)
    (hGleave : G ≤ leaveGraph S₀.chosen)
    (hsmall : 3 + Kpair < delta)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D 0 S₀)
    (hupper : ∀ j S,
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D j S →
      S.available.card ≤ M)
    (hselected : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D) S₀).probability
        (fun z ↦ ¬ timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D z.1.1 z.2) ≤ epsilon)
    (hepsilon : epsilon < 1) :
    let active := timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    let Good : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
      fun z ↦ active z.1.1 z.2
    ∃ hGood : 0 < L.probability Good,
      (∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
        (L.conditionOn Good hGood).probability
            (fun z ↦ Q ⊆ z.2.chosen \ S₀.chosen ∧
              E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
          (alpha / (1 - epsilon)) ^ Q.card *
            (eta / (1 - epsilon)) ^ E.card) ∧
      (L.conditionOn Good hGood).SupportedOn Good ∧
      1 - epsilon ≤ L.probability Good := by
  classical
  dsimp only
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let Good : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ active z.1.1 z.2
  have hlower : 1 - epsilon ≤ L.probability Good := by
    rw [L.probability_not Good] at hinactive
    calc
      1 - epsilon ≤ 1 - (1 - L.probability Good) :=
        tsub_le_tsub_left hinactive 1
      _ = L.probability Good :=
        tsub_tsub_cancel_of_le (L.probability_le_one Good)
  have hGood : 0 < L.probability Good :=
    (tsub_pos_iff_lt.mpr hepsilon).trans_le hlower
  refine ⟨hGood, ?_, L.conditionOn_supported Good hGood, hlower⟩
  intro Q E
  have hraw :=
    conditionedTimedAggregateAveragePairBand_probability_newSelected_residual_le
      n F H G X Kpair Kglobal Kinc Delta delta I D M k hD hkM h3k
      alpha eta S₀ hInv₀ houtside₀ hHG hGleave hsmall hactive₀ hupper
      hselected hsurvived hGood Q E
  have hden : 0 < 1 - epsilon := tsub_pos_iff_lt.mpr hepsilon
  have halpha : alpha / L.probability Good ≤ alpha / (1 - epsilon) := by
    exact div_le_div_of_nonneg_left zero_le hden hlower
  have heta : eta / L.probability Good ≤ eta / (1 - epsilon) := by
    exact div_le_div_of_nonneg_left zero_le hden hlower
  calc
    (L.conditionOn Good hGood).probability
        (fun z ↦ Q ⊆ z.2.chosen \ S₀.chosen ∧
          E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
        (alpha / L.probability Good) ^ Q.card *
          (eta / L.probability Good) ^ E.card := by
      simpa only [L, Good, active] using hraw
    _ ≤ (alpha / (1 - epsilon)) ^ Q.card *
        (eta / (1 - epsilon)) ^ E.card := by
      gcongr

end

end Erdos207
