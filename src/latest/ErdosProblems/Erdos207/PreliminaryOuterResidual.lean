/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AggregatePreliminaryGreedyJointLaw
import ErdosProblems.Erdos207.FiniteConditioning

/-!
# Residual outer edges after the preliminary cover

The preliminary greedy phase protects every pair which is not contained in
the flexible set, not merely pairs crossing the flexible-set boundary.  This
file records the corresponding strengthening of the mixed product law.  It
will be used to control the internal residual graph before the internal-edge
cover-down.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Edges of `G` which are not wholly contained in `U`. -/
def outerGraphEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) : Finset (Sym2 V) :=
  (graphEdges G).filter fun e ↦ ¬ e.toFinset ⊆ U

@[simp]
lemma mem_outerGraphEdges_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {e : Sym2 V} :
    e ∈ outerGraphEdges G U ↔ e ∈ graphEdges G ∧ ¬ e.toFinset ⊆ U := by
  classical
  simp [outerGraphEdges]

/-- Outer edges which remain uncovered after the preliminary family `P`. -/
def preliminaryResidualOuterEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (P : TripleSystemOn V) :
    Finset (Sym2 V) :=
  outerGraphEdges G U \ graphEdges (coveredGraph P)

lemma preliminaryResidualOuterEdges_subset_outerGraphEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (P : TripleSystemOn V) :
    preliminaryResidualOuterEdges G U P ⊆ outerGraphEdges G U :=
  sdiff_subset

lemma greedyUncoveredOuterEdges_eq_preliminaryResidual
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V) :
    greedyUncoveredEdges (outerGraphEdges G U) S =
      preliminaryResidualOuterEdges G U S.chosen :=
  rfl

/-- Outside-pair survival supplies an available extension through every
still-uncovered outer edge. -/
theorem availablePair_nonempty_of_outsideLeavePairsAlive_outer
    {V : Type*} [Fintype V] [DecidableEq V]
    {H G : SimpleGraph V} {X : Finset V} {S : GreedyStateOn V}
    (hHG : Disjoint H G) (houtside : OutsideLeavePairsAlive H X S) :
    ∀ e ∈ greedyUncoveredEdges (outerGraphEdges G X) S,
      (availableTrianglesContainingPair S e.toFinset).Nonempty := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have heouter : s(u, v) ∈ outerGraphEdges G X := (mem_sdiff.mp he).1
      have hGset : s(u, v) ∈ G.edgeSet :=
        mem_graphEdges_iff.mp (mem_outerGraphEdges_iff.mp heouter).1
      have hG : G.Adj u v := by
        change G.Adj u v at hGset
        exact hGset
      have hnotBoth : ¬ (u ∈ X ∧ v ∈ X) := by
        have hnotSub := (mem_outerGraphEdges_iff.mp heouter).2
        intro huv
        apply hnotSub
        intro x hx
        simp only [Sym2.toFinset_mk_eq, mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact huv.1
        · exact huv.2
      have hnotH : ¬ H.Adj u v := by
        intro hH
        exact SimpleGraph.disjoint_left.mp hHG u v hH hG
      have hnotCovered : ¬ (coveredGraph S.chosen).Adj u v := by
        intro hcovered
        exact (mem_sdiff.mp he).2 (mem_graphEdges_iff.mpr hcovered)
      have hleave : (leaveGraph S.chosen).Adj u v :=
        leaveGraph_adj.mpr ⟨hG.ne, hnotCovered⟩
      simpa [PairAlive, Sym2.toFinset_mk_eq] using
        (houtside u v hnotH hnotBoth hleave)

/-- The pair floor supplies the quantitative choice count through every
currently uncovered outer edge. -/
theorem outerEdgeSupply_of_outsideLeavePairsAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    {H G : SimpleGraph V} {X : Finset V} {S : GreedyStateOn V}
    {d : ℕ} (hHG : Disjoint H G)
    (houtside : OutsideLeavePairsAlive H X S)
    (hfloor : HasAvailablePairFloor d S) :
    ∀ e ∈ greedyUncoveredEdges (outerGraphEdges G X) S,
      d ≤ (greedyChoicesCoveringEdge S e).card := by
  intro e he
  have heG : e ∈ graphEdges G :=
    (mem_outerGraphEdges_iff.mp (mem_sdiff.mp he).1).1
  have hdiag : ¬ e.IsDiag :=
    G.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp heG)
  rw [card_greedyChoicesCoveringEdge_eq_availablePair S e hdiag]
  exact hfloor e.toFinset
    (Sym2.card_toFinset_of_not_isDiag e hdiag)
    (availablePair_nonempty_of_outsideLeavePairsAlive_outer
      hHG houtside e he)

/-- The aggregate preliminary law satisfies the mixed product estimate for
all residual outer edges.  The proof is the crossing-edge argument with the
larger protected ambient edge family. -/
theorem timedAggregateAveragePairBand_probability_selected_preliminaryResidualOuter_le
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
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D) S₀).probability
        (fun z ↦ Q ⊆ z.2.chosen ∧
          E ⊆ preliminaryResidualOuterEdges G X z.2.chosen) ≤
      alpha ^ Q.card * eta ^ E.card + epsilon := by
  classical
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
      ∀ e ∈ greedyUncoveredEdges (outerGraphEdges G X) S,
        3 * k ≤ (greedyChoicesCoveringEdge S e).card := by
    intro j S hS hact e he
    exact h3k.trans (outerEdgeSupply_of_outsideLeavePairsAlive
      hHG hS.2 hact.1.1.2.2.2.2 e he)
  have hscalar : ∀ j S B, Inv S → active j S →
      B ⊆ greedyUncoveredEdges (outerGraphEdges G X) S →
      ((S.available.card - B.card * (3 * k) / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card := by
    intro j S B _hS hact _hB
    have hA : 0 < S.available.card :=
      card_pos.mpr hact.1.1.1
    exact preliminary_survival_scalar S.available.card M k B.card
      hA (hupper j S hact) hkM
  by_cases hE : E ⊆ outerGraphEdges G X
  · have hQ : Disjoint Q S₀.chosen := by
      rw [hchosen₀]
      simp
    have hB : E ⊆ greedyUncoveredEdges (outerGraphEdges G X) S₀ := by
      rw [greedyUncoveredEdges_eq_self_of_chosen_eq_empty
        (outerGraphEdges G X) S₀ hchosen₀]
      exact hE
    have htracked : L.probability (fun z ↦
        Q ⊆ z.2.chosen ∧
          E ⊆ timedActiveTrackedUncoveredEdges active
            (outerGraphEdges G X) z) ≤
        alpha ^ Q.card * eta ^ E.card := by
      exact timedStoppedGreedyProcess_probability_selectedTrackedUncovered_le_product
        n F active (outerGraphEdges G X) Inv D (3 * k) hD theta alpha eta S₀
          ⟨hInv₀, houtside₀⟩ hactive₀ hInvStep hfloorD hsupply hscalar
          hselected Q E hQ hB (hsurvived Q)
    calc
      L.probability (fun z ↦ Q ⊆ z.2.chosen ∧
          E ⊆ preliminaryResidualOuterEdges G X z.2.chosen) ≤
          L.probability (fun z ↦
            (Q ⊆ z.2.chosen ∧
              E ⊆ timedActiveTrackedUncoveredEdges active
                (outerGraphEdges G X) z) ∨
            ¬ active z.1.1 z.2) := by
        apply L.probability_mono
        intro z hz
        by_cases hact : active z.1.1 z.2
        · left
          exact ⟨hz.1, by
            simpa only [timedActiveTrackedUncoveredEdges, if_pos hact,
              greedyUncoveredOuterEdges_eq_preliminaryResidual] using hz.2⟩
        · exact Or.inr hact
      _ ≤ L.probability (fun z ↦
            Q ⊆ z.2.chosen ∧
              E ⊆ timedActiveTrackedUncoveredEdges active
                (outerGraphEdges G X) z) +
          L.probability (fun z ↦ ¬ active z.1.1 z.2) :=
        L.probability_or_le _ _
      _ ≤ alpha ^ Q.card * eta ^ E.card + epsilon :=
        add_le_add htracked (by simpa [L, active] using hinactive)
  · calc
      L.probability (fun z ↦ Q ⊆ z.2.chosen ∧
          E ⊆ preliminaryResidualOuterEdges G X z.2.chosen) ≤
          L.probability (fun _ ↦ False) := by
        apply L.probability_mono
        intro z hz
        exact hE (hz.2.trans
          (preliminaryResidualOuterEdges_subset_outerGraphEdges
            G X z.2.chosen))
      _ = 0 := L.probability_false
      _ ≤ alpha ^ Q.card * eta ^ E.card + epsilon := bot_le

/-- Pure mixed product estimate after intersecting with the terminal active
event.  Unlike the preceding unconditional theorem, there is no exceptional
term because active residual edges are exactly the tracked uncovered edges. -/
theorem timedAggregateAveragePairBand_probability_active_selected_residualOuter_le
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
        E ⊆ preliminaryResidualOuterEdges G X z.2.chosen) ≤
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
      ∀ e ∈ greedyUncoveredEdges (outerGraphEdges G X) S,
        3 * k ≤ (greedyChoicesCoveringEdge S e).card := by
    intro j S hS hact e he
    exact h3k.trans (outerEdgeSupply_of_outsideLeavePairsAlive
      hHG hS.2 hact.1.1.2.2.2.2 e he)
  have hscalar : ∀ j S B, Inv S → active j S →
      B ⊆ greedyUncoveredEdges (outerGraphEdges G X) S →
      ((S.available.card - B.card * (3 * k) / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card := by
    intro j S B _hS hact _hB
    have hA : 0 < S.available.card := card_pos.mpr hact.1.1.1
    exact preliminary_survival_scalar S.available.card M k B.card
      hA (hupper j S hact) hkM
  by_cases hE : E ⊆ outerGraphEdges G X
  · have hQ : Disjoint Q S₀.chosen := by
      rw [hchosen₀]
      simp
    have hB : E ⊆ greedyUncoveredEdges (outerGraphEdges G X) S₀ := by
      rw [greedyUncoveredEdges_eq_self_of_chosen_eq_empty
        (outerGraphEdges G X) S₀ hchosen₀]
      exact hE
    have htracked : L.probability (fun z ↦
        Q ⊆ z.2.chosen ∧
          E ⊆ timedActiveTrackedUncoveredEdges active
            (outerGraphEdges G X) z) ≤
        alpha ^ Q.card * eta ^ E.card := by
      exact timedStoppedGreedyProcess_probability_selectedTrackedUncovered_le_product
        n F active (outerGraphEdges G X) Inv D (3 * k) hD theta alpha eta S₀
          ⟨hInv₀, houtside₀⟩ hactive₀ hInvStep hfloorD hsupply hscalar
          hselected Q E hQ hB (hsurvived Q)
    exact htracked.trans' <| by
      apply L.probability_mono
      intro z hz
      refine ⟨hz.2.1, ?_⟩
      have hact : active (z.1 : ℕ) z.2 := hz.1
      simpa only [timedActiveTrackedUncoveredEdges, if_pos hact,
        greedyUncoveredOuterEdges_eq_preliminaryResidual] using hz.2.2
  · calc
      L.probability (fun z ↦ active z.1.1 z.2 ∧ Q ⊆ z.2.chosen ∧
          E ⊆ preliminaryResidualOuterEdges G X z.2.chosen) ≤
          L.probability (fun _ ↦ False) := by
        apply L.probability_mono
        intro z hz
        exact hE (hz.2.2.trans
          (preliminaryResidualOuterEdges_subset_outerGraphEdges
            G X z.2.chosen))
      _ = 0 := L.probability_false
      _ ≤ alpha ^ Q.card * eta ^ E.card := zero_le

/-- Relative version of the outer-residual law.  It charges only triangles
selected after the initial packing and uses containment of `G` in the
initial leave to initialize every tracked outer edge. -/
theorem timedAggregateAveragePairBand_probability_active_newSelected_residualOuter_le
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
        E ⊆ preliminaryResidualOuterEdges G X z.2.chosen) ≤
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
      ∀ e ∈ greedyUncoveredEdges (outerGraphEdges G X) S,
        3 * k ≤ (greedyChoicesCoveringEdge S e).card := by
    intro j S hS hact e he
    exact h3k.trans (outerEdgeSupply_of_outsideLeavePairsAlive
      hHG hS.2 hact.1.1.2.2.2.2 e he)
  have hscalar : ∀ j S B, Inv S → active j S →
      B ⊆ greedyUncoveredEdges (outerGraphEdges G X) S →
      ((S.available.card - B.card * (3 * k) / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card := by
    intro j S B _hS hact _hB
    have hA : 0 < S.available.card := card_pos.mpr hact.1.1.1
    exact preliminary_survival_scalar S.available.card M k B.card
      hA (hupper j S hact) hkM
  by_cases hQ : Disjoint Q S₀.chosen
  · by_cases hE : E ⊆ outerGraphEdges G X
    · have hB : E ⊆ greedyUncoveredEdges (outerGraphEdges G X) S₀ := by
        intro e he
        have heOuter := hE he
        rw [greedyUncoveredEdges, mem_sdiff]
        refine ⟨heOuter, ?_⟩
        induction e using Sym2.inductionOn with
        | _ u v =>
            have heGset : s(u, v) ∈ G.edgeSet :=
              mem_graphEdges_iff.mp
                (mem_outerGraphEdges_iff.mp heOuter).1
            have hGadj : G.Adj u v := by
              change G.Adj u v at heGset
              exact heGset
            have hleave := leaveGraph_adj.mp (hGleave hGadj)
            intro hcovered
            exact hleave.2 (mem_graphEdges_iff.mp hcovered)
      have htracked : L.probability (fun z ↦
          Q ⊆ z.2.chosen ∧
            E ⊆ timedActiveTrackedUncoveredEdges active
              (outerGraphEdges G X) z) ≤
          alpha ^ Q.card * eta ^ E.card := by
        exact timedStoppedGreedyProcess_probability_selectedTrackedUncovered_le_product
          n F active (outerGraphEdges G X) Inv D (3 * k) hD theta alpha eta S₀
            ⟨hInv₀, houtside₀⟩ hactive₀ hInvStep hfloorD hsupply hscalar
            hselected Q E hQ hB (hsurvived Q)
      exact htracked.trans' <| by
        apply L.probability_mono
        intro z hz
        refine ⟨hz.2.1.trans sdiff_subset, ?_⟩
        have hact : active (z.1 : ℕ) z.2 := hz.1
        simpa only [timedActiveTrackedUncoveredEdges, if_pos hact,
          greedyUncoveredOuterEdges_eq_preliminaryResidual] using hz.2.2
    · calc
        L.probability (fun z ↦ active z.1.1 z.2 ∧
            Q ⊆ z.2.chosen \ S₀.chosen ∧
            E ⊆ preliminaryResidualOuterEdges G X z.2.chosen) ≤
            L.probability (fun _ ↦ False) := by
          apply L.probability_mono
          intro z hz
          exact hE (hz.2.2.trans
            (preliminaryResidualOuterEdges_subset_outerGraphEdges
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
          E ⊆ preliminaryResidualOuterEdges G X z.2.chosen) ≤
          L.probability (fun _ ↦ False) := by
        apply L.probability_mono
        intro z hz
        exact himpossible z hz.2.1
      _ = 0 := L.probability_false
      _ ≤ alpha ^ Q.card * eta ^ E.card := zero_le

/-- Conditioning a pure mixed product event on its common good event absorbs
the single normalizer into both product bases. -/
theorem FiniteLaw.conditionOn_probability_mixedProduct_le
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Omega) (Good : Omega → Prop)
    (selected : Omega → TripleSystemOn V)
    (residual : Omega → Finset (Sym2 V))
    (alpha eta : ℝ≥0) (hGood : 0 < L.probability Good)
    (hraw : ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
      L.probability (fun omega ↦ Good omega ∧
        Q ⊆ selected omega ∧ E ⊆ residual omega) ≤
          alpha ^ Q.card * eta ^ E.card) :
    ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
      (L.conditionOn Good hGood).probability (fun omega ↦
        Q ⊆ selected omega ∧ E ⊆ residual omega) ≤
        (alpha / L.probability Good) ^ Q.card *
          (eta / L.probability Good) ^ E.card := by
  intro Q E
  let Event : Omega → Prop := fun omega ↦
    Q ⊆ selected omega ∧ E ⊆ residual omega
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
    calc
      (L.conditionOn Good hGood).probability Event =
          L.probability (fun omega ↦ Good omega ∧ Event omega) /
            L.probability Good :=
        L.conditionOn_probability Good Event hGood
      _ ≤ (alpha ^ Q.card * eta ^ E.card) /
          L.probability Good := by
        gcongr
        simpa only [Event, and_assoc] using hraw Q E
      _ ≤ (alpha ^ Q.card * eta ^ E.card) /
          (L.probability Good) ^ (Q.card + E.card) := by
        exact div_le_div_of_nonneg_left zero_le (pow_pos hGood _) hpow
      _ = (alpha / L.probability Good) ^ Q.card *
          (eta / L.probability Good) ^ E.card := by
        rw [pow_add, div_pow, div_pow]
        field_simp

/-- Conditioning on terminal activity gives a pure outer-residual product
law with the explicit lower normalizer `1 - epsilon`. -/
theorem exists_conditionedTimedAggregateAveragePairBand_outerProductLaw
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
              E ⊆ preliminaryResidualOuterEdges G X z.2.chosen) ≤
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
  have hraw : ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
      L.probability (fun z ↦ Good z ∧ Q ⊆ z.2.chosen ∧
        E ⊆ preliminaryResidualOuterEdges G X z.2.chosen) ≤
        alpha ^ Q.card * eta ^ E.card := by
    intro Q E
    simpa only [L, Good, active] using
      (timedAggregateAveragePairBand_probability_active_selected_residualOuter_le
        n F H G X Kpair Kglobal Kinc Delta delta I D M k hD hkM h3k
        alpha eta S₀ hInv₀ houtside₀ hHG hsmall hchosen₀ hactive₀
        hupper hselected hsurvived Q E)
  intro Q E
  have hconditioned := L.conditionOn_probability_mixedProduct_le Good
    (fun z ↦ z.2.chosen)
    (fun z ↦ preliminaryResidualOuterEdges G X z.2.chosen)
    alpha eta hGood hraw Q E
  have hden : 0 < 1 - epsilon := tsub_pos_iff_lt.mpr hepsilon
  have halpha : alpha / L.probability Good ≤ alpha / (1 - epsilon) :=
    div_le_div_of_nonneg_left zero_le hden hlower
  have heta : eta / L.probability Good ≤ eta / (1 - epsilon) :=
    div_le_div_of_nonneg_left zero_le hden hlower
  exact hconditioned.trans (by gcongr)

/-- Outer graph edges incident with a fixed vertex. -/
def outerIncidentEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (v : V) : Finset (Sym2 V) :=
  (outerGraphEdges G U).filter fun e ↦ v ∈ e.toFinset

@[simp]
lemma mem_outerIncidentEdges_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {v : V} {e : Sym2 V} :
    e ∈ outerIncidentEdges G U v ↔
      e ∈ outerGraphEdges G U ∧ v ∈ e.toFinset := by
  classical
  simp [outerIncidentEdges]

/-- A mixed product estimate with one common exceptional term yields the
usual witness-union tail for the number of residual edges in a fixed test
family.  This form deliberately keeps the finite witness multiplier on the
exceptional term; later parameter choices may make that term arbitrarily
small. -/
theorem FiniteLaw.probability_card_inter_residualOuter_ge_le_of_mixedProduct
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq V]
    (L : FiniteLaw Omega) (selected : Omega → TripleSystemOn V)
    (residual : Omega → Finset (Sym2 V))
    (tests : Finset (Sym2 V)) (alpha eta epsilon : ℝ≥0) (r : ℕ)
    (hmixed : ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
      L.probability (fun omega ↦ Q ⊆ selected omega ∧
        E ⊆ residual omega) ≤
        alpha ^ Q.card * eta ^ E.card + epsilon) :
    L.probability (fun omega ↦
        r ≤ (tests ∩ residual omega).card) ≤
      (tests.powersetCard r).card * (eta ^ r + epsilon) := by
  let event : Finset (Sym2 V) → Omega → Prop :=
    fun E omega ↦ E ⊆ residual omega
  calc
    L.probability (fun omega ↦
        r ≤ (tests ∩ residual omega).card) ≤
        L.probability (fun omega ↦
          ∃ E ∈ tests.powersetCard r, event E omega) := by
      apply L.probability_mono
      intro omega hlarge
      obtain ⟨E, hEsub, hEcard⟩ := exists_subset_card_eq hlarge
      exact ⟨E, mem_powersetCard.mpr
        ⟨hEsub.trans inter_subset_left, hEcard⟩,
        hEsub.trans inter_subset_right⟩
    _ ≤ ∑ E ∈ tests.powersetCard r, L.probability (event E) :=
      L.probability_exists_le (tests.powersetCard r) event
    _ ≤ ∑ _E ∈ tests.powersetCard r, (eta ^ r + epsilon) := by
      apply sum_le_sum
      intro E hE
      have hcard : E.card = r := (mem_powersetCard.mp hE).2
      have h := hmixed (∅ : TripleSystemOn V) E
      simpa only [empty_subset, true_and, card_empty, pow_zero, one_mul,
        hcard] using h
    _ = (tests.powersetCard r).card * (eta ^ r + epsilon) := by
      rw [mul_add]
      simp

/-- Uniform union bound for large residual outer degree at some vertex. -/
theorem FiniteLaw.probability_exists_large_residualOuter_incidence_le
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq V]
    (L : FiniteLaw Omega) (G : SimpleGraph V) (U : Finset V)
    (selected : Omega → TripleSystemOn V)
    (residual : Omega → Finset (Sym2 V))
    (alpha eta epsilon : ℝ≥0) (r : ℕ)
    (hmixed : ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
      L.probability (fun omega ↦ Q ⊆ selected omega ∧
        E ⊆ residual omega) ≤
        alpha ^ Q.card * eta ^ E.card + epsilon) :
    L.probability (fun omega ↦ ∃ v : V,
        r ≤ (outerIncidentEdges G U v ∩ residual omega).card) ≤
      ∑ v : V, ((outerIncidentEdges G U v).powersetCard r).card *
        (eta ^ r + epsilon) := by
  calc
    L.probability (fun omega ↦ ∃ v : V,
        r ≤ (outerIncidentEdges G U v ∩ residual omega).card) ≤
        ∑ v ∈ (univ : Finset V), L.probability (fun omega ↦
          r ≤ (outerIncidentEdges G U v ∩ residual omega).card) := by
      simpa using L.probability_exists_le (univ : Finset V)
        (fun v omega ↦
          r ≤ (outerIncidentEdges G U v ∩ residual omega).card)
    _ ≤ ∑ v ∈ (univ : Finset V),
        ((outerIncidentEdges G U v).powersetCard r).card *
          (eta ^ r + epsilon) := by
      apply sum_le_sum
      intro v _hv
      exact L.probability_card_inter_residualOuter_ge_le_of_mixedProduct
        selected residual (outerIncidentEdges G U v)
          alpha eta epsilon r hmixed
    _ = ∑ v : V, ((outerIncidentEdges G U v).powersetCard r).card *
        (eta ^ r + epsilon) := by simp

end

end Erdos207
