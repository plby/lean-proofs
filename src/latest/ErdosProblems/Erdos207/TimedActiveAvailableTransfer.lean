/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PendingGreedySurvival
import ErdosProblems.Erdos207.SelectedAvailableEnvelopeProduct
import ErdosProblems.Erdos207.SupportRestrictedSelectedAvailableTransfer
import ErdosProblems.Erdos207.TimedActiveGreedyJointLaw

/-!
# Selected/available transfer on a clocked active greedy process

Both availability and residual edges are gated by the active predicate.
Consequently an early stopped state cannot satisfy a nonempty pending
prescription.  A synchronized support predicate records that an active state
seen at external evolution step `i` has internal clock exactly `i`; this lets
time-dependent trajectory estimates be used with their correct index.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

def timedActiveTrackedAvailable
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (active : ℕ → GreedyStateOn V → Prop)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n) : TripleSystemOn V := by
  classical
  exact if active z.1.1 z.2 then z.2.available else ∅

/-- Reachable support at external step `i`: the internal clock cannot be
ahead, the base invariant holds, and a state which has not stopped is exactly
synchronized with `i`. -/
def TimedGreedySynchronized
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (active : ℕ → GreedyStateOn V → Prop)
    (Inv : GreedyStateOn V → Prop) (i : ℕ)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n) : Prop :=
  z.1.1 ≤ i ∧ Inv z.2 ∧
    (z.1.1 = i ∨ ¬ active z.1.1 z.2)

theorem timedStoppedGreedyKernel_supported_synchronized
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (Inv : GreedyStateOn V → Prop)
    (hInv : ∀ j, j < n → ∀ S, Inv S → active j S →
      (greedyKernel F S).SupportedOn Inv)
    (i : ℕ) (hi : i < n)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n)
    (hz : TimedGreedySynchronized active Inv i z) :
    (FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F) active z).SupportedOn
      (TimedGreedySynchronized active Inv (i + 1)) := by
  classical
  unfold FiniteLaw.timedStoppedKernel
  split_ifs with hrun
  · have hztime : z.1.1 = i :=
      hz.2.2.resolve_right (not_not_intro hrun.2)
    exact (hInv z.1.1 hrun.1 z.2 hz.2.1 hrun.2).map
      (fun S' ↦ (FiniteLaw.advanceTime z.1 hrun.1, S'))
      (fun S' hS' ↦ ⟨by simp [hztime], hS', Or.inl (by simp [hztime])⟩)
  · apply FiniteLaw.supportedOn_pure
    refine ⟨hz.1.trans (Nat.le_succ i), hz.2.1, Or.inr ?_⟩
    intro hactive
    have hzlt : z.1.1 < n := lt_of_le_of_lt hz.1 hi
    exact hrun ⟨hzlt, hactive⟩

theorem timedStoppedGreedyKernel_antitone_activeTrackedAvailable
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (Inv : GreedyStateOn V → Prop)
    (i : ℕ) (hi : i < n)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n)
    (hz : TimedGreedySynchronized active Inv i z) :
    (FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F) active z).SupportedOn
      (fun z' ↦ timedActiveTrackedAvailable active z' ⊆
        timedActiveTrackedAvailable active z) := by
  classical
  by_cases hactive : active z.1.1 z.2
  · have hztime : z.1.1 = i :=
      hz.2.2.resolve_right (not_not_intro hactive)
    have hzlt : z.1.1 < n := by omega
    unfold FiniteLaw.timedStoppedKernel
    rw [dif_pos ⟨hzlt, hactive⟩]
    exact (greedyKernel_antitone_available F z.2).map
      (fun S' ↦ (FiniteLaw.advanceTime z.1 hzlt, S'))
      (fun S' hsub ↦ by
        simp only [timedActiveTrackedAvailable, if_pos hactive]
        by_cases hnext : active (z.1.1 + 1) S'
        · simpa [hnext] using hsub
        · simp [hnext])
  · have hstop : ¬ (z.1.1 < n ∧ active z.1.1 z.2) :=
      fun h ↦ hactive h.2
    unfold FiniteLaw.timedStoppedKernel
    rw [dif_neg hstop]
    exact FiniteLaw.supportedOn_pure _ Subset.rfl

theorem timedStoppedGreedyKernel_newChosen_subset_activeTrackedAvailable
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (Inv : GreedyStateOn V → Prop)
    (i : ℕ) (hi : i < n)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n)
    (hz : TimedGreedySynchronized active Inv i z) :
    (FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F) active z).SupportedOn
      (fun z' ↦ z'.2.chosen \ z.2.chosen ⊆
        timedActiveTrackedAvailable active z) := by
  classical
  by_cases hactive : active z.1.1 z.2
  · have hztime : z.1.1 = i :=
      hz.2.2.resolve_right (not_not_intro hactive)
    have hzlt : z.1.1 < n := by omega
    unfold FiniteLaw.timedStoppedKernel
    rw [dif_pos ⟨hzlt, hactive⟩]
    exact (greedyKernel_newChosen_subset_available F z.2).map
      (fun S' ↦ (FiniteLaw.advanceTime z.1 hzlt, S'))
      (fun S' hsub ↦ by
        simpa [timedActiveTrackedAvailable, hactive] using hsub)
  · have hstop : ¬ (z.1.1 < n ∧ active z.1.1 z.2) :=
      fun h ↦ hactive h.2
    unfold FiniteLaw.timedStoppedKernel
    rw [dif_neg hstop]
    exact FiniteLaw.supportedOn_pure _ (by simp)

/-- One supportwise transfer step for the clocked active process. -/
theorem timedStoppedGreedyKernel_probability_selectedAvailableUncovered_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (Inv : GreedyStateOn V → Prop)
    (E : Finset (Sym2 V)) (D d : ℕ → ℕ)
    (theta : ℕ → ℝ≥0)
    (hD : ∀ i, i < n → 0 < D i)
    (hfloor : ∀ i S, i < n → Inv S → active i S →
      D i ≤ S.available.card)
    (Q Sfix : TripleSystemOn V) (hSQ : Sfix ⊆ Q)
    (B : Finset (Sym2 V))
    (hQ : IsPackingOn Q)
    (hQB : Disjoint (Q.biUnion tripleEdgeFinset) B)
    (hBoffdiag : ∀ e ∈ B, ¬ e.IsDiag)
    (hsupply : ∀ i S, i < n → Inv S → active i S →
      Q \ Sfix ⊆ S.available → B ⊆ greedyUncoveredEdges E S →
      ∀ e ∈ pendingSurvivalEdges (Q \ Sfix) B,
        d i ≤ (greedyChoicesCoveringEdge S e).card)
    (hscalar : ∀ i S, i < n → Inv S → active i S →
      ((S.available.card -
          ((3 * (Q \ Sfix).card + B.card) * d i -
            (3 * (Q \ Sfix).card + B.card).choose 2) : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤
        theta i ^ (3 * (Q \ Sfix).card + B.card))
    (i : ℕ) (hi : i < n)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n)
    (hz : TimedGreedySynchronized active Inv i z) :
    (FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F) active z).probability
        (SelectedAvailableUncoveredEvent
          (fun z' ↦ z'.2.chosen)
          (timedActiveTrackedAvailable active)
          (timedActiveTrackedUncoveredEdges active E)
          Q Sfix B) ≤
      theta i ^ (3 * (Q \ Sfix).card + B.card) *
          nnrealIndicator
            (SelectedAvailableUncoveredEvent
              (fun z' ↦ z'.2.chosen)
              (timedActiveTrackedAvailable active)
              (timedActiveTrackedUncoveredEdges active E)
              Q Sfix B z) +
        ∑ x ∈ Sfix, nnrealIndicatorMul
          (SelectedAvailableUncoveredEvent
            (fun z' ↦ z'.2.chosen)
            (timedActiveTrackedAvailable active)
            (timedActiveTrackedUncoveredEdges active E)
            Q (Sfix.erase x) B z)
          (D i : ℝ≥0)⁻¹ := by
  apply kernel_probability_selectedAvailableUncovered_le
    (fun z ↦ FiniteLaw.timedStoppedKernel n
      (fun _ ↦ greedyKernel F) active z)
    (fun z' ↦ z'.2.chosen)
    (timedActiveTrackedAvailable active)
    (timedActiveTrackedUncoveredEdges active E)
    (D i : ℝ≥0)⁻¹ (theta i) z
    (timedStoppedGreedyKernel_monotone_singleInsertion n F active z)
    (timedStoppedGreedyKernel_antitone_activeTrackedAvailable
      n F active Inv i hi z hz)
    (timedStoppedGreedyKernel_antitone_activeTracked_of_reachable
      n F active E Inv i hi z ⟨hz.1, hz.2.1⟩)
    (timedStoppedGreedyKernel_newChosen_subset_activeTrackedAvailable
      n F active Inv i hi z hz)
    Q Sfix hSQ B
  · intro hevent
    by_cases hactive : active z.1.1 z.2
    · have hztime : z.1.1 = i :=
        hz.2.2.resolve_right (not_not_intro hactive)
      have hzlt : z.1.1 < n := by omega
      have hPendingPacking : IsPackingOn (Q \ Sfix) :=
        hQ.mono sdiff_subset
      have hEdgeSubset :
          (Q \ Sfix).biUnion tripleEdgeFinset ⊆
            Q.biUnion tripleEdgeFinset := by
        intro e he
        obtain ⟨T, hT, heT⟩ := mem_biUnion.mp he
        exact mem_biUnion.mpr ⟨T, (mem_sdiff.mp hT).1, heT⟩
      have hPendingB :
          Disjoint ((Q \ Sfix).biUnion tripleEdgeFinset) B :=
        hQB.mono_left hEdgeSubset
      have hBactual : B ⊆ greedyUncoveredEdges E z.2 := by
        simpa [timedActiveTrackedUncoveredEdges, hactive] using
          hevent.2.2.2.2
      have hA : z.2.available.Nonempty := card_pos.mp
        (lt_of_lt_of_le (hD i hi)
          (hfloor i z.2 hi hz.2.1 (hztime ▸ hactive)))
      unfold FiniteLaw.timedStoppedKernel
      rw [dif_pos ⟨hzlt, hactive⟩, FiniteLaw.probability_map]
      calc
        (greedyKernel F z.2).probability (fun S' ↦
            Q \ Sfix ⊆ timedActiveTrackedAvailable active
              (FiniteLaw.advanceTime z.1 hzlt, S') ∧
            B ⊆ timedActiveTrackedUncoveredEdges active E
              (FiniteLaw.advanceTime z.1 hzlt, S')) ≤
          (greedyKernel F z.2).probability (fun S' ↦
            Q \ Sfix ⊆ S'.available ∧
              B ⊆ greedyUncoveredEdges E S') := by
          apply (greedyKernel F z.2).probability_mono
          intro S' htracked
          by_cases hnext : active (z.1.1 + 1) S'
          · simpa [timedActiveTrackedAvailable,
              timedActiveTrackedUncoveredEdges, hnext] using htracked
          · have hPendingEmpty : Q \ Sfix = ∅ := subset_empty.mp (by
                simpa [timedActiveTrackedAvailable, hnext] using htracked.1)
            have hBempty : B = ∅ := subset_empty.mp (by
                simpa [timedActiveTrackedUncoveredEdges, hnext] using htracked.2)
            simp [hPendingEmpty, hBempty]
        _ ≤ theta i ^ (3 * (Q \ Sfix).card + B.card) :=
          greedyKernel_probability_pending_available_uncovered_le
            F E z.2 (Q \ Sfix) B (d i) (theta i) hA
            hPendingPacking hPendingB hBoffdiag hBactual
            (hsupply i z.2 hi hz.2.1 (hztime ▸ hactive)
              (by simpa [timedActiveTrackedAvailable, hactive] using
                hevent.2.2.2.1) hBactual)
            (hscalar i z.2 hi hz.2.1 (hztime ▸ hactive))
    · have hPendingEmpty : Q \ Sfix = ∅ := subset_empty.mp (by
          simpa [timedActiveTrackedAvailable, hactive] using
            hevent.2.2.2.1)
      have hBempty : B = ∅ := subset_empty.mp (by
          simpa [timedActiveTrackedUncoveredEdges, hactive] using
            hevent.2.2.2.2)
      simpa [hPendingEmpty, hBempty] using
        (FiniteLaw.probability_le_one
          (FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F) active z)
          (fun z' ↦ Q \ Sfix ⊆ timedActiveTrackedAvailable active z' ∧
            B ⊆ timedActiveTrackedUncoveredEdges active E z'))
  · intro x hx hevent hxnot
    by_cases hactive : active z.1.1 z.2
    · have hztime : z.1.1 = i :=
        hz.2.2.resolve_right (not_not_intro hactive)
      have hzlt : z.1.1 < n := by omega
      unfold FiniteLaw.timedStoppedKernel
      rw [dif_pos ⟨hzlt, hactive⟩, FiniteLaw.probability_map]
      exact ((greedyKernel F z.2).probability_mono
        (fun _ h ↦ h.1)).trans
          (greedyKernel_probability_new_triangle_le F z.2 x (D i)
            (hD i hi) (hfloor i z.2 hi hz.2.1 (hztime ▸ hactive)) hxnot)
    · have hxPending : x ∈ Q \ Sfix.erase x := by
          exact mem_sdiff.mpr ⟨hSQ hx, by simp⟩
      have hxEmpty : x ∈ (∅ : TripleSystemOn V) := by
        have := hevent.2.2.2.1 hxPending
        simpa [timedActiveTrackedAvailable, hactive] using this
      simpa using hxEmpty

/-- Full retrospective product law on the support of the timed active
process. -/
theorem timedStoppedGreedyProcess_probability_selectedAvailableTracked_le_product
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (Inv : GreedyStateOn V → Prop)
    (E : Finset (Sym2 V)) (D d : ℕ → ℕ)
    (theta rho : ℕ → ℝ≥0)
    (S₀ : GreedyStateOn V)
    (hInv₀ : Inv S₀) (hactive₀ : active 0 S₀)
    (hInv : ∀ i, i < n → ∀ S, Inv S → active i S →
      (greedyKernel F S).SupportedOn Inv)
    (hD : ∀ i, i < n → 0 < D i)
    (hfloor : ∀ i S, i < n → Inv S → active i S →
      D i ≤ S.available.card)
    (Q : TripleSystemOn V) (B : Finset (Sym2 V))
    (hQpacking : IsPackingOn Q)
    (hQB : Disjoint (Q.biUnion tripleEdgeFinset) B)
    (hBoffdiag : ∀ e ∈ B, ¬ e.IsDiag)
    (hsupply : ∀ i S R, i < n → Inv S → active i S → R ⊆ Q →
      Q \ R ⊆ S.available → B ⊆ greedyUncoveredEdges E S →
      ∀ e ∈ pendingSurvivalEdges (Q \ R) B,
        d i ≤ (greedyChoicesCoveringEdge S e).card)
    (hscalar : ∀ i S R, i < n → Inv S → active i S → R ⊆ Q →
      ((S.available.card -
          ((3 * (Q \ R).card + B.card) * d i -
            (3 * (Q \ R).card + B.card).choose 2) : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤
        theta i ^ (3 * (Q \ R).card + B.card))
    (htheta : ∀ i, theta i ≤ 1)
    (hadjust : ∀ i, (D i : ℝ≥0)⁻¹ ≤
      theta i ^ (3 * Q.card + B.card) * rho i)
    (hQselected : Disjoint Q S₀.chosen)
    (hQavailable : Q ⊆ S₀.available)
    (hB : B ⊆ greedyUncoveredEdges E S₀) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
        (fun z ↦ Q ⊆ z.2.chosen ∧
          B ⊆ timedActiveTrackedUncoveredEdges active E z) ≤
      cumulativeSurvival theta n ^ B.card *
        transferPointWeight theta rho n ^ Q.card := by
  let z₀ : FiniteLaw.TimedState (GreedyStateOn V) n :=
    (⟨0, by omega⟩, S₀)
  let Kt : ℕ → FiniteLaw.TimedState (GreedyStateOn V) n →
      FiniteLaw (FiniteLaw.TimedState (GreedyStateOn V) n) :=
    fun _ z ↦ FiniteLaw.timedStoppedKernel n
      (fun _ ↦ greedyKernel F) active z
  let P : ℕ → FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    TimedGreedySynchronized active Inv
  have hP₀ : P 0 z₀ := by
    exact ⟨by simp [z₀], hInv₀, Or.inl (by simp [z₀])⟩
  have hQavailTracked : Q ⊆ timedActiveTrackedAvailable active z₀ := by
    simpa [z₀, timedActiveTrackedAvailable, hactive₀] using hQavailable
  have hBtracked : B ⊆ timedActiveTrackedUncoveredEdges active E z₀ := by
    simpa [z₀, timedActiveTrackedUncoveredEdges, hactive₀] using hB
  have hraw :=
    evolveKernels_probability_selectedAvailableUncovered_le_envelope_of_supported
      Kt (fun z ↦ z.2.chosen)
      (timedActiveTrackedAvailable active)
      (timedActiveTrackedUncoveredEdges active E)
      (fun i ↦ (D i : ℝ≥0)⁻¹) theta P n
      (fun i hi z hz ↦
        timedStoppedGreedyKernel_supported_synchronized
          n F active Inv hInv i hi z hz)
      Q B
      (fun i hi z hz R hRQ ↦
        timedStoppedGreedyKernel_probability_selectedAvailableUncovered_le
          n F active Inv E D d theta hD hfloor Q R hRQ B
          hQpacking hQB hBoffdiag
          (fun j S hj hIS hact ↦ hsupply j S R hj hIS hact hRQ)
          (fun j S hj hIS hact ↦ hscalar j S R hj hIS hact hRQ)
          i hi z hz)
      z₀ hP₀ (by simpa [z₀] using hQselected)
      hQavailTracked hBtracked Q Subset.rfl n le_rfl
  rw [selectedAvailableUncoveredEvent_self] at hraw
  have henv := selectedAvailableUncoveredEnvelope_le_product
    (fun i ↦ (D i : ℝ≥0)⁻¹) theta rho Q B.card
      htheta hadjust n Q Subset.rfl
  have hbound := hraw.trans henv
  change (FiniteLaw.evolveKernels Kt n (FiniteLaw.pure z₀)).probability
      (fun z ↦ Q ⊆ z.2.chosen ∧
        B ⊆ timedActiveTrackedUncoveredEdges active E z) ≤ _
  simpa [FiniteLaw.timedStoppedProcessLaw, Kt, z₀, setWeight] using hbound

/-- A genuine terminal uncovered-edge event is contained in the union of
the active-gated tracked event and terminal inactivity.  This is the
time-dependent analogue of the stopping-error split used for a fixed
availability threshold. -/
theorem timedStoppedGreedyProcess_probability_selectedUncovered_le_tracked_add_inactive
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (E : Finset (Sym2 V)) (S₀ : GreedyStateOn V)
    (Q : TripleSystemOn V) (B : Finset (Sym2 V)) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
        (fun z ↦ Q ⊆ z.2.chosen ∧ B ⊆ greedyUncoveredEdges E z.2) ≤
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
          (fun z ↦ Q ⊆ z.2.chosen ∧
            B ⊆ timedActiveTrackedUncoveredEdges active E z) +
        (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
          (fun z ↦ ¬ active z.1.1 z.2) := by
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  calc
    L.probability
        (fun z ↦ Q ⊆ z.2.chosen ∧ B ⊆ greedyUncoveredEdges E z.2) ≤
        L.probability (fun z ↦
          (Q ⊆ z.2.chosen ∧
            B ⊆ timedActiveTrackedUncoveredEdges active E z) ∨
          ¬ active z.1.1 z.2) := by
      apply L.probability_mono
      intro z hz
      by_cases hactive : active z.1.1 z.2
      · exact Or.inl ⟨hz.1, by
          simpa [timedActiveTrackedUncoveredEdges, hactive] using hz.2⟩
      · exact Or.inr hactive
    _ ≤ L.probability (fun z ↦ Q ⊆ z.2.chosen ∧
          B ⊆ timedActiveTrackedUncoveredEdges active E z) +
        L.probability (fun z ↦ ¬ active z.1.1 z.2) :=
      L.probability_or_le _ _

end

end Erdos207
