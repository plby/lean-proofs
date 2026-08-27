/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialSparsificationStrongLaw
import ErdosProblems.Erdos207.OutsidePairSurvival

/-!
# Tracking only the live pairs in the initial sparsification

Pairs belonging to the absorber graph, pairs wholly inside the final
flexible set, and diagonal `Sym2` values do not need a random-survival
estimate.  This file separates those deterministic prescriptions from the
genuine live leave edges.  The omitted density factors are paid by the
constant in the strong-distribution estimate.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The prescribed pairs for which outside-pair survival supplies a live
available star. -/
def outsideTrackablePart
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (E : Finset (Sym2 V)) :
    Finset (Sym2 V) := by
  classical
  exact E.filter fun e ↦
    ¬ e.IsDiag ∧ e ∉ graphEdges H ∧ ¬ e.toFinset ⊆ X

lemma outsideTrackablePart_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (E : Finset (Sym2 V)) :
    outsideTrackablePart H X E ⊆ E := by
  classical
  intro e he
  exact (mem_filter.mp (by
    simpa only [outsideTrackablePart] using he)).1

lemma outsideTrackablePart_subset_offdiagPart
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (E : Finset (Sym2 V)) :
    outsideTrackablePart H X E ⊆ offdiagPart E := by
  classical
  intro e he
  change e ∈ E.filter (fun e ↦
    ¬ e.IsDiag ∧ e ∉ graphEdges H ∧ ¬ e.toFinset ⊆ X) at he
  rw [mem_filter] at he
  exact mem_offdiagPart_iff.mpr ⟨he.1, he.2.1⟩

lemma outsideTrackablePart_offdiag
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (E : Finset (Sym2 V)) :
    ∀ e ∈ outsideTrackablePart H X E, ¬ e.IsDiag := by
  classical
  intro e he
  change e ∈ E.filter (fun e ↦
    ¬ e.IsDiag ∧ e ∉ graphEdges H ∧ ¬ e.toFinset ⊆ X) at he
  exact (mem_filter.mp he).2.1

lemma outsideTrackablePart_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {X : Finset V} {E : Finset (Sym2 V)}
    {e : Sym2 V} (he : e ∈ outsideTrackablePart H X E) :
    e ∉ graphEdges H := by
  classical
  change e ∈ E.filter (fun e ↦
    ¬ e.IsDiag ∧ e ∉ graphEdges H ∧ ¬ e.toFinset ⊆ X) at he
  exact (mem_filter.mp he).2.2.1

lemma outsideTrackablePart_not_both_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {X : Finset V} {E : Finset (Sym2 V)}
    {e : Sym2 V} (he : e ∈ outsideTrackablePart H X E) :
    ¬ e.toFinset ⊆ X := by
  classical
  change e ∈ E.filter (fun e ↦
    ¬ e.IsDiag ∧ e ∉ graphEdges H ∧ ¬ e.toFinset ⊆ X) at he
  exact (mem_filter.mp he).2.2.2

/-- A prescribed uncovered event implies survival of every chosen tracked
subfamily.  This is the event-level bridge used by the sharp recurrence. -/
lemma subset_greedyUncoveredEdges_of_tracked_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    {E B : Finset (Sym2 V)} (hB : B ⊆ offdiagPart E)
    (S : GreedyStateOn V)
    (hE : ∀ e ∈ E, e ∉ (coveredGraph S.chosen).edgeSet) :
    B ⊆ greedyUncoveredEdges
      (graphEdges (SimpleGraph.completeGraph V)) S := by
  exact hB.trans
    ((offdiagPart_subset_greedyUncoveredEdges_complete_iff E S).2 hE)

/-- The terminal actual selected/uncovered event is bounded by a sharp
product which tracks only `B`. -/
theorem timedStoppedGreedyProcess_probability_initialEvent_le_trackedProduct
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (Inv : GreedyStateOn V → Prop)
    (D d : ℕ → ℕ) (theta rho : ℕ → ℝ≥0)
    (S₀ : GreedyStateOn V)
    (hInv₀ : Inv S₀) (hactive₀ : active 0 S₀)
    (hInv : ∀ i, i < n → ∀ S, Inv S → active i S →
      (greedyKernel F S).SupportedOn Inv)
    (hD : ∀ i, i < n → 0 < D i)
    (hfloor : ∀ i S, i < n → Inv S → active i S →
      D i ≤ S.available.card)
    (Q : TripleSystemOn V) (E B : Finset (Sym2 V))
    (hB : B ⊆ offdiagPart E)
    (hQpacking : IsPackingOn Q)
    (hQB : Disjoint (Q.biUnion tripleEdgeFinset) B)
    (hsupply : ∀ i S R, i < n → Inv S → active i S → R ⊆ Q →
      Q \ R ⊆ S.available →
      B ⊆ greedyUncoveredEdges
        (graphEdges (SimpleGraph.completeGraph V)) S →
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
    (hE₀ : ∀ e ∈ E, e ∉ (coveredGraph S₀.chosen).edgeSet) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
        (fun z ↦ Q ⊆ z.2.chosen ∧
          ∀ e ∈ E, e ∉ (coveredGraph z.2.chosen).edgeSet) ≤
      cumulativeSurvival theta n ^ B.card *
          transferPointWeight theta rho n ^ Q.card +
        (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
          (fun z ↦ ¬ active z.1.1 z.2) := by
  let Eall := graphEdges (SimpleGraph.completeGraph V)
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  have hBoff : ∀ e ∈ B, ¬ e.IsDiag := by
    intro e he
    exact offdiagPart_offdiag E e (hB he)
  have hB₀ : B ⊆ greedyUncoveredEdges Eall S₀ := by
    simpa only [Eall] using
      subset_greedyUncoveredEdges_of_tracked_subset hB S₀ hE₀
  have hsplit :=
    timedStoppedGreedyProcess_probability_selectedUncovered_le_tracked_add_inactive
      n F active Eall S₀ Q B
  have hproduct :=
    timedStoppedGreedyProcess_probability_selectedAvailableTracked_le_product
      n F active Inv Eall D d theta rho S₀ hInv₀ hactive₀ hInv hD hfloor
      Q B hQpacking hQB hBoff hsupply hscalar htheta hadjust
      hQselected hQavailable hB₀
  calc
    L.probability (fun z ↦ Q ⊆ z.2.chosen ∧
        ∀ e ∈ E, e ∉ (coveredGraph z.2.chosen).edgeSet) ≤
        L.probability (fun z ↦ Q ⊆ z.2.chosen ∧
          B ⊆ greedyUncoveredEdges Eall z.2) := by
      apply L.probability_mono
      intro z hz
      exact ⟨hz.1, subset_greedyUncoveredEdges_of_tracked_subset
        hB z.2 hz.2⟩
    _ ≤ L.probability (fun z ↦ Q ⊆ z.2.chosen ∧
          B ⊆ timedActiveTrackedUncoveredEdges active Eall z) +
        L.probability (fun z ↦ ¬ active z.1.1 z.2) := hsplit
    _ ≤ cumulativeSurvival theta n ^ B.card *
          transferPointWeight theta rho n ^ Q.card +
        L.probability (fun z ↦ ¬ active z.1.1 z.2) := by
      gcongr

/-- Structural incompatibilities can still be discharged using the full
prescribed edge family, while the compatible probability estimate may use a
smaller tracked subfamily. -/
theorem initialProductBound_of_tracked_patterns
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq Omega] [DecidableEq V]
    (L : FiniteLaw Omega) (selected : Omega → TripleSystemOn V)
    (ambient : TripleSystemOn V)
    (tracked : Finset (Sym2 V) → Finset (Sym2 V))
    (survival point p C b : ℝ≥0)
    (hstruct : L.SupportedOn fun omega ↦
      IsPackingOn (selected omega) ∧ selected omega ⊆ ambient)
    (hcompatible : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      IsPackingOn Q →
      Disjoint (Q.biUnion tripleEdgeFinset) (offdiagPart E) →
      Q ⊆ ambient →
      L.probability (fun omega ↦ Q ⊆ selected omega ∧
          ∀ e ∈ E, e ∉ (coveredGraph (selected omega)).edgeSet) ≤
        survival ^ (tracked E).card * point ^ Q.card + b)
    (hscale : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      survival ^ (tracked E).card * point ^ Q.card + b ≤
        C ^ (Q.card + E.card) *
          (p ^ E.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b)) :
    IsInitialProductBound L selected p C b := by
  intro Q E
  by_cases hQpacking : IsPackingOn Q
  · by_cases hdisjoint :
        Disjoint (Q.biUnion tripleEdgeFinset) (offdiagPart E)
    · by_cases hQambient : Q ⊆ ambient
      · exact (hcompatible Q E hQpacking hdisjoint hQambient).trans
          (hscale Q E)
      · calc
          L.probability (fun omega ↦ Q ⊆ selected omega ∧
              ∀ e ∈ E,
                e ∉ (coveredGraph (selected omega)).edgeSet) ≤
              L.probability (fun _ ↦ False) := by
            apply L.probability_mono_of_supported hstruct
            intro omega hs hevent
            exact (hQambient (hevent.1.trans hs.2)).elim
          _ = 0 := L.probability_false
          _ ≤ C ^ (Q.card + E.card) *
              (p ^ E.card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b) := bot_le
    · calc
        L.probability (fun omega ↦ Q ⊆ selected omega ∧
            ∀ e ∈ E,
              e ∉ (coveredGraph (selected omega)).edgeSet) ≤
            L.probability (fun _ ↦ False) := by
          apply L.probability_mono_of_supported hstruct
          intro omega _hs hevent
          rw [Finset.not_disjoint_iff] at hdisjoint
          obtain ⟨e, heQ, heE⟩ := hdisjoint
          obtain ⟨T, hTQ, heT⟩ := mem_biUnion.mp heQ
          have hecovered :
              e ∈ (coveredGraph (selected omega)).edgeSet := by
            rw [coveredGraph_edgeSet_eq_biUnion]
            exact mem_biUnion.mpr ⟨T, hevent.1 hTQ, heT⟩
          exact (hevent.2 e (offdiagPart_subset E heE) hecovered).elim
        _ = 0 := L.probability_false
        _ ≤ C ^ (Q.card + E.card) *
            (p ^ E.card *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b) := bot_le
  · calc
      L.probability (fun omega ↦ Q ⊆ selected omega ∧
          ∀ e ∈ E,
            e ∉ (coveredGraph (selected omega)).edgeSet) ≤
          L.probability (fun _ ↦ False) := by
        apply L.probability_mono_of_supported hstruct
        intro omega hs hevent
        exact (hQpacking (hs.1.mono hevent.1)).elim
      _ = 0 := L.probability_false
      _ ≤ C ^ (Q.card + E.card) *
          (p ^ E.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b) := bot_le

/-- It is enough to prove the sharp product estimate for bounded
prescriptions.  For larger prescriptions the additive error, amplified by
the strong-law constant, may be used to dominate the trivial probability
bound `1`. -/
theorem initialProductBound_of_bounded_tracked_patterns
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq Omega] [DecidableEq V]
    (L : FiniteLaw Omega) (selected : Omega → TripleSystemOn V)
    (ambient : TripleSystemOn V)
    (tracked : Finset (Sym2 V) → Finset (Sym2 V))
    (K : ℕ) (survival point p C b : ℝ≥0)
    (hstruct : L.SupportedOn fun omega ↦
      IsPackingOn (selected omega) ∧ selected omega ⊆ ambient)
    (hsmall : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      IsPackingOn Q →
      Disjoint (Q.biUnion tripleEdgeFinset) (offdiagPart E) →
      Q ⊆ ambient → Q.card + E.card ≤ K →
      L.probability (fun omega ↦ Q ⊆ selected omega ∧
          ∀ e ∈ E, e ∉ (coveredGraph (selected omega)).edgeSet) ≤
        survival ^ (tracked E).card * point ^ Q.card + b)
    (hscale : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      Q.card + E.card ≤ K →
      survival ^ (tracked E).card * point ^ Q.card + b ≤
        C ^ (Q.card + E.card) *
          (p ^ E.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b))
    (hlarge : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      K < Q.card + E.card →
      1 ≤ C ^ (Q.card + E.card) *
        (p ^ E.card *
          (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b)) :
    IsInitialProductBound L selected p C b := by
  intro Q E
  by_cases hQpacking : IsPackingOn Q
  · by_cases hdisjoint :
        Disjoint (Q.biUnion tripleEdgeFinset) (offdiagPart E)
    · by_cases hQambient : Q ⊆ ambient
      · by_cases hcard : Q.card + E.card ≤ K
        · exact (hsmall Q E hQpacking hdisjoint hQambient hcard).trans
            (hscale Q E hcard)
        · exact (L.probability_le_one _).trans
            (hlarge Q E (Nat.lt_of_not_ge hcard))
      · calc
          L.probability (fun omega ↦ Q ⊆ selected omega ∧
              ∀ e ∈ E,
                e ∉ (coveredGraph (selected omega)).edgeSet) ≤
              L.probability (fun _ ↦ False) := by
            apply L.probability_mono_of_supported hstruct
            intro omega hs hevent
            exact (hQambient (hevent.1.trans hs.2)).elim
          _ = 0 := L.probability_false
          _ ≤ C ^ (Q.card + E.card) *
              (p ^ E.card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b) := bot_le
    · calc
        L.probability (fun omega ↦ Q ⊆ selected omega ∧
            ∀ e ∈ E,
              e ∉ (coveredGraph (selected omega)).edgeSet) ≤
            L.probability (fun _ ↦ False) := by
          apply L.probability_mono_of_supported hstruct
          intro omega _hs hevent
          rw [Finset.not_disjoint_iff] at hdisjoint
          obtain ⟨e, heQ, heE⟩ := hdisjoint
          obtain ⟨T, hTQ, heT⟩ := mem_biUnion.mp heQ
          have hecovered :
              e ∈ (coveredGraph (selected omega)).edgeSet := by
            rw [coveredGraph_edgeSet_eq_biUnion]
            exact mem_biUnion.mpr ⟨T, hevent.1 hTQ, heT⟩
          exact (hevent.2 e (offdiagPart_subset E heE) hecovered).elim
        _ = 0 := L.probability_false
        _ ≤ C ^ (Q.card + E.card) *
            (p ^ E.card *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b) := bot_le
  · calc
      L.probability (fun omega ↦ Q ⊆ selected omega ∧
          ∀ e ∈ E,
            e ∉ (coveredGraph (selected omega)).edgeSet) ≤
          L.probability (fun _ ↦ False) := by
        apply L.probability_mono_of_supported hstruct
        intro omega hs hevent
        exact (hQpacking (hs.1.mono hevent.1)).elim
      _ = 0 := L.probability_false
      _ ≤ C ^ (Q.card + E.card) *
          (p ^ E.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b) := bot_le

/-- Scalar conversion when only a subfamily of the prescribed edges is
tracked.  Every omitted factor is harmless once `1 ≤ C*p`. -/
theorem initialProductScale_of_tracked_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (tracked : Finset (Sym2 V) → Finset (Sym2 V))
    (survival point p C b : ℝ≥0)
    (htracked : ∀ E, tracked E ⊆ E)
    (hsurvival : survival ≤ C * p)
    (hpoint : point ≤ C * (Fintype.card V : ℝ≥0)⁻¹)
    (hCp : 1 ≤ C * p) (hC : 1 ≤ C)
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) :
    survival ^ (tracked E).card * point ^ Q.card + b ≤
      C ^ (Q.card + E.card) *
        (p ^ E.card *
          (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b) := by
  let Ninv : ℝ≥0 := (Fintype.card V : ℝ≥0)⁻¹
  have hBcard : (tracked E).card ≤ E.card :=
    card_le_card (htracked E)
  have hsurvivalPow :
      survival ^ (tracked E).card ≤ (C * p) ^ (tracked E).card := by
    exact pow_le_pow_left₀ zero_le hsurvival _
  have hpointPow : point ^ Q.card ≤ (C * Ninv) ^ Q.card := by
    exact pow_le_pow_left₀ zero_le
      (by simpa only [Ninv] using hpoint) _
  have hmissing :
      (C * p) ^ (tracked E).card ≤ (C * p) ^ E.card :=
    pow_le_pow_right₀ hCp hBcard
  have hmain :
      survival ^ (tracked E).card * point ^ Q.card ≤
        C ^ (Q.card + E.card) *
          (p ^ E.card * Ninv ^ Q.card) := by
    calc
      survival ^ (tracked E).card * point ^ Q.card ≤
          (C * p) ^ (tracked E).card * (C * Ninv) ^ Q.card := by
        gcongr
      _ ≤ (C * p) ^ E.card * (C * Ninv) ^ Q.card := by
        gcongr
      _ = C ^ (Q.card + E.card) *
          (p ^ E.card * Ninv ^ Q.card) := by
        rw [mul_pow, mul_pow, pow_add]
        ring
  have hCpow : 1 ≤ C ^ (Q.card + E.card) := one_le_pow₀ hC
  calc
    survival ^ (tracked E).card * point ^ Q.card + b ≤
        C ^ (Q.card + E.card) *
            (p ^ E.card * Ninv ^ Q.card) +
          C ^ (Q.card + E.card) * b := by
      exact add_le_add hmain (by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hCpow (zero_le : 0 ≤ b))
    _ = C ^ (Q.card + E.card) *
        (p ^ E.card *
          (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b) := by
      simp only [Ninv, mul_add]

end

end Erdos207
