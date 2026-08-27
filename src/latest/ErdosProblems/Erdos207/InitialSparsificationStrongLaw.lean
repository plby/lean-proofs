/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialSparsificationReserveLaw
import ErdosProblems.Erdos207.SupportedConditionedPreliminaryKernel
import ErdosProblems.Erdos207.TimedActiveAvailableTransfer

/-!
# Strong distribution from the long initial greedy phase

This file converts the sharp timed selected/available/uncovered product law
into the initial-family strong-distribution interface.  Diagonal `Sym2`
elements are separated explicitly: they are never graph edges, and their
missing density factor is paid for by the multiplicative constant.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- The genuine graph edges in an arbitrary finite family of symmetric
pairs. -/
def offdiagPart {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) : Finset (Sym2 V) :=
  E.filter fun e ↦ ¬ e.IsDiag

lemma offdiagPart_subset {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) : offdiagPart E ⊆ E := by
  exact filter_subset _ _

lemma offdiagPart_offdiag {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) :
    ∀ e ∈ offdiagPart E, ¬ e.IsDiag := by
  intro e he
  exact (mem_filter.mp he).2

lemma mem_offdiagPart_iff {V : Type*} [DecidableEq V]
    {E : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ offdiagPart E ↔ e ∈ E ∧ ¬ e.IsDiag := by
  simp [offdiagPart]

/-- Every nondiagonal symmetric pair is an edge of the complete graph. -/
lemma mem_graphEdges_completeGraph_iff_not_isDiag
    {V : Type*} [Fintype V] [DecidableEq V] {e : Sym2 V} :
    e ∈ graphEdges (SimpleGraph.completeGraph V) ↔ ¬ e.IsDiag := by
  rw [mem_graphEdges_iff]
  simpa only [SimpleGraph.edgeSet_top, Set.mem_compl_iff,
    Sym2.mem_diagSet]

/-- The paper's assertion that every prescribed pair is uncovered is
equivalent to inclusion of its nondiagonal part in the complete-graph
residual set. -/
lemma offdiagPart_subset_greedyUncoveredEdges_complete_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (S : GreedyStateOn V) :
    offdiagPart E ⊆
        greedyUncoveredEdges (graphEdges (SimpleGraph.completeGraph V)) S ↔
      ∀ e ∈ E, e ∉ (coveredGraph S.chosen).edgeSet := by
  constructor
  · intro h e heE hecovered
    have hnondiag : ¬ e.IsDiag :=
      (coveredGraph S.chosen).not_isDiag_of_mem_edgeSet hecovered
    have heoff : e ∈ offdiagPart E :=
      mem_offdiagPart_iff.mpr ⟨heE, hnondiag⟩
    have heuncovered := h heoff
    rw [greedyUncoveredEdges, mem_sdiff] at heuncovered
    exact heuncovered.2 (mem_graphEdges_iff.mpr hecovered)
  · intro h e heoff
    have hedata := mem_offdiagPart_iff.mp heoff
    rw [greedyUncoveredEdges, mem_sdiff]
    refine ⟨mem_graphEdges_completeGraph_iff_not_isDiag.mpr hedata.2, ?_⟩
    intro hecovered
    exact h e hedata.1 (mem_graphEdges_iff.mp hecovered)

/-- Mixed selected/uncovered product estimate for the initial family, before
an independent reserve sample is adjoined. -/
def IsInitialProductBound
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Omega) (selected : Omega → TripleSystemOn V)
    (p C b : ℝ≥0) : Prop :=
  ∀ (Ifix : TripleSystemOn V) (Efix : Finset (Sym2 V)),
    L.probability (fun omega ↦
        Ifix ⊆ selected omega ∧
        ∀ e ∈ Efix, e ∉ (coveredGraph (selected omega)).edgeSet) ≤
      C ^ (Ifix.card + Efix.card) *
        (p ^ Efix.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card + b)

/-- An initial product bound is precisely ordinary strong distribution when
all selected triangles are assigned to the initial family. -/
theorem IsInitialProductBound.toStronglyWellDistributed
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} {L : FiniteLaw Omega} {W : Vortex V ell}
    {k : Fin (ell + 1)} {selected : Omega → TripleSystemOn V}
    {p C b : ℝ≥0}
    (h : IsInitialProductBound L selected p C b) :
    IsStronglyWellDistributed L W k selected
      (fun _ ↦ (∅ : TripleSystemOn V)) p C b := by
  intro Ifix Dfix Efix _hdisjoint
  by_cases hD : Dfix = ∅
  · subst Dfix
    have hraw := h Ifix Efix
    have hevent :
        StrongDistributionEvent selected
          (fun _ ↦ (∅ : TripleSystemOn V)) Ifix ∅ Efix =
        (fun omega ↦ Ifix ⊆ selected omega ∧
          ∀ e ∈ Efix,
            e ∉ (coveredGraph (selected omega)).edgeSet) := by
      funext omega
      simp [StrongDistributionEvent]
    rw [hevent]
    simpa [laterTriangleScale] using hraw
  · have himpossible : ∀ omega,
        ¬ StrongDistributionEvent selected
          (fun _ ↦ (∅ : TripleSystemOn V)) Ifix Dfix Efix omega := by
      intro omega hevent
      exact hD (subset_empty.mp hevent.2.1)
    calc
      L.probability (StrongDistributionEvent selected
          (fun _ ↦ (∅ : TripleSystemOn V)) Ifix Dfix Efix) ≤
          L.probability (fun _ ↦ False) := by
        apply L.probability_mono
        intro omega hevent
        exact (himpossible omega hevent).elim
      _ = 0 := L.probability_false
      _ ≤ C ^ (Ifix.card + Dfix.card + Efix.card) *
          (p ^ Efix.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
              laterTriangleScale W k p Dfix + b) := bot_le

/-- It suffices to estimate compatible prescribed patterns.  Packing,
ambient-family, and edge-disjointness failures make the selected/uncovered
event impossible on the structural support of the greedy law. -/
theorem initialProductBound_of_compatible_patterns
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq Omega] [DecidableEq V]
    (L : FiniteLaw Omega) (selected : Omega → TripleSystemOn V)
    (ambient : TripleSystemOn V) (survival point p C b : ℝ≥0)
    (hstruct : L.SupportedOn fun omega ↦
      IsPackingOn (selected omega) ∧ selected omega ⊆ ambient)
    (hcompatible : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      IsPackingOn Q →
      Disjoint (Q.biUnion tripleEdgeFinset) (offdiagPart E) →
      Q ⊆ ambient →
      L.probability (fun omega ↦ Q ⊆ selected omega ∧
          ∀ e ∈ E, e ∉ (coveredGraph (selected omega)).edgeSet) ≤
        survival ^ (offdiagPart E).card * point ^ Q.card + b)
    (hscale : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      survival ^ (offdiagPart E).card * point ^ Q.card + b ≤
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
          have hecovered : e ∈ (coveredGraph (selected omega)).edgeSet := by
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

/-- The two scalar outputs of the retrospective recurrence imply the full
strong-distribution scalar inequality.  Extra diagonal `Sym2` elements are
paid for by the assumption `1 ≤ C * p`, while `1 ≤ C` absorbs the additive
stopping error outside the multiplicative bracket. -/
theorem initialProductScale_of_survival_point
    {V : Type*} [Fintype V] [DecidableEq V]
    (survival point p C b : ℝ≥0)
    (hsurvival : survival ≤ C * p)
    (hpoint : point ≤ C * (Fintype.card V : ℝ≥0)⁻¹)
    (hCp : 1 ≤ C * p) (hC : 1 ≤ C)
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) :
    survival ^ (offdiagPart E).card * point ^ Q.card + b ≤
      C ^ (Q.card + E.card) *
        (p ^ E.card *
          (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b) := by
  let Ninv : ℝ≥0 := (Fintype.card V : ℝ≥0)⁻¹
  have hBcard : (offdiagPart E).card ≤ E.card :=
    card_le_card (offdiagPart_subset E)
  have hsurvivalPow :
      survival ^ (offdiagPart E).card ≤
        (C * p) ^ (offdiagPart E).card := by
    exact pow_le_pow_left₀ zero_le hsurvival _
  have hpointPow : point ^ Q.card ≤ (C * Ninv) ^ Q.card := by
    exact pow_le_pow_left₀ zero_le
      (by simpa only [Ninv] using hpoint) _
  have hdiag :
      (C * p) ^ (offdiagPart E).card ≤ (C * p) ^ E.card :=
    pow_le_pow_right₀ hCp hBcard
  have hmain :
      survival ^ (offdiagPart E).card * point ^ Q.card ≤
        C ^ (Q.card + E.card) *
          (p ^ E.card * Ninv ^ Q.card) := by
    calc
      survival ^ (offdiagPart E).card * point ^ Q.card ≤
          (C * p) ^ (offdiagPart E).card * (C * Ninv) ^ Q.card := by
        gcongr
      _ ≤ (C * p) ^ E.card * (C * Ninv) ^ Q.card := by
        gcongr
      _ = C ^ (Q.card + E.card) *
          (p ^ E.card * Ninv ^ Q.card) := by
        rw [mul_pow, mul_pow, pow_add]
        ring
  have hCpow : 1 ≤ C ^ (Q.card + E.card) := one_le_pow₀ hC
  calc
    survival ^ (offdiagPart E).card * point ^ Q.card + b ≤
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

/-- The terminal actual event is bounded by the sharp active-gated product
law plus the probability that the good-state predicate has stopped. -/
theorem timedStoppedGreedyProcess_probability_initialEvent_le_product_add_inactive
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
    (Q : TripleSystemOn V) (E : Finset (Sym2 V))
    (hQpacking : IsPackingOn Q)
    (hQE : Disjoint (Q.biUnion tripleEdgeFinset) (offdiagPart E))
    (hsupply : ∀ i S R, i < n → Inv S → active i S → R ⊆ Q →
      Q \ R ⊆ S.available →
      offdiagPart E ⊆ greedyUncoveredEdges
        (graphEdges (SimpleGraph.completeGraph V)) S →
      ∀ e ∈ pendingSurvivalEdges (Q \ R) (offdiagPart E),
        d i ≤ (greedyChoicesCoveringEdge S e).card)
    (hscalar : ∀ i S R, i < n → Inv S → active i S → R ⊆ Q →
      ((S.available.card -
          ((3 * (Q \ R).card + (offdiagPart E).card) * d i -
            (3 * (Q \ R).card + (offdiagPart E).card).choose 2) : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤
        theta i ^ (3 * (Q \ R).card + (offdiagPart E).card))
    (htheta : ∀ i, theta i ≤ 1)
    (hadjust : ∀ i, (D i : ℝ≥0)⁻¹ ≤
      theta i ^ (3 * Q.card + (offdiagPart E).card) * rho i)
    (hQselected : Disjoint Q S₀.chosen)
    (hQavailable : Q ⊆ S₀.available)
    (hE₀ : ∀ e ∈ E, e ∉ (coveredGraph S₀.chosen).edgeSet) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
        (fun z ↦ Q ⊆ z.2.chosen ∧
          ∀ e ∈ E, e ∉ (coveredGraph z.2.chosen).edgeSet) ≤
      cumulativeSurvival theta n ^ (offdiagPart E).card *
          transferPointWeight theta rho n ^ Q.card +
        (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
          (fun z ↦ ¬ active z.1.1 z.2) := by
  let Eall := graphEdges (SimpleGraph.completeGraph V)
  let B := offdiagPart E
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  have hB₀ : B ⊆ greedyUncoveredEdges Eall S₀ := by
    simpa only [B, Eall] using
      (offdiagPart_subset_greedyUncoveredEdges_complete_iff E S₀).2 hE₀
  have hsplit :=
    timedStoppedGreedyProcess_probability_selectedUncovered_le_tracked_add_inactive
      n F active Eall S₀ Q B
  have hproduct :=
    timedStoppedGreedyProcess_probability_selectedAvailableTracked_le_product
      n F active Inv Eall D d theta rho S₀ hInv₀ hactive₀ hInv hD hfloor
      Q B hQpacking (by simpa only [B] using hQE)
      (by simpa only [B] using offdiagPart_offdiag E)
      (by simpa only [B] using hsupply)
      (by simpa only [B] using hscalar) htheta
      (by simpa only [B] using hadjust) hQselected hQavailable hB₀
  calc
    L.probability (fun z ↦ Q ⊆ z.2.chosen ∧
        ∀ e ∈ E, e ∉ (coveredGraph z.2.chosen).edgeSet) =
        L.probability (fun z ↦ Q ⊆ z.2.chosen ∧
          B ⊆ greedyUncoveredEdges Eall z.2) := by
      congr 1
      funext z
      simp only [B, Eall,
        offdiagPart_subset_greedyUncoveredEdges_complete_iff]
    _ ≤ L.probability (fun z ↦ Q ⊆ z.2.chosen ∧
          B ⊆ timedActiveTrackedUncoveredEdges active Eall z) +
        L.probability (fun z ↦ ¬ active z.1.1 z.2) := hsplit
    _ ≤ cumulativeSurvival theta n ^ B.card *
          transferPointWeight theta rho n ^ Q.card +
        L.probability (fun z ↦ ¬ active z.1.1 z.2) := by
      gcongr
    _ = cumulativeSurvival theta n ^ (offdiagPart E).card *
          transferPointWeight theta rho n ^ Q.card +
        L.probability (fun z ↦ ¬ active z.1.1 z.2) := rfl

/-- Complete abstract initial-stage strong law.  All combinatorial
incompatibilities are discharged here; an application only has to provide
the synchronized trajectory estimates, the early-stopping tail, and the
final scalar comparison. -/
theorem timedStoppedGreedyProcess_initialProductBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (Inv : GreedyStateOn V → Prop)
    (D d : ℕ → ℕ) (theta rho : ℕ → ℝ≥0)
    (S₀ : GreedyStateOn V)
    (hchosen₀ : S₀.chosen = ∅)
    (hInv₀ : Inv S₀) (hactive₀ : active 0 S₀)
    (hInv : ∀ i, i < n → ∀ S, Inv S →
      (greedyKernel F S).SupportedOn Inv)
    (hstructInv : ∀ S, Inv S →
      IsPackingOn S.chosen ∧ S.chosen ⊆ S₀.available)
    (hD : ∀ i, i < n → 0 < D i)
    (hfloor : ∀ i S, i < n → Inv S → active i S →
      D i ≤ S.available.card)
    (hsupply : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      IsPackingOn Q →
      Disjoint (Q.biUnion tripleEdgeFinset) (offdiagPart E) →
      Q ⊆ S₀.available →
      ∀ i S R, i < n → Inv S → active i S → R ⊆ Q →
        Q \ R ⊆ S.available →
        offdiagPart E ⊆ greedyUncoveredEdges
          (graphEdges (SimpleGraph.completeGraph V)) S →
        ∀ e ∈ pendingSurvivalEdges (Q \ R) (offdiagPart E),
          d i ≤ (greedyChoicesCoveringEdge S e).card)
    (hscalar : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      IsPackingOn Q →
      Disjoint (Q.biUnion tripleEdgeFinset) (offdiagPart E) →
      Q ⊆ S₀.available →
      ∀ i S R, i < n → Inv S → active i S → R ⊆ Q →
        ((S.available.card -
            ((3 * (Q \ R).card + (offdiagPart E).card) * d i -
              (3 * (Q \ R).card + (offdiagPart E).card).choose 2) : ℕ) : ℝ≥0) *
            (S.available.card : ℝ≥0)⁻¹ ≤
          theta i ^ (3 * (Q \ R).card + (offdiagPart E).card))
    (htheta : ∀ i, theta i ≤ 1)
    (hadjust : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      IsPackingOn Q →
      Disjoint (Q.biUnion tripleEdgeFinset) (offdiagPart E) →
      Q ⊆ S₀.available →
      ∀ i, (D i : ℝ≥0)⁻¹ ≤
        theta i ^ (3 * Q.card + (offdiagPart E).card) * rho i)
    (p C b : ℝ≥0)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
          (fun z ↦ ¬ active z.1.1 z.2) ≤ b)
    (hscale : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      cumulativeSurvival theta n ^ (offdiagPart E).card *
          transferPointWeight theta rho n ^ Q.card + b ≤
        C ^ (Q.card + E.card) *
          (p ^ E.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b)) :
    IsInitialProductBound
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀)
      (fun z ↦ z.2.chosen) p C b := by
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  have hInvSupport : L.SupportedOn (fun z ↦ Inv z.2) := by
    exact FiniteLaw.timedStoppedProcessLaw_supported n
      (fun _ ↦ greedyKernel F) active S₀ hInv₀ hInv
  have hstruct : L.SupportedOn fun z ↦
      IsPackingOn z.2.chosen ∧ z.2.chosen ⊆ S₀.available := by
    intro z hz
    exact hstructInv z.2 (hInvSupport z hz)
  apply initialProductBound_of_compatible_patterns L
    (fun z ↦ z.2.chosen) S₀.available
    (cumulativeSurvival theta n) (transferPointWeight theta rho n)
    p C b hstruct
  · intro Q E hQpacking hQE hQavailable
    have hE₀ : ∀ e ∈ E,
        e ∉ (coveredGraph S₀.chosen).edgeSet := by
      intro e heE hecovered
      rw [hchosen₀, coveredGraph_edgeSet_eq_biUnion] at hecovered
      simpa using hecovered
    have hraw :=
      timedStoppedGreedyProcess_probability_initialEvent_le_product_add_inactive
        n F active Inv D d theta rho S₀ hInv₀ hactive₀
        (fun i hi S hIS _hactive ↦ hInv i hi S hIS) hD hfloor
        Q E hQpacking hQE
        (hsupply Q E hQpacking hQE hQavailable)
        (hscalar Q E hQpacking hQE hQavailable) htheta
        (hadjust Q E hQpacking hQE hQavailable)
        (by simpa [hchosen₀]) hQavailable hE₀
    exact hraw.trans (by gcongr)
  · exact hscale

end

end Erdos207
