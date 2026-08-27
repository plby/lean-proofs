/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GraphRestrictedDistribution
import ErdosProblems.Erdos207.BoundedSharpInitialLaw
import ErdosProblems.Erdos207.PatternSurvival
import ErdosProblems.Erdos207.TimedStoppedIndexedInvariant

/-! # The sharp initial law for genuine working-graph edge prescriptions -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem initialGraphProductBound_of_bounded_compatible_patterns
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (selected : Ω → TripleSystemOn V) (G : SimpleGraph V)
    (ambient : TripleSystemOn V) (K : ℕ) (survival point p C b : ℝ≥0)
    (hstruct : L.SupportedOn fun ω ↦ IsPackingOn (selected ω) ∧ selected ω ⊆ ambient)
    (hcompatible : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      IsPackingOn Q → Q ⊆ ambient → Disjoint (Q.biUnion tripleEdgeFinset) E → E ⊆ graphEdges G →
      Q.card + E.card ≤ K →
      L.probability (fun ω ↦ Q ⊆ selected ω ∧ ∀ e ∈ E, e ∉ (coveredGraph (selected ω)).edgeSet) ≤
        survival ^ E.card * point ^ Q.card + b)
    (hsurvival : survival ≤ C * p) (hpoint : point ≤ C * (Fintype.card V : ℝ≥0)⁻¹)
    (hC : 1 ≤ C)
    (hlarge : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)), K < Q.card + E.card →
      1 ≤ C ^ (Q.card + E.card) * (p ^ E.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b)) :
    IsInitialGraphProductBound L selected G p C b := by
  classical
  intro Q E hE
  by_cases hcard : Q.card + E.card ≤ K
  · by_cases hgood : IsPackingOn Q ∧ Q ⊆ ambient ∧ Disjoint (Q.biUnion tripleEdgeFinset) E
    · exact (hcompatible Q E hgood.1 hgood.2.1 hgood.2.2 hE hcard).trans
        (initialGraphProductScale_of_survival_point survival point p C b hsurvival hpoint hC Q E)
    · have hzero : L.probability (fun ω ↦ Q ⊆ selected ω ∧
          ∀ e ∈ E, e ∉ (coveredGraph (selected ω)).edgeSet) ≤ L.probability (fun _ ↦ False) := by
        apply L.probability_mono_of_supported hstruct
        intro ω hω hevent
        apply hgood
        refine ⟨hω.1.mono hevent.1, hevent.1.trans hω.2, disjoint_left.mpr ?_⟩
        intro e heQ heE
        obtain ⟨T, hT, heT⟩ := mem_biUnion.mp heQ
        apply hevent.2 e heE
        rw [coveredGraph_edgeSet_eq_biUnion]
        exact mem_biUnion.mpr ⟨T, hevent.1 hT, heT⟩
      rw [L.probability_false] at hzero
      exact hzero.trans zero_le
  · exact (L.probability_le_one _).trans (hlarge Q E (Nat.lt_of_not_ge hcard))

theorem pendingSurvivalEdges_supply_of_graph_floor
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {Q : TripleSystemOn V}
    {G : SimpleGraph V} {E : Finset (Sym2 V)} {d : ℕ}
    (hInv : GreedyInvariant F S) (hQ : Q ⊆ S.available)
    (havailable : ∀ T ∈ S.available, tripleEdgeFinset T ⊆ graphEdges G)
    (hE : E ⊆ graphEdges G)
    (huncovered : E ⊆ greedyUncoveredEdges (graphEdges (SimpleGraph.completeGraph V)) S)
    (hfloor : ∀ e ∈ graphEdges G, e ∉ (coveredGraph S.chosen).edgeSet →
      d ≤ (greedyChoicesCoveringEdge S e).card) :
    ∀ e ∈ pendingSurvivalEdges Q E, d ≤ (greedyChoicesCoveringEdge S e).card := by
  intro e he
  rw [pendingSurvivalEdges, mem_union] at he
  rcases he with heQ | heE
  · obtain ⟨T, hT, heT⟩ := mem_biUnion.mp heQ
    exact hfloor e (havailable T (hQ hT) heT) (hInv.available_edge_not_covered (hQ hT) heT)
  · apply hfloor e (hE heE)
    intro hc
    exact (mem_sdiff.mp (huncovered heE)).2 (mem_graphEdges_iff.mpr hc)

theorem timedStoppedGreedyProcess_boundedSharpInitialGraphProductBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (G : SimpleGraph V)
    (active : ℕ → GreedyStateOn V → Prop) (Inv : GreedyStateOn V → Prop)
    (D d M : ℕ → ℕ) (K : ℕ) (S₀ : GreedyStateOn V)
    (hchosen₀ : S₀.chosen = ∅) (hInv₀ : Inv S₀) (hactive₀ : active 0 S₀)
    (hInv : ∀ i, i < n → ∀ S, Inv S → active i S → (greedyKernel F S).SupportedOn Inv)
    (hstructInv : ∀ S, Inv S → GreedyInvariant F S ∧ S.available ⊆ S₀.available ∧ S.chosen ⊆ S₀.available)
    (hambient : ∀ T ∈ S₀.available, tripleEdgeFinset T ⊆ graphEdges G)
    (hD : ∀ i, i < n → 0 < D i)
    (hfloor : ∀ i S, i < n → Inv S → active i S → D i ≤ S.available.card)
    (hpairFloor : ∀ i S, i < n → Inv S → active i S →
      ∀ e ∈ graphEdges G, e ∉ (coveredGraph S.chosen).edgeSet → d i ≤ (greedyChoicesCoveringEdge S e).card)
    (hupper : ∀ i S, i < n → Inv S → active i S → S.available.card ≤ M i)
    (hdM : ∀ i, i < n → d i ≤ M i)
    (heffective : ∀ i, i < n → d i - 3 * K < M i)
    (p C b : ℝ≥0)
    (hinactive : (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ ¬ active z.1.1 z.2) ≤ b)
    (hsurvival : cumulativeSurvival (boundedSharpSurvivalSchedule n M d (3 * K)) n ≤ C * p)
    (hpoint : transferPointWeight (boundedSharpSurvivalSchedule n M d (3 * K))
      (boundedSharpTransferSchedule n D M d (3 * K)) n ≤ C * (Fintype.card V : ℝ≥0)⁻¹)
    (hC : 1 ≤ C)
    (hlarge : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)), K < Q.card + E.card →
      1 ≤ C ^ (Q.card + E.card) * (p ^ E.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b)) :
    IsInitialGraphProductBound
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀)
      (fun z ↦ z.2.chosen) G p C b := by
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  let theta := boundedSharpSurvivalSchedule n M d (3 * K)
  let rho := boundedSharpTransferSchedule n D M d (3 * K)
  have hsupport : L.SupportedOn (fun z ↦ Inv z.2) :=
    FiniteLaw.timedStoppedProcessLaw_supported_indexed n (fun _ ↦ greedyKernel F) active
      (fun _ ↦ Inv) S₀ hInv₀ hInv
  have hstruct : L.SupportedOn (fun z ↦ IsPackingOn z.2.chosen ∧ z.2.chosen ⊆ S₀.available) :=
    fun z hz ↦ ⟨(hstructInv z.2 (hsupport z hz)).1.1, (hstructInv z.2 (hsupport z hz)).2.2⟩
  apply initialGraphProductBound_of_bounded_compatible_patterns L (fun z ↦ z.2.chosen) G S₀.available K
    (cumulativeSurvival theta n) (transferPointWeight theta rho n) p C b hstruct
    ?_ hsurvival hpoint hC hlarge
  intro Q E hQpacking hQavailable hQE hE hcard
  have hEoff : E ⊆ offdiagPart E := by rw [offdiagPart_eq_of_subset_graphEdges hE]
  have hE₀ : ∀ e ∈ E, e ∉ (coveredGraph S₀.chosen).edgeSet := by
    intro e _
    simp only [hchosen₀, coveredGraph_empty, SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false, not_false_eq_true]
  have hsupply : ∀ i S R, i < n → Inv S → active i S → R ⊆ Q → Q \ R ⊆ S.available →
      E ⊆ greedyUncoveredEdges (graphEdges (SimpleGraph.completeGraph V)) S →
      ∀ e ∈ pendingSurvivalEdges (Q \ R) E, d i ≤ (greedyChoicesCoveringEdge S e).card := by
    intro i S R hi hIS hact _ hpending hEuncovered
    exact pendingSurvivalEdges_supply_of_graph_floor (hstructInv S hIS).1 hpending
      (fun T hT ↦ hambient T ((hstructInv S hIS).2.1 hT)) hE hEuncovered (hpairFloor i S hi hIS hact)
  have hscalar : ∀ i S R, i < n → Inv S → active i S → R ⊆ Q →
      ((S.available.card - ((3 * (Q \ R).card + E.card) * d i -
        (3 * (Q \ R).card + E.card).choose 2) : ℕ) : ℝ≥0) * (S.available.card : ℝ≥0)⁻¹ ≤
      theta i ^ (3 * (Q \ R).card + E.card) := by
    intro i S R hi hIS hact hRQ
    have hk := pending_edge_count_le_three_mul_patternCutoff hRQ (Subset.refl E) hcard
    simpa only [theta, boundedSharpSurvivalSchedule, if_pos hi, boundedSharpSurvivalTheta] using
      sharp_survival_scalar_of_card_le S.available.card (M i) (d i) (3 * K) _
        ((hD i hi).trans_le (hfloor i S hi hIS hact)) (hupper i S hi hIS hact) (hdM i hi) hk
  have htheta : ∀ i, theta i ≤ 1 := by
    intro i
    by_cases hi : i < n
    · simpa only [theta, boundedSharpSurvivalSchedule, if_pos hi] using
        boundedSharpSurvivalTheta_le_one (M i) (d i) (3 * K)
          (lt_of_le_of_lt (Nat.zero_le _) (heffective i hi))
    · simp [theta, boundedSharpSurvivalSchedule, if_neg hi]
  have hadjust : ∀ i, (D i : ℝ≥0)⁻¹ ≤ theta i ^ (3 * Q.card + E.card) * rho i := by
    intro i
    have hk : 3 * Q.card + E.card ≤ 3 * K := by omega
    by_cases hi : i < n
    · simpa only [theta, rho, boundedSharpSurvivalSchedule, boundedSharpTransferSchedule, if_pos hi] using
        inv_le_pow_mul_boundedSharpTransferRho (D i) (M i) (d i) (3 * K) _ hk
          (lt_of_le_of_lt (Nat.zero_le _) (heffective i hi))
          (boundedSharpSurvivalTheta_pos (M i) (d i) (3 * K) (heffective i hi))
    · simp [theta, rho, boundedSharpSurvivalSchedule, boundedSharpTransferSchedule, if_neg hi]
  have hraw := timedStoppedGreedyProcess_probability_initialEvent_le_trackedProduct n F active Inv D d theta rho
    S₀ hInv₀ hactive₀ hInv hD hfloor Q E E hEoff hQpacking hQE hsupply hscalar htheta hadjust
    (by simp [hchosen₀]) hQavailable hE₀
  exact hraw.trans (add_le_add le_rfl hinactive)

end

end Erdos207
