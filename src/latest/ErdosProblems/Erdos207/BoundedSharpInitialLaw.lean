/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OutsideTrackableSupply
import ErdosProblems.Erdos207.BoundedSharpSurvivalScalar

/-!
# The bounded sharp law for the initial sparsification

This is the law-level endpoint of the retrospective recurrence.  The active
predicate may encode any synchronized trajectory estimates.  Its only
quantitative obligations here are time-dependent lower floors for total
availability and live pair stars, and an upper envelope for total
availability.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Totalized survival schedule; values beyond the finite horizon are set
to one because the stopped process never inspects them. -/
def boundedSharpSurvivalSchedule
    (n : ℕ) (M d : ℕ → ℕ) (K i : ℕ) : ℝ≥0 :=
  if i < n then boundedSharpSurvivalTheta (M i) (d i) K else 1

/-- Totalized point-transfer schedule corresponding to
`boundedSharpSurvivalSchedule`. -/
def boundedSharpTransferSchedule
    (n : ℕ) (D M d : ℕ → ℕ) (K i : ℕ) : ℝ≥0 :=
  if i < n then boundedSharpTransferRho (D i) (M i) (d i) K
  else (D i : ℝ≥0)⁻¹

lemma pending_edge_count_le_three_mul_patternCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {Q R : TripleSystemOn V} {E B : Finset (Sym2 V)} {K : ℕ}
    (hR : R ⊆ Q) (hB : B ⊆ E) (hcard : Q.card + E.card ≤ K) :
    3 * (Q \ R).card + B.card ≤ 3 * K := by
  have hQR : (Q \ R).card ≤ Q.card := card_le_card sdiff_subset
  have hBE : B.card ≤ E.card := card_le_card hB
  omega

/-- Complete sharp initial product law for all bounded prescriptions, with
large prescriptions paid by the amplified additive error. -/
theorem timedStoppedGreedyProcess_boundedSharpInitialProductBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H : SimpleGraph V) (X : Finset V)
    (active : ℕ → GreedyStateOn V → Prop)
    (Inv : GreedyStateOn V → Prop)
    (D d M : ℕ → ℕ) (K : ℕ)
    (S₀ : GreedyStateOn V)
    (hchosen₀ : S₀.chosen = ∅)
    (hInv₀ : Inv S₀) (hactive₀ : active 0 S₀)
    (hInv : ∀ i, i < n → ∀ S, Inv S → active i S →
      (greedyKernel F S).SupportedOn Inv)
    (hstructInv : ∀ S, Inv S →
      IsPackingOn S.chosen ∧ S.chosen ⊆ S₀.available)
    (houtside : ∀ S, Inv S → OutsideLeavePairsAlive H X S)
    (hD : ∀ i, i < n → 0 < D i)
    (hfloor : ∀ i S, i < n → Inv S → active i S →
      D i ≤ S.available.card)
    (hpairFloor : ∀ i S, i < n → Inv S → active i S →
      HasAvailablePairFloor (d i) S)
    (hupper : ∀ i S, i < n → Inv S → active i S →
      S.available.card ≤ M i)
    (hdM : ∀ i, i < n → d i ≤ M i)
    (heffective : ∀ i, i < n → d i - 3 * K < M i)
    (p C b : ℝ≥0)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
          (fun z ↦ ¬ active z.1.1 z.2) ≤ b)
    (hsurvival : cumulativeSurvival
        (boundedSharpSurvivalSchedule n M d (3 * K)) n ≤
      C * p)
    (hpoint : transferPointWeight
        (boundedSharpSurvivalSchedule n M d (3 * K))
        (boundedSharpTransferSchedule n D M d (3 * K)) n ≤
      C * (Fintype.card V : ℝ≥0)⁻¹)
    (hCp : 1 ≤ C * p) (hC : 1 ≤ C)
    (hlarge : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      K < Q.card + E.card →
      1 ≤ C ^ (Q.card + E.card) *
        (p ^ E.card *
          (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b)) :
    IsInitialProductBound
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀)
      (fun z ↦ z.2.chosen) p C b := by
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let tracked : Finset (Sym2 V) → Finset (Sym2 V) :=
    outsideTrackablePart H X
  let theta : ℕ → ℝ≥0 := fun i ↦
    boundedSharpSurvivalSchedule n M d (3 * K) i
  let rho : ℕ → ℝ≥0 := fun i ↦
    boundedSharpTransferSchedule n D M d (3 * K) i
  have hInvSupport : L.SupportedOn (fun z ↦ Inv z.2) := by
    apply (FiniteLaw.supportedOn_pure
      (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦ Inv z.2)
      hInv₀).evolveKernels
    intro _j z hz
    classical
    unfold FiniteLaw.timedStoppedKernel
    split_ifs with hrun
    · exact (hInv z.1.1 hrun.1 z.2 hz hrun.2).map
        (fun S' ↦ (FiniteLaw.advanceTime z.1 hrun.1, S'))
        (fun _S' hS' ↦ hS')
    · exact FiniteLaw.supportedOn_pure _ hz
  have hstruct : L.SupportedOn fun z ↦
      IsPackingOn z.2.chosen ∧ z.2.chosen ⊆ S₀.available := by
    intro z hz
    exact hstructInv z.2 (hInvSupport z hz)
  apply initialProductBound_of_bounded_tracked_patterns L
    (fun z ↦ z.2.chosen) S₀.available tracked K
    (cumulativeSurvival theta n) (transferPointWeight theta rho n)
    p C b hstruct
  · intro Q E hQpacking hQE hQavailable hcard
    let B := tracked E
    have hBoff : B ⊆ offdiagPart E := by
      simpa only [B, tracked] using
        outsideTrackablePart_subset_offdiagPart H X E
    have hQB : Disjoint (Q.biUnion tripleEdgeFinset) B :=
      hQE.mono_right hBoff
    have hE₀ : ∀ e ∈ E,
        e ∉ (coveredGraph S₀.chosen).edgeSet := by
      intro e heE hecovered
      rw [hchosen₀, coveredGraph_edgeSet_eq_biUnion] at hecovered
      simpa using hecovered
    have hsupply : ∀ i S R, i < n → Inv S → active i S → R ⊆ Q →
        Q \ R ⊆ S.available →
        B ⊆ greedyUncoveredEdges
          (graphEdges (SimpleGraph.completeGraph V)) S →
        ∀ e ∈ pendingSurvivalEdges (Q \ R) B,
          d i ≤ (greedyChoicesCoveringEdge S e).card := by
      intro i S R hi hIS hactive hRQ hpending hBuncovered
      simpa only [B, tracked] using
        pendingSurvivalEdges_supply_of_pairFloor_trackable
          (H := H) (X := X) (E := E)
          (hpairFloor i S hi hIS hactive) (houtside S hIS)
          hpending hBuncovered
    have hscalar : ∀ i S R, i < n → Inv S → active i S → R ⊆ Q →
        ((S.available.card -
            ((3 * (Q \ R).card + B.card) * d i -
              (3 * (Q \ R).card + B.card).choose 2) : ℕ) : ℝ≥0) *
            (S.available.card : ℝ≥0)⁻¹ ≤
          theta i ^ (3 * (Q \ R).card + B.card) := by
      intro i S R hi hIS hactive hRQ
      have hA : 0 < S.available.card :=
        (hD i hi).trans_le (hfloor i S hi hIS hactive)
      have hAM : S.available.card ≤ M i := hupper i S hi hIS hactive
      have hk : 3 * (Q \ R).card + B.card ≤ 3 * K :=
        pending_edge_count_le_three_mul_patternCutoff hRQ
          (outsideTrackablePart_subset H X E) hcard
      simpa only [theta, boundedSharpSurvivalSchedule, if_pos hi,
        boundedSharpSurvivalTheta] using
        sharp_survival_scalar_of_card_le S.available.card (M i) (d i)
          (3 * K) (3 * (Q \ R).card + B.card)
          hA hAM (hdM i hi) hk
    have htheta : ∀ i, theta i ≤ 1 := by
      intro i
      by_cases hi : i < n
      · simpa only [theta, boundedSharpSurvivalSchedule, if_pos hi] using
          boundedSharpSurvivalTheta_le_one (M i) (d i) (3 * K)
            (lt_of_le_of_lt (Nat.zero_le _) (heffective i hi))
      · simp [theta, boundedSharpSurvivalSchedule, if_neg hi]
    have hadjust : ∀ i, (D i : ℝ≥0)⁻¹ ≤
        theta i ^ (3 * Q.card + B.card) * rho i := by
      intro i
      have hk : 3 * Q.card + B.card ≤ 3 * K := by
        have hBE : B.card ≤ E.card := card_le_card
          (outsideTrackablePart_subset H X E)
        omega
      by_cases hi : i < n
      · have hMpos : 0 < M i :=
          lt_of_le_of_lt (Nat.zero_le _) (heffective i hi)
        have htpos : 0 < boundedSharpSurvivalTheta (M i) (d i) (3 * K) :=
          boundedSharpSurvivalTheta_pos (M i) (d i) (3 * K)
            (heffective i hi)
        simpa only [theta, rho, boundedSharpSurvivalSchedule,
          boundedSharpTransferSchedule, if_pos hi] using
          inv_le_pow_mul_boundedSharpTransferRho
            (D i) (M i) (d i) (3 * K) (3 * Q.card + B.card)
            hk hMpos htpos
      · simp [theta, rho, boundedSharpSurvivalSchedule,
          boundedSharpTransferSchedule, if_neg hi]
    have hraw :=
      timedStoppedGreedyProcess_probability_initialEvent_le_trackedProduct
        n F active Inv D d theta rho S₀ hInv₀ hactive₀
        (fun i hi S hIS hactive ↦ hInv i hi S hIS hactive) hD hfloor
        Q E B hBoff hQpacking hQB hsupply hscalar htheta hadjust
        (by simpa [hchosen₀]) hQavailable hE₀
    exact hraw.trans (by
      simpa only [B, tracked] using
        add_le_add_right hinactive
          (cumulativeSurvival theta n ^ B.card *
            transferPointWeight theta rho n ^ Q.card))
  · intro Q E _hcard
    exact initialProductScale_of_tracked_subset tracked
      (cumulativeSurvival theta n) (transferPointWeight theta rho n)
      p C b
      (by
        intro E'
        simpa only [tracked] using outsideTrackablePart_subset H X E')
      (by simpa only [theta] using hsurvival)
      (by simpa only [theta, rho] using hpoint) hCp hC Q E
  · exact hlarge

end

end Erdos207
