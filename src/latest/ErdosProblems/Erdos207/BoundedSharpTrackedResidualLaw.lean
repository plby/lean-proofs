/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BoundedSharpInitialLaw

/-!
# The sharp tracked-edge law retained by the initial sparsification

The coarse `IsInitialProductBound` deliberately pays for absorber edges and
root-internal pairs by a factor satisfying `1 ≤ C * p`.  That coarse form is
therefore not suitable for the residual-star tail.  For genuinely trackable
outer edges the proof before that last coarse comparison gives the sharper
survival product.  This file exposes precisely that retained estimate.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The bounded sharp process retains the unamplified product estimate for
every bounded family consisting entirely of trackable outside pairs. -/
theorem timedStoppedGreedyProcess_probability_trackableUncovered_le
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
    (b : ℝ≥0)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
          (fun z ↦ ¬ active z.1.1 z.2) ≤ b) :
    ∀ E : Finset (Sym2 V), E.card ≤ K →
      outsideTrackablePart H X E = E →
      (FiniteLaw.timedStoppedProcessLaw n
          (fun _ ↦ greedyKernel F) active S₀).probability
          (fun z ↦ ∀ e ∈ E,
            e ∉ (coveredGraph z.2.chosen).edgeSet) ≤
        cumulativeSurvival
            (boundedSharpSurvivalSchedule n M d (3 * K)) n ^ E.card + b := by
  intro E hEcard htrack
  let theta : ℕ → ℝ≥0 := fun i ↦
    boundedSharpSurvivalSchedule n M d (3 * K) i
  let rho : ℕ → ℝ≥0 := fun i ↦
    boundedSharpTransferSchedule n D M d (3 * K) i
  let Q : TripleSystemOn V := ∅
  have hBoff : E ⊆ offdiagPart E := by
    intro e he
    exact outsideTrackablePart_subset_offdiagPart H X E
      (by simpa only [htrack] using he)
  have hQB : Disjoint (Q.biUnion tripleEdgeFinset) E := by
    simp [Q]
  have hE₀ : ∀ e ∈ E,
      e ∉ (coveredGraph S₀.chosen).edgeSet := by
    intro e heE hecovered
    rw [hchosen₀, coveredGraph_edgeSet_eq_biUnion] at hecovered
    simpa using hecovered
  have hsupply : ∀ i S R, i < n → Inv S → active i S → R ⊆ Q →
      Q \ R ⊆ S.available →
      E ⊆ greedyUncoveredEdges
        (graphEdges (SimpleGraph.completeGraph V)) S →
      ∀ e ∈ pendingSurvivalEdges (Q \ R) E,
        d i ≤ (greedyChoicesCoveringEdge S e).card := by
    intro i S R hi hIS hactive hRQ hpending hEuncovered
    have htrackSub : outsideTrackablePart H X E ⊆
        greedyUncoveredEdges
          (graphEdges (SimpleGraph.completeGraph V)) S := by
      simpa only [htrack] using hEuncovered
    have hs := pendingSurvivalEdges_supply_of_pairFloor_trackable
      (H := H) (X := X) (E := E)
      (hpairFloor i S hi hIS hactive) (houtside S hIS)
      hpending htrackSub
    simpa only [htrack] using hs
  have hscalar : ∀ i S R, i < n → Inv S → active i S → R ⊆ Q →
      ((S.available.card -
          ((3 * (Q \ R).card + E.card) * d i -
            (3 * (Q \ R).card + E.card).choose 2) : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤
        theta i ^ (3 * (Q \ R).card + E.card) := by
    intro i S R hi hIS hactive hRQ
    have hRempty : R = ∅ := by
      apply Subset.antisymm
      · simpa only [Q] using hRQ
      · exact empty_subset R
    subst R
    have hA : 0 < S.available.card :=
      (hD i hi).trans_le (hfloor i S hi hIS hactive)
    have hAM : S.available.card ≤ M i := hupper i S hi hIS hactive
    have hk : 3 * (Q \ ∅).card + E.card ≤ 3 * K := by
      simp only [Q, empty_sdiff, card_empty, zero_mul, zero_add]
      omega
    simpa only [theta, boundedSharpSurvivalSchedule, if_pos hi,
      boundedSharpSurvivalTheta] using
      sharp_survival_scalar_of_card_le S.available.card (M i) (d i)
        (3 * K) (3 * (Q \ ∅).card + E.card)
        hA hAM (hdM i hi) hk
  have htheta : ∀ i, theta i ≤ 1 := by
    intro i
    by_cases hi : i < n
    · simpa only [theta, boundedSharpSurvivalSchedule, if_pos hi] using
        boundedSharpSurvivalTheta_le_one (M i) (d i) (3 * K)
          (lt_of_le_of_lt (Nat.zero_le _) (heffective i hi))
    · simp [theta, boundedSharpSurvivalSchedule, if_neg hi]
  have hadjust : ∀ i, (D i : ℝ≥0)⁻¹ ≤
      theta i ^ (3 * Q.card + E.card) * rho i := by
    intro i
    have hk : 3 * Q.card + E.card ≤ 3 * K := by
      simp only [Q, card_empty, zero_mul, zero_add]
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
          (D i) (M i) (d i) (3 * K) (3 * Q.card + E.card)
          hk hMpos htpos
    · simp [theta, rho, boundedSharpSurvivalSchedule,
        boundedSharpTransferSchedule, if_neg hi]
  have hraw :=
    timedStoppedGreedyProcess_probability_initialEvent_le_trackedProduct
      n F active Inv D d theta rho S₀ hInv₀ hactive₀ hInv hD hfloor
      Q E E hBoff (by
        intro u v huv T hT
        simp [Q] at hT) hQB hsupply hscalar htheta hadjust
      (by simp [Q, hchosen₀]) (by simp [Q]) hE₀
  have hraw' :
      (FiniteLaw.timedStoppedProcessLaw n
          (fun _ ↦ greedyKernel F) active S₀).probability
          (fun z ↦ ∀ e ∈ E,
            e ∉ (coveredGraph z.2.chosen).edgeSet) ≤
        cumulativeSurvival
            (boundedSharpSurvivalSchedule n M d (3 * K)) n ^ E.card +
          (FiniteLaw.timedStoppedProcessLaw n
            (fun _ ↦ greedyKernel F) active S₀).probability
              (fun z ↦ ¬ active z.1.1 z.2) := by
    simpa only [Q, empty_subset, true_and, theta, rho, card_empty, pow_zero,
      mul_one] using hraw
  exact hraw'.trans (add_le_add_right hinactive _)

end

end Erdos207
