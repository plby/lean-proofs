/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.JointInclusionFactorialTail
import ErdosProblems.Erdos207.OuterOnlySharpScheduledInitialProductLaw

/-!
# Residual-degree tails from bounded tracked-edge moments

The witness order `s` controls the interference allowance in the sharp
survival schedule.  The independent parameter `R` is the actual residual
degree cutoff required by the subsequent internal cover-down.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

def trackedResidualOuterFactorialTail
    (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V)
    (survival b : ℝ≥0) (s R : ℕ) : ℝ≥0 :=
  ∑ v : V,
    ((outerIncidentEdges G U v).card.choose s : ℝ≥0) *
      (survival ^ s + b) / (R.choose s : ℝ≥0)

theorem probability_exists_large_residualOuter_incidence_le_of_tracked_moment
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Omega} {selected : Omega → TripleSystemOn V}
    (G : SimpleGraph V) (U : Finset V) (survival b : ℝ≥0)
    (s R : ℕ) (hsR : s ≤ R)
    (htracked : ∀ E : Finset (Sym2 V), E.card = s →
      E ⊆ outerGraphEdges G U →
      L.probability (fun omega ↦
        ∀ e ∈ E, e ∉ (coveredGraph (selected omega)).edgeSet) ≤
          survival ^ E.card + b) :
    L.probability (fun omega ↦ ∃ v : V,
      R ≤ (outerIncidentEdges G U v ∩
        preliminaryResidualOuterEdges G U (selected omega)).card) ≤
      trackedResidualOuterFactorialTail V G U survival b s R := by
  classical
  have hraw := L.probability_exists_card_inter_ge_le_factorialMoment
    (fun omega ↦ preliminaryResidualOuterEdges G U (selected omega))
    (outerIncidentEdges G U) univ s (fun _ ↦ R) (survival ^ s + b)
    (fun _ _ ↦ hsR) (by
      intro v _hv E hE
      have hcard := (mem_powersetCard.mp hE).2
      have houter : E ⊆ outerGraphEdges G U := by
        intro e he
        exact (mem_outerIncidentEdges_iff.mp
          ((mem_powersetCard.mp hE).1 he)).1
      calc
        L.probability (fun omega ↦
            E ⊆ preliminaryResidualOuterEdges G U (selected omega)) ≤
            L.probability (fun omega ↦ ∀ e ∈ E,
              e ∉ (coveredGraph (selected omega)).edgeSet) := by
          apply L.probability_mono
          intro omega hres
          exact subset_uncovered_of_subset_preliminaryResidualOuterEdges hres
        _ ≤ survival ^ s + b := by
          simpa only [hcard] using htracked E hcard houter)
  simpa only [mem_univ, true_and, trackedResidualOuterFactorialTail] using hraw

/-- Uniform degree bounds turn the exact binomial ratio into a power. -/
theorem trackedResidualOuterFactorialTail_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (survival b : ℝ≥0)
    (s R m : ℕ) (hR : 0 < R) (hs : 2 * s ≤ R)
    (hdegree : ∀ v : V, (outerIncidentEdges G U v).card ≤ m) :
    trackedResidualOuterFactorialTail V G U survival b s R ≤
      (Fintype.card V : ℝ≥0) * (2 * (m : ℝ≥0) / R) ^ s *
        (survival ^ s + b) := by
  unfold trackedResidualOuterFactorialTail
  calc
    (∑ v : V,
        ((outerIncidentEdges G U v).card.choose s : ℝ≥0) *
          (survival ^ s + b) / (R.choose s : ℝ≥0)) ≤
        ∑ _v : V, (2 * (m : ℝ≥0) / R) ^ s * (survival ^ s + b) := by
      apply sum_le_sum
      intro v _hv
      rw [mul_div_right_comm]
      apply mul_le_mul_of_nonneg_right _ zero_le
      apply (choose_ratio_le_two_mul_div_pow _ R s hR hs).trans
      gcongr
      exact_mod_cast hdegree v
    _ = (Fintype.card V : ℝ≥0) * (2 * (m : ℝ≥0) / R) ^ s *
        (survival ^ s + b) := by simp [mul_assoc]

/-- Sharp scheduled outer-only residual tail, retaining a small witness
order independently of the terminal degree cutoff. -/
theorem timedSharpScheduledOuterOnly_probability_not_internalIncidenceGood_le_moment
    {V : Type*} [Fintype V] [DecidableEq V]
    (fuel : ℕ) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (U : Finset V) (A : TripleSystemOn V)
    (S₀ : GreedyStateOn V)
    (Kpair Kglobal Kinc Delta delta I Dcut s R : ℕ)
    (Dschedule dschedule Mschedule uschedule : ℕ → ℕ)
    (b : ℝ≥0) (hsR : s ≤ R)
    (hAbs₀ : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S₀)
    (houtside₀ : OutsideLeavePairsAlive
      (internalOuterGraph G U)ᶜ U S₀)
    (hchosen₀ : S₀.chosen = ∅)
    (hsmallPair : 3 + Kpair < delta)
    (hactive₀ : timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
      Kinc Delta delta I Dcut Dschedule dschedule Mschedule uschedule 0 S₀)
    (hD : ∀ i, i < fuel → 0 < Dschedule i)
    (hdM : ∀ i, i < fuel → dschedule i ≤ Mschedule i)
    (heffective : ∀ i, i < fuel → dschedule i - 3 * s < Mschedule i)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw fuel (fun _ ↦ greedyKernel F)
        (timedSharpScheduledAggregatePairBandActive F Kpair Kglobal Kinc
          Delta delta I Dcut Dschedule dschedule Mschedule uschedule)
        S₀).probability
        (fun z ↦ ¬ timedSharpScheduledAggregatePairBandActive F Kpair
          Kglobal Kinc Delta delta I Dcut Dschedule dschedule Mschedule
            uschedule z.1.1 z.2) ≤ b) :
    let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
      Kinc Delta delta I Dcut Dschedule dschedule Mschedule uschedule
    let L := FiniteLaw.timedStoppedProcessLaw fuel
      (fun _ ↦ greedyKernel F) active S₀
    L.probability (fun z ↦ ¬ ∀ v : V,
      (scheduledEdgesAt
        (preliminaryResidualInternalEdges G U z.2.chosen) v).card < R) ≤
      trackedResidualOuterFactorialTail V (internalOuterGraph G U) U
        (cumulativeSurvival
          (boundedSharpSurvivalSchedule fuel Mschedule dschedule (3 * s))
          fuel) b s R := by
  dsimp only
  let Gout := internalOuterGraph G U
  let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
    Kinc Delta delta I Dcut Dschedule dschedule Mschedule uschedule
  let L := FiniteLaw.timedStoppedProcessLaw fuel
    (fun _ ↦ greedyKernel F) active S₀
  have htracked : ∀ E : Finset (Sym2 V), E.card = s →
      E ⊆ outerGraphEdges Gout U →
      L.probability (fun z ↦
        ∀ e ∈ E, e ∉ (coveredGraph z.2.chosen).edgeSet) ≤
        cumulativeSurvival
            (boundedSharpSurvivalSchedule fuel Mschedule dschedule (3 * s))
            fuel ^ E.card + b := by
    intro E hEcard hE
    have htrackable : outsideTrackablePart Goutᶜ U E = E :=
      outsideTrackablePart_eq_self_of_subset_outerGraphEdges
        disjoint_compl_left hE
    simpa only [L, active, Gout] using
      timedSharpScheduledAggregatePairBand_probability_trackableUncovered_le
        fuel F Goutᶜ U (outerOnlyAvailable U A) S₀ Kpair Kglobal Kinc
        Delta delta I Dcut s Dschedule dschedule Mschedule uschedule b
        hAbs₀ houtside₀ hchosen₀ hsmallPair hactive₀ hD hdM heffective
        hinactive E (by omega) htrackable
  have hraw :=
    probability_exists_large_residualOuter_incidence_le_of_tracked_moment
      Gout U
      (cumulativeSurvival
        (boundedSharpSurvivalSchedule fuel Mschedule dschedule (3 * s)) fuel)
      b s R hsR htracked
  have hstar : ∀ (P : TripleSystemOn V) (v : V),
      scheduledEdgesAt (internalOuterEdges G U) v ∩
          preliminaryResidualInternalEdges G U P =
        scheduledEdgesAt (preliminaryResidualInternalEdges G U P) v := by
    intro P v
    ext e
    simp only [mem_inter, mem_scheduledEdgesAt_iff]
    constructor
    · rintro ⟨⟨_heInternal, hev⟩, heResidual⟩
      exact ⟨heResidual, hev⟩
    · rintro ⟨heResidual, hev⟩
      exact ⟨⟨preliminaryResidualInternalEdges_subset_internalOuterEdges
        G U P heResidual, hev⟩, heResidual⟩
  simpa only [L, Gout, outerIncidentEdges_internalOuterGraph,
    preliminaryResidualOuterEdges_internalOuterGraph, hstar, not_forall,
    not_lt] using hraw

end

end Erdos207
