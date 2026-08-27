/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpScheduledBoundedSharpInitialLaw
import ErdosProblems.Erdos207.SharpScheduledTrackedResidualLaw
import ErdosProblems.Erdos207.TrackedResidualIncidence
import ErdosProblems.Erdos207.OuterOnlyPreliminaryGeometry

/-!
# The sharp scheduled initial law on the outer-only family

The long initial sparsification is run only on triangles disjoint from the
first inner vortex set.  This wrapper combines the bounded sharp product law
with the structural support facts needed by the first master transition.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The sharp tracked-edge law controls precisely the residual
outside--outside stars used by the internal cover.  Crossing edges are not
charged to this event. -/
theorem timedSharpScheduledOuterOnly_probability_not_internalIncidenceGood_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (fuel : ℕ) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (U : Finset V) (A : TripleSystemOn V)
    (S₀ : GreedyStateOn V)
    (Kpair Kglobal Kinc Delta delta I Dcut r : ℕ)
    (Dschedule dschedule Mschedule uschedule : ℕ → ℕ)
    (b : ℝ≥0)
    (hAbs₀ : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S₀)
    (houtside₀ : OutsideLeavePairsAlive
      (internalOuterGraph G U)ᶜ U S₀)
    (hchosen₀ : S₀.chosen = ∅)
    (hsmallPair : 3 + Kpair < delta)
    (hactive₀ : timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
      Kinc Delta delta I Dcut Dschedule dschedule Mschedule uschedule 0 S₀)
    (hD : ∀ i, i < fuel → 0 < Dschedule i)
    (hdM : ∀ i, i < fuel → dschedule i ≤ Mschedule i)
    (heffective : ∀ i, i < fuel →
      dschedule i - 3 * r < Mschedule i)
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
        (preliminaryResidualInternalEdges G U z.2.chosen) v).card < r) ≤
      trackedResidualOuterIncidenceTail V (internalOuterGraph G U) U
        (cumulativeSurvival
          (boundedSharpSurvivalSchedule fuel Mschedule dschedule (3 * r))
          fuel) b r := by
  dsimp only
  let Gout := internalOuterGraph G U
  let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
    Kinc Delta delta I Dcut Dschedule dschedule Mschedule uschedule
  let L := FiniteLaw.timedStoppedProcessLaw fuel
    (fun _ ↦ greedyKernel F) active S₀
  have htracked : ∀ E : Finset (Sym2 V), E.card = r →
      E ⊆ outerGraphEdges Gout U →
      L.probability (fun z ↦
        ∀ e ∈ E, e ∉ (coveredGraph z.2.chosen).edgeSet) ≤
        cumulativeSurvival
            (boundedSharpSurvivalSchedule fuel Mschedule dschedule (3 * r))
            fuel ^ E.card + b := by
    intro E hEcard hE
    have htrackable : outsideTrackablePart Goutᶜ U E = E :=
      outsideTrackablePart_eq_self_of_subset_outerGraphEdges
        disjoint_compl_left hE
    simpa only [L, active, Gout] using
      timedSharpScheduledAggregatePairBand_probability_trackableUncovered_le
        fuel F Goutᶜ U (outerOnlyAvailable U A) S₀ Kpair Kglobal Kinc
        Delta delta I Dcut r Dschedule dschedule Mschedule uschedule b
        hAbs₀ houtside₀ hchosen₀ hsmallPair hactive₀ hD hdM heffective
        hinactive E (by omega) htrackable
  have hraw := probability_exists_large_residualOuter_incidence_le_of_tracked
    Gout U
      (cumulativeSurvival
        (boundedSharpSurvivalSchedule fuel Mschedule dschedule (3 * r)) fuel)
      b r htracked
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

/-- A sharp scheduled outer-only process supplies both the initial product
estimate and the packing/avoidance/geometry certificate used by the first
master transition. -/
theorem timedSharpScheduledOuterOnly_initialProductLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (fuel : ℕ) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (U : Finset V) (A : TripleSystemOn V)
    (S₀ : GreedyStateOn V)
    (Kpair Kglobal Kinc Delta delta I Dcut K : ℕ)
    (Dschedule dschedule Mschedule uschedule : ℕ → ℕ)
    (p C b : ℝ≥0)
    (hAbs₀ : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S₀)
    (houtside₀ : OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S₀)
    (hchosen₀ : S₀.chosen = ∅)
    (hsmallPair : 3 + Kpair < delta)
    (hactive₀ : timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
      Kinc Delta delta I Dcut Dschedule dschedule Mschedule uschedule 0 S₀)
    (hD : ∀ i, i < fuel → 0 < Dschedule i)
    (hdM : ∀ i, i < fuel → dschedule i ≤ Mschedule i)
    (heffective : ∀ i, i < fuel →
      dschedule i - 3 * K < Mschedule i)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw fuel (fun _ ↦ greedyKernel F)
        (timedSharpScheduledAggregatePairBandActive F Kpair Kglobal Kinc
          Delta delta I Dcut Dschedule dschedule Mschedule uschedule)
        S₀).probability
        (fun z ↦ ¬ timedSharpScheduledAggregatePairBandActive F Kpair
          Kglobal Kinc Delta delta I Dcut Dschedule dschedule Mschedule
            uschedule z.1.1 z.2) ≤ b)
    (hsurvival : cumulativeSurvival
        (boundedSharpSurvivalSchedule fuel Mschedule dschedule (3 * K))
        fuel ≤ C * p)
    (hpoint : transferPointWeight
        (boundedSharpSurvivalSchedule fuel Mschedule dschedule (3 * K))
        (boundedSharpTransferSchedule fuel Dschedule Mschedule dschedule
          (3 * K)) fuel ≤
      C * (Fintype.card V : ℝ≥0)⁻¹)
    (hCp : 1 ≤ C * p) (hC : 1 ≤ C)
    (hlarge : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      K < Q.card + E.card →
      1 ≤ C ^ (Q.card + E.card) *
        (p ^ E.card *
          (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b)) :
    let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
      Kinc Delta delta I Dcut Dschedule dschedule Mschedule uschedule
    let L := FiniteLaw.timedStoppedProcessLaw fuel
      (fun _ ↦ greedyKernel F) active S₀
    IsInitialProductBound L (fun z ↦ z.2.chosen) p C b ∧
      L.SupportedOn (fun z ↦
        z.2.chosen ⊆ A ∧ IsPackingOn z.2.chosen ∧
          AvoidsForbidden z.2.chosen F ∧
          TrianglesDisjointFrom U z.2.chosen) := by
  dsimp only
  let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
    Kinc Delta delta I Dcut Dschedule dschedule Mschedule uschedule
  let L := FiniteLaw.timedStoppedProcessLaw fuel
    (fun _ ↦ greedyKernel F) active S₀
  have hproduct : IsInitialProductBound L (fun z ↦ z.2.chosen) p C b := by
    simpa only [L, active] using
      timedSharpScheduledAggregatePairBand_boundedSharpInitialProductBound
        fuel F (internalOuterGraph G U)ᶜ U (outerOnlyAvailable U A) S₀
        Kpair Kglobal Kinc Delta delta I Dcut K Dschedule dschedule
        Mschedule uschedule p C b hAbs₀ houtside₀ hchosen₀ hsmallPair
        hactive₀ hD hdM heffective hinactive hsurvival hpoint hCp hC hlarge
  have hsupport : L.SupportedOn (fun z ↦
      AbsorberGreedyInvariant F (outerOnlyAvailable U A) z.2) := by
    apply FiniteLaw.timedStoppedProcessLaw_supported fuel
      (fun _ ↦ greedyKernel F) active S₀ hAbs₀
    intro _i _hi S hS
    exact absorberGreedyKernel_supported hS
  refine ⟨hproduct, ?_⟩
  intro z hz
  have hS := hsupport z hz
  have hselectedOuter : z.2.chosen ⊆ outerOnlyAvailable U A := hS.2.1.1
  refine ⟨hselectedOuter.trans (outerOnlyAvailable_subset U A),
    hS.1.1, hS.1.2.1, ?_⟩
  intro T hT
  exact (mem_outerOnlyAvailable_iff.mp (hselectedOuter hT)).2

end

end Erdos207
