/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ConditionedCompressedProtectedReserveStage
import ErdosProblems.Erdos207.MasterOutsidePairSurvival
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryKernel

/-!
# A reserve-protected preliminary stage relative to an old master packing

The first reserve-protected wrapper used a fixed graph and started from the
empty packing.  A genuine later vortex step has a graph, availability, and
old `I/D` split depending on the current master outcome.  This file packages
the pointwise application of the same twice-conditioned kernel.  Only the
new difference from `I ∪ D` is charged in the product law.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The total reserve-protected preliminary kernel at a later master state. -/
def relativeReserveProtectedPreliminaryKernel
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (U : Finset V)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool)
    (Kpair Kglobal Kinc Delta delta Icut Dcut d : ℕ)
    (omega : Omega) :
    FiniteLaw (FiniteLaw.TimedState (GreedyStateOn V) n) :=
  reserveProtectedConditionedPreliminaryKernel n F (G omega) U
    (reserveEdges (G omega) U (bits omega)) (A omega)
    (I omega ∪ D omega) Kpair Kglobal Kinc Delta delta Icut Dcut d

/-- The genuinely new preliminary family at a later master state. -/
def relativeReserveProtectedPreliminaryAdded
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (I D : Omega → TripleSystemOn V) (omega : Omega)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n) : TripleSystemOn V :=
  z.2.chosen \ (I omega ∪ D omega)

/-- All support and product facts needed to attach the fixed-reserve internal
kernel to a later preliminary stage. -/
structure RelativeReserveProtectedPreliminaryFacts
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    (L : FiniteLaw Omega) (F : ForbiddenFamilyOn V) (U : Finset V)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool)
    (n Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint cutoff : ℕ)
    (alphaPre etaPre : ℝ≥0) where
  outerProduct : ∀ omega, 0 < L.mass omega → ∀ Q E,
    (relativeReserveProtectedPreliminaryKernel n F U G A I D bits
      Kpair Kglobal Kinc Delta delta Icut Dcut d omega).probability
      (fun z ↦
        Q ⊆ relativeReserveProtectedPreliminaryAdded I D omega z ∧
          E ⊆ preliminaryResidualOuterEdges
            (reserveProtectedOuterGraph (G omega) U
              (reserveEdges (G omega) U (bits omega))) U z.2.chosen) ≤
      alphaPre ^ Q.card * etaPre ^ E.card
  trajectory : (L.jointBind
      (relativeReserveProtectedPreliminaryKernel n F U G A I D bits
        Kpair Kglobal Kinc Delta delta Icut Dcut d)).SupportedOn (fun z ↦
    RelativeGreedyTrajectory F
      (relativePreliminaryInitialState (I z.1 ∪ D z.1)
        (reserveProtectedOuterAvailable (G z.1) U
          (reserveEdges (G z.1) U (bits z.1)) (A z.1))) z.2.2)
  addedCard : (L.jointBind
      (relativeReserveProtectedPreliminaryKernel n F U G A I D bits
        Kpair Kglobal Kinc Delta delta Icut Dcut d)).SupportedOn (fun z ↦
    (relativeReserveProtectedPreliminaryAdded I D z.1 z.2).card ≤ n)
  atMostOne : (L.jointBind
      (relativeReserveProtectedPreliminaryKernel n F U G A I D bits
        Kpair Kglobal Kinc Delta delta Icut Dcut d)).SupportedOn (fun z ↦
    TrianglesMeetAtMostOne U
      (relativeReserveProtectedPreliminaryAdded I D z.1 z.2))
  protectedAvailable : (L.jointBind
      (relativeReserveProtectedPreliminaryKernel n F U G A I D bits
        Kpair Kglobal Kinc Delta delta Icut Dcut d)).SupportedOn (fun z ↦
    relativeReserveProtectedPreliminaryAdded I D z.1 z.2 ⊆
      reserveProtectedAvailable (reserveEdges (G z.1) U (bits z.1))
        (A z.1))
  selected : (L.jointBind
      (relativeReserveProtectedPreliminaryKernel n F U G A I D bits
        Kpair Kglobal Kinc Delta delta Icut Dcut d)).SupportedOn (fun z ↦
    relativeReserveProtectedPreliminaryAdded I D z.1 z.2 ⊆ A z.1)
  oldDisjoint : (L.jointBind
      (relativeReserveProtectedPreliminaryKernel n F U G A I D bits
        Kpair Kglobal Kinc Delta delta Icut Dcut d)).SupportedOn (fun z ↦
    Disjoint (I z.1 ∪ D z.1)
      (relativeReserveProtectedPreliminaryAdded I D z.1 z.2))
  packing : (L.jointBind
      (relativeReserveProtectedPreliminaryKernel n F U G A I D bits
        Kpair Kglobal Kinc Delta delta Icut Dcut d)).SupportedOn (fun z ↦
    IsPackingOn (I z.1 ∪ (D z.1 ∪
      relativeReserveProtectedPreliminaryAdded I D z.1 z.2)))
  avoids : (L.jointBind
      (relativeReserveProtectedPreliminaryKernel n F U G A I D bits
        Kpair Kglobal Kinc Delta delta Icut Dcut d)).SupportedOn (fun z ↦
    AvoidsForbidden (I z.1 ∪ (D z.1 ∪
      relativeReserveProtectedPreliminaryAdded I D z.1 z.2)) F)
  accumulate : (L.jointBind
      (relativeReserveProtectedPreliminaryKernel n F U G A I D bits
        Kpair Kglobal Kinc Delta delta Icut Dcut d)).SupportedOn (fun z ↦
    I z.1 ∪ (D z.1 ∪
      relativeReserveProtectedPreliminaryAdded I D z.1 z.2) = z.2.2.chosen)
  supply : (L.jointBind
      (relativeReserveProtectedPreliminaryKernel n F U G A I D bits
        Kpair Kglobal Kinc Delta delta Icut Dcut d)).SupportedOn (fun z ↦
    ∀ e ∈ internalOuterEdges (G z.1) U,
      a + Dint ≤ (activeReserveWedgeVertices (G z.1) U
        (iterationExtensionVertices (A z.1)
          (SimpleGraph.edge e.out.1 e.out.2) U)
        e.out.1 e.out.2 (bits z.1)).card)
  incidence : (L.jointBind
      (relativeReserveProtectedPreliminaryKernel n F U G A I D bits
        Kpair Kglobal Kinc Delta delta Icut Dcut d)).SupportedOn (fun z ↦
    ∀ v : V, (scheduledEdgesAt
      (preliminaryResidualInternalEdges (G z.1) U
        (I z.1 ∪ D z.1 ∪
          relativeReserveProtectedPreliminaryAdded I D z.1 z.2)) v).card ≤ d)

/-- Pointwise-good old master states and the common reserve-good event give
the complete later-stage preliminary package.  The two displayed rate
bounds permit a uniform product base even though the incidence tail depends
on the current graph. -/
theorem relativeReserveProtectedPreliminaryFacts
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} (i : Fin ell)
    {level : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {p etaMaster xi : ℝ≥0} {h : ℕ}
    (hpoint : L.SupportedOn fun omega ↦
      IsMasterStagePointwiseGood W level F (G omega) (A omega)
        (I omega) (D omega) p etaMaster xi h)
    (cutoff : ℕ)
    (hstageGood : L.SupportedOn fun omega ↦
      ReserveProtectedStageGood W i (G omega) (A omega)
        (I omega ∪ D omega) cutoff (bits omega))
    (n Kpair Kglobal Kinc Delta delta Icut Dcut M supply d a Dint : ℕ)
    (hDcut : 0 < Dcut) (hsupplyM : supply ≤ M)
    (h3supply : 3 * supply ≤ delta)
    (alpha eta epsilon alphaPre etaPre : ℝ≥0)
    (hsmall : 3 + Kpair < delta)
    (hactive₀ : L.SupportedOn fun omega ↦
      timedAggregateAveragePairBandActive F Kpair Kglobal Kinc Delta
        delta Icut Dcut 0
        (relativePreliminaryInitialState (I omega ∪ D omega)
          (reserveProtectedOuterAvailable (G omega) (W.U i.succ)
            (reserveEdges (G omega) (W.U i.succ) (bits omega))
            (A omega))))
    (hupper : ∀ omega, 0 < L.mass omega → ∀ j S,
      timedAggregateAveragePairBandActive F Kpair Kglobal Kinc Delta
        delta Icut Dcut j S → S.available.card ≤ M)
    (hselected : (n : ℝ≥0) * (Dcut : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - supply : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (hinactive : ∀ omega, 0 < L.mass omega →
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedAggregateAveragePairBandActive F Kpair Kglobal Kinc Delta
          delta Icut Dcut)
        (relativePreliminaryInitialState (I omega ∪ D omega)
          (reserveProtectedOuterAvailable (G omega) (W.U i.succ)
            (reserveEdges (G omega) (W.U i.succ) (bits omega))
            (A omega)))).probability
        (fun z ↦ ¬ timedAggregateAveragePairBandActive F Kpair Kglobal
          Kinc Delta delta Icut Dcut z.1.1 z.2) ≤ epsilon)
    (hepsilon : epsilon < 1)
    (htail : ∀ omega, 0 < L.mass omega →
      residualOuterIncidenceTail V
        (internalOuterGraph (G omega) (W.U i.succ)) (W.U i.succ)
        (eta / (1 - epsilon)) (d + 1) < 1)
    (halphaPre : ∀ omega, 0 < L.mass omega →
      alpha / (1 - epsilon) /
        (1 - residualOuterIncidenceTail V
          (internalOuterGraph (G omega) (W.U i.succ)) (W.U i.succ)
          (eta / (1 - epsilon)) (d + 1)) ≤ alphaPre)
    (hetaPre : ∀ omega, 0 < L.mass omega →
      eta / (1 - epsilon) /
        (1 - residualOuterIncidenceTail V
          (internalOuterGraph (G omega) (W.U i.succ)) (W.U i.succ)
          (eta / (1 - epsilon)) (d + 1)) ≤ etaPre)
    (hcutoff : a + Dint ≤ cutoff) :
    RelativeReserveProtectedPreliminaryFacts L F (W.U i.succ) G A I D bits
      n Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint cutoff
      alphaPre etaPre := by
  let Kpre := relativeReserveProtectedPreliminaryKernel n F (W.U i.succ)
    G A I D bits Kpair Kglobal Kinc Delta delta Icut Dcut d
  let added : Omega → FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := relativeReserveProtectedPreliminaryAdded I D
  have hSpec (omega : Omega) (hmass : 0 < L.mass omega) :=
    reserveProtectedConditionedPreliminaryKernel_spec n F (G omega)
      (W.U i.succ) (reserveEdges (G omega) (W.U i.succ) (bits omega))
      (A omega) (I omega ∪ D omega)
      (reserveEdges_subset_crossingEdges (G omega) (W.U i.succ)
        (bits omega))
      Kpair Kglobal Kinc Delta delta Icut Dcut M supply d hDcut hsupplyM
      h3supply alpha eta epsilon
      (greedyInvariant_relativePreliminaryInitialState_of_masterPointwiseGood
        (hpoint omega hmass))
      (hpoint omega hmass).2.2.2.2.1 (hstageGood omega hmass).2 hsmall
      (hactive₀ omega hmass) (hupper omega hmass) hselected hsurvived
      (hinactive omega hmass) hepsilon (htail omega hmass)
  have hOuter (omega : Omega) (hmass : 0 < L.mass omega) :=
    reserveProtectedConditionedPreliminaryKernel_outerProduct n F (G omega)
      (W.U i.succ) (reserveEdges (G omega) (W.U i.succ) (bits omega))
      (A omega) (I omega ∪ D omega)
      (reserveEdges_subset_crossingEdges (G omega) (W.U i.succ)
        (bits omega))
      Kpair Kglobal Kinc Delta delta Icut Dcut M supply d hDcut hsupplyM
      h3supply alpha eta epsilon
      (greedyInvariant_relativePreliminaryInitialState_of_masterPointwiseGood
        (hpoint omega hmass))
      (hpoint omega hmass).2.2.2.2.1 (hstageGood omega hmass).2 hsmall
      (hactive₀ omega hmass) (hupper omega hmass) hselected hsurvived
      (hinactive omega hmass) hepsilon (htail omega hmass)
  have hmasses : ∀ z, 0 < (L.jointBind Kpre).mass z →
      0 < L.mass z.1 ∧ 0 < (Kpre z.1).mass z.2 := by
    intro z hz
    exact (FiniteLaw.jointBind_mass_pos_iff L Kpre z.1 z.2).mp hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro omega hmass Q E
    have hraw := hOuter omega hmass Q E
    exact hraw.trans (by
      gcongr
      · exact halphaPre omega hmass
      · exact hetaPre omega hmass)
  · intro z hz
    have hm := hmasses z hz
    simpa only [Kpre, relativeReserveProtectedPreliminaryKernel] using
      (hSpec z.1 hm.1).2.1 z.2 hm.2
  · intro z hz
    have hm := hmasses z hz
    have hInv :=
      greedyInvariant_relativePreliminaryInitialState_of_masterPointwiseGood
        (hpoint z.1 hm.1)
    simpa only [Kpre, relativeReserveProtectedPreliminaryKernel,
      relativeReserveProtectedPreliminaryAdded] using
      reserveProtectedConditionedPreliminaryKernel_supported_added_card_le
        n F (G z.1) (W.U i.succ)
        (reserveEdges (G z.1) (W.U i.succ) (bits z.1)) (A z.1)
        (I z.1 ∪ D z.1) Kpair Kglobal Kinc Delta delta Icut Dcut d
        hInv z.2 hm.2
  · intro z hz T hT x y hxT hxU hyT hyU
    have hm := hmasses z hz
    have htraj := (hSpec z.1 hm.1).2.1 z.2 hm.2
    have hsub : relativeReserveProtectedPreliminaryAdded I D z.1 z.2 ⊆
        reserveProtectedOuterAvailable (G z.1) (W.U i.succ)
          (reserveEdges (G z.1) (W.U i.succ) (bits z.1)) (A z.1) := by
      simpa only [relativeReserveProtectedPreliminaryAdded,
        relativePreliminaryInitialState_chosen,
        relativePreliminaryInitialState_available] using
          htraj.added_subset_available
    exact trianglesMeetAtMostOne_reserveProtectedOuterAvailable
      (G z.1) (W.U i.succ)
      (reserveEdges (G z.1) (W.U i.succ) (bits z.1)) (A z.1)
      T (hsub hT) hxT hxU hyT hyU
  · intro z hz
    have hm := hmasses z hz
    simpa only [Kpre, added, relativeReserveProtectedPreliminaryKernel,
      relativeReserveProtectedPreliminaryAdded] using
      (hSpec z.1 hm.1).2.2.2.1 z.2 hm.2
  · intro z hz
    exact ((show relativeReserveProtectedPreliminaryAdded I D z.1 z.2 ⊆
        reserveProtectedAvailable
          (reserveEdges (G z.1) (W.U i.succ) (bits z.1)) (A z.1) from
      (by
        have hm := hmasses z hz
        simpa only [Kpre, added, relativeReserveProtectedPreliminaryKernel,
          relativeReserveProtectedPreliminaryAdded] using
          (hSpec z.1 hm.1).2.2.2.1 z.2 hm.2))).trans
      (reserveProtectedAvailable_subset _ _)
  · intro z _hz
    rw [Finset.disjoint_left]
    intro T hTold hTnew
    exact (mem_sdiff.mp hTnew).2 hTold
  · intro z hz
    have hm := hmasses z hz
    have htraj := (hSpec z.1 hm.1).2.1 z.2 hm.2
    have hs := htraj.structural_newPart
      (I := I z.1) (D := D z.1)
      (A := reserveProtectedOuterAvailable (G z.1) (W.U i.succ)
        (reserveEdges (G z.1) (W.U i.succ) (bits z.1)) (A z.1))
      rfl rfl (hpoint z.1 hm.1).1
    simpa only [relativeReserveProtectedPreliminaryAdded,
      relativePreliminaryInitialState_chosen] using hs.2.2
  · intro z hz
    have hm := hmasses z hz
    have htraj := (hSpec z.1 hm.1).2.1 z.2 hm.2
    have hacc : I z.1 ∪ (D z.1 ∪
        relativeReserveProtectedPreliminaryAdded I D z.1 z.2) =
        z.2.2.chosen := by
      simpa only [relativeReserveProtectedPreliminaryAdded, ← union_assoc,
        relativePreliminaryInitialState_chosen] using htraj.initial_union_added
    rw [hacc]
    exact htraj.1.2.1
  · intro z hz
    have hm := hmasses z hz
    have htraj := (hSpec z.1 hm.1).2.1 z.2 hm.2
    simpa only [relativeReserveProtectedPreliminaryAdded, ← union_assoc,
      relativePreliminaryInitialState_chosen] using htraj.initial_union_added
  · intro z hz e he
    have hm := hmasses z hz
    exact hcutoff.trans (Nat.le_of_lt ((hstageGood z.1 hm.1).1 e he))
  · intro z hz v
    have hm := hmasses z hz
    simpa only [Kpre, added, relativeReserveProtectedPreliminaryKernel,
      relativeReserveProtectedPreliminaryAdded, union_assoc] using
      (hSpec z.1 hm.1).2.2.2.2 z.2 hm.2 v

end

end Erdos207
