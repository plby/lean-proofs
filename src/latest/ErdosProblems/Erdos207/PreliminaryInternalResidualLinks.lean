/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryInternalComposition
import ErdosProblems.Erdos207.InternalEdgeIntermediateLaw

/-!
# Residual links after the preliminary and internal laws

The preliminary family covers every crossing edge outside its augmented
reserve by definition.  Combining that fact with the supported internal-edge
cover gives exactly `InternalOutcomeReady`, hence the canonical residual
links and all reserve-spoke certificates on the whole support.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Structural support of the preliminary state together with support of the
internal kernel gives the complete input expected by the residual-link
constructor. -/
theorem FiniteLaw.SupportedOn.internalOutcomeReady_of_internalCover
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V]
    {law : FiniteLaw Omega} {K : Omega → FiniteLaw Xi}
    {G : Omega → SimpleGraph V} {U : Finset V}
    {reserve : Omega → Finset (Sym2 V)} {F : ForbiddenFamilyOn V}
    {A I D Mstar P0 : Omega → TripleSystemOn V}
    {Q : Omega → Xi → TripleSystemOn V}
    (hbase : law.SupportedOn fun omega ↦
      (∀ v, Even ((neighborsIn (G omega) univ v).card)) ∧
      G omega ≤ leaveGraph (I omega ∪ D omega) ∧
      ConsistsOfTriangles (G omega) (A omega) ∧
      Mstar omega ⊆ A omega ∧
      Disjoint (I omega) (D omega ∪ Mstar omega) ∧
      IsPackingOn (P0 omega))
    (hP0 : ∀ omega, P0 omega = I omega ∪ (D omega ∪ Mstar omega))
    (hcrossing : ∀ omega,
      CoversCrossingOutsideReserve (G omega) U (reserve omega)
        (Mstar omega))
    (hinternal : (law.jointBind K).SupportedOn fun z ↦
      GreedyReachable F (P0 z.1) (Q z.1 z.2) ∧
      Q z.1 z.2 ⊆ P0 z.1 ∪ A z.1 ∧
      (Q z.1 z.2 \ P0 z.1).card ≤
        (internalOuterEdges (G z.1) U).card ∧
      ∀ e ∈ internalOuterEdges (G z.1) U,
        (coveredGraph (Q z.1 z.2)).Adj e.out.1 e.out.2) :
    (law.jointBind K).SupportedOn
      (InternalOutcomeReady
        (fun z ↦ G z.1) U (fun z ↦ reserve z.1) F
        (fun z ↦ A z.1) (fun z ↦ I z.1) (fun z ↦ D z.1)
        (fun z ↦ Mstar z.1) (fun z ↦ Q z.1 z.2)) := by
  have hbaseJoint : (law.jointBind K).SupportedOn fun z ↦
      (∀ v, Even ((neighborsIn (G z.1) univ v).card)) ∧
      G z.1 ≤ leaveGraph (I z.1 ∪ D z.1) ∧
      ConsistsOfTriangles (G z.1) (A z.1) ∧
      Mstar z.1 ⊆ A z.1 ∧
      Disjoint (I z.1) (D z.1 ∪ Mstar z.1) ∧
      IsPackingOn (P0 z.1) := by
    have h := hbase.jointBind (K := K)
      (Q := fun _omega _xi ↦ True)
      (fun _omega _hbase ↦ by intro _xi _hmass; trivial)
    exact fun z hz ↦ (h z hz).1
  intro z hmass
  have hb := hbaseJoint z hmass
  have hi := hinternal z hmass
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1,
    hb.2.2.2.2.1, ?_, ?_, ?_, hi.2.2.2, ?_⟩
  · simpa only [hP0 z.1] using hb.2.2.2.2.2
  · simpa only [hP0 z.1] using hi.1
  · simpa only [hP0 z.1] using hi.2.1
  · exact hcrossing z.1

/-- Specialize the preceding support bridge to the reserve obtained by
adjoining the preliminary residual crossing edges. -/
theorem FiniteLaw.SupportedOn.internalOutcomeReady_of_preliminaryReserve
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V]
    {law : FiniteLaw Omega} {K : Omega → FiniteLaw Xi}
    {G : Omega → SimpleGraph V} {U : Finset V}
    {sampled : Omega → Finset (Sym2 V)} {F : ForbiddenFamilyOn V}
    {A I D Mstar P0 : Omega → TripleSystemOn V}
    {Q : Omega → Xi → TripleSystemOn V}
    (hbase : law.SupportedOn fun omega ↦
      (∀ v, Even ((neighborsIn (G omega) univ v).card)) ∧
      G omega ≤ leaveGraph (I omega ∪ D omega) ∧
      ConsistsOfTriangles (G omega) (A omega) ∧
      Mstar omega ⊆ A omega ∧
      Disjoint (I omega) (D omega ∪ Mstar omega) ∧
      IsPackingOn (P0 omega))
    (hP0 : ∀ omega, P0 omega = I omega ∪ (D omega ∪ Mstar omega))
    (hinternal : (law.jointBind K).SupportedOn fun z ↦
      GreedyReachable F (P0 z.1) (Q z.1 z.2) ∧
      Q z.1 z.2 ⊆ P0 z.1 ∪ A z.1 ∧
      (Q z.1 z.2 \ P0 z.1).card ≤
        (internalOuterEdges (G z.1) U).card ∧
      ∀ e ∈ internalOuterEdges (G z.1) U,
        (coveredGraph (Q z.1 z.2)).Adj e.out.1 e.out.2) :
    (law.jointBind K).SupportedOn
      (InternalOutcomeReady
        (fun z ↦ G z.1) U
        (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
          (Mstar z.1)) F
        (fun z ↦ A z.1) (fun z ↦ I z.1) (fun z ↦ D z.1)
        (fun z ↦ Mstar z.1) (fun z ↦ Q z.1 z.2)) := by
  apply hbase.internalOutcomeReady_of_internalCover hP0
    (reserve := fun omega ↦ preliminaryAugmentedReserve
      (G omega) U (sampled omega) (Mstar omega))
  · intro omega
    exact coversCrossingOutsideReserve_preliminaryAugmentedReserve
      (G omega) U (sampled omega) (Mstar omega)
  · exact hinternal

/-- The canonical residual links therefore exist as one total function on
the joint sample type and satisfy every intermediate-state and reserve-spoke
condition at positive-mass outcomes. -/
theorem FiniteLaw.SupportedOn.preliminaryInternalResidualLinks
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V]
    {law : FiniteLaw Omega} {K : Omega → FiniteLaw Xi}
    {G : Omega → SimpleGraph V} {U : Finset V}
    {sampled : Omega → Finset (Sym2 V)} {F : ForbiddenFamilyOn V}
    {A I D Mstar P0 : Omega → TripleSystemOn V}
    {Q : Omega → Xi → TripleSystemOn V}
    (hbase : law.SupportedOn fun omega ↦
      (∀ v, Even ((neighborsIn (G omega) univ v).card)) ∧
      G omega ≤ leaveGraph (I omega ∪ D omega) ∧
      ConsistsOfTriangles (G omega) (A omega) ∧
      Mstar omega ⊆ A omega ∧
      Disjoint (I omega) (D omega ∪ Mstar omega) ∧
      IsPackingOn (P0 omega))
    (hP0 : ∀ omega, P0 omega = I omega ∪ (D omega ∪ Mstar omega))
    (hinternal : (law.jointBind K).SupportedOn fun z ↦
      GreedyReachable F (P0 z.1) (Q z.1 z.2) ∧
      Q z.1 z.2 ⊆ P0 z.1 ∪ A z.1 ∧
      (Q z.1 z.2 \ P0 z.1).card ≤
        (internalOuterEdges (G z.1) U).card ∧
      ∀ e ∈ internalOuterEdges (G z.1) U,
        (coveredGraph (Q z.1 z.2)).Adj e.out.1 e.out.2) :
    let Omega' := Omega × Xi
    let G' : Omega' → SimpleGraph V := fun z ↦ G z.1
    let reserve' : Omega' → Finset (Sym2 V) := fun z ↦
      preliminaryAugmentedReserve (G z.1) U (sampled z.1) (Mstar z.1)
    let A' : Omega' → TripleSystemOn V := fun z ↦ A z.1
    let I' : Omega' → TripleSystemOn V := fun z ↦ I z.1
    let D' : Omega' → TripleSystemOn V := fun z ↦ D z.1
    let Mstar' : Omega' → TripleSystemOn V := fun z ↦ Mstar z.1
    let Q' : Omega' → TripleSystemOn V := fun z ↦ Q z.1 z.2
    let R' : Omega' → TripleSystemOn V := fun z ↦
      internalStageFamily (I' z) (D' z) (Mstar' z) (Q' z)
    let center : Omega' → ({x : V // x ∉ U} ↪ V) := fun _ ↦
      outsideVertexEmbedding U
    let links := Erdos207.internalOutcomeResidualLinks G' U reserve' F
      A' I' D' Mstar' Q'
    (law.jointBind K).SupportedOn (fun z ↦
      IsIntermediateLinkState (G' z) U (A' z) (I' z) (D' z) (R' z)
          (links z) ∧
        (∀ o, (links z o).center = center z o) ∧
        (∀ o, center z o ∉ U) ∧
        (∀ o, (links z o).left ⊆ U) ∧
        (∀ o, (links z o).right ⊆ U) ∧
        (∀ o, (links z o).SpokesIn (reserve' z))) := by
  dsimp only
  have hready := hbase.internalOutcomeReady_of_preliminaryReserve
    (sampled := sampled) hP0 hinternal
  exact hready.internalOutcomeResidualLinks

end

end Erdos207
