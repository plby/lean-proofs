/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterCoverDownExtraction
import ErdosProblems.Erdos207.SupportedLinkCoverKernel

/-!
# Support-aware robust final link stage

At the terminal vortex layer no post-link probability estimate is needed.
Consequently supportwise existence of the simultaneous robust-link law can
be totalized immediately and fed to the deterministic outside-packing
extraction theorem.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Iterated terminal form: current availability is only a subfamily of the
original absorber-relative availability, while old selected triangles are
tracked in that original family. -/
theorem exists_ksssOutsidePacking_of_supportedRobustFinalStage_available_subset
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    {law : FiniteLaw Omega}
    {G : Omega → SimpleGraph V}
    {A I D R : Omega → TripleSystemOn V}
    {K : (omega : Omega) → {x : V // x ∉ X} → BipartiteLink V}
    {alpha : ℝ≥0}
    (hA : law.SupportedOn fun omega ↦
      A omega ⊆ outsideAvailableTriangles H B)
    (hselected : law.SupportedOn fun omega ↦
      I omega ∪ D omega ⊆ outsideAvailableTriangles H B)
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph
        (graphDifference (SimpleGraph.completeGraph V) H)
        (G omega) (I omega) (D omega))
    (hstate : law.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) X (A omega) (I omega) (D omega)
        (R omega) (K omega))
    (hready : law.SupportedOn fun omega ↦
      HasSimultaneousLinkCoverFamilyLaw
        (absorberErdosForbiddenConfigurationsOn q B)
        (A omega) (I omega ∪ (D omega ∪ R omega)) (K omega) alpha) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  let linkLaw : Omega → FiniteLaw (TripleSystemOn V) :=
    supportedSimultaneousLinkCoverKernel
      (absorberErdosForbiddenConfigurationsOn q B) A
      (fun omega ↦ I omega ∪ (D omega ∪ R omega)) K alpha
  have hlinkFull :=
    hready.jointBind_supportedSimultaneousLinkCoverKernel
      (absorberErdosForbiddenConfigurationsOn q B) A
      (fun omega ↦ I omega ∪ (D omega ∪ R omega)) K alpha
  have hlink : (law.jointBind linkLaw).SupportedOn fun z ↦
      IsSimultaneousLinkCover
        (absorberErdosForbiddenConfigurationsOn q B) (A z.1)
        (I z.1 ∪ (D z.1 ∪ R z.1)) (K z.1) z.2 := by
    intro z hz
    exact (hlinkFull z hz).1
  exact exists_ksssOutsidePacking_of_supportedFinalLinkKernel_available_subset
    (linkLaw := linkLaw) hA hselected hcover hstate hlink

/-- A robust-link law at every positive-mass intermediate state completes
the terminal cover-down.  Zero-mass states use the harmless empty fallback
provided by `supportedSimultaneousLinkCoverKernel`. -/
theorem exists_ksssOutsidePacking_of_supportedRobustFinalStage
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    {law : FiniteLaw Omega}
    {G : Omega → SimpleGraph V}
    {A I D R : Omega → TripleSystemOn V}
    {K : (omega : Omega) → {x : V // x ∉ X} → BipartiteLink V}
    {alpha : ℝ≥0}
    (hA : ∀ omega, A omega = outsideAvailableTriangles H B)
    (hselected : law.SupportedOn fun omega ↦
      I omega ∪ D omega ⊆ A omega)
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph
        (graphDifference (SimpleGraph.completeGraph V) H)
        (G omega) (I omega) (D omega))
    (hstate : law.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) X (A omega) (I omega) (D omega)
        (R omega) (K omega))
    (hready : law.SupportedOn fun omega ↦
      HasSimultaneousLinkCoverFamilyLaw
        (absorberErdosForbiddenConfigurationsOn q B)
        (A omega) (I omega ∪ (D omega ∪ R omega)) (K omega) alpha) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  let linkLaw : Omega → FiniteLaw (TripleSystemOn V) :=
    supportedSimultaneousLinkCoverKernel
      (absorberErdosForbiddenConfigurationsOn q B) A
      (fun omega ↦ I omega ∪ (D omega ∪ R omega)) K alpha
  have hlinkFull :=
    hready.jointBind_supportedSimultaneousLinkCoverKernel
      (absorberErdosForbiddenConfigurationsOn q B) A
      (fun omega ↦ I omega ∪ (D omega ∪ R omega)) K alpha
  have hlink : (law.jointBind linkLaw).SupportedOn fun z ↦
      IsSimultaneousLinkCover
        (absorberErdosForbiddenConfigurationsOn q B) (A z.1)
        (I z.1 ∪ (D z.1 ∪ R z.1)) (K z.1) z.2 := by
    intro z hz
    exact (hlinkFull z hz).1
  exact exists_ksssOutsidePacking_of_supportedFinalLinkKernel
    (linkLaw := linkLaw) hA hselected hcover hstate hlink

end

end Erdos207
