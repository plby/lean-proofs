/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RawInternalRootedConditioning
import ErdosProblems.Erdos207.InternalEdgeIntermediateLaw
import ErdosProblems.Erdos207.PreliminaryAugmentedReserve

/-!
# Residual links after rooted conditioning of the raw internal law

Root conditioning changes the law but not its sample type.  This direct
support bridge therefore reconstructs `InternalOutcomeReady` without
requiring the conditioned law itself to be displayed as a joint bind.
-/

namespace Erdos207

open Finset

noncomputable section

theorem FiniteLaw.SupportedOn.internalOutcomeReady_of_directInternalCover
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {law : FiniteLaw Omega} {G : Omega → SimpleGraph V} {U : Finset V}
    {reserve : Omega → Finset (Sym2 V)} {F : ForbiddenFamilyOn V}
    {A I D Mstar P0 Q : Omega → TripleSystemOn V}
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
    (hinternal : law.SupportedOn fun omega ↦
      GreedyReachable F (P0 omega) (Q omega) ∧
      Q omega ⊆ P0 omega ∪ A omega ∧
      (Q omega \ P0 omega).card ≤ (internalOuterEdges (G omega) U).card ∧
      ∀ e ∈ internalOuterEdges (G omega) U,
        (coveredGraph (Q omega)).Adj e.out.1 e.out.2) :
    law.SupportedOn (InternalOutcomeReady G U reserve F A I D Mstar Q) := by
  intro omega hmass
  have hb := hbase omega hmass
  have hi := hinternal omega hmass
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1,
    hb.2.2.2.2.1, ?_, ?_, ?_, hi.2.2.2, hcrossing omega⟩
  · simpa only [hP0 omega] using hb.2.2.2.2.2
  · simpa only [hP0 omega] using hi.1
  · simpa only [hP0 omega] using hi.2.1

/-- Direct residual-link construction for a law obtained by conditioning the
preliminary/internal joint law on rooted success. -/
theorem FiniteLaw.SupportedOn.rawPreliminaryInternalResidualLinks
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {law : FiniteLaw Omega} {G : Omega → SimpleGraph V} {U : Finset V}
    {sampled : Omega → Finset (Sym2 V)} {F : ForbiddenFamilyOn V}
    {A I D Mstar P0 Q : Omega → TripleSystemOn V}
    (hbase : law.SupportedOn fun omega ↦
      (∀ v, Even ((neighborsIn (G omega) univ v).card)) ∧
      G omega ≤ leaveGraph (I omega ∪ D omega) ∧
      ConsistsOfTriangles (G omega) (A omega) ∧
      Mstar omega ⊆ A omega ∧
      Disjoint (I omega) (D omega ∪ Mstar omega) ∧
      IsPackingOn (P0 omega))
    (hP0 : ∀ omega, P0 omega = I omega ∪ (D omega ∪ Mstar omega))
    (hinternal : law.SupportedOn fun omega ↦
      GreedyReachable F (P0 omega) (Q omega) ∧
      Q omega ⊆ P0 omega ∪ A omega ∧
      (Q omega \ P0 omega).card ≤ (internalOuterEdges (G omega) U).card ∧
      ∀ e ∈ internalOuterEdges (G omega) U,
        (coveredGraph (Q omega)).Adj e.out.1 e.out.2) :
    let reserve : Omega → Finset (Sym2 V) := fun omega ↦
      preliminaryAugmentedReserve (G omega) U (sampled omega) (Mstar omega)
    let R : Omega → TripleSystemOn V := fun omega ↦
      internalStageFamily (I omega) (D omega) (Mstar omega) (Q omega)
    let center : Omega → ({x : V // x ∉ U} ↪ V) := fun _ ↦
      outsideVertexEmbedding U
    let links := Erdos207.internalOutcomeResidualLinks
      G U reserve F A I D Mstar Q
    law.SupportedOn (fun omega ↦
      IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega)
          (R omega) (links omega) ∧
        (∀ o, (links omega o).center = center omega o) ∧
        (∀ o, center omega o ∉ U) ∧
        (∀ o, (links omega o).left ⊆ U) ∧
        (∀ o, (links omega o).right ⊆ U) ∧
        (∀ o, (links omega o).SpokesIn (reserve omega))) := by
  dsimp only
  let reserve : Omega → Finset (Sym2 V) := fun omega ↦
    preliminaryAugmentedReserve (G omega) U (sampled omega) (Mstar omega)
  have hready : law.SupportedOn
      (InternalOutcomeReady G U reserve F A I D Mstar Q) := by
    apply hbase.internalOutcomeReady_of_directInternalCover hP0
    · intro omega
      exact coversCrossingOutsideReserve_preliminaryAugmentedReserve
        (G omega) U (sampled omega) (Mstar omega)
    · exact hinternal
  simpa only [reserve] using hready.internalOutcomeResidualLinks

end

end Erdos207
