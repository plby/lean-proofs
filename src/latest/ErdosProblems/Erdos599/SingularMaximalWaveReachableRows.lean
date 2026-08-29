/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeCompletedMachine
import ErdosProblems.Erdos599.SingularSafeDesignatedLimit
import ErdosProblems.Erdos599.SingularSafeTreeResurrection
import ErdosProblems.Erdos599.SingularMaximalWaveInitialProfile

/-!
# Reachable singular rows from maximal-wave restoration

An arbitrary lower-cardinal target linkage is not a sound singular row:
deleting its carrier can hinder a still-unprocessed source.  A repair of one
chosen residual hindrance is not enough either, since another maximal wave
may have a different initial profile.

The exact graph-facing certificate which feeds the already verified
safe-completed row machine is M-dependent initial-profile restoration: for
each maximal wave after deleting the chosen carrier, one may build a fresh
ambient wave with the required initial coordinates.  The restoring paths
need not contain either the chosen target linkage or the residual wave.

For comparison this file also retains the stronger literal-union certificate
`MaximalWaveResurrectingBatch`.  It is a useful sufficient output of a
boundary-covered construction, but it is not the unconditional selection
target: already a branching one-source star has safe batches but no fixed
target path whose union with every residual maximal wave is an ambient wave.

Both selection statements below are local to one deleted web and one
lower-cardinal request.  `InitialProfileReachableSelectionBelow` is the sound
one consumed by the public reduction; the literal selector is kept only as a
strictly stronger adapter.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMaximalWaveReachableRows

open SingularSafeCompletedMachine SingularSafeDesignatedLinkage
  SingularSafeDesignatedLimit SingularSafeTreeResurrection
  SingularMaximalWaveInitialProfile

universe u

variable {V : Type u}

/-- A reachable batch consists of the retained target linkage together with
the exact M-dependent limit certificate.  Restoring families may depend on
the maximal residual wave and may reroute every path. -/
structure InitialProfileReachableBatch (G : DWeb V) (A : Set V) where
  paths : Set G.DPath
  linkage : IsLinkageBetween G A G.target paths
  profiles : MaximalWaveInitialProfilesLiftAcrossDelete
    G (G.vertexSet paths)

namespace InitialProfileReachableBatch

variable {G : DWeb V} {A : Set V}

/-- The M-dependent profile certificate is precisely what is needed to
prove safety of the retained carrier in an unhindered ambient web. -/
theorem residual_unhindered
    (hG : G.IsUnhindered) (B : InitialProfileReachableBatch G A) :
    (G.delete (G.vertexSet B.paths)).IsUnhindered :=
  isUnhindered_delete_of_initialProfiles hG B.profiles

/-- Forget the restoration proof after compiling it to the safe-designated
state consumed by the reachable-row recursion. -/
def toSafeDesignated
    (hG : G.IsUnhindered) (B : InitialProfileReachableBatch G A) :
    SafeDesignatedLinkage G A where
  paths := B.paths
  linkage := B.linkage
  residual_unhindered := B.residual_unhindered hG

end InitialProfileReachableBatch

/-- A target batch for `A` which simultaneously resurrects every maximal
wave in the deletion of its carrier.  The resurrection is literal at the
whole-family level; no selected residual profile or preferred maximal wave
is hidden in the structure. -/
structure MaximalWaveResurrectingBatch (G : DWeb V) (A : Set V) where
  paths : Set G.DPath
  linkage : IsLinkageBetween G A G.target paths
  resurrects : ∀ M : (G.delete (G.vertexSet paths)).Wave, IsMax M →
    G.IsWave
      (paths ∪ G.liftDeleteFamily (G.vertexSet paths) M.1)

namespace MaximalWaveResurrectingBatch

variable {G : DWeb V} {A : Set V}

/-- Simultaneous resurrection makes the carrier deletion unhindered.  The
proof is the maximal-wave limit argument, with the deleted sources ruled out
using the exact initial set of the selected linkage. -/
theorem residual_unhindered
    (hG : G.IsUnhindered) (B : MaximalWaveResurrectingBatch G A) :
    (G.delete (G.vertexSet B.paths)).IsUnhindered := by
  apply isUnhindered_of_maximalWaveComplete
  intro M hMmax
  have hfull :
      G.initialSet
          (B.paths ∪ G.liftDeleteFamily (G.vertexSet B.paths) M.1) =
        G.source :=
    G.isUnhindered_iff.mp hG _ (B.resurrects M hMmax)
  rw [G.initialSet_union, B.linkage.initialSet_eq,
    G.initialSet_liftDeleteFamily] at hfull
  apply Set.Subset.antisymm M.2.2.1
  intro x hx
  have hxUnion : x ∈ A ∪
      (G.delete (G.vertexSet B.paths)).initialSet M.1 :=
    hfull.symm ▸ hx.1
  rcases hxUnion with hxA | hxM
  · have hxInitial : x ∈ G.initialSet B.paths := by
      simpa only [B.linkage.initialSet_eq] using hxA
    obtain ⟨p, hp, hxp⟩ := hxInitial
    exact (hx.2 ⟨p, hp, hxp ▸ p.initial_mem_support⟩).elim
  · exact hxM

/-- Forget resurrection after using it to discharge the exact safe-linkage
state consumed by the completed-row recursion. -/
def toSafeDesignated
    (hG : G.IsUnhindered) (B : MaximalWaveResurrectingBatch G A) :
    SafeDesignatedLinkage G A where
  paths := B.paths
  linkage := B.linkage
  residual_unhindered := B.residual_unhindered hG

/-- Carrier-boundary coverage is a concrete sufficient constructor for the
simultaneous resurrection state.  This is the direct bridge from retained
safe trees or a finite boundary-repair construction to the reachable-row
machine. -/
def ofBoundaryCovered
    (hNorm : G.IsNormalized) (hA : A ⊆ G.source)
    {P : Set G.DPath} (hP : IsLinkageBetween G A G.target P)
    (hcover : CarrierBoundaryWaveCovered G P) :
    MaximalWaveResurrectingBatch G A where
  paths := P
  linkage := hP
  resurrects M hMmax :=
    maximal_wave_resurrects_with_linkage
      hNorm hA hP hcover M hMmax

end MaximalWaveResurrectingBatch

/-- The local simultaneous-selection statement needed at each reachable
safe-completed successor.  In contrast to `SafeBatchSelectionBelow`, the
result exposes the maximal-wave resurrection geometry which a finite repair
must actually construct. -/
def MaximalWaveResurrectionSelectionBelow
    (G : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ (X A : Set V), (G.delete X).IsUnhindered →
    A ⊆ (G.delete X).source → #A < kappa →
      Nonempty (MaximalWaveResurrectingBatch (G.delete X) A)

/-- The sound local selection statement at each successor.  Unlike the
literal selector above, this permits a different completely rerouted ambient
wave for each maximal wave in the final residual. -/
def InitialProfileReachableSelectionBelow
    (G : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ (X A : Set V), (G.delete X).IsUnhindered →
    A ⊆ (G.delete X).source → #A < kappa →
      Nonempty (InitialProfileReachableBatch (G.delete X) A)

/-- A graph-level selection target phrased only in terms of the outgoing
boundary of the chosen linkage carrier. -/
def BoundaryCoveredSelectionBelow
    (G : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ (X A : Set V), (G.delete X).IsUnhindered →
    A ⊆ (G.delete X).source → #A < kappa →
      ∃ P : Set (G.delete X).DPath,
        IsLinkageBetween (G.delete X) A (G.delete X).target P ∧
          CarrierBoundaryWaveCovered (G.delete X) P

/-- Boundary-covered lower-cardinal batches supply simultaneous
maximal-wave resurrection. -/
theorem maximalWaveResurrectionSelectionBelow_of_boundaryCovered
    {G : DWeb V} (hNorm : G.IsNormalized) {kappa : Cardinal.{u}}
    (hselect : BoundaryCoveredSelectionBelow G kappa) :
    MaximalWaveResurrectionSelectionBelow G kappa := by
  intro X A hresidual hA hcard
  obtain ⟨P, hP, hcover⟩ := hselect X A hresidual hA hcard
  exact ⟨MaximalWaveResurrectingBatch.ofBoundaryCovered
    (SingularSafeCompletedMachine.isNormalized_delete hNorm X)
      hA hP hcover⟩

/-- Simultaneous maximal-wave resurrection compiles to the safe batches used
by the genuine reachable-row successor. -/
theorem safeBatchSelectionBelow_of_maximalWaveResurrection
    {G : DWeb V} {kappa : Cardinal.{u}}
    (hselect : MaximalWaveResurrectionSelectionBelow G kappa) :
    SafeBatchSelectionBelow G kappa := by
  intro X A hresidual hA hcard
  obtain ⟨B⟩ := hselect X A hresidual hA hcard
  exact ⟨SafeBatchInDeletion.ofSafeDesignated
    (B.toSafeDesignated hresidual)⟩

/-- M-dependent reachable batches compile to the actual successor input of
the safe-completed row machine. -/
theorem safeBatchSelectionBelow_of_initialProfileReachable
    {G : DWeb V} {kappa : Cardinal.{u}}
    (hselect : InitialProfileReachableSelectionBelow G kappa) :
    SafeBatchSelectionBelow G kappa := by
  intro X A hresidual hA hcard
  obtain ⟨B⟩ := hselect X A hresidual hA hcard
  exact ⟨SafeBatchInDeletion.ofSafeDesignated
    (B.toSafeDesignated hresidual)⟩

/-- Public singular extension reduction through the actual initial,
successor, and omega-limit safe-completed machine.  The only remaining
mathematical input is the local all-maximal resurrection selection above;
no arbitrary-row continuation or one-profile limit assumption is used. -/
theorem singularExtensionClauseAt_of_maximalWaveResurrection
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hselect :
      MaximalWaveResurrectionSelectionBelow Gamma.normalized kappa) :
    ExtensionClauseAt Gamma kappa := by
  exact singularExtensionClauseAt_of_safeBatchSelection
    kappa hkappa hsingular Gamma hGamma
      (safeBatchSelectionBelow_of_maximalWaveResurrection hselect)

/-- Public singular extension reduction through the sound M-dependent
reachable-row invariant.  The safe-completed machine supplies the initial,
successor, and omega-limit rows; this theorem contains no arbitrary-row or
literal-union assumption. -/
theorem singularExtensionClauseAt_of_initialProfileReachable
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hselect :
      InitialProfileReachableSelectionBelow Gamma.normalized kappa) :
    ExtensionClauseAt Gamma kappa := by
  exact singularExtensionClauseAt_of_safeBatchSelection
    kappa hkappa hsingular Gamma hGamma
      (safeBatchSelectionBelow_of_initialProfileReachable hselect)

/-- Boundary-covered batch selection is therefore sufficient for the exact
singular extension clause. -/
theorem singularExtensionClauseAt_of_boundaryCoveredSelection
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hselect :
      BoundaryCoveredSelectionBelow Gamma.normalized kappa) :
    ExtensionClauseAt Gamma kappa := by
  apply singularExtensionClauseAt_of_maximalWaveResurrection
    kappa hkappa hsingular Gamma hGamma
  exact maximalWaveResurrectionSelectionBelow_of_boundaryCovered
    Gamma.normalized_isNormalized hselect

#print axioms MaximalWaveResurrectingBatch.residual_unhindered
#print axioms InitialProfileReachableBatch.residual_unhindered
#print axioms safeBatchSelectionBelow_of_maximalWaveResurrection
#print axioms safeBatchSelectionBelow_of_initialProfileReachable
#print axioms singularExtensionClauseAt_of_maximalWaveResurrection
#print axioms singularExtensionClauseAt_of_initialProfileReachable
#print axioms maximalWaveResurrectionSelectionBelow_of_boundaryCovered
#print axioms singularExtensionClauseAt_of_boundaryCoveredSelection

end SingularMaximalWaveReachableRows
end CardinalInduction
end Erdos599
