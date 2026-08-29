/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularReroutedLimitRestoration
import ErdosProblems.Erdos599.SingularMaximalWaveInitialProfile

/-!
# M-dependent rerouting as a safe-batch selector

The linkage whose carrier is deleted need not itself occur in the ambient
resurrection of a maximal residual wave.  The sound intrinsic witness may
be an arbitrary ambient family with the exact deleted-source initial set;
in particular it need not itself be a target linkage.

This file connects that exact M-dependent exchange output to the completed
singular machine.  All limit geometry is discharged here: a uniform producer
of reroutable batches gives `SafeBatchSelectionBelow`, and hence the public
singular extension clause.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularReroutedSafeBatchMachine

open SingularReroutedMaximalWave SingularReroutedLimitRestoration
  SingularMaximalWaveInitialProfile SingularSafeDesignatedLinkage
  SingularSafeCompletedMachine

universe u

variable {V : Type u}

/-! ## Separating the lower-cardinal choice from the M-dependent exchange -/

/-- Canonical provisional linkage supplied unconditionally by the lower
cardinal induction hypothesis.  It is chosen in the actual deleted residual,
not in an auxiliary web with a larger source. -/
noncomputable def lowerChosenLinkage
    {G : DWeb V} (hNorm : G.IsNormalized) {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (X A : Set V) (hresidual : (G.delete X).IsUnhindered)
    (hA : A ⊆ (G.delete X).source) (hAcard : #A < kappa) :
    Set (G.delete X).DPath :=
  Classical.choose
    (SingularExtension.exists_smallSourceLinkage_of_lower
      hlower (G.delete X) hresidual
      (SingularSafeCompletedMachine.isNormalized_delete hNorm X)
      hA hAcard)

/-- The canonical lower-cardinal choice is a genuine target linkage. -/
theorem lowerChosenLinkage_spec
    {G : DWeb V} (hNorm : G.IsNormalized) {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (X A : Set V) (hresidual : (G.delete X).IsUnhindered)
    (hA : A ⊆ (G.delete X).source) (hAcard : #A < kappa) :
    IsLinkageBetween (G.delete X) A (G.delete X).target
      (lowerChosenLinkage hNorm hlower X A hresidual hA hAcard) :=
  Classical.choose_spec
    (SingularExtension.exists_smallSourceLinkage_of_lower
      hlower (G.delete X) hresidual
      (SingularSafeCompletedMachine.isNormalized_delete hNorm X)
      hA hAcard)

/-! ## The weakest initial-profile selector -/

/-- Uniform machine input using only M-dependent ambient waves with the
correct initial coordinates.  Neither the retained linkage nor the residual
maximal wave must occur literally in the ambient comparison wave. -/
def InitialProfileSelectionBelow
    (G : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ (X A : Set V), (G.delete X).IsUnhindered →
    A ⊆ (G.delete X).source → #A < kappa →
    ∃ P : Set (G.delete X).DPath,
      IsLinkageBetween (G.delete X) A (G.delete X).target P ∧
        MaximalWaveInitialProfilesLiftAcrossDelete (G.delete X)
          ((G.delete X).vertexSet P)

/-- Initial-profile restoration makes the retained provisional linkage a
safe batch in its deleted ambient residual. -/
theorem safeBatchSelectionBelow_of_initialProfiles
    {G : DWeb V} {kappa : Cardinal.{u}}
    (hselect : InitialProfileSelectionBelow G kappa) :
    SafeBatchSelectionBelow G kappa := by
  intro X A hresidual hA hAcard
  obtain ⟨P, hP, hprofiles⟩ := hselect X A hresidual hA hAcard
  exact ⟨{
    paths := P
    linkage := hP
    residual := isUnhindered_delete_of_initialProfiles
      hresidual hprofiles }⟩

/-- Public singular endpoint for the weakest initial-profile selector. -/
theorem singularExtensionClauseAt_of_initialProfileSelection
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hselect : InitialProfileSelectionBelow Gamma.normalized kappa) :
    ExtensionClauseAt Gamma kappa := by
  apply SingularSafeCompletedMachine.singularExtensionClauseAt_of_safeBatchSelection
    kappa hkappa hsingular Gamma hGamma
  exact safeBatchSelectionBelow_of_initialProfiles hselect

/-- Exact initial-profile exchange obligation for the canonical linkage
selected by lower cardinal induction. -/
def LowerChosenInitialProfilesBelow
    (G : DWeb V) (hNorm : G.IsNormalized) (kappa : Cardinal.{u})
    (hlower : UniversalCardinalInductionBelow V kappa) : Prop :=
  ∀ (X A : Set V) (hresidual : (G.delete X).IsUnhindered)
      (hA : A ⊆ (G.delete X).source) (hAcard : #A < kappa),
    MaximalWaveInitialProfilesLiftAcrossDelete (G.delete X)
      ((G.delete X).vertexSet
        (lowerChosenLinkage hNorm hlower X A hresidual hA hAcard))

/-- Lower induction chooses the retained linkage; initial-profile exchange
supplies its exact limit certificate. -/
theorem initialProfileSelectionBelow_of_lower_exchange
    {G : DWeb V} (hNorm : G.IsNormalized) {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hexchange : LowerChosenInitialProfilesBelow G hNorm kappa hlower) :
    InitialProfileSelectionBelow G kappa := by
  intro X A hresidual hA hAcard
  exact ⟨lowerChosenLinkage hNorm hlower X A hresidual hA hAcard,
    lowerChosenLinkage_spec hNorm hlower X A hresidual hA hAcard,
    hexchange X A hresidual hA hAcard⟩

/-- End-to-end singular branch from lower induction and the weakest sound
M-dependent initial-profile exchange. -/
theorem singularExtensionClauseAt_of_lower_initialProfiles
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hexchange : LowerChosenInitialProfilesBelow Gamma.normalized
      Gamma.normalized_isNormalized kappa hlower) :
    ExtensionClauseAt Gamma kappa := by
  apply singularExtensionClauseAt_of_initialProfileSelection
    kappa hkappa hsingular Gamma hGamma
  exact initialProfileSelectionBelow_of_lower_exchange
    Gamma.normalized_isNormalized hlower hexchange

/-- Sound intrinsic exchange for the canonical lower-cardinal linkage.  The
M-dependent resurrection family is only required to have the exact deleted
source initial set; it need not itself reach the target.  This weaker form is
necessary already for a one-source branching web. -/
def LowerChosenReroutedResurrectionBelow
    (G : DWeb V) (hNorm : G.IsNormalized) (kappa : Cardinal.{u})
    (hlower : UniversalCardinalInductionBelow V kappa) : Prop :=
  ∀ (X A : Set V) (hresidual : (G.delete X).IsUnhindered)
      (hA : A ⊆ (G.delete X).source) (hAcard : #A < kappa),
    MaximalWavesRerouteAcrossDelete (G.delete X)
      ((G.delete X).vertexSet
        (lowerChosenLinkage hNorm hlower X A hresidual hA hAcard))

/-- Lower induction plus the intrinsic M-dependent exchange gives the sound
rerouted-resurrection selector. -/
theorem reroutedResurrectionSelectionBelow_of_lower_exchange
    {G : DWeb V} (hNorm : G.IsNormalized) {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hexchange :
      LowerChosenReroutedResurrectionBelow G hNorm kappa hlower) :
    ReroutedResurrectionSelectionBelow G kappa := by
  intro X A hresidual hA hAcard
  exact ⟨lowerChosenLinkage hNorm hlower X A hresidual hA hAcard,
    lowerChosenLinkage_spec hNorm hlower X A hresidual hA hAcard,
    hexchange X A hresidual hA hAcard⟩

/-- Sound end-to-end singular branch from lower induction and intrinsic
M-dependent resurrection.  Unlike the optional target-linkage specialization
above, this endpoint also covers branching safe paths whose only ambient
resurrection uses a trivial source component. -/
theorem singularExtensionClauseAt_of_lower_reroutedResurrection
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hexchange : LowerChosenReroutedResurrectionBelow Gamma.normalized
      Gamma.normalized_isNormalized kappa hlower) :
    ExtensionClauseAt Gamma kappa := by
  apply singularExtensionClauseAt_of_reroutedResurrection
    kappa hkappa hsingular Gamma hGamma
  exact reroutedResurrectionSelectionBelow_of_lower_exchange
    Gamma.normalized_isNormalized hlower hexchange

#print axioms lowerChosenLinkage_spec
#print axioms safeBatchSelectionBelow_of_initialProfiles
#print axioms singularExtensionClauseAt_of_initialProfileSelection
#print axioms initialProfileSelectionBelow_of_lower_exchange
#print axioms singularExtensionClauseAt_of_lower_initialProfiles
#print axioms reroutedResurrectionSelectionBelow_of_lower_exchange
#print axioms singularExtensionClauseAt_of_lower_reroutedResurrection

end SingularReroutedSafeBatchMachine
end CardinalInduction
end Erdos599
