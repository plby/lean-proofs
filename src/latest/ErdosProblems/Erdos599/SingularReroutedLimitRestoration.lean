/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMaximalWaveInitialProfile
import ErdosProblems.Erdos599.SingularSafeCompletedMachine

/-!
# Machine adapters for rerouted maximal-wave restoration

Literal preservation of every target path selected before a singular limit
is too strong.  `SingularMaximalWaveInitialProfile` gives the exact consumer:
for each maximal wave `M` in the final deletion, one may construct a fresh
ambient wave whose initial set is exactly the union of the ambient sources
deleted by the limiting carrier and the initial set of `M`.  No path of `M`
has to be preserved literally.

This file connects that M-dependent resurrection theorem to the
safe-designated linkage and safe-completed row APIs.  The linkage retained
by the machine is used only to name the limiting carrier; the family used
to resurrect a particular maximal wave may be rerouted completely and may
depend on that wave.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularReroutedLimitRestoration

open SingularReroutedMaximalWave SingularMaximalWaveInitialProfile
  SingularSafeCompletedMachine
  SingularSafeDesignatedLinkage SingularSafeDesignatedLimit

universe u

variable {V : Type u}

/-- The earlier fixed trivial-source resurrection predicate is a special
case of M-dependent rerouting.  This bridge lets existing concrete
resurrection proofs feed the new machine adapter without rebuilding their
wave families. -/
theorem maximalWavesRerouteAcrossDelete_of_trivialResurrection
    {G : DWeb V} {X : Set V}
    (hresurrect : MaximalWavesResurrectAcrossDelete G X) :
    MaximalWavesRerouteAcrossDelete G X := by
  intro M hMmax
  refine ⟨{
    paths := G.trivialPath '' (G.source ∩ X)
    initialSet_eq := G.initialSet_trivialPaths (G.source ∩ X)
    wave := ?_ }⟩
  simpa only [resurrectedWaveFamily, Set.union_comm] using
    hresurrect M hMmax

/-- If the deletion is already known to be unhindered, a full ambient
maximal wave witnesses every required initial profile.  This converse to
`isUnhindered_delete_of_initialProfiles` is useful for auditing the exact
strength of the restoration interface. -/
theorem maximalWaveInitialProfiles_of_delete_isUnhindered
    {G : DWeb V} {X : Set V} (hG : G.IsUnhindered)
    (hdelete : (G.delete X).IsUnhindered) :
    MaximalWaveInitialProfilesLiftAcrossDelete G X := by
  intro M hMmax
  obtain ⟨W, hWmax⟩ := G.exists_maximal_wave
  refine ⟨{
    paths := W.1
    wave := W.2
    initialSet_eq := ?_ }⟩
  have hWfull : G.initialSet W.1 = G.source :=
    maximalWaveComplete_of_isUnhindered hG W hWmax
  have hMfull :
      (G.delete X).initialSet M.1 = (G.delete X).source :=
    maximalWaveComplete_of_isUnhindered hdelete M hMmax
  rw [hWfull, hMfull]
  ext x
  simp only [DWeb.delete_source, Set.mem_union, Set.mem_inter_iff,
    Set.mem_sdiff]
  tauto

/-- In an unhindered ambient web, M-dependent initial-profile restoration
across a deletion is equivalent to safety of that deletion.  The profile
form is geometrically more flexible, but it is not an unconditional
arbitrary-carrier principle. -/
theorem maximalWaveInitialProfiles_iff_delete_isUnhindered
    {G : DWeb V} {X : Set V} (hG : G.IsUnhindered) :
    MaximalWaveInitialProfilesLiftAcrossDelete G X ↔
      (G.delete X).IsUnhindered := by
  exact ⟨isUnhindered_delete_of_initialProfiles hG,
    maximalWaveInitialProfiles_of_delete_isUnhindered hG⟩

/-- A retained target linkage plus M-dependent initial-profile restoration
supplies the safe-designated linkage consumed by the completed-row machine.
No equality, inclusion, or carrier relation between the retained linkage and
any restoring family is assumed. -/
def safeDesignatedLinkageOfInitialProfiles
    {G : DWeb V} (hG : G.IsUnhindered)
    {A : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hprofiles : MaximalWaveInitialProfilesLiftAcrossDelete
      G (G.vertexSet P)) :
    SafeDesignatedLinkage G A where
  paths := P
  linkage := hP
  residual_unhindered :=
    isUnhindered_delete_of_initialProfiles hG hprofiles

/-- Compatibility adapter for the stronger literal-residual rerouting
interface. -/
def safeDesignatedLinkageOfReroutedResurrection
    {G : DWeb V} (hG : G.IsUnhindered)
    {A : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hreroute : MaximalWavesRerouteAcrossDelete
      G (G.vertexSet P)) :
    SafeDesignatedLinkage G A :=
  safeDesignatedLinkageOfInitialProfiles hG hP
    (maximalWaveInitialProfiles_of_rerouted hreroute)

/-- Deleted-ambient initial-profile adapter in the exact format used by one
safe-completed-row successor. -/
def safeBatchInDeletionOfInitialProfiles
    {G : DWeb V} {X A : Set V}
    (hresidual : (G.delete X).IsUnhindered)
    {P : Set (G.delete X).DPath}
    (hP : IsLinkageBetween (G.delete X) A
      (G.delete X).target P)
    (hprofiles : MaximalWaveInitialProfilesLiftAcrossDelete
      (G.delete X) ((G.delete X).vertexSet P)) :
    SafeBatchInDeletion G X A :=
  SafeBatchInDeletion.ofSafeDesignated
    (safeDesignatedLinkageOfInitialProfiles
      hresidual hP hprofiles)

/-- Compatibility adapter for a deleted-ambient literal-residual rerouting
witness. -/
def safeBatchInDeletionOfReroutedResurrection
    {G : DWeb V} {X A : Set V}
    (hresidual : (G.delete X).IsUnhindered)
    {P : Set (G.delete X).DPath}
    (hP : IsLinkageBetween (G.delete X) A
      (G.delete X).target P)
    (hreroute : MaximalWavesRerouteAcrossDelete
      (G.delete X) ((G.delete X).vertexSet P)) :
    SafeBatchInDeletion G X A :=
  safeBatchInDeletionOfInitialProfiles hresidual hP
    (maximalWaveInitialProfiles_of_rerouted hreroute)

/-- The exact lower-cardinal selector needed by limit restoration.  It
chooses a retained target linkage and restores only the initial profile of
each maximal wave in the final residual.  The restoring ambient wave may
reroute every residual component. -/
def InitialProfileRestorationSelectionBelow
    (G : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ (X A : Set V), (G.delete X).IsUnhindered →
    A ⊆ (G.delete X).source → #A < kappa →
    ∃ P : Set (G.delete X).DPath,
      IsLinkageBetween (G.delete X) A (G.delete X).target P ∧
        MaximalWaveInitialProfilesLiftAcrossDelete (G.delete X)
          ((G.delete X).vertexSet P)

/-- Stronger compatibility selector retaining the lifted residual family
literally inside each M-dependent resurrection.  The resurrection family
is intentionally not required to be a target linkage, but this predicate is
still stronger than `InitialProfileRestorationSelectionBelow`. -/
def ReroutedResurrectionSelectionBelow
    (G : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ (X A : Set V), (G.delete X).IsUnhindered →
    A ⊆ (G.delete X).source → #A < kappa →
    ∃ P : Set (G.delete X).DPath,
      IsLinkageBetween (G.delete X) A (G.delete X).target P ∧
        MaximalWavesRerouteAcrossDelete (G.delete X)
          ((G.delete X).vertexSet P)

/-- Literal-residual rerouting is a sufficient producer for the weaker
initial-profile selector. -/
theorem initialProfileRestorationSelectionBelow_of_rerouted
    {G : DWeb V} {kappa : Cardinal.{u}}
    (hselect : ReroutedResurrectionSelectionBelow G kappa) :
    InitialProfileRestorationSelectionBelow G kappa := by
  intro X A hresidual hA hcard
  obtain ⟨P, hP, hreroute⟩ :=
    hselect X A hresidual hA hcard
  exact ⟨P, hP,
    maximalWaveInitialProfiles_of_rerouted hreroute⟩

/-- An M-dependent literal-residual rerouting selector gives the safe-batch
selector required by the completed-row machine. -/
theorem safeBatchSelectionBelow_of_reroutedResurrection
    {G : DWeb V} {kappa : Cardinal.{u}}
    (hselect : ReroutedResurrectionSelectionBelow G kappa) :
    SafeBatchSelectionBelow G kappa := by
  intro X A hresidual hA hcard
  obtain ⟨P, hP, hreroute⟩ :=
    hselect X A hresidual hA hcard
  exact ⟨safeBatchInDeletionOfReroutedResurrection
    hresidual hP hreroute⟩

/-- M-dependent initial-profile restoration gives the exact safe-batch
selector required by the completed-row machine. -/
theorem safeBatchSelectionBelow_of_initialProfiles
    {G : DWeb V} {kappa : Cardinal.{u}}
    (hselect : InitialProfileRestorationSelectionBelow G kappa) :
    SafeBatchSelectionBelow G kappa := by
  intro X A hresidual hA hcard
  obtain ⟨P, hP, hprofiles⟩ :=
    hselect X A hresidual hA hcard
  exact ⟨safeBatchInDeletionOfInitialProfiles
    hresidual hP hprofiles⟩

/-- Conversely, an already safe batch supplies initial-profile witnesses by
choosing a full maximal wave in its unhindered ambient residual. -/
theorem initialProfileRestorationSelectionBelow_of_safeBatch
    {G : DWeb V} {kappa : Cardinal.{u}}
    (hselect : SafeBatchSelectionBelow G kappa) :
    InitialProfileRestorationSelectionBelow G kappa := by
  intro X A hresidual hA hcard
  obtain ⟨B⟩ := hselect X A hresidual hA hcard
  exact ⟨B.paths, B.linkage,
    maximalWaveInitialProfiles_of_delete_isUnhindered
      hresidual B.residual⟩

/-- Machine-level audit: the uniform initial-profile selector is exactly as
strong as the safe-batch selector.  Its advantage is a less rigid geometric
target for an exchange construction, not a weaker final safety property. -/
theorem initialProfileRestorationSelectionBelow_iff_safeBatchSelection
    {G : DWeb V} {kappa : Cardinal.{u}} :
    InitialProfileRestorationSelectionBelow G kappa ↔
      SafeBatchSelectionBelow G kappa := by
  exact ⟨safeBatchSelectionBelow_of_initialProfiles,
    initialProfileRestorationSelectionBelow_of_safeBatch⟩

/-- Public singular extension endpoint.  All row recursion and literal
forward-extension bookkeeping come from the safe-completed machine; its
only new graph-theoretic input is the sound M-dependent rerouting selector. -/
theorem singularExtensionClauseAt_of_reroutedResurrection
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hselect : ReroutedResurrectionSelectionBelow
      Gamma.normalized kappa) :
    ExtensionClauseAt Gamma kappa := by
  exact singularExtensionClauseAt_of_safeBatchSelection
    kappa hkappa hsingular Gamma hGamma
      (safeBatchSelectionBelow_of_reroutedResurrection hselect)

/-- Public singular extension endpoint with the minimal initial-profile
restoration hypothesis.  In particular, no lifted residual path is required
to occur in the restoring ambient wave. -/
theorem singularExtensionClauseAt_of_initialProfiles
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hselect : InitialProfileRestorationSelectionBelow
      Gamma.normalized kappa) :
    ExtensionClauseAt Gamma kappa := by
  exact singularExtensionClauseAt_of_safeBatchSelection
    kappa hkappa hsingular Gamma hGamma
      (safeBatchSelectionBelow_of_initialProfiles hselect)

end SingularReroutedLimitRestoration
end CardinalInduction
end Erdos599
