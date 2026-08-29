/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GeneralArrow315
import ErdosProblems.Erdos599.SingularMaximalWaveInitialProfile
import ErdosProblems.Erdos599.SingularSourcePartRestoration

/-!
# General-arrow restoration of a maximal-wave initial profile

Restoring the source vertices of a deleted carrier is automatic.  The
remaining carrier is disjoint from the ambient source, so Aharoni--Berger
Lemma 3.15 is the appropriate operation for restoring it: arrow the lifted
source-restored wave with a wave in the quotient by the non-source carrier.

This file records the exact seam.  The only non-structural input left by the
general arrow is its meeting hypothesis: every path of the quotient wave must
meet the roof of the source-restored residual wave away from the deleted
carrier.  No member of the original residual wave, or of the selected
linkage, is required to survive literally.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularGeneralArrowInitialProfile

open SingularMaximalWaveInitialProfile SingularSourcePartRestoration

universe u

variable {V : Type u}

/-- The exact Lemma 3.15 meeting certificate after the source part of `X`
has been restored.  The wave `restored` already has the required initial
profile; `quotient` is used only to restore the source-disjoint set
`X \ G.source`. -/
structure GeneralArrowProfileData (G : DWeb V) (X : Set V)
    (M : (G.delete X).Wave) where
  restored : Set (G.delete (X \ G.source)).DPath
  restored_wave : (G.delete (X \ G.source)).IsWave restored
  restored_initialSet :
    (G.delete (X \ G.source)).initialSet restored =
      (G.source ∩ X) ∪ (G.delete X).initialSet M.1
  quotient : Set (G.quotient (X \ G.source)).DPath
  quotient_wave : (G.quotient (X \ G.source)).IsWave quotient
  quotient_meets : ∀ q ∈ quotient, ∃ u ∈ q.support,
    u ∉ X \ G.source ∧
      u ∈ (G.delete (X \ G.source)).roof
        ((G.delete (X \ G.source)).terminalFrontier restored)

namespace GeneralArrowProfileData

variable {G : DWeb V} {X : Set V} {M : (G.delete X).Wave}

/-- The carrier which remains after source restoration is disjoint from the
ambient source, exactly as required by Lemma 3.15. -/
theorem source_disjoint_nonSourceCarrier
    (D : GeneralArrowProfileData G X M) :
    Disjoint G.source (X \ G.source) :=
  Set.disjoint_sdiff_right

/-- The general arrow associated to a profile datum. -/
def paths (D : GeneralArrowProfileData G X M) : Set G.DPath :=
  G.arrow (G.liftDeleteFamily (X \ G.source) D.restored)
    (SafeLink.liftQuotientFamily G (X \ G.source) D.quotient)

/-- Lemma 3.15 restores the non-source carrier and produces an ambient
wave. -/
theorem paths_isWave (D : GeneralArrowProfileData G X M)
    (hNoEnter : G.NoEdgeEnters G.source) :
    G.IsWave D.paths := by
  exact G.isWave_arrow_delete_quotient Set.Subset.rfl hNoEnter
    D.source_disjoint_nonSourceCarrier D.restored_wave D.quotient_wave
      D.quotient_meets

/-- The general arrow preserves the initial coordinates of the
source-restored wave, hence gives exactly the weak profile required by the
maximal-wave argument. -/
theorem initialSet_paths (D : GeneralArrowProfileData G X M) :
    G.initialSet D.paths =
      (G.source ∩ X) ∪ (G.delete X).initialSet M.1 := by
  unfold paths
  have hforward := G.forwardExtension_arrow
    (G.liftDeleteFamily (X \ G.source) D.restored)
    (SafeLink.liftQuotientFamily G (X \ G.source) D.quotient)
  rw [← G.initialSet_eq_of_forwardExtension hforward,
    G.initialSet_liftDeleteFamily, D.restored_initialSet]

/-- Package a successful general arrow as the exact initial-profile witness.
This construction is fully rerouted: its paths need not contain the selected
linkage or the lifted residual wave. -/
def toInitialProfileWaveWitness (D : GeneralArrowProfileData G X M)
    (hNoEnter : G.NoEdgeEnters G.source) :
    InitialProfileWaveWitness G X M where
  paths := D.paths
  wave := D.paths_isWave hNoEnter
  initialSet_eq := D.initialSet_paths

end GeneralArrowProfileData

/-- Source restoration supplies all fields of `GeneralArrowProfileData`
except the quotient wave and its Lemma 3.15 meeting property.  This is the
construction-facing form: a selector may inspect the restored wave before
choosing the quotient wave. -/
theorem exists_generalArrowProfileData
    (G : DWeb V) (X : Set V) (M : (G.delete X).Wave)
    (hquotient : ∀ (W : Set (G.delete (X \ G.source)).DPath),
      (G.delete (X \ G.source)).IsWave W →
      (G.delete (X \ G.source)).initialSet W =
        (G.source ∩ X) ∪ (G.delete X).initialSet M.1 →
      ∃ U : Set (G.quotient (X \ G.source)).DPath,
        (G.quotient (X \ G.source)).IsWave U ∧
          ∀ q ∈ U, ∃ u ∈ q.support,
            u ∉ X \ G.source ∧
              u ∈ (G.delete (X \ G.source)).roof
                ((G.delete (X \ G.source)).terminalFrontier W)) :
    Nonempty (GeneralArrowProfileData G X M) := by
  obtain ⟨W, hW, hWinitial⟩ :=
    exists_wave_after_restoring_sourcePart G X M
  obtain ⟨U, hU, hmeet⟩ := hquotient W hW hWinitial
  exact ⟨{
    restored := W
    restored_wave := hW
    restored_initialSet := hWinitial
    quotient := U
    quotient_wave := hU
    quotient_meets := hmeet }⟩

/-- A successful quotient-wave selection gives the weak ambient profile
required to prove the final deletion unhindered. -/
theorem exists_initialProfileWaveWitness_of_generalArrow
    (G : DWeb V) (hNorm : G.IsNormalized)
    (X : Set V) (M : (G.delete X).Wave)
    (hquotient : ∀ (W : Set (G.delete (X \ G.source)).DPath),
      (G.delete (X \ G.source)).IsWave W →
      (G.delete (X \ G.source)).initialSet W =
        (G.source ∩ X) ∪ (G.delete X).initialSet M.1 →
      ∃ U : Set (G.quotient (X \ G.source)).DPath,
        (G.quotient (X \ G.source)).IsWave U ∧
          ∀ q ∈ U, ∃ u ∈ q.support,
            u ∉ X \ G.source ∧
              u ∈ (G.delete (X \ G.source)).roof
                ((G.delete (X \ G.source)).terminalFrontier W)) :
    Nonempty (InitialProfileWaveWitness G X M) := by
  obtain ⟨D⟩ := exists_generalArrowProfileData G X M hquotient
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  exact ⟨D.toInitialProfileWaveWitness hNoEnter⟩

/-! ## Exact strength of the weak profile -/

/-- If the deletion is already unhindered, the ambient trivial wave has the
required profile for every residual wave.  Thus the weak profile condition
does not impose any extra geometry beyond residual unhinderedness. -/
theorem maximalWaveInitialProfiles_of_delete_isUnhindered
    {G : DWeb V} {X : Set V}
    (hdelete : (G.delete X).IsUnhindered) :
    MaximalWaveInitialProfilesLiftAcrossDelete G X := by
  intro M _hMmax
  refine ⟨{
    paths := G.trivialWave
    wave := G.isWave_trivialWave
    initialSet_eq := ?_ }⟩
  rw [G.initialSet_trivialWave,
    (G.delete X).isUnhindered_iff.mp hdelete M.1 M.2]
  ext a
  change a ∈ G.source ↔
    (a ∈ G.source ∧ a ∈ X) ∨ (a ∈ G.source ∧ a ∉ X)
  tauto

/-- In an unhindered ambient web, maximal-wave initial-profile restoration
is equivalent to the desired residual unhinderedness.  This pinpoints the
role of the subsequent exchange theorem: it is an exact reformulation of
safe deletion, not a stronger frozen-carrier invariant. -/
theorem maximalWaveInitialProfiles_iff_delete_isUnhindered
    {G : DWeb V} {X : Set V} (hG : G.IsUnhindered) :
    MaximalWaveInitialProfilesLiftAcrossDelete G X ↔
      (G.delete X).IsUnhindered := by
  constructor
  · exact isUnhindered_delete_of_initialProfiles hG
  · exact maximalWaveInitialProfiles_of_delete_isUnhindered

#print axioms GeneralArrowProfileData.paths_isWave
#print axioms GeneralArrowProfileData.initialSet_paths
#print axioms exists_generalArrowProfileData
#print axioms exists_initialProfileWaveWitness_of_generalArrow
#print axioms maximalWaveInitialProfiles_of_delete_isUnhindered
#print axioms maximalWaveInitialProfiles_iff_delete_isUnhindered

end SingularGeneralArrowInitialProfile
end CardinalInduction
end Erdos599
