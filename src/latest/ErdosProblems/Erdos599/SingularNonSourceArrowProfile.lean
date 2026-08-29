/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GeneralArrow315
import ErdosProblems.Erdos599.SingularMaximalWaveInitialProfile

/-!
# Splitting source vertices from a singular carrier

The deletion--quotient arrow requires its commitment set to be disjoint
from the source.  A linkage carrier is not disjoint from the source: it
contains precisely the selected initial vertices.  The correct reduction is
to delete only the non-source part of the carrier and restore the selected
sources by trivial paths.

The first theorem below is the wave-level, set-valued form of the elementary
source-deletion argument.  It does not assume that the ambient web is
unhindered.  The second theorem applies it to an arbitrary carrier `X` and
then invokes the source-disjoint deletion--quotient arrow.  Its output is the
exact initial-profile witness used by the singular limit consumer.  Thus the
remaining exchange problem is cleanly localized to producing a quotient
wave whose paths meet the retained roof; no false literal preservation of
the residual wave is used.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularNonSourceArrowProfile

open SingularMaximalWaveInitialProfile

universe u

variable {V : Type u}

private theorem initialSet_castWave {H K : DWeb V} (h : H = K)
    (W : H.Wave) :
    K.initialSet (h ▸ W).1 = H.initialSet W.1 := by
  cases h
  rfl

/-- Restore an arbitrary set of deleted source vertices by trivial paths.
At wave level this is unconditional: target paths meeting the restored set
are caught there, while target paths avoiding it remain in the deletion. -/
theorem sourceResurrection_isWave
    (G : DWeb V) {A : Set V} (hA : A ⊆ G.source)
    {M : Set (G.delete A).DPath} (hM : (G.delete A).IsWave M) :
    G.IsWave
      (G.trivialPath '' A ∪ G.liftDeleteFamily A M) := by
  let L : Set G.DPath := G.liftDeleteFamily A M
  let R : Set G.DPath := G.trivialPath '' A ∪ L
  have hLavoid : Disjoint (G.vertexSet L) A :=
    G.vertexSet_liftDeleteFamily_disjoint hM.2.1
  have hLwarp : G.IsWarp L := hM.1.liftDeleteFamily
  have hRwarp : G.IsWarp R := by
    apply Set.PairwiseDisjoint.union (G.isWarp_trivialPaths A) hLwarp
    rintro p ⟨a, haA, rfl⟩ q hqL _hpq
    rw [G.support_trivialPath]
    apply Set.disjoint_singleton_left.2
    intro haq
    exact Set.disjoint_left.1 hLavoid
      (G.mem_vertexSet.mpr ⟨q, hqL, haq⟩) haA
  have hRinitial :
      G.initialSet R = A ∪ (G.delete A).initialSet M := by
    simp only [R, L, G.initialSet_union, G.initialSet_trivialPaths,
      G.initialSet_liftDeleteFamily]
  have hRsource : G.initialSet R ⊆ G.source := by
    rw [hRinitial]
    exact Set.union_subset hA (hM.2.1.trans Set.sdiff_subset)
  have hAfrontier : A ⊆ G.terminalFrontier R := by
    intro a ha
    exact ⟨G.trivialPath a, Or.inl ⟨a, ha, rfl⟩,
      G.terminal?_trivialPath a⟩
  have hRroof : G.source ⊆ G.roof (G.terminalFrontier R) := by
    intro a ha p hp
    by_cases hmeet : (p.support ∩ A).Nonempty
    · obtain ⟨x, hxp, hxA⟩ := hmeet
      exact ⟨x, hxp, hAfrontier hxA⟩
    · have havoid : SafeLink.Walk.Avoids p.walk A := by
        intro x hxp hxA
        exact hmeet ⟨x, hxp, hxA⟩
      let q : DirectedPath.FinitePath (G.delete A).graph :=
        SafeLink.FinitePath.toDelete G A p havoid
      have haDelete : a ∈ (G.delete A).source :=
        ⟨ha, havoid a (hp.1 ▸ p.walk.start_mem_support)⟩
      have hpfinishDelete : p.finish ∈ (G.delete A).target :=
        ⟨hp.2, havoid p.finish p.walk.end_mem_support⟩
      obtain ⟨x, hxq, hxFrontier⟩ := hM.2.2 haDelete q
        ⟨by simpa [q] using hp.1, by simpa [q] using hpfinishDelete⟩
      obtain ⟨r, hrM, hrterm⟩ := hxFrontier
      refine ⟨x, by simpa [q] using hxq, ?_⟩
      refine ⟨G.liftDeletePath A r, Or.inr ?_, ?_⟩
      · exact ⟨r, hrM, rfl⟩
      · simpa using hrterm
  exact ⟨hRwarp, hRsource, hRroof⟩

/-- Initial coordinates of the source-restored wave. -/
theorem initialSet_sourceResurrection
    (G : DWeb V) (A : Set V) (M : Set (G.delete A).DPath) :
    G.initialSet
        (G.trivialPath '' A ∪ G.liftDeleteFamily A M) =
      A ∪ (G.delete A).initialSet M := by
  rw [G.initialSet_union, G.initialSet_trivialPaths,
    G.initialSet_liftDeleteFamily]

/-- The non-source part of a carrier is disjoint from the ambient source. -/
theorem disjoint_source_sdiff_source (G : DWeb V) (X : Set V) :
    Disjoint G.source (X \ G.source) := by
  exact Set.disjoint_left.2 (fun _ hx hX ↦ hX.2 hx)

/-- Deleting the non-source part and then the source part of `X` is the
same web as deleting all of `X`. -/
theorem delete_nonSource_delete_sourceInter
    (G : DWeb V) (X : Set V) :
    (G.delete (X \ G.source)).delete (G.source ∩ X) = G.delete X := by
  rw [G.delete_delete]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
  tauto

/-- A residual wave after deleting `X`, viewed after deleting only the
non-source part of `X`, becomes a wave when the removed sources are restored
by trivial paths. -/
noncomputable def sourceRestoredResidualWave
    (G : DWeb V) (X : Set V) (M : (G.delete X).Wave) :
    (G.delete (X \ G.source)).Wave := by
  let H := G.delete (X \ G.source)
  let A := G.source ∩ X
  have heq : H.delete A = G.delete X :=
    delete_nonSource_delete_sourceInter G X
  let M' : (H.delete A).Wave := heq.symm ▸ M
  have hA : A ⊆ H.source := by
    rintro a ⟨haSource, haX⟩
    exact ⟨haSource, fun ha ↦ ha.2 haSource⟩
  exact ⟨H.trivialPath '' A ∪ H.liftDeleteFamily A M'.1,
    sourceResurrection_isWave H hA M'.2⟩

/-- The restored residual wave has exactly the deleted-source coordinates
together with the old residual coordinates. -/
theorem initialSet_sourceRestoredResidualWave
    (G : DWeb V) (X : Set V) (M : (G.delete X).Wave) :
    (G.delete (X \ G.source)).initialSet
        (sourceRestoredResidualWave G X M).1 =
      (G.source ∩ X) ∪ (G.delete X).initialSet M.1 := by
  let H := G.delete (X \ G.source)
  let A := G.source ∩ X
  have heq : H.delete A = G.delete X :=
    delete_nonSource_delete_sourceInter G X
  let M' : (H.delete A).Wave := heq.symm ▸ M
  change H.initialSet (H.trivialPath '' A ∪ H.liftDeleteFamily A M'.1) = _
  rw [initialSet_sourceResurrection]
  change A ∪ (H.delete A).initialSet M'.1 =
    A ∪ (G.delete X).initialSet M.1
  exact congrArg (fun S ↦ A ∪ S)
    (initialSet_castWave heq.symm M)

/-- Source-disjoint quotient-arrow exchange produces the exact flexible
initial-profile witness.  Notice that the arrow may reroute every residual
component; only its initial set is retained. -/
noncomputable def initialProfileWitness_of_nonSourceArrow
    (G : DWeb V) (hNoEnter : G.NoEdgeEnters G.source)
    (X : Set V) (M : (G.delete X).Wave)
    (W : (G.quotient (X \ G.source)).Wave)
    (hmeet : ∀ q ∈ W.1, ∃ u ∈ q.support,
      u ∉ X \ G.source ∧
      u ∈ (G.delete (X \ G.source)).roof
        ((G.delete (X \ G.source)).terminalFrontier
          (sourceRestoredResidualWave G X M).1)) :
    InitialProfileWaveWitness G X M := by
  let Z := X \ G.source
  let U := sourceRestoredResidualWave G X M
  let R := G.arrow (G.liftDeleteFamily Z U.1)
    (SafeLink.liftQuotientFamily G Z W.1)
  have hRwave : G.IsWave R :=
    G.isWave_arrow_delete_quotient (X := Z) (Z := Z)
      Set.Subset.rfl hNoEnter (disjoint_source_sdiff_source G X)
      U.2 W.2 hmeet
  refine ⟨R, hRwave, ?_⟩
  have hforward := G.forwardExtension_arrow
    (G.liftDeleteFamily Z U.1)
    (SafeLink.liftQuotientFamily G Z W.1)
  rw [← G.initialSet_eq_of_forwardExtension hforward,
    G.initialSet_liftDeleteFamily,
    initialSet_sourceRestoredResidualWave]

/-- Pointwise quotient meeting, over the non-source part of `X`, is a
sound and sufficient exchange condition for all maximal residual waves. -/
def NonSourceArrowExchange (G : DWeb V) (X : Set V) : Prop :=
  ∀ M : (G.delete X).Wave, IsMax M →
    ∃ W : (G.quotient (X \ G.source)).Wave,
      ∀ q ∈ W.1, ∃ u ∈ q.support,
        u ∉ X \ G.source ∧
        u ∈ (G.delete (X \ G.source)).roof
          ((G.delete (X \ G.source)).terminalFrontier
            (sourceRestoredResidualWave G X M).1)

/-- The source-disjoint exchange condition compiles directly to the
machine-facing maximal-wave initial-profile predicate. -/
theorem maximalWaveInitialProfiles_of_nonSourceArrowExchange
    {G : DWeb V} (hNoEnter : G.NoEdgeEnters G.source) {X : Set V}
    (hexchange : NonSourceArrowExchange G X) :
    MaximalWaveInitialProfilesLiftAcrossDelete G X := by
  intro M hMmax
  obtain ⟨W, hmeet⟩ := hexchange M hMmax
  exact ⟨initialProfileWitness_of_nonSourceArrow
    G hNoEnter X M W hmeet⟩

#print axioms sourceResurrection_isWave
#print axioms initialSet_sourceRestoredResidualWave
#print axioms maximalWaveInitialProfiles_of_nonSourceArrowExchange

end SingularNonSourceArrowProfile
end CardinalInduction
end Erdos599
