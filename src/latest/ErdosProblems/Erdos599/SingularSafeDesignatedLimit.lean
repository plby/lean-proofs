/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeDesignatedLinkage
import ErdosProblems.Erdos599.WaveLimits

/-!
# The exact limit obligation for safely completing a designated source set

Repeated applications of the safe-link theorem preserve unhinderedness at
each successor stage, but unhinderedness need not be continuous under an
infinite increasing union of deleted carriers.  This file isolates the exact
additional assertion needed at a limit.

The assertion is expressed intrinsically in the final residual web: every
maximal wave must start at the entire residual source.  It is equivalent to
unhinderedness.  The nontrivial implication uses the maximal-hindrance
extension theorem: if the residual were hindered, some maximal wave would
still be a hindrance and would therefore witness failure of the condition.

This is deliberately stronger than checking all of the proper initial
segments of a deletion chain.  It is the condition that a progressive
infinite safe-selection construction must establish at each limit stage.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSafeDesignatedLimit

open SingularSafeDesignatedLinkage

universe u

variable {V : Type u}

/-- Every maximal wave starts at the whole source.  By maximal-hindrance
extension this is exactly unhinderedness, but this formulation is the useful
limit invariant: it only asks a global construction to rule out maximal
residual hindrances. -/
def MaximalWaveComplete (G : DWeb V) : Prop :=
  ∀ M : G.Wave, IsMax M → G.initialSet M.1 = G.source

/-- In an unhindered web, every wave (and hence every maximal wave) starts at
the whole source. -/
theorem maximalWaveComplete_of_isUnhindered
    {G : DWeb V} (hG : G.IsUnhindered) :
    MaximalWaveComplete G := by
  intro M _hMmax
  exact G.isUnhindered_iff.mp hG M.1 M.2

/-- It suffices to check full source coverage only for maximal waves.  If a
hindrance existed, the maximal-hindrance extension theorem would produce a
maximal wave which is still a hindrance. -/
theorem isUnhindered_of_maximalWaveComplete
    {G : DWeb V} (hG : MaximalWaveComplete G) :
    G.IsUnhindered := by
  rw [G.isUnhindered_iff_not_isHindered]
  intro hHindered
  obtain ⟨M, hMmax, hMhinder⟩ := G.exists_maximal_hindrance hHindered
  exact hMhinder.2 (hG M hMmax)

theorem maximalWaveComplete_iff_isUnhindered (G : DWeb V) :
    MaximalWaveComplete G ↔ G.IsUnhindered := by
  exact ⟨isUnhindered_of_maximalWaveComplete,
    maximalWaveComplete_of_isUnhindered⟩

/-! ## Resurrecting final waves at an earlier safe stage

Suppose `X` is the part of a carrier added between an earlier safe stage
`G` and a limit residual `G.delete X`.  A final wave lifts to the earlier
graph, but need not remain a wave there: target paths can enter `X`.  The
right comparison object also puts trivial paths at all earlier sources
which are removed by `X`.  If that augmented family is an earlier wave,
earlier unhinderedness forces the final wave to start everywhere it should.
-/

/-- Lift a wave from a later deletion and put trivial paths at the source
vertices which exist at the earlier stage but are removed by that deletion. -/
def resurrectedWaveFamily (G : DWeb V) (X : Set V)
    (M : (G.delete X).Wave) : Set G.DPath :=
  G.liftDeleteFamily X M.1 ∪ G.trivialPath '' (G.source ∩ X)

/-- The sole separator obligation for a resurrected family.  Its two
terminal frontiers are the final wave frontier and the later-deleted source
vertices. -/
def ResurrectionSeparates (G : DWeb V) (X : Set V)
    (M : (G.delete X).Wave) : Prop :=
  G.source ⊆ G.roof
    ((G.delete X).terminalFrontier M.1 ∪ (G.source ∩ X))

theorem resurrectedWaveFamily_isWarp
    (G : DWeb V) (X : Set V) (M : (G.delete X).Wave) :
    G.IsWarp (resurrectedWaveFamily G X M) := by
  have havoid : Disjoint
      (G.vertexSet (G.liftDeleteFamily X M.1)) X :=
    G.vertexSet_liftDeleteFamily_disjoint M.2.2.1
  apply Set.PairwiseDisjoint.union M.2.1.liftDeleteFamily
    (G.isWarp_trivialPaths (G.source ∩ X))
  rintro p hp q ⟨x, hx, rfl⟩ _hpq
  rw [G.support_trivialPath]
  apply Set.disjoint_singleton_right.2
  intro hxp
  exact Set.disjoint_left.1 havoid ⟨p, hp, hxp⟩ hx.2

theorem initialSet_resurrectedWaveFamily
    (G : DWeb V) (X : Set V) (M : (G.delete X).Wave) :
    G.initialSet (resurrectedWaveFamily G X M) =
      (G.delete X).initialSet M.1 ∪ (G.source ∩ X) := by
  rw [resurrectedWaveFamily, G.initialSet_union,
    G.initialSet_liftDeleteFamily, G.initialSet_trivialPaths]

theorem terminalFrontier_resurrectedWaveFamily
    (G : DWeb V) (X : Set V) (M : (G.delete X).Wave) :
    G.terminalFrontier (resurrectedWaveFamily G X M) =
      (G.delete X).terminalFrontier M.1 ∪ (G.source ∩ X) := by
  rw [resurrectedWaveFamily, G.terminalFrontier_union,
    G.terminalFrontier_liftDeleteFamily, G.terminalFrontier_trivialPaths]

/-- Once the final wave is lifted and later-completed sources are restored
as trivial components, all structural wave conditions are automatic.  The
only genuine continuity condition is the displayed separator inclusion. -/
theorem isWave_resurrectedWaveFamily_iff
    (G : DWeb V) (X : Set V) (M : (G.delete X).Wave) :
    G.IsWave (resurrectedWaveFamily G X M) ↔
      ResurrectionSeparates G X M := by
  constructor
  · intro hW
    rw [ResurrectionSeparates,
      ← terminalFrontier_resurrectedWaveFamily G X M]
    exact hW.2.2
  · intro hsep
    refine ⟨resurrectedWaveFamily_isWarp G X M, ?_, ?_⟩
    · rw [initialSet_resurrectedWaveFamily]
      exact Set.union_subset
        (M.2.2.1.trans Set.sdiff_subset) Set.inter_subset_left
    · rw [terminalFrontier_resurrectedWaveFamily]
      exact hsep

/-- The construction-specific continuity assertion needed at an infinite
limit: every maximal final wave, after adding trivial paths at the sources
completed on the way to the limit, is already a wave at the earlier safe
stage. -/
def MaximalWavesResurrectAcrossDelete (G : DWeb V) (X : Set V) : Prop :=
  ∀ M : (G.delete X).Wave, IsMax M →
    G.IsWave (resurrectedWaveFamily G X M)

/-- Resurrection across a deletion transports unhinderedness to the final
residual.  This is the precise limit lemma for a progressive construction:
successor safety supplies `hG`, while the global closure/switching argument
must supply `hresurrect`. -/
theorem maximalWaveComplete_delete_of_resurrection
    {G : DWeb V} {X : Set V}
    (hG : G.IsUnhindered)
    (hresurrect : MaximalWavesResurrectAcrossDelete G X) :
    MaximalWaveComplete (G.delete X) := by
  intro M hMmax
  have hfull := G.isUnhindered_iff.mp hG
    (resurrectedWaveFamily G X M) (hresurrect M hMmax)
  rw [resurrectedWaveFamily, G.initialSet_union,
    G.initialSet_liftDeleteFamily, G.initialSet_trivialPaths] at hfull
  apply Set.Subset.antisymm
  · exact M.2.2.1
  · intro a ha
    have haEarlier : a ∈ G.source := ha.1
    have haUnion : a ∈ (G.delete X).initialSet M.1 ∪
        (G.source ∩ X) := hfull.symm ▸ haEarlier
    rcases haUnion with haInitial | haDeleted
    · exact haInitial
    · exact (ha.2 haDeleted.2).elim

theorem isUnhindered_delete_of_resurrection
    {G : DWeb V} {X : Set V}
    (hG : G.IsUnhindered)
    (hresurrect : MaximalWavesResurrectAcrossDelete G X) :
    (G.delete X).IsUnhindered :=
  isUnhindered_of_maximalWaveComplete
    (maximalWaveComplete_delete_of_resurrection hG hresurrect)

/-- The limit obligation for a candidate path family is maximal-wave
completeness in the web left after deleting its whole carrier. -/
def LimitMaximalWaveComplete (G : DWeb V) (P : Set G.DPath) : Prop :=
  MaximalWaveComplete (G.delete (G.vertexSet P))

theorem limitMaximalWaveComplete_iff
    (G : DWeb V) (P : Set G.DPath) :
    LimitMaximalWaveComplete G P ↔
      (G.delete (G.vertexSet P)).IsUnhindered := by
  exact maximalWaveComplete_iff_isUnhindered _

/-- A designated linkage whose final residual satisfies the exact maximal
wave limit condition is an ambiently safe designated linkage. -/
def safeDesignatedLinkageOfLimit
    {G : DWeb V} {A : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hlimit : LimitMaximalWaveComplete G P) :
    SafeDesignatedLinkage G A where
  paths := P
  linkage := hP
  residual_unhindered :=
    isUnhindered_of_maximalWaveComplete hlimit

/-- Existential form used by transfinite safe-batch selectors.  The only
genuinely new limit premise, beyond constructing the limiting linkage, is
the maximal-wave condition in its final residual. -/
theorem exists_safeDesignatedLinkage_of_limit
    {G : DWeb V} {A : Set V}
    (hlimit : ∃ P : Set G.DPath,
      IsLinkageBetween G A G.target P ∧
        LimitMaximalWaveComplete G P) :
    Nonempty (SafeDesignatedLinkage G A) := by
  obtain ⟨P, hP, hPmax⟩ := hlimit
  exact ⟨safeDesignatedLinkageOfLimit hP hPmax⟩

#print axioms maximalWaveComplete_iff_isUnhindered
#print axioms isUnhindered_delete_of_resurrection
#print axioms exists_safeDesignatedLinkage_of_limit

end SingularSafeDesignatedLimit
end CardinalInduction
end Erdos599
