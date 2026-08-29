/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClause
import ErdosProblems.Erdos599.SliceHalfwayCore

/-!
# The current-cardinal provisional target row

The current extension clause, applied to the source subweb on a designated
`kappa`-set, links that set to the target.  In a normalized web the resulting
paths avoid every other source.  Hence adjoining the trivial paths at the
remaining sources gives a finite-character warp with the whole ambient source
as initial set, while retaining genuine target links for the designated set.

This is the strongest direct consequence of the current extension clause
before the Section 9 closing-up construction.  The resulting row is not in
general a wave: its terminal frontier need not separate the designated sources
from the target.  Consequently maximal-wave conversion cannot be applied to it
without the replacement/scheduler argument.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

open DirectedPath

universe u

variable {V : Type u}

/-- A finite linkage from an arbitrary source subset to the target supplies
the source-faithful suffix certificate for that subset. -/
private theorem linksToTarget_of_linkageToTarget
    {G : DWeb V} {A : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P) :
    LinksToTarget G P A := by
  intro a ha
  have haInitial : a ∈ G.initialSet P := hP.initialSet_eq.symm ▸ ha
  obtain ⟨p, hpP, hpInitial⟩ := haInitial
  obtain ⟨q, rfl⟩ := hP.finiteCharacter hpP
  change q.start = a at hpInitial
  obtain ⟨r, hr, _hends, hsource⟩ :=
    hP.endpointPure (.inl q) hpP
  have hrq : r = q := by simpa using hr.symm
  subst r
  refine ⟨.inl q, hpP, q, rfl, ?_, ?_⟩
  · simpa only [hpInitial] using hsource
  · refine ⟨[], q.walk.support.tail, ?_, q.finish, ?_, ?_⟩
    · have hsupport :
          q.walk.support = q.start :: q.walk.support.tail := by
        have h := (List.cons_head_tail q.walk.support_ne_nil).symm
        simpa only [q.walk.head_support] using h
      exact hsupport.trans
        (congrArg (fun x ↦ x :: q.walk.support.tail) hpInitial)
    · apply hP.terminalFrontier_subset
      exact ⟨.inl q, hpP, rfl⟩
    · have hsupport :
          q.walk.support = q.start :: q.walk.support.tail := by
        have h := (List.cons_head_tail q.walk.support_ne_nil).symm
        simpa only [q.walk.head_support] using h
      have hfinish : q.finish ∈ q.start :: q.walk.support.tail := by
        rw [← hsupport]
        exact q.finish_mem_support
      simpa only [hpInitial] using hfinish

/-- The current-cardinal extension clause links the designated source subweb.

The complementary linkage in the definition of `ExtensionClauseAt` is empty,
because the designated set is the whole source of the auxiliary web. -/
theorem exists_designatedSourceLinkage_of_current
    {kappa : Cardinal.{u}}
    (hext : UniversalExtensionClauseAt V kappa)
    (G : DWeb V) (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) (hcard : #A = kappa) :
    ∃ P : Set G.DPath, IsLinkageBetween G A G.target P := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro u v huv hv
    exact (hNorm huv).1 hv
  have hsubUnhindered : (G.sourceSubweb A).IsUnhindered :=
    hG.sourceSubweb G hNoEnter hA
  have hlinkable : IsLinkable (G.sourceSubweb A) := by
    apply linkable_of_extension_at_source_card (G.sourceSubweb A)
    simpa only [DWeb.sourceSubweb_source, hcard] using
      hext (G.sourceSubweb A) hsubUnhindered
  obtain ⟨P, hP⟩ := hlinkable
  change IsLinkageBetween G A G.target P at hP
  exact ⟨P, hP⟩

/-- Adjoin the missing sources as trivial paths.  The result is the exact
current-cardinal analogue of the provisional row used in the singular branch.
-/
theorem exists_provisionalTargetRow_of_current
    {kappa : Cardinal.{u}}
    (hext : UniversalExtensionClauseAt V kappa)
    (G : DWeb V) (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) (hcard : #A = kappa) :
    ∃ W : Set G.DPath,
      G.IsWarp W ∧ G.HasFiniteCharacter W ∧
      G.initialSet W = G.source ∧ LinksToTarget G W A := by
  obtain ⟨P, hP⟩ :=
    exists_designatedSourceLinkage_of_current hext G hG hNorm hA hcard
  let R : Set G.DPath := G.trivialPath '' (G.source \ A)
  let W : Set G.DPath := P ∪ R
  have hcross : ∀ p ∈ P, ∀ q ∈ R, p ≠ q →
      Disjoint p.support q.support := by
    intro p hp q hq _hpq
    obtain ⟨x, hx, rfl⟩ := hq
    rw [G.support_trivialPath]
    apply Set.disjoint_singleton_right.2
    intro hxp
    have hxInitial : x = p.initial :=
      hNorm.eq_initial_of_mem_path p hxp hx.1
    have hpInitial : p.initial ∈ A := by
      rw [← hP.initialSet_eq]
      exact ⟨p, hp, rfl⟩
    exact hx.2 (hxInitial.symm ▸ hpInitial)
  have hwarp : G.IsWarp W := by
    apply Set.PairwiseDisjoint.union hP.isWarp
      (G.isWarp_trivialPaths (G.source \ A))
    exact hcross
  have hRfinite : G.HasFiniteCharacter R := by
    rintro p ⟨x, _hx, rfl⟩
    exact ⟨DirectedPath.FinitePath.trivial G.graph x, rfl⟩
  have hfinite : G.HasFiniteCharacter W := by
    intro p hp
    rcases hp with hp | hp
    · exact hP.finiteCharacter hp
    · exact hRfinite hp
  have hinitial : G.initialSet W = G.source := by
    change G.initialSet (P ∪ (G.trivialPath '' (G.source \ A))) = G.source
    rw [G.initialSet_union, G.initialSet_trivialPaths, hP.initialSet_eq,
      Set.union_comm, Set.sdiff_union_of_subset hA]
  have hlinksP : LinksToTarget G P A :=
    linksToTarget_of_linkageToTarget hP
  have hlinks : LinksToTarget G W A := by
    intro a ha
    obtain ⟨p, hp, hpa⟩ := hlinksP a ha
    exact ⟨p, Or.inl hp, hpa⟩
  exact ⟨W, hwarp, hfinite, hinitial, hlinks⟩

end CardinalInduction
end Erdos599
