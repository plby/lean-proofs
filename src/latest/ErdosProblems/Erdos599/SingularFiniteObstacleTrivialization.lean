/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualTouchedPaths
import ErdosProblems.Erdos599.SingularFiniteExactBoundaryRepair
import ErdosProblems.Erdos599.RoofQuotient

/-!
# Trivializing the finitely many paths which meet a new obstacle

When a warp is moved to a vertex-deleted web, only finitely many of its
members may meet a finite local obstacle.  Instead of trying to cut those
members immediately before their first obstacle contact, replace each such
member by the trivial path at its initial vertex.  This preserves the entire
initial profile and loses only finitely many terminal-frontier vertices.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteObstacleTrivialization

open DWeb
open SingularMarkedResidualTouchedPaths
open SingularFiniteExactBoundaryRepair

universe u

variable {V : Type u}

/-- Delete a local obstacle from a warp by retaining the members which avoid
it and replacing every member which meets it by the trivial path at its
initial vertex. -/
theorem exists_deleteWarp_preserving_initial_losing_finite_frontier
    (G : DWeb V) {R : Set G.DPath}
    (hR : G.IsWarp R) (hRfinite : G.HasFiniteCharacter R)
    {X S : Set V} (hSfinite : S.Finite)
    (hcontact : G.vertexSet R ∩ X ⊆ S)
    (hinitialAvoid : Disjoint (G.initialSet R) X) :
    ∃ W : Set ((G.delete X).DPath),
      (G.delete X).IsWarp W ∧
      (G.delete X).HasFiniteCharacter W ∧
      (G.delete X).initialSet W = G.initialSet R ∧
      (G.terminalFrontier R \ (G.delete X).terminalFrontier W).Finite := by
  let Bad := pathsMeetingVertices G R S
  let Good := R \ Bad
  have hBadFinite : Bad.Finite :=
    pathsMeetingVertices_finite_of_isWarp hR hSfinite
  have hGoodAvoid : Disjoint (G.vertexSet Good) X := by
    rw [Set.disjoint_left]
    intro x hxGood hxX
    obtain ⟨p, hpGood, hxp⟩ := hxGood
    have hxS : x ∈ S := hcontact ⟨⟨p, hpGood.1, hxp⟩, hxX⟩
    exact hpGood.2 ⟨hpGood.1, ⟨x, hxp, hxS⟩⟩
  let GoodD := G.restrictDeleteFamily X Good hGoodAvoid
  let BI := G.initialSet Bad
  let T := (G.delete X).trivialPath '' BI
  let W := GoodD ∪ T
  have hGoodWarp : G.IsWarp Good := fun p hp q hq hpq ↦
    hR hp.1 hq.1 hpq
  have hGoodDWarp : (G.delete X).IsWarp GoodD :=
    DWeb.IsWarp.restrictDeleteFamily G hGoodWarp hGoodAvoid
  have hTWarp : (G.delete X).IsWarp T :=
    (G.delete X).isWarp_trivialPaths BI
  have hCross : Set.PairwiseDisjoint (GoodD ∪ T)
      DirectedPath.Path.support := by
    apply Set.PairwiseDisjoint.union hGoodDWarp hTWarp
    rintro pg hpg pt hpt _hne
    obtain ⟨p, _hp, rfl⟩ := hpg
    obtain ⟨y, hyBI, rfl⟩ := hpt
    apply Set.disjoint_left.2
    intro x hxGood hxTrivial
    have hxy : x = y := by
      simpa only [(G.delete X).support_trivialPath,
        Set.mem_singleton_iff] using hxTrivial
    subst x
    obtain ⟨q, hqBad, hqy⟩ := hyBI
    have hyp : y ∈ p.1.support := by
      simpa only [G.support_restrictDeleteMember] using hxGood
    have hpq : p.1 ≠ q := by
      intro hpq
      subst q
      exact p.2.2 hqBad
    exact Set.disjoint_left.1 (hR p.2.1 hqBad.1 hpq)
      hyp (hqy ▸ q.initial_mem_support)
  have hGoodFinite : G.HasFiniteCharacter Good := by
    intro p hp
    exact hRfinite hp.1
  have hGoodDFinite : (G.delete X).HasFiniteCharacter GoodD :=
    G.fd_hasFiniteCharacter_restrictDeleteFamily hGoodFinite hGoodAvoid
  have hWfinite : (G.delete X).HasFiniteCharacter W := by
    intro p hp
    rcases hp with hpGood | hpT
    · exact hGoodDFinite hpGood
    · obtain ⟨x, _hx, rfl⟩ := hpT
      exact ⟨DirectedPath.FinitePath.trivial (G.delete X).graph x, rfl⟩
  have hInitialPartition : G.initialSet Good ∪ G.initialSet Bad =
      G.initialSet R := by
    ext x
    constructor
    · rintro (hx | hx)
      · obtain ⟨p, hp, hpx⟩ := hx
        exact ⟨p, hp.1, hpx⟩
      · obtain ⟨p, hp, hpx⟩ := hx
        exact ⟨p, hp.1, hpx⟩
    · rintro ⟨p, hpR, hpx⟩
      by_cases hpBad : p ∈ Bad
      · exact Or.inr ⟨p, hpBad, hpx⟩
      · exact Or.inl ⟨p, ⟨hpR, hpBad⟩, hpx⟩
  have hWinitial : (G.delete X).initialSet W = G.initialSet R := by
    rw [(G.delete X).initialSet_union,
      G.initialSet_restrictDeleteFamily,
      (G.delete X).initialSet_trivialPaths]
    exact hInitialPartition
  have hGap : G.terminalFrontier R \
      (G.delete X).terminalFrontier W ⊆ G.terminalFrontier Bad := by
    rintro x ⟨hxR, hxNotW⟩
    obtain ⟨p, hpR, hpx⟩ := hxR
    by_cases hpBad : p ∈ Bad
    · exact ⟨p, hpBad, hpx⟩
    · have hpGood : p ∈ Good := ⟨hpR, hpBad⟩
      let pGood : Good := ⟨p, hpGood⟩
      apply False.elim
      apply hxNotW
      rw [(G.delete X).terminalFrontier_union]
      left
      rw [G.terminalFrontier_restrictDeleteFamily]
      exact ⟨p, hpGood, hpx⟩
  exact ⟨W, hCross, hWfinite, hWinitial,
    (terminalFrontier_finite_of_family_finite hBadFinite).subset hGap⟩

/-- Source-subset form used by the finite roof absorber. -/
theorem exists_deleteWarp_preserving_initial_source_losing_finite_frontier
    (G : DWeb V) {R : Set G.DPath}
    (hR : G.IsWarp R) (hRfinite : G.HasFiniteCharacter R)
    (hRsource : G.initialSet R ⊆ G.source)
    {X S : Set V} (hSfinite : S.Finite)
    (hcontact : G.vertexSet R ∩ X ⊆ S)
    (hinitialAvoid : Disjoint (G.initialSet R) X) :
    ∃ W : Set ((G.delete X).DPath),
      (G.delete X).IsWarp W ∧
      (G.delete X).HasFiniteCharacter W ∧
      (G.delete X).initialSet W = G.initialSet R ∧
      (G.delete X).initialSet W ⊆ (G.delete X).source ∧
      (G.terminalFrontier R \ (G.delete X).terminalFrontier W).Finite := by
  obtain ⟨W, hW, hWfinite, hWinitial, hgap⟩ :=
    exists_deleteWarp_preserving_initial_losing_finite_frontier
      G hR hRfinite hSfinite hcontact hinitialAvoid
  refine ⟨W, hW, hWfinite, hWinitial, ?_, hgap⟩
  rw [hWinitial]
  intro x hx
  exact ⟨hRsource hx, fun hxX ↦
    Set.disjoint_left.1 hinitialAvoid hx hxX⟩

#print axioms exists_deleteWarp_preserving_initial_losing_finite_frontier
#print axioms exists_deleteWarp_preserving_initial_source_losing_finite_frontier

end SingularFiniteObstacleTrivialization
end CardinalInduction
end Erdos599
