/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedSourceFirstFiniteResidualMatching

/-!
# Exact finite successor accounting for a protected residual matching

A finite residual matching need not avoid every member of the old stopped
warp.  The sound one-step operation removes precisely the old members met by
the matching warp and retains the complementary subfamily literally.  The
set of removed old members, and hence its old terminal frontier, is finite.

This file records the exact accounting.  In particular it does **not** claim
that the new frontier is already a separator.  The finite set
`finiteResidualBoundaryCost` is the additional obligation which a subsequent
matching step must absorb.  A protected member supported inside the avoided
carrier is retained literally.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath
open PopularGroundingBridge

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "T₁" =>
  reservedStrongSelectedSourceFirstBB (L := L) (hL := hL) (S := S)

/-- Old stopped-warp members touched by the finite matching carrier. -/
def finiteResidualTouchedOwners
    (Y W : Set Gamma.DPath) : Set Gamma.DPath :=
  {p | p ∈ Y ∧ (p.support ∩ Gamma.vertexSet W).Nonempty}

/-- Old stopped-warp members retained literally after the finite matching. -/
def finiteResidualUntouchedOwners
    (Y W : Set Gamma.DPath) : Set Gamma.DPath :=
  Y \ finiteResidualTouchedOwners Y W

/-- The honest one-step successor family: the new finite matching together
with the literal untouched part of the old stopped warp. -/
def finiteResidualSuccessorFamily
    (Y W : Set Gamma.DPath) : Set Gamma.DPath :=
  W ∪ finiteResidualUntouchedOwners Y W

/-- The precise finite old-frontier cost of the one-step operation. -/
def finiteResidualBoundaryCost
    (Y W : Set Gamma.DPath) : Set V :=
  Gamma.terminalFrontier (finiteResidualTouchedOwners Y W)

/-- The carrier of a finite family of finite paths is finite. -/
theorem finiteFamily_vertexSet_finite
    {W : Set Gamma.DPath} (hW : W.Finite)
    (hfinite : Gamma.HasFiniteCharacter W) :
    (Gamma.vertexSet W).Finite := by
  have hunion : Gamma.vertexSet W = ⋃ p ∈ W, p.support := by
    ext x
    simp [DWeb.vertexSet]
  rw [hunion]
  exact hW.biUnion fun p hp ↦ by
    obtain ⟨q, rfl⟩ := hfinite hp
    exact q.support_finite

private theorem pathsThrough_finite
    {Y : Set Gamma.DPath} (hY : Gamma.IsWarp Y) (x : V) :
    {p | p ∈ Y ∧ x ∈ p.support}.Finite := by
  classical
  let F : Set Gamma.DPath := {p | p ∈ Y ∧ x ∈ p.support}
  by_cases hF : F.Nonempty
  · obtain ⟨p, hpF⟩ := hF
    apply (Set.finite_singleton p).subset
    intro q hqF
    have hqp : q = p := by
      by_contra hqp
      exact Set.disjoint_left.1 (hY hqF.1 hpF.1 hqp)
        hqF.2 hpF.2
    simpa only [Set.mem_singleton_iff] using hqp
  · change F.Finite
    rw [Set.not_nonempty_iff_eq_empty.mp hF]
    exact Set.finite_empty

private theorem pathsMeetingVertices_finite
    {Y : Set Gamma.DPath} (hY : Gamma.IsWarp Y)
    {carrier : Set V} (hcarrier : carrier.Finite) :
    {p | p ∈ Y ∧ (p.support ∩ carrier).Nonempty}.Finite := by
  induction carrier, hcarrier using Set.Finite.induction_on with
  | empty =>
      have hempty : {p | p ∈ Y ∧ (p.support ∩ ∅).Nonempty} = ∅ := by
        ext p
        simp
      rw [hempty]
      exact Set.finite_empty
  | @insert x carrier hx hcarrier ih =>
      have hsub : {p | p ∈ Y ∧
          (p.support ∩ insert x carrier).Nonempty} ⊆
          {p | p ∈ Y ∧ x ∈ p.support} ∪
            {p | p ∈ Y ∧ (p.support ∩ carrier).Nonempty} := by
        intro p hp
        obtain ⟨hpY, y, hyp, hy⟩ := hp
        rcases hy with rfl | hyCarrier
        · exact Or.inl ⟨hpY, hyp⟩
        · exact Or.inr ⟨hpY, y, hyp, hyCarrier⟩
      exact ((pathsThrough_finite hY x).union ih).subset hsub

private theorem finiteResidualTouchedOwners_subset
    (Y W : Set Gamma.DPath) :
    finiteResidualTouchedOwners Y W ⊆ Y := by
  exact fun _ hp ↦ hp.1

private theorem initialSet_diff_of_subfamily
    {Y P : Set Gamma.DPath} (hY : Gamma.IsWarp Y) (hPY : P ⊆ Y) :
    Gamma.initialSet (Y \ P) =
      Gamma.initialSet Y \ Gamma.initialSet P := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p, hp.1, rfl⟩, ?_⟩
    rintro ⟨q, hqP, hqinitial⟩
    have hpq : p = q :=
      DWeb.IsWarp.eq_of_initial_eq Gamma hY hp.1 (hPY hqP)
        hqinitial.symm
    exact hp.2 (hpq ▸ hqP)
  · rintro ⟨⟨p, hpY, rfl⟩, hpInitial⟩
    refine ⟨p, ⟨hpY, ?_⟩, rfl⟩
    intro hpP
    exact hpInitial ⟨p, hpP, rfl⟩

private theorem terminalFrontier_diff_of_subfamily
    {Y P : Set Gamma.DPath} (hY : Gamma.IsWarp Y) (hPY : P ⊆ Y) :
    Gamma.terminalFrontier (Y \ P) =
      Gamma.terminalFrontier Y \ Gamma.terminalFrontier P := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    refine ⟨⟨p, hp.1, hpx⟩, ?_⟩
    rintro ⟨q, hqP, hqx⟩
    have hpq : p = q := by
      by_contra hpq
      exact Set.disjoint_left.1 (hY hp.1 (hPY hqP) hpq)
        (Gamma.terminal_mem_support hpx)
        (Gamma.terminal_mem_support hqx)
    exact hp.2 (hpq ▸ hqP)
  · rintro ⟨⟨p, hpY, hpx⟩, hpFrontier⟩
    refine ⟨p, ⟨hpY, ?_⟩, hpx⟩
    intro hpP
    exact hpFrontier ⟨p, hpP, hpx⟩

/-- Only finitely many old warp members are touched in one finite step. -/
theorem finiteResidualTouchedOwners_finite
    {Y W : Set Gamma.DPath} (hY : Gamma.IsWarp Y)
    (hW : W.Finite) (hfinite : Gamma.HasFiniteCharacter W) :
    (finiteResidualTouchedOwners Y W).Finite := by
  exact pathsMeetingVertices_finite hY
    (finiteFamily_vertexSet_finite hW hfinite)

/-- The old frontier lost in one finite step is finite. -/
theorem finiteResidualBoundaryCost_finite
    {Y W : Set Gamma.DPath} (hY : Gamma.IsWarp Y)
    (hW : W.Finite) (hfinite : Gamma.HasFiniteCharacter W) :
    (finiteResidualBoundaryCost Y W).Finite := by
  have htouched := finiteResidualTouchedOwners_finite hY hW hfinite
  have himage : (Gamma.terminal? ''
      finiteResidualTouchedOwners Y W).Finite :=
    htouched.image Gamma.terminal?
  have hpreimage : (some ⁻¹' (Gamma.terminal? ''
      finiteResidualTouchedOwners Y W)).Finite :=
    himage.preimage
      (Set.injOn_of_injective (Option.some_injective V))
  apply hpreimage.subset
  rintro x ⟨p, hp, hpx⟩
  exact ⟨p, hp, hpx⟩

/-- The matching carrier is disjoint from every literally untouched old
member. -/
theorem finiteResidualSuccessor_cross_disjoint
    (Y W : Set Gamma.DPath) :
    Disjoint (Gamma.vertexSet W)
      (Gamma.vertexSet (finiteResidualUntouchedOwners Y W)) := by
  rw [Set.disjoint_left]
  intro x hxW hxOld
  obtain ⟨p, hpOld, hxp⟩ := hxOld
  exact hpOld.2 ⟨hpOld.1, x, hxp, hxW⟩

/-- The one-step successor is an honest warp. -/
theorem finiteResidualSuccessorFamily_isWarp
    {Y W : Set Gamma.DPath} (hY : Gamma.IsWarp Y)
    (hW : Gamma.IsWarp W) :
    Gamma.IsWarp (finiteResidualSuccessorFamily Y W) := by
  apply Set.PairwiseDisjoint.union hW
    (hY.subset Set.diff_subset)
  intro p hpW q hqOld _hpq
  apply Set.disjoint_left.2
  intro x hxp hxq
  exact Set.disjoint_left.1
    (finiteResidualSuccessor_cross_disjoint Y W)
    ⟨p, hpW, hxp⟩ ⟨q, hqOld, hxq⟩

/-- Exact initial-set accounting for the finite successor. -/
theorem finiteResidualSuccessorFamily_initialSet
    {Y W : Set Gamma.DPath} (hY : Gamma.IsWarp Y) :
    Gamma.initialSet (finiteResidualSuccessorFamily Y W) =
      Gamma.initialSet W ∪
        (Gamma.initialSet Y \
          Gamma.initialSet (finiteResidualTouchedOwners Y W)) := by
  rw [finiteResidualSuccessorFamily, Gamma.initialSet_union,
    finiteResidualUntouchedOwners,
    initialSet_diff_of_subfamily (Gamma := Gamma) hY
      (finiteResidualTouchedOwners_subset Y W)]

/-- Exact terminal-frontier accounting for the finite successor.  The old
frontier loss is exactly `finiteResidualBoundaryCost Y W`. -/
theorem finiteResidualSuccessorFamily_terminalFrontier
    {Y W : Set Gamma.DPath} (hY : Gamma.IsWarp Y) :
    Gamma.terminalFrontier (finiteResidualSuccessorFamily Y W) =
      Gamma.terminalFrontier W ∪
        (Gamma.terminalFrontier Y \ finiteResidualBoundaryCost Y W) := by
  rw [finiteResidualSuccessorFamily, Gamma.terminalFrontier_union,
    finiteResidualUntouchedOwners,
    terminalFrontier_diff_of_subfamily (Gamma := Gamma) hY
      (finiteResidualTouchedOwners_subset Y W)]
  rfl

/-- If both old and new initials are ambient sources, every successor
initial is an ambient source. -/
theorem finiteResidualSuccessorFamily_initialSet_subset_source
    {Y W : Set Gamma.DPath}
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source)
    (hWsource : Gamma.initialSet W ⊆ Gamma.source) :
    Gamma.initialSet (finiteResidualSuccessorFamily Y W) ⊆ Gamma.source := by
  rw [finiteResidualSuccessorFamily, Gamma.initialSet_union]
  apply Set.union_subset hWsource
  rintro x ⟨q, hq, rfl⟩
  exact hYsource ⟨q, hq.1, rfl⟩

/-- Every terminal of a family whose initials are ambient sources is rooted
from an ambient source using that same family's edges. -/
theorem terminalFrontier_rooted_in_family
    {J : Set Gamma.DPath}
    (hsource : Gamma.initialSet J ⊆ Gamma.source)
    {t : V} (ht : t ∈ Gamma.terminalFrontier J) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ Alternating.familyEdges J) a t := by
  obtain ⟨p, hpJ, hpTerminal⟩ := ht
  cases p with
  | inr r => cases hpTerminal
  | inl q =>
      have hstart : q.start ∈ Gamma.source := by
        apply hsource
        exact ⟨Sum.inl q, hpJ, rfl⟩
      have hedge : q.edgeSet ⊆ Alternating.familyEdges J := by
        intro e he
        simp only [Alternating.familyEdges, Set.mem_iUnion]
        exact ⟨Sum.inl q, hpJ, he⟩
      have hwalk : Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ Alternating.familyEdges J)
          q.start q.finish :=
        Relation.ReflTransGen.mono
          (r := fun x y ↦ (x, y) ∈ q.edgeSet)
          (p := fun x y ↦ (x, y) ∈ Alternating.familyEdges J)
          (fun _ _ he ↦ hedge he) q.start q.finish
          (Alternating.Walk.reflTransGen_edgeSet q.walk)
      exact ⟨q.start, hstart, Option.some.inj hpTerminal ▸ hwalk⟩

/-- Hence every exact successor terminal is rooted inside the exact
successor family. -/
theorem finiteResidualSuccessorFamily_terminal_rooted
    {Y W : Set Gamma.DPath}
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source)
    (hWsource : Gamma.initialSet W ⊆ Gamma.source)
    {t : V}
    (ht : t ∈ Gamma.terminalFrontier
      (finiteResidualSuccessorFamily Y W)) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ Alternating.familyEdges
          (finiteResidualSuccessorFamily Y W)) a t := by
  exact terminalFrontier_rooted_in_family
    (finiteResidualSuccessorFamily_initialSet_subset_source
      hYsource hWsource) ht

/-- A protected old member whose support is disjoint from the finite
matching carrier is retained literally. -/
theorem mem_finiteResidualUntouchedOwners_of_disjoint
    {Y W : Set Gamma.DPath} {p : Gamma.DPath}
    (hpY : p ∈ Y) (hdisjoint : Disjoint p.support (Gamma.vertexSet W)) :
    p ∈ finiteResidualUntouchedOwners Y W := by
  refine ⟨hpY, ?_⟩
  rintro ⟨_hpY, x, hxp, hxW⟩
  exact Set.disjoint_left.1 hdisjoint hxp hxW

theorem mem_finiteResidualSuccessorFamily_of_disjoint
    {Y W : Set Gamma.DPath} {p : Gamma.DPath}
    (hpY : p ∈ Y) (hdisjoint : Disjoint p.support (Gamma.vertexSet W)) :
    p ∈ finiteResidualSuccessorFamily Y W := by
  exact Or.inr (mem_finiteResidualUntouchedOwners_of_disjoint hpY hdisjoint)

/-- Concrete finite successor accounting for the protected Menger matching.

The finite set `B` is exactly the old stopped frontier sacrificed by this
one matching warp.  It is returned as a new residual obligation; no claim is
made that `C ∪ (terminalFrontier Y \ B)` is already a separator.  The
protected path `p` is retained literally because its support is contained in
the avoided carrier `Z`. -/
theorem exists_protectedFiniteResidualSuccessorAccounting
    {R Z : Set V} {Y : Set Gamma.DPath} {p : Gamma.DPath}
    (hR : R.Finite) (hRT : R ⊆ T₁) (hRZ : Disjoint R Z)
    (hY : Gamma.IsWarp Y)
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source)
    (hYterminal : Gamma.terminalFrontier Y ⊆ T₁)
    (hpY : p ∈ Y) (hpZ : p.support ⊆ Z) :
    ∃ (P : Set (Bridge.DirectedABPath (Gamma.delete Z).graph
          (Gamma.source \ Z) R)) (C B : Set V) (W : Set Gamma.DPath),
      Bridge.DirectedIsPathPacking P ∧
      Bridge.DirectedIsABSeparator (Gamma.delete Z).graph
        (Gamma.source \ Z) R C ∧
      Bridge.DirectedIsOrthogonal P C ∧
      P.Finite ∧ C.Finite ∧ Disjoint C Z ∧
      Gamma.IsWarp W ∧ W.Finite ∧ Gamma.HasFiniteCharacter W ∧
      Gamma.initialSet W ⊆ Gamma.source \ Z ∧
      Gamma.terminalFrontier W = C ∧
      Disjoint (Gamma.vertexSet W) Z ∧
      B = finiteResidualBoundaryCost Y W ∧ B.Finite ∧ B ⊆ T₁ ∧
      Gamma.IsWarp (finiteResidualSuccessorFamily Y W) ∧
      Gamma.initialSet (finiteResidualSuccessorFamily Y W) ⊆ Gamma.source ∧
      Gamma.terminalFrontier (finiteResidualSuccessorFamily Y W) =
        C ∪ (Gamma.terminalFrontier Y \ B) ∧
      (∀ t ∈ Gamma.terminalFrontier (finiteResidualSuccessorFamily Y W),
        ∃ a ∈ Gamma.source,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ Alternating.familyEdges
              (finiteResidualSuccessorFamily Y W)) a t) ∧
      p ∈ finiteResidualSuccessorFamily Y W ∧
      Popular.IsSeparator Gamma ((T₁ \ R) ∪ Z ∪ C) := by
  obtain ⟨P, C, hpacking, hseparator, horthogonal, hPfinite, hCfinite,
      hCZ, hSep⟩ :=
    exists_protectedFiniteResidualMatching hR hRT hRZ
  obtain ⟨W, hW, hWfamily, hWfinite, hWsource, hWterminal, hWZ⟩ :=
    exists_finiteProtectedOrthogonalWarp hpacking horthogonal hPfinite
  let B : Set V := finiteResidualBoundaryCost Y W
  have hBfinite : B.Finite :=
    finiteResidualBoundaryCost_finite hY hWfamily hWfinite
  have hBT : B ⊆ T₁ := by
    intro b hb
    apply hYterminal
    obtain ⟨q, hq, hqb⟩ := hb
    exact ⟨q, hq.1, hqb⟩
  have hWambientSource : Gamma.initialSet W ⊆ Gamma.source :=
    fun _ hx ↦ (hWsource hx).1
  have hpWdisjoint : Disjoint p.support (Gamma.vertexSet W) :=
    hWZ.symm.mono_left hpZ
  refine ⟨P, C, B, W, hpacking, hseparator, horthogonal, hPfinite,
    hCfinite, hCZ, hW, hWfamily, hWfinite, hWsource, hWterminal, hWZ,
    rfl, hBfinite, hBT, finiteResidualSuccessorFamily_isWarp hY hW,
    finiteResidualSuccessorFamily_initialSet_subset_source
      hYsource hWambientSource, ?_, ?_,
    mem_finiteResidualSuccessorFamily_of_disjoint hpY hpWdisjoint, hSep⟩
  · rw [finiteResidualSuccessorFamily_terminalFrontier hY, hWterminal]
  · intro t ht
    exact finiteResidualSuccessorFamily_terminal_rooted
      hYsource hWambientSource ht

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.exists_protectedFiniteResidualSuccessorAccounting
