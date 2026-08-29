/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteProxyReference
import ErdosProblems.Erdos599.HalfwayOutsideReference

/-!
# Fractured assignment against a reference warp containing rays

This file keeps the finite-character simultaneous-assignment compiler intact.
It runs that compiler against `finiteProxyReference Y` and then promotes the
unchanged assigned traces to the original boundary-aligned warp `Y`.
-/

noncomputable section

open Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath
open _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {Z Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}

/-- A nontrivial backward link cannot be carried by a singleton ray proxy,
so its proxy owner is an actual finite member of the original reference. -/
theorem backwardLink_has_finiteOriginalOwner
    (hQ : BackwardLinksOn (finiteProxyReference Y) Q)
    {l : Link Gamma.graph} (hl : l ∈ Q.links)
    (hbackward : l.direction = .backward) :
    ∃ p : FinitePath Gamma.graph, (.inl p : Gamma.DPath) ∈ Y ∧
      l.path.IsSubpathOf (.inl p : Gamma.DPath) := by
  obtain ⟨q, hqProxy, hlq⟩ := hQ l hl hbackward
  obtain ⟨p, hpY, hpq⟩ := hqProxy
  rcases p with p | r
  · subst q
    exact ⟨p, hpY, hlq⟩
  · subst q
    have hstart : l.path.start = r.initial := by
      have hmem := hlq.1 l.path.start_mem_support
      rw [finiteProxyPath_ray, Gamma.support_trivialPath] at hmem
      simpa using hmem
    have hfinish : l.path.finish = r.initial := by
      have hmem := hlq.1 l.path.finish_mem_support
      rw [finiteProxyPath_ray, Gamma.support_trivialPath] at hmem
      simpa using hmem
    exact False.elim (l.nontrivial (hstart.trans hfinish.symm))

/-- Consequently every proxy-alternating backward link is a backward link on
the original reference. -/
theorem backwardLinksOn_of_finiteProxyReference
    (hQ : BackwardLinksOn (finiteProxyReference Y) Q) :
    BackwardLinksOn Y Q := by
  intro l hl hbackward
  obtain ⟨p, hpY, hlp⟩ :=
    backwardLink_has_finiteOriginalOwner hQ hl hbackward
  exact ⟨.inl p, hpY, hlp⟩

/-- No backward edge selected against the finite proxy can lie on an omitted
reference ray. -/
theorem backwardIntersection_ray_eq_empty_of_finiteProxyReference
    (hY : Gamma.IsWarp Y)
    (hQ : BackwardLinksOn (finiteProxyReference Y) Q)
    (r : Ray Gamma.graph) (hrY : (.inr r : Gamma.DPath) ∈ Y) :
    Q.directionEdges .backward ∩ r.edgeSet = ∅ := by
  ext e
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨heBackward, her⟩
  simp only [AltPath.directionEdges, Set.mem_iUnion] at heBackward
  obtain ⟨l, hlQ, hldir, hel⟩ := heBackward
  obtain ⟨p, hpY, hlp⟩ :=
    backwardLink_has_finiteOriginalOwner hQ hlQ hldir
  have hpne : (.inl p : Gamma.DPath) ≠ .inr r := by simp
  have hdisjoint : Disjoint p.support r.support := hY hpY hrY hpne
  have helEnds := l.path.edgeSet_subset_support_prod hel
  have herEnds := r.edgeSet_subset_support_prod her
  exact Set.disjoint_left.1 hdisjoint (hlp.1 helEnds.1) herEnds.1

/-- A proxy-maximal finite terminal is outside the original reference by the
original terminal boundary condition. -/
theorem terminal_not_mem_original_of_proxyMaximal
    (hboundary : BoundaryAligned Z Y)
    (hmax : Q.IsInfinite ∨
      ∃ v ∈ Gamma.terminalFrontier Z \
          Gamma.vertexSet (finiteProxyReference Y),
        Q.terminal? = some v)
    {t : V} (ht : Q.terminal? = some t) :
    t ∉ Gamma.vertexSet Y := by
  rcases hmax with hinfinite | ⟨v, hv, hvterm⟩
  · have hnone : Q.terminal? = none :=
      Q.isInfinite_iff_terminal?_eq_none.mp hinfinite
    rw [ht] at hnone
    contradiction
  · have htv : t = v := Option.some.inj (ht.symm.trans hvterm)
    subst v
    exact (terminalFrontier_sdiff_finiteProxyReference_subset
      hboundary hv).2

/-- Safeness promotes from the finite proxy to the original reference once
the assigned source and the maximal terminal are tied to the original
boundary-aligned first family. -/
theorem isSafe_of_finiteProxyReference
    (hboundary : BoundaryAligned Z Y)
    (hY : Gamma.IsWarp Y)
    (hsource : Q.initial ∈ Gamma.initialSet Z \ Gamma.initialSet Y)
    (hmax : Q.IsInfinite ∨
      ∃ v ∈ Gamma.terminalFrontier Z \
          Gamma.vertexSet (finiteProxyReference Y),
        Q.terminal? = some v)
    (hQ : IsSafe (finiteProxyReference Y) Q) :
    IsSafe Y Q := by
  refine ⟨⟨hY, backwardLinksOn_of_finiteProxyReference hQ.1.2.1,
    ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro _hfirst
    exact hboundary.initial_outside hsource
  · intro t hterminal _hlast
    exact terminal_not_mem_original_of_proxyMaximal
      hboundary hmax hterminal
  · intro p hpY
    rcases p with p | r
    · exact hQ.2.1 (.inl p) ⟨.inl p, hpY, rfl⟩
    · left
      exact backwardIntersection_ray_eq_empty_of_finiteProxyReference
        hY hQ.1.2.1 r hpY
  · rintro ⟨R, hR⟩
    apply hQ.2.2.1
    refine ⟨R, ?_⟩
    intro e he
    have heOriginal := hR he
    exact ⟨heOriginal.1, fun heProxy ↦
      heOriginal.2 (familyEdges_finiteProxyReference_subset Y heProxy)⟩
  · rintro ⟨C, hC⟩
    apply hQ.2.2.2
    refine ⟨C, ?_⟩
    intro e he
    have heOriginal := hC he
    exact ⟨heOriginal.1, fun heProxy ↦
      heOriginal.2 (familyEdges_finiteProxyReference_subset Y heProxy)⟩

/-- Reindex a source from the original-reference domain to the definitionally
equal proxy-reference domain. -/
def toFiniteProxySource
    (z : {x : V // x ∈ Gamma.initialSet Z \ Gamma.initialSet Y}) :
    {x : V // x ∈ Gamma.initialSet Z \
      Gamma.initialSet (finiteProxyReference Y)} := by
  refine ⟨z.1, z.property.1, ?_⟩
  simpa only [initialSet_finiteProxyReference] using z.property.2

@[simp] theorem toFiniteProxySource_val
    (z : {x : V // x ∈ Gamma.initialSet Z \ Gamma.initialSet Y}) :
    (toFiniteProxySource z : V) = z.1 := rfl

theorem toFiniteProxySource_injective :
    Function.Injective
      (toFiniteProxySource (Gamma := Gamma) (Z := Z) (Y := Y)) := by
  intro s t hst
  apply Subtype.ext
  have hval := congrArg
    (fun z : {x : V // x ∈ Gamma.initialSet Z \
      Gamma.initialSet (finiteProxyReference Y)} ↦ z.1) hst
  exact hval

/-- Promote a simultaneous assignment against the finite proxy to the
original boundary-aligned reference, without changing any assigned trace. -/
noncomputable def liftFiniteProxyAssignment
    (hboundary : BoundaryAligned Z Y)
    (hY : Gamma.IsWarp Y)
    (A : SimultaneousAssignment Z (finiteProxyReference Y)) :
    SimultaneousAssignment Z Y where
  assigned z := A.assigned (toFiniteProxySource z)
  starts_at z := A.starts_at (toFiniteProxySource z)
  safe z := by
    apply isSafe_of_finiteProxyReference hboundary hY
      (hmax := A.maximal (toFiniteProxySource z))
    · rw [A.starts_at (toFiniteProxySource z)]
      exact z.property
    · exact A.safe (toFiniteProxySource z)
  leaving z := by
    rcases A.maximal (toFiniteProxySource z) with hinfinite |
        ⟨v, hv, hterm⟩
    · exact Or.inl hinfinite
    · exact Or.inr ⟨v, hterm,
        (terminalFrontier_sdiff_finiteProxyReference_subset
          hboundary hv).2⟩
  maximal z := by
    rcases A.maximal (toFiniteProxySource z) with hinfinite |
        ⟨v, hv, hterm⟩
    · exact Or.inl hinfinite
    · exact Or.inr ⟨v,
        terminalFrontier_sdiff_finiteProxyReference_subset hboundary hv,
        hterm⟩
  finite_terminals_injective := by
    intro s t v hs ht
    apply toFiniteProxySource_injective
    exact A.finite_terminals_injective hs ht

@[simp] theorem liftFiniteProxyAssignment_assigned
    (hboundary : BoundaryAligned Z Y)
    (hY : Gamma.IsWarp Y)
    (A : SimultaneousAssignment Z (finiteProxyReference Y))
    (z : {x : V // x ∈ Gamma.initialSet Z \ Gamma.initialSet Y}) :
    (liftFiniteProxyAssignment hboundary hY A).assigned z =
      A.assigned (toFiniteProxySource z) := rfl

namespace FracturedAssignmentPeel

/-- Promote a bracket-preserving fractured assignment from the proxy to the
original reference.  Forward-owner provenance is literally unchanged. -/
noncomputable def BracketFracturedAssignment.liftFiniteProxy
    {Z : FracturedWarp Gamma}
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (B : BracketFracturedAssignment Z (finiteProxyReference Y)) :
    BracketFracturedAssignment Z Y where
  assignment := liftFiniteProxyAssignment hboundary hY B.assignment
  bracket_safe := by
    intro z
    have hlocal := B.bracket_safe (toFiniteProxySource z)
    have hsafe :=
      (liftFiniteProxyAssignment hboundary hY B.assignment).safe z
    exact ⟨hsafe, hsafe.1, hlocal.2.2⟩

@[simp] theorem BracketFracturedAssignment.liftFiniteProxy_assigned
    {Z : FracturedWarp Gamma}
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (B : BracketFracturedAssignment Z (finiteProxyReference Y))
    (z : {x : V // x ∈ Gamma.initialSet Z.paths \
      Gamma.initialSet Y}) :
    (B.liftFiniteProxy hboundary hY).assignment.assigned z =
      B.assignment.assigned (toFiniteProxySource z) := rfl

/-- Ray-compatible boundary-aligned fractured assignment.  The first warp
and its recombination remain finite-character, but the reference warp need
not be. -/
theorem exists_bracketFracturedAssignment_anyReference
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths) :
    Nonempty (BracketFracturedAssignment Z Y) := by
  have hinitialProxy :
      Gamma.initialSet (finiteProxyReference Y) ⊆
        Gamma.initialSet Z.paths := by
    rwa [initialSet_finiteProxyReference]
  obtain ⟨B⟩ := exists_bracketFracturedAssignment Z
    (_root_.Erdos599.Blueprint.LinkageBlueprint.BoundaryAligned.finiteProxyReference
      hboundary)
    (finiteProxyReference_isWarp hY) hZfinite hZedgeFinite
    (finiteProxyReference_hasFiniteCharacter Y) hinitialProxy
  exact ⟨B.liftFiniteProxy hboundary hY⟩

end FracturedAssignmentPeel

namespace OutsideFracturedWarp

variable {W : Set Gamma.DPath} {X : Set V}

/-- Cut-facing form of the arbitrary-reference fractured compiler. -/
theorem exists_bracketFracturedAssignment_anyReference
    (F : OutsideFracturedWarp W X)
    (hboundary : BoundaryAligned F.holes.paths Y)
    (hY : Gamma.IsWarp Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet F.holes.paths) :
    Nonempty (FracturedAssignmentPeel.BracketFracturedAssignment F.holes Y) :=
  FracturedAssignmentPeel.exists_bracketFracturedAssignment_anyReference
    F.holes hboundary hY F.finiteCharacter F.edgeWarpFiniteCharacter hinitial

end OutsideFracturedWarp

#print axioms isSafe_of_finiteProxyReference
#print axioms FracturedAssignmentPeel.exists_bracketFracturedAssignment_anyReference

end LinkageBlueprint
end Blueprint
end Erdos599
