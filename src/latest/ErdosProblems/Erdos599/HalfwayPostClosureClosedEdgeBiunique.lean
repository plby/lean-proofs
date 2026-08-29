/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureShortcutSourceCompatibility

/-!
# Biuniqueness of the actual closed 9.31 edge relation

Every forward edge of a compressed outside assignment is still an edge of
the literal outside family.  Therefore it cannot collide at a closed
endpoint with an edge of the inside restriction.  Combined with occurrence
compatibility of the shortcut union, this proves biuniqueness of the exact
inside-plus-shortcut relation.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- A compressed forward edge comes from the literal outside part of the
ambient interval family, not merely from the ambient family. -/
theorem assigned_forwardEdge_mem_outsideFamily
    (A : PostClosureMacroCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    {e : V × V}
    (he : e ∈
      (A.toPostClosureCompressorAssignment.assignment.produced.bracket
        |>.assignment.assigned s).directionEdges .forward) :
    e ∈ outsideFamilyEdges T.interval.ambientInterval Rlimit.closedSet := by
  simp only [AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hl, hdir, hel⟩ := he
  have hfragment :=
    (A.toPostClosureCompressorAssignment.assignment.produced.bracket
      |>.bracket_safe s).isBracketAlternating.2 l hl hdir
  have hfamily : l.path.edgeSet ⊆
      familyEdges A.fractured.outside.holes.edgeWarp :=
    edgeSet_subset_familyEdges_of_isFragmentOf hfragment
  rw [A.fractured.outside.edgeWarp_familyEdges] at hfamily
  exact hfamily hel

theorem sourceInsideEdges_biUnique :
    Relator.BiUnique (fun x y =>
      (x, y) ∈ sourceInsideEdges T.interval.ambientInterval
        Rlimit.closedSet) := by
  have hfamily := Alternating.IsWarp.familyEdges_biUnique
    T.interval.ambientInterval_linkage.isWarp
  constructor
  · intro x w y hxy hwy
    exact hfamily.1 hxy.1 hwy.1
  · intro x y w hxy hxw
    exact hfamily.2 hxy.1 hxw.1

/-- An inside edge and an actual shortcut cannot have a common head. -/
theorem inside_shortcut_no_common_head
    (A : PostClosureMacroCompressorAssignment T)
    {a b y : V}
    (hay : (a, y) ∈ sourceInsideEdges T.interval.ambientInterval
      Rlimit.closedSet)
    (hby : (b, y) ∈
      A.toPostClosureCompressorAssignment.actualPostClosureShortcutEdges) :
    False := by
  let A0 := A.toPostClosureCompressorAssignment
  rw [A0.mem_actualPostClosureShortcutEdges_iff] at hby
  obtain ⟨s, hby⟩ := hby
  obtain ⟨q, hqy⟩ := A0.segmentation_shortcut_head_hasIncoming_forward s
    (A0.actualClosedClassifiedContactSegmentation s)
    (A0.actualClosedClassifiedContactSegmentation_contactSet_subset s) hby
  have houtside := A.assigned_forwardEdge_mem_outsideFamily s hqy
  have haq : a = q :=
    (Alternating.IsWarp.familyEdges_biUnique
      T.interval.ambientInterval_linkage.isWarp).1 hay.1 houtside.1
  exact houtside.2 ⟨haq ▸ hay.2.1, hay.2.2⟩

/-- An inside edge and an actual shortcut cannot have a common tail. -/
theorem inside_shortcut_no_common_tail
    (A : PostClosureMacroCompressorAssignment T)
    {x b c : V}
    (hxb : (x, b) ∈ sourceInsideEdges T.interval.ambientInterval
      Rlimit.closedSet)
    (hxc : (x, c) ∈
      A.toPostClosureCompressorAssignment.actualPostClosureShortcutEdges) :
    False := by
  let A0 := A.toPostClosureCompressorAssignment
  rw [A0.mem_actualPostClosureShortcutEdges_iff] at hxc
  obtain ⟨s, hxc⟩ := hxc
  obtain ⟨q, hxq⟩ := A0.actualSegmentation_shortcut_tail_hasOutgoing_forward
    s hxc
  have houtside := A.assigned_forwardEdge_mem_outsideFamily s hxq
  have hbq : b = q :=
    (Alternating.IsWarp.familyEdges_biUnique
      T.interval.ambientInterval_linkage.isWarp).2 hxb.1 houtside.1
  exact houtside.2 ⟨hxb.2.1, hbq ▸ hxb.2.2⟩

/-- Equality-shaped form of the incoming cross-incidence fact.  In fact the
hypotheses are inconsistent: the literal interval edge would be both inside
and outside the closed carrier. -/
theorem shortcutHead_eq_of_intervalIncoming_closed
    (A : PostClosureMacroCompressorAssignment T)
    {x y a : V}
    (hxy : (x, y) ∈
      A.toPostClosureCompressorAssignment.actualPostClosureShortcutEdges)
    (hay : (a, y) ∈ familyEdges T.interval.ambientInterval)
    (haX : a ∈ Rlimit.closedSet) (hyX : y ∈ Rlimit.closedSet) :
    a = x := by
  exact False.elim (A.inside_shortcut_no_common_head
    ⟨hay, haX, hyX⟩ hxy)

/-- Equality-shaped form of the outgoing cross-incidence fact.  As above,
the stronger statement is that the hypotheses cannot simultaneously hold. -/
theorem shortcutTail_eq_of_intervalOutgoing_closed
    (A : PostClosureMacroCompressorAssignment T)
    {x y b : V}
    (hxy : (x, y) ∈
      A.toPostClosureCompressorAssignment.actualPostClosureShortcutEdges)
    (hxb : (x, b) ∈ familyEdges T.interval.ambientInterval)
    (hbX : b ∈ Rlimit.closedSet) (hxX : x ∈ Rlimit.closedSet) :
    b = y := by
  exact False.elim (A.inside_shortcut_no_common_tail
    ⟨hxb, hxX, hbX⟩ hxy)

/-- The source-faithful inside-plus-shortcut relation is biunique. -/
theorem actualPostClosureClosedEdges_biUnique
    (A : PostClosureMacroCompressorAssignment T) :
    Relator.BiUnique (fun x y =>
      (x, y) ∈
        A.toPostClosureCompressorAssignment.actualPostClosureClosedEdges) := by
  let A0 := A.toPostClosureCompressorAssignment
  have hinside : Relator.BiUnique (fun x y =>
      (x, y) ∈ sourceInsideEdges T.interval.ambientInterval
        Rlimit.closedSet) := sourceInsideEdges_biUnique
  have hshortcut := A.actualPostClosureShortcutEdges_biUnique
  constructor
  · intro x w y hxy hwy
    rcases hxy with hxy | hxy <;> rcases hwy with hwy | hwy
    · exact hinside.1 hxy hwy
    · exact False.elim (A.inside_shortcut_no_common_head hxy hwy)
    · exact False.elim (A.inside_shortcut_no_common_head hwy hxy)
    · exact hshortcut.1 hxy hwy
  · intro x y w hxy hxw
    rcases hxy with hxy | hxy <;> rcases hxw with hxw | hxw
    · exact hinside.2 hxy hxw
    · exact False.elim (A.inside_shortcut_no_common_tail hxy hxw)
    · exact False.elim (A.inside_shortcut_no_common_tail hxw hxy)
    · exact hshortcut.2 hxy hxw

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment.actualPostClosureClosedEdges_biUnique
