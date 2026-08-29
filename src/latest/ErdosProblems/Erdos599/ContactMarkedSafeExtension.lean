/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingDichotomy

/-!
# Contact-marked preservation in the safe-path recursion

Rule 2 in the source proof of Lemma 4.13 extends a finite safe alternating
path by a forward fragment ending at the first new reference contact and by
one backward reference interval.  The existing safe-stage theorem proves
source safeness, but the exact switch additionally needs forward-edge
disjointness and coverage of every forward vertex contact.  This module
proves that the same Rule-2 extension preserves those two certificates.

The theorem is a genuine constructor step; it does not assume the completed
path is switching-safe as a result premise.  Choosing the first contact and
the owner-convex backward interval remains the geometric producer's task.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- A safe bracket path together with the two occurrence-level conditions
needed by exact switching. -/
def IsBracketSwitchingSafe (U Y : Set Gamma.DPath)
    (Q : AltPath Gamma.graph) : Prop :=
  IsBracketSafe U Y Q ∧ ForwardLinksOff Y Q ∧
    ForwardVertexContactsCovered Y Q

theorem IsBracketSwitchingSafe.isSwitchingSafe
    {U Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (h : IsBracketSwitchingSafe U Y Q) : IsSwitchingSafe Y Q :=
  ⟨h.1.1, h.2.1, h.2.2⟩

theorem IsBracketSwitchingSafe.isBracketSafe
    {U Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (h : IsBracketSwitchingSafe U Y Q) : IsBracketSafe U Y Q :=
  h.1

/-- Appending the source proof's first-new-contact forward fragment and its
owner-convex backward interval preserves the full switching-ready invariant. -/
theorem isBracketSwitchingSafe_snoc_forward_backward
    {Z Y : Set Gamma.DPath} (hZ : Gamma.IsWarp Z)
    (hZfin : Gamma.HasFiniteCharacter Z)
    (T : FiniteTrace Gamma.graph) (F R : Link Gamma.graph)
    (hTFjoin : T.terminal = F.entry)
    (hTFalt : T.lastLink.direction ≠ F.direction)
    (hTFcompat : T.SnocCompatible F)
    (hFRjoin : (T.snoc F hTFjoin hTFalt hTFcompat).terminal = R.entry)
    (hFRalt : (T.snoc F hTFjoin hTFalt hTFcompat).lastLink.direction ≠
      R.direction)
    (hFRcompat : (T.snoc F hTFjoin hTFalt hTFcompat).SnocCompatible R)
    (hT : IsBracketSwitchingSafe Z Y (.finite T))
    (hFdir : F.direction = .forward)
    (hRdir : R.direction = .backward)
    (hFZ : IsFragmentOf F.path Z)
    (hRY : IsFragmentOf R.path Y)
    (hFoff : Disjoint F.path.edgeSet (familyEdges Y))
    (hcontacts : F.path.support ∩ Gamma.vertexSet Y ⊆
      (AltPath.finite T).directionVertices .backward ∪ R.path.support)
    (hIntervals : ∀ p ∈ Y,
      IsEdgeInterval
        ((AltPath.finite ((T.snoc F hTFjoin hTFalt hTFcompat).snoc R
          hFRjoin hFRalt hFRcompat)).directionEdges .backward ∩
            p.edgeSet) p) :
    IsBracketSwitchingSafe Z Y
      (.finite ((T.snoc F hTFjoin hTFalt hTFcompat).snoc R
        hFRjoin hFRalt hFRcompat)) := by
  let TF := T.snoc F hTFjoin hTFalt hTFcompat
  let TFR := TF.snoc R hFRjoin hFRalt hFRcompat
  have hlinksTF : TF.links = T.links ∪ {F} := by
    simpa [TF] using FiniteTrace.links_snoc T F hTFjoin hTFalt hTFcompat
  have hlinksTFR : TFR.links = TF.links ∪ {R} := by
    simpa [TFR] using FiniteTrace.links_snoc TF R hFRjoin hFRalt hFRcompat
  have hsafe : IsBracketSafe Z Y (.finite TFR) := by
    exact isBracketSafe_snoc_forward_backward hZ hZfin T F R
      hTFjoin hTFalt hTFcompat hFRjoin hFRalt hFRcompat hT.1
      hFdir hRdir hFZ hRY hFoff hcontacts hIntervals
  have hoff : ForwardLinksOff Y (.finite TFR) := by
    intro l hl hldir
    change l ∈ TFR.links at hl
    rw [hlinksTFR, hlinksTF] at hl
    rcases hl with (hlT | hlF) | hlR
    · exact hT.2.1 l hlT hldir
    · have hlF' : l = F := by simpa using hlF
      subst l
      exact hFoff
    · have hlR' : l = R := by simpa using hlR
      subst l
      rw [hRdir] at hldir
      contradiction
  have hcovered : ForwardVertexContactsCovered Y (.finite TFR) := by
    intro x hx
    rcases hx with ⟨hxforward, hxY⟩
    simp only [AltPath.directionVertices, Set.mem_iUnion] at hxforward ⊢
    rcases hxforward with ⟨l, hl, hldir, hxl⟩
    change l ∈ TFR.links at hl
    rw [hlinksTFR, hlinksTF] at hl
    rcases hl with (hlT | hlF) | hlR
    · have hxold : x ∈ (AltPath.finite T).directionVertices .backward :=
        hT.2.2 ⟨by
          simp only [AltPath.directionVertices, Set.mem_iUnion]
          exact ⟨l, hlT, hldir, hxl⟩, hxY⟩
      simp only [AltPath.directionVertices, Set.mem_iUnion] at hxold
      rcases hxold with ⟨b, hbT, hbdir, hxb⟩
      exact ⟨b, by
        change b ∈ TFR.links
        rw [hlinksTFR, hlinksTF]
        exact Or.inl (Or.inl hbT), hbdir, hxb⟩
    · have hlF' : l = F := by simpa using hlF
      subst l
      rcases hcontacts ⟨hxl, hxY⟩ with hxold | hxR
      · simp only [AltPath.directionVertices, Set.mem_iUnion] at hxold
        rcases hxold with ⟨b, hbT, hbdir, hxb⟩
        exact ⟨b, by
          change b ∈ TFR.links
          rw [hlinksTFR, hlinksTF]
          exact Or.inl (Or.inl hbT), hbdir, hxb⟩
      · exact ⟨R, by
          change R ∈ TFR.links
          rw [hlinksTFR]
          exact Or.inr (Set.mem_singleton R), hRdir, hxR⟩
    · have hlR' : l = R := by simpa using hlR
      subst l
      rw [hRdir] at hldir
      contradiction
  exact ⟨hsafe, hoff, hcovered⟩

end Alternating
end Erdos599
