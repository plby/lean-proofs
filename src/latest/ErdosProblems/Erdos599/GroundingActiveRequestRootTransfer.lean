/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteAlternatingRoot
import ErdosProblems.Erdos599.GroundingErasedDecode

/-!
# Root transfer for one active erased request

This module specializes the finite alternating terminal-root lemma to the
literal simultaneous erased switch.  It makes the remaining grounding
obligation exact: one must root the erased route's initial vertex and the
ambient starts of all its backward links.  No global compatibility or warp
realization hypothesis is used.

The stationary selected-root prefix supplies only a path in the limiting
ladder.  Turning such a prefix into one of the reachability premises below
requires proving that its edges survive `CE` deletion and simultaneous
forward-conflict deletion.  For a backward link, its owner must additionally
be proved different from the stationary unused record.  Those facts are not
consequences of initial-source non-use; see
`GroundingSelectedRootPrefixObstruction`.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingErasedDecode

open DirectedPath Alternating PopularAuxiliary.Input
open PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- If every possible terminal anchor of one active erased request is rooted
in `A`, and this request's forward edges survive the final old-request tail
filter, then its request exit is rooted in `A` in the full simultaneous
switched relation.  The survival premise is essential: membership in the
active forward union alone no longer implies membership in the final
relation after endpoint pruning. -/
theorem activeRequest_rooted_of_anchor_reachability
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (c : ActiveControlRequest U S K)
    {A : Set V}
    (hforwardSurvives :
      (selectedErasedCompression U S K
          (chosenRequest c.1)).path.directionEdges .forward ⊆
        erasedSelectedSwitchedEdges U S K)
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K) a
        (selectedRequestTrace U S K (chosenRequest c.1)).initial)
    (hbackward : ∀ (l : Link Gamma.graph),
      l ∈ (selectedErasedCompression U S K
          (chosenRequest c.1)).path.links →
      l.direction = .backward →
      ∀ parent ∈ L.ladder.paths, l.path.IsSubpathOf parent →
        ∃ a ∈ A,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K)
            a l.path.start) :
    ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K) a
        (requestExit (chosenRequest c.1)) := by
  let r := chosenRequest c.1
  let T := selectedRequestTrace U S K r
  let C := selectedErasedCompression U S K r
  have hforward : C.path.directionEdges .forward ⊆
      erasedSelectedSwitchedEdges U S K := by
    simpa only [C, r] using hforwardSurvives
  have hback : BackwardLinksOn L.ladder.paths C.path :=
    selectedErasedCompression_backwardLinksOn U S K r
  cases hpath : C.path with
  | trivial v =>
      obtain ⟨a, ha, hareach⟩ := hinitial
      have hvInitial : v = T.initial := by
        simpa [C, T, hpath, AltPath.initial] using C.initial_eq
      have hvExit : v = requestExit r := by
        apply Option.some.inj
        simpa [C, hpath, AltPath.terminal?] using C.terminal_eq
      have hInitialExit : T.initial = requestExit r :=
        hvInitial.symm.trans hvExit
      refine ⟨a, ha, ?_⟩
      change Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K)
        a (requestExit r)
      rw [← hInitialExit]
      exact hareach
  | finite Q =>
      have hbackQ : BackwardLinksOn L.ladder.paths (.finite Q) := by
        simpa [hpath] using hback
      have hforwardQ :
          (AltPath.finite Q).directionEdges .forward ⊆
            erasedSelectedSwitchedEdges U S K := by
        simpa [hpath] using hforward
      have hInitial : Q.initial = T.initial := by
        simpa [C, T, hpath, AltPath.initial] using C.initial_eq
      have hTerminal : Q.terminal = requestExit r := by
        apply Option.some.inj
        simpa [C, hpath, AltPath.terminal?] using C.terminal_eq
      have hinitialQ : ∃ a ∈ A,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K)
            a Q.initial := by
        simpa [r, hInitial] using hinitial
      have hbackwardQ : ∀ (l : Link Gamma.graph),
          l ∈ (AltPath.finite Q).links → l.direction = .backward →
          ∀ parent ∈ L.ladder.paths, l.path.IsSubpathOf parent →
            ∃ a ∈ A,
              Relation.ReflTransGen
                (fun x y ↦
                  (x, y) ∈ erasedSelectedSwitchedEdges U S K)
                a l.path.start := by
        intro l hl hldir parent hparent hsub
        apply hbackward l
        · change l ∈ C.path.links
          rw [hpath]
          exact hl
        · exact hldir
        · exact hparent
        · exact hsub
      obtain ⟨a, ha, hareach⟩ := Q.exists_root_reaching_terminal
        hbackQ hforwardQ hinitialQ hbackwardQ
      exact ⟨a, ha, by simpa [r, hTerminal] using hareach⟩
  | infinite Q =>
      have hfalse : (none : Option V) = some (requestExit r) := by
        simpa [C, hpath, AltPath.terminal?] using C.terminal_eq
      cases hfalse

/-- Pointwise rooted transfer for the sound active-contact carrier.  Every
actual forward-route vertex is rooted once the route's forward edges
survive the final endpoint filter and the initial/backward-owner anchors are
rooted. -/
theorem activeRequest_forwardVertex_rooted_of_anchor_reachability
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (c : ActiveControlRequest U S K)
    {A : Set V}
    (hforwardSurvives :
      (selectedErasedCompression U S K
          (chosenRequest c.1)).path.directionEdges .forward ⊆
        erasedSelectedSwitchedEdges U S K)
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K) a
        (selectedRequestTrace U S K (chosenRequest c.1)).initial)
    (hbackward : ∀ (l : Link Gamma.graph),
      l ∈ (selectedErasedCompression U S K
          (chosenRequest c.1)).path.links →
      l.direction = .backward →
      ∀ parent ∈ L.ladder.paths, l.path.IsSubpathOf parent →
        ∃ a ∈ A,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K)
            a l.path.start)
    {x : V}
    (hx : x ∈ (selectedErasedCompression U S K
      (chosenRequest c.1)).path.directionVertices .forward) :
    ∃ a ∈ A,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdges U S K) a x := by
  let r := chosenRequest c.1
  let T := selectedRequestTrace U S K r
  let C := selectedErasedCompression U S K r
  have hback : BackwardLinksOn L.ladder.paths C.path :=
    selectedErasedCompression_backwardLinksOn U S K r
  cases hpath : C.path with
  | trivial v =>
      change x ∈ C.path.directionVertices .forward at hx
      rw [hpath] at hx
      simp [AltPath.directionVertices, AltPath.links] at hx
  | finite Q =>
      have hbackQ : BackwardLinksOn L.ladder.paths (.finite Q) := by
        simpa [hpath] using hback
      have hforwardQ :
          (AltPath.finite Q).directionEdges .forward ⊆
            erasedSelectedSwitchedEdges U S K := by
        change C.path.directionEdges .forward ⊆
          erasedSelectedSwitchedEdges U S K at hforwardSurvives
        rw [hpath] at hforwardSurvives
        exact hforwardSurvives
      have hInitial : Q.initial = T.initial := by
        simpa [C, T, hpath, AltPath.initial] using C.initial_eq
      have hinitialQ : ∃ a ∈ A,
          Relation.ReflTransGen
            (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdges U S K)
            a Q.initial := by
        simpa [r, hInitial] using hinitial
      have hbackwardQ : ∀ (l : Link Gamma.graph),
          l ∈ (AltPath.finite Q).links → l.direction = .backward →
          ∀ parent ∈ L.ladder.paths, l.path.IsSubpathOf parent →
            ∃ a ∈ A,
              Relation.ReflTransGen
                (fun u v ↦
                  (u, v) ∈ erasedSelectedSwitchedEdges U S K)
                a l.path.start := by
        intro l hl hldir parent hparent hsub
        apply hbackward l
        · change l ∈ C.path.links
          rw [hpath]
          exact hl
        · exact hldir
        · exact hparent
        · exact hsub
      apply Q.exists_root_reaching_forwardVertex
        hbackQ hforwardQ hinitialQ hbackwardQ
      change x ∈ C.path.directionVertices .forward at hx
      rw [hpath] at hx
      exact hx
  | infinite Q =>
      have hfalse : (none : Option V) = some (requestExit r) := by
        simpa [C, hpath, AltPath.terminal?] using C.terminal_eq
      cases hfalse

/-- Pointwise rooted transfer for the pruned active-contact carrier.  In
contrast to the full-forward statement above, no edge-survival premise is
needed: source-side retained prefixes are part of the final relation by
construction. -/
theorem activeRequest_retainedForwardVertex_rooted_of_anchor_reachability
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (c : ActiveControlRequest U S K)
    {A : Set V}
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K) a
        (selectedRequestTrace U S K (chosenRequest c.1)).initial)
    (hbackward : ∀ (l : Link Gamma.graph),
      l ∈ (selectedErasedCompression U S K
          (chosenRequest c.1)).path.links →
      l.direction = .backward →
      ∀ parent ∈ L.ladder.paths, l.path.IsSubpathOf parent →
        ∃ a ∈ A,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K)
            a l.path.start)
    {x : V}
    (hx : x ∈ retainedForwardVertices (L := L) S.cut
      (selectedErasedCompression U S K
        (chosenRequest c.1)).path) :
    ∃ a ∈ A,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdges U S K) a x := by
  let r := chosenRequest c.1
  let T := selectedRequestTrace U S K r
  let C := selectedErasedCompression U S K r
  have hback : BackwardLinksOn L.ladder.paths C.path :=
    selectedErasedCompression_backwardLinksOn U S K r
  cases hpath : C.path with
  | trivial v =>
      change x ∈ retainedForwardVertices (L := L) S.cut C.path at hx
      rw [hpath] at hx
      simp [retainedForwardVertices, AltPath.links] at hx
  | finite Q =>
      have hbackQ : BackwardLinksOn L.ladder.paths (.finite Q) := by
        simpa [hpath] using hback
      have hInitial : Q.initial = T.initial := by
        simpa [C, T, hpath, AltPath.initial] using C.initial_eq
      have hinitialQ : ∃ a ∈ A,
          Relation.ReflTransGen
            (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdges U S K)
            a Q.initial := by
        simpa [r, hInitial] using hinitial
      have hxQ : x ∈ retainedForwardVertices (L := L) S.cut
          (AltPath.finite Q) := by
        change x ∈ retainedForwardVertices (L := L) S.cut C.path at hx
        simpa [hpath] using hx
      obtain ⟨l, hl, hldir, hlx⟩ :=
        retainedForwardVertices_reachable S.cut (AltPath.finite Q) hxQ
      have hprefix : retainedForwardEdges (L := L) S.cut
          (AltPath.finite Q) ⊆ erasedSelectedSwitchedEdges U S K := by
        have hprefixC :=
          activeRetainedForwardEdges_subset_switched U S K c
        change retainedForwardEdges (L := L) S.cut C.path ⊆
          erasedSelectedSwitchedEdges U S K at hprefixC
        rw [hpath] at hprefixC
        exact hprefixC
      have hlx' : Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdges U S K)
          l.path.start x :=
        Relation.ReflTransGen.mono
          (r := fun u v ↦ (u, v) ∈
            retainedForwardEdges (L := L) S.cut (AltPath.finite Q))
          (p := fun u v ↦
            (u, v) ∈ erasedSelectedSwitchedEdges U S K)
          (fun _ _ h ↦ hprefix h) _ _ hlx
      rcases Q.initial_or_backwardOwner_eq_forwardStart
          hbackQ l hl hldir with hstart |
          ⟨b, hb, hbdir, parent, hparent, hbsub, hbstart⟩
      · obtain ⟨a, ha, haroot⟩ := hinitialQ
        exact ⟨a, ha, haroot.trans (hstart ▸ hlx')⟩
      · have hbC : b ∈ C.path.links := by
          rw [hpath]
          exact hb
        obtain ⟨a, ha, haroot⟩ :=
          hbackward b hbC hbdir parent hparent hbsub
        exact ⟨a, ha, haroot.trans (hbstart ▸ hlx')⟩
  | infinite Q =>
      have hfalse : (none : Option V) = some (requestExit r) := by
        simpa [C, hpath, AltPath.terminal?] using C.terminal_eq
      cases hfalse

/-- Boundary-parametric retained-contact transfer.  Every vertex of the
source-side prefix retained up to `T` is rooted in the `T`-stopped switch,
provided the route's initial anchor and every backward-link owner start are
rooted there. -/
theorem activeRequestAt_retainedForwardVertex_rooted_of_anchor_reachability
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V)
    (c : ActiveControlRequestAt U S K T)
    {A : Set V}
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T) a
        (selectedRequestTrace U S K (chosenRequest c.1)).initial)
    (hbackward : ∀ (l : Link Gamma.graph),
      l ∈ (selectedErasedCompression U S K
          (chosenRequest c.1)).path.links →
      l.direction = .backward →
      ∀ parent ∈ L.ladder.paths, l.path.IsSubpathOf parent →
        ∃ a ∈ A,
          Relation.ReflTransGen
            (fun x y ↦
              (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T)
            a l.path.start)
    {x : V}
    (hx : x ∈ retainedForwardVerticesAt T
      (selectedErasedCompression U S K
        (chosenRequest c.1)).path) :
    ∃ a ∈ A,
      Relation.ReflTransGen
        (fun u v ↦
          (u, v) ∈ erasedSelectedSwitchedEdgesAt U S K T) a x := by
  let r := chosenRequest c.1
  let Tr := selectedRequestTrace U S K r
  let C := selectedErasedCompression U S K r
  have hback : BackwardLinksOn L.ladder.paths C.path :=
    selectedErasedCompression_backwardLinksOn U S K r
  cases hpath : C.path with
  | trivial v =>
      change x ∈ retainedForwardVerticesAt T C.path at hx
      rw [hpath] at hx
      simp [retainedForwardVerticesAt, AltPath.links] at hx
  | finite Q =>
      have hbackQ : BackwardLinksOn L.ladder.paths (.finite Q) := by
        simpa [hpath] using hback
      have hInitial : Q.initial = Tr.initial := by
        simpa [C, Tr, hpath, AltPath.initial] using C.initial_eq
      have hinitialQ : ∃ a ∈ A,
          Relation.ReflTransGen
            (fun u v ↦
              (u, v) ∈ erasedSelectedSwitchedEdgesAt U S K T)
            a Q.initial := by
        simpa [r, hInitial] using hinitial
      have hxQ : x ∈ retainedForwardVerticesAt T
          (AltPath.finite Q) := by
        change x ∈ retainedForwardVerticesAt T C.path at hx
        simpa [hpath] using hx
      obtain ⟨l, hl, hldir, hlx⟩ :=
        retainedForwardVerticesAt_reachable T (AltPath.finite Q) hxQ
      have hprefix : retainedForwardEdgesAt T
          (AltPath.finite Q) ⊆ erasedSelectedSwitchedEdgesAt U S K T := by
        have hprefixC :=
          activeRetainedForwardEdgesAt_subset_switched U S K T c
        change retainedForwardEdgesAt T C.path ⊆
          erasedSelectedSwitchedEdgesAt U S K T at hprefixC
        rw [hpath] at hprefixC
        exact hprefixC
      have hlx' : Relation.ReflTransGen
          (fun u v ↦
            (u, v) ∈ erasedSelectedSwitchedEdgesAt U S K T)
          l.path.start x :=
        Relation.ReflTransGen.mono
          (r := fun u v ↦
            (u, v) ∈ retainedForwardEdgesAt T (AltPath.finite Q))
          (p := fun u v ↦
            (u, v) ∈ erasedSelectedSwitchedEdgesAt U S K T)
          (fun _ _ h ↦ hprefix h) _ _ hlx
      rcases Q.initial_or_backwardOwner_eq_forwardStart
          hbackQ l hl hldir with hstart |
          ⟨b, hb, hbdir, parent, hparent, hbsub, hbstart⟩
      · obtain ⟨a, ha, haroot⟩ := hinitialQ
        exact ⟨a, ha, haroot.trans (hstart ▸ hlx')⟩
      · have hbC : b ∈ C.path.links := by
          rw [hpath]
          exact hb
        obtain ⟨a, ha, haroot⟩ :=
          hbackward b hbC hbdir parent hparent hbsub
        exact ⟨a, ha, haroot.trans (hbstart ▸ hlx')⟩
  | infinite Q =>
      have hfalse : (none : Option V) = some (requestExit r) := by
        simpa [C, hpath, AltPath.terminal?] using C.terminal_eq
      cases hfalse

/-- In the pre-stopped switch every forward-route vertex is in the retained
carrier, so the boundary-parametric root transfer has no additional
survival premise. -/
theorem activeRequestAt_empty_forwardVertex_rooted_of_anchor_reachability
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (c : ActiveControlRequestAt U S K (∅ : Set V))
    {A : Set V}
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦
          (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K ∅) a
        (selectedRequestTrace U S K (chosenRequest c.1)).initial)
    (hbackward : ∀ (l : Link Gamma.graph),
      l ∈ (selectedErasedCompression U S K
          (chosenRequest c.1)).path.links →
      l.direction = .backward →
      ∀ parent ∈ L.ladder.paths, l.path.IsSubpathOf parent →
        ∃ a ∈ A,
          Relation.ReflTransGen
            (fun x y ↦
              (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K ∅)
            a l.path.start)
    {x : V}
    (hx : x ∈ (selectedErasedCompression U S K
      (chosenRequest c.1)).path.directionVertices .forward) :
    ∃ a ∈ A,
      Relation.ReflTransGen
        (fun u v ↦
          (u, v) ∈ erasedSelectedSwitchedEdgesAt U S K ∅) a x := by
  apply activeRequestAt_retainedForwardVertex_rooted_of_anchor_reachability
    U S K ∅ c hinitial hbackward
  simpa only [retainedForwardVerticesAt_empty] using hx

end GroundingErasedDecode
end Erdos599
