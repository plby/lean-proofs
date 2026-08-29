/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Blueprint
import ErdosProblems.Erdos599.SafeSwitching
import ErdosProblems.Erdos599.WaveLimits

/-!
# Splicing a real path onto a linkage blueprint

This file implements the operation denoted by `\diamond` in the proof of
Assertion 9.30.  One finite member of a cut blueprint is replaced by its
concatenation with a real path.  The freshness hypothesis says precisely that
the new path meets the old blueprint only at the splicing vertex.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint

open DirectedPath

universe u

variable {V : Type u}

namespace LinkageBlueprint

variable {Γ : DWeb V} {Y : Set Γ.DPath} {κ : Cardinal.{u}}

/-- Regard a path of the original graph as a path of the imaginary graph. -/
def liftOriginal (P : FinitePath Γ.graph) :
    FinitePath (imaginaryGraph Γ Y κ) :=
  P.lift (fun h ↦ original_adj_imaginaryGraph h)

@[simp] theorem liftOriginal_support (P : FinitePath Γ.graph) :
    (liftOriginal (Y := Y) (κ := κ) P).support = P.support :=
  FinitePath.support_lift _ P

@[simp] theorem liftOriginal_start (P : FinitePath Γ.graph) :
    (liftOriginal (Y := Y) (κ := κ) P).start = P.start :=
  rfl

@[simp] theorem liftOriginal_finish (P : FinitePath Γ.graph) :
    (liftOriginal (Y := Y) (κ := κ) P).finish = P.finish :=
  rfl

@[simp] theorem walk_edgeSet_lift {D E : Digraph V}
    (hDE : ∀ {x y}, D.Adj x y → E.Adj x y) :
    ∀ {a b : V} (p : Walk D a b), (p.lift hDE).edgeSet = p.edgeSet
  | _, _, .nil => rfl
  | _, _, .cons h p => by simp [Walk.lift, Walk.edgeSet_cons, walk_edgeSet_lift hDE p]

@[simp] theorem liftOriginal_edgeSet (P : FinitePath Γ.graph) :
    (liftOriginal (Y := Y) (κ := κ) P).edgeSet = P.edgeSet :=
  walk_edgeSet_lift _ P.walk

theorem FinitePath.edgeSet_appendFinite
    {D : Digraph V} (p q : FinitePath D)
    (hstart : q.start = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish}) :
    (p.appendFinite q hstart hinter).edgeSet = p.edgeSet ∪ q.edgeSet := by
  rcases q with ⟨qstart, qfinish, qwalk, hq⟩
  dsimp only at hstart
  subst qstart
  have hdisjoint : p.walk.support.Disjoint qwalk.support.tail := by
    apply List.disjoint_left.2
    intro x hxp hxq
    have hxqSupport : x ∈ qwalk.support :=
      List.mem_of_mem_tail hxq
    have hxeq : x = p.finish := Set.mem_singleton_iff.mp
      (hinter ⟨hxp, hxqSupport⟩)
    have hhead : qwalk.support.head qwalk.support_ne_nil = p.finish :=
      qwalk.head_support
    exact hq.rel_head_tail hxq (by simpa only [hhead, hxeq])
  have happend :
      p.appendFinite
          (⟨p.finish, qfinish, qwalk, hq⟩ : FinitePath D) rfl hinter =
        p.appendWalkOfDisjoint qwalk hq hdisjoint := by
    rfl
  rw [happend]
  exact
    Erdos599.Alternating.RelationDecomposition.ForwardOrientation.Walk.edgeSet_append
      p.walk qwalk

/-- The finite path produced by one splice. -/
def diamondPath (p : FinitePath (imaginaryGraph Γ Y κ))
    (P : FinitePath Γ.graph)
    (hstart : P.start = p.finish)
    (hfresh : p.support ∩ P.support ⊆ {p.finish}) :
    FinitePath (imaginaryGraph Γ Y κ) :=
  let P' := liftOriginal (Y := Y) (κ := κ) P
  p.appendFinite P' (by
    calc
      P'.start = P.start := liftOriginal_start P
      _ = p.finish := hstart) (by
    simpa only [P', liftOriginal_support] using hfresh)

@[simp] theorem diamondPath_start
    (p : FinitePath (imaginaryGraph Γ Y κ)) (P : FinitePath Γ.graph)
    (hstart : P.start = p.finish)
    (hfresh : p.support ∩ P.support ⊆ {p.finish}) :
    (diamondPath p P hstart hfresh).start = p.start :=
  by
    unfold diamondPath
    apply FinitePath.appendFinite_start

@[simp] theorem diamondPath_finish
    (p : FinitePath (imaginaryGraph Γ Y κ)) (P : FinitePath Γ.graph)
    (hstart : P.start = p.finish)
    (hfresh : p.support ∩ P.support ⊆ {p.finish}) :
    (diamondPath p P hstart hfresh).finish = P.finish :=
  by
    unfold diamondPath
    rw [FinitePath.appendFinite_finish, liftOriginal_finish]

@[simp] theorem diamondPath_support
    (p : FinitePath (imaginaryGraph Γ Y κ)) (P : FinitePath Γ.graph)
    (hstart : P.start = p.finish)
    (hfresh : p.support ∩ P.support ⊆ {p.finish}) :
    (diamondPath p P hstart hfresh).support = p.support ∪ P.support := by
  unfold diamondPath
  rw [FinitePath.support_appendFinite_eq_union, liftOriginal_support]

@[simp] theorem diamondPath_edgeSet
    (p : FinitePath (imaginaryGraph Γ Y κ)) (P : FinitePath Γ.graph)
    (hstart : P.start = p.finish)
    (hfresh : p.support ∩ P.support ⊆ {p.finish}) :
    (diamondPath p P hstart hfresh).edgeSet = p.edgeSet ∪ P.edgeSet := by
  let P' := liftOriginal (Y := Y) (κ := κ) P
  have hstart' : P'.start = p.finish := by
    calc
      P'.start = P.start := liftOriginal_start P
      _ = p.finish := hstart
  have hfresh' : p.support ∩ P'.support ⊆ {p.finish} := by
    simpa only [P', liftOriginal_support] using hfresh
  change (p.appendFinite P' hstart' hfresh').edgeSet = _
  rw [FinitePath.edgeSet_appendFinite]
  change p.edgeSet ∪ (liftOriginal (Y := Y) (κ := κ) P).edgeSet = _
  rw [liftOriginal_edgeSet]

/-- Replace `p` by its splice with `P`. -/
def diamondPaths (cut : LinkageBlueprint Γ Y κ)
    (p : FinitePath (imaginaryGraph Γ Y κ))
    (P : FinitePath Γ.graph)
    (hstart : P.start = p.finish)
    (hfresh : p.support ∩ P.support ⊆ {p.finish}) :
    Set (Path (imaginaryGraph Γ Y κ)) :=
  (cut.paths \ {(.inl p : Path (imaginaryGraph Γ Y κ))}) ∪
    {(.inl (diamondPath p P hstart hfresh) :
      Path (imaginaryGraph Γ Y κ))}

theorem diamondPaths_isWarp
    (cut : LinkageBlueprint Γ Y κ)
    (p : FinitePath (imaginaryGraph Γ Y κ)) (hp : (.inl p : Path _) ∈ cut.paths)
    (P : FinitePath Γ.graph) (hstart : P.start = p.finish)
    (hinter : p.support ∩ P.support ⊆ {p.finish})
    (hfreshCut : cut.vertexSet ∩ P.support ⊆ {p.finish}) :
    (imaginaryWeb Γ Y κ).IsWarp
      (diamondPaths cut p P hstart hinter) := by
  change (diamondPaths cut p P hstart hinter).PairwiseDisjoint Path.support
  intro r hr s hs hrs
  simp only [diamondPaths, Set.mem_union, Set.mem_diff,
    Set.mem_singleton_iff] at hr hs
  rcases hr with hr | rfl <;> rcases hs with hs | rfl
  · exact cut.isWarp hr.1 hs.1 hrs
  · change Disjoint r.support (diamondPath p P hstart hinter).support
    rw [diamondPath_support]
    rw [Set.disjoint_union_right]
    constructor
    · exact cut.isWarp hr.1 hp (fun h ↦ hr.2 (by simpa [h]))
    · apply Set.disjoint_left.2
      intro x hxr hxP
      have hxin : x ∈ cut.vertexSet := ⟨r, hr.1, hxr⟩
      have hxeq : x = p.finish := Set.mem_singleton_iff.mp
        (hfreshCut ⟨hxin, hxP⟩)
      have hxPp : x ∈ p.support := hxeq ▸ p.finish_mem_support
      exact Set.disjoint_left.1
        (cut.isWarp hr.1 hp (fun h ↦ hr.2 (by simpa [h]))) hxr hxPp
  · change Disjoint (diamondPath p P hstart hinter).support s.support
    rw [diamondPath_support]
    rw [Set.disjoint_union_left]
    constructor
    · exact cut.isWarp hp hs.1 (fun h ↦ hs.2 (by simpa [h.symm]))
    · apply Set.disjoint_left.2
      intro x hxP hxs
      have hxin : x ∈ cut.vertexSet := ⟨s, hs.1, hxs⟩
      have hxeq : x = p.finish := Set.mem_singleton_iff.mp
        (hfreshCut ⟨hxin, hxP⟩)
      have hxPp : x ∈ p.support := hxeq ▸ p.finish_mem_support
      exact Set.disjoint_left.1
        (cut.isWarp hp hs.1 (fun h ↦ hs.2 (by simpa [h]))) hxPp hxs
  · exact (hrs rfl).elim

/-- The concrete `cut \diamond P` blueprint. -/
def diamond (cut : LinkageBlueprint Γ Y κ)
    (p : FinitePath (imaginaryGraph Γ Y κ)) (hp : (.inl p : Path _) ∈ cut.paths)
    (P : FinitePath Γ.graph) (hstart : P.start = p.finish)
    (hfreshCut : cut.vertexSet ∩ P.support ⊆ {p.finish}) :
    LinkageBlueprint Γ Y κ where
  paths := diamondPaths cut p P hstart
    (fun x hx ↦ hfreshCut ⟨⟨.inl p, hp, hx.1⟩, hx.2⟩)
  isWarp := diamondPaths_isWarp cut p hp P hstart
    (fun x hx ↦ hfreshCut ⟨⟨.inl p, hp, hx.1⟩, hx.2⟩) hfreshCut

end LinkageBlueprint
end Blueprint
end Erdos599
