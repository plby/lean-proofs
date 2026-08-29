/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeHammockOmegaClosure
import ErdosProblems.Erdos599.FiniteOwnerStrongRay
import ErdosProblems.Erdos599.OutsideFracturedOccurrenceHammock

/-!
# Native shortcut edges and finite-owner trapping

An actual shortcut retains a safe occurrence over the original finite row.
Simultaneous native hammock closure makes each such shortcut imaginary and
each non-strong shortcut stay on one original owner. Consequently any ray
made from inside-row edges and these shortcuts has infinitely many strong
edges. No disjoint path family or distinct-terminal assignment is assumed to
exist here. The legacy alternating-path graph is not changed.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {W Y : Set Gamma.DPath} {X : Set V} {rho : Cardinal.{u}} {s t : V}

/-- A literal finite outside occurrence with its original row provenance. -/
structure OutsideRoute (W Y : Set Gamma.DPath) (X : Set V) (s t : V) where
  occurrence : CurrentSafeOccurrence W Y s
  terminal_eq : occurrence.terminal? = some t
  distinct : s ≠ t
  source_mem : s ∈ X
  terminal_mem : t ∈ X
  source_off : s ∉ Gamma.vertexSet Y
  terminal_off : t ∉ Gamma.vertexSet Y
  cut_intersection : occurrence.vertexSet ∩ X ⊆ {s, t}
  outside : ¬occurrence.vertexSet ⊆ X

def IsShortcut (W Y : Set Gamma.DPath) (X : Set V) (s t : V) : Prop :=
  Nonempty (OutsideRoute W Y X s t)

/-- Native imaginary edges use genuine large occurrence hammocks. -/
def IsImaginary (Y : Set Gamma.DPath) (rho : Cardinal.{u}) (s t : V) : Prop :=
  ColouredSafeHammock.HasCard Y s (some t) (fun _ ↦ True) (succ rho)

/-- Strong native imaginary edges have relationally nondegenerate routes. -/
def IsStrong (Y : Set Gamma.DPath) (rho : Cardinal.{u}) (s t : V) : Prop :=
  ColouredSafeHammock.HasCard Y s (some t)
    (fun A ↦ ¬A.HasFiniteSwitchedPathTo t) (succ rho)

theorem IsStrong.isImaginary (h : IsStrong Y rho s t) :
    IsImaginary Y rho s t := by
  obtain ⟨H, hH, hcard⟩ := h
  refine ⟨H, ⟨?_, hH.2⟩, hcard⟩
  intro A hA
  obtain ⟨hvalid, hend, hs, ht, _⟩ := hH.1 hA
  exact ⟨hvalid, hend, hs, ht, trivial⟩

/-- The graph made from the literal inside row and certified outside chords. -/
def graph (W Y : Set Gamma.DPath) (X : Set V) : Digraph V where
  Adj s t := ((s, t) ∈ familyEdges W ∧ s ∈ X ∧ t ∈ X) ∨ IsShortcut W Y X s t

/-- No conversion to a link-compatible alternating path is used. -/
theorem OutsideRoute.isImaginary (R : OutsideRoute W Y X s t)
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (hclosed : ColouredSafeHammockOmegaClosure.OmegaClosed Y rho X) :
    IsImaginary Y rho s t := by
  apply ColouredSafeHammock.hasCard_of_external
    (hclosed.2 s R.source_mem t R.terminal_mem).1
    (A := toAmbient R.occurrence) ?_ ?_ ?_
  · refine ⟨toAmbient_valid R.occurrence hW hfinite,
      by simpa using R.terminal_eq, R.source_off, ?_, trivial⟩
    intro v hv
    exact Option.some.inj hv ▸ R.terminal_off
  · simpa using R.cut_intersection
  · simpa using R.outside

theorem OutsideRoute.common_owner_of_not_strong (R : OutsideRoute W Y X s t)
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y)
    (hclosed : ColouredSafeHammockOmegaClosure.OmegaClosed Y rho X)
    (hnot : ¬IsStrong Y rho s t) :
    ∃ p ∈ W, s ∈ p.support ∧ t ∈ p.support :=
  ColouredSafeHammock.endpoints_same_forward_owner_of_not_large_nondegenerate
    R.occurrence hW hfinite hY R.terminal_eq R.distinct R.source_off R.terminal_off
    (hclosed.2 s R.source_mem t R.terminal_mem).2 R.cut_intersection R.outside hnot

theorem adj_original_or_imaginary
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (hclosed : ColouredSafeHammockOmegaClosure.OmegaClosed Y rho X)
    (h : (graph W Y X).Adj s t) :
    Gamma.graph.Adj s t ∨ IsImaginary Y rho s t := by
  rcases h with hrow | hshortcut
  · left
    simp only [familyEdges, Set.mem_iUnion] at hrow
    obtain ⟨⟨p, _hp, he⟩, _⟩ := hrow
    exact p.edgeSet_subset_adj he
  · change Nonempty (OutsideRoute W Y X s t) at hshortcut
    obtain ⟨R⟩ := hshortcut
    exact Or.inr (R.isImaginary hW hfinite hclosed)

theorem adj_common_owner_of_not_strong
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y)
    (hclosed : ColouredSafeHammockOmegaClosure.OmegaClosed Y rho X)
    (h : (graph W Y X).Adj s t) (hnot : ¬IsStrong Y rho s t) :
    ∃ p ∈ W, s ∈ p.support ∧ t ∈ p.support := by
  rcases h with hrow | hshortcut
  · simp only [familyEdges, Set.mem_iUnion] at hrow
    obtain ⟨⟨p, hp, he⟩, _⟩ := hrow
    exact ⟨p, hp, p.edgeSet_subset_support_prod he⟩
  · change Nonempty (OutsideRoute W Y X s t) at hshortcut
    obtain ⟨R⟩ := hshortcut
    exact R.common_owner_of_not_strong hW hfinite hY hclosed hnot

/-- A weak ray tail would lie on one finite original row member. This
conclusion is independent of the still-needed simultaneous assignment. -/
theorem strongIndices_infinite
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y)
    (hclosed : ColouredSafeHammockOmegaClosure.OmegaClosed Y rho X)
    (r : Ray (graph W Y X)) :
    {n : ℕ | IsStrong Y rho (r n) (r (n + 1))}.Infinite := by
  apply LinkageBlueprint.edgePredicateIndices_infinite_of_complement_common_finite_owner
    (IsStrong Y rho) hW hfinite
    (E := {e | (graph W Y X).Adj e.1 e.2})
    (fun he hnot ↦ adj_common_owner_of_not_strong hW hfinite hY hclosed he hnot) r
  intro e he
  obtain ⟨n, rfl⟩ := he
  exact r.adj_succ n

/-- A marked shortcut retains a genuine filter, for example capture inside
a stage roof, in addition to native nondegeneracy. -/
def IsMarked (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (extra : ∀ s, Occurrence Y s → Prop) (s t : V) : Prop :=
  ColouredSafeHammock.HasCard Y s (some t)
    (fun A ↦ extra s A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ rho)

theorem IsMarked.isStrong {extra : ∀ s, Occurrence Y s → Prop}
    (h : IsMarked Y rho extra s t) : IsStrong Y rho s t := by
  obtain ⟨H, hH, hcard⟩ := h
  refine ⟨H, ⟨?_, hH.2⟩, hcard⟩
  intro A hA
  obtain ⟨hvalid, hend, hs, ht, _hextra, hnondeg⟩ := hH.1 hA
  exact ⟨hvalid, hend, hs, ht, hnondeg⟩

theorem OutsideRoute.common_owner_of_not_marked (R : OutsideRoute W Y X s t)
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) {extra : ∀ s, Occurrence Y s → Prop}
    (hclosed : ColouredSafeHammockOmegaClosure.FilteredOmegaClosed Y extra rho X)
    (hextra : extra s (toAmbient R.occurrence))
    (hnot : ¬IsMarked Y rho extra s t) :
    ∃ p ∈ W, s ∈ p.support ∧ t ∈ p.support :=
  ColouredSafeHammock.endpoints_same_forward_owner_of_not_large_filtered
    R.occurrence hW hfinite hY R.terminal_eq R.distinct R.source_off R.terminal_off
    (hclosed.2 s R.source_mem t R.terminal_mem).2 hextra
    R.cut_intersection R.outside hnot

/-- The filtered strong-ray argument applies to any actual edge relation
whose non-row edges retain certified filtered outside occurrences. -/
theorem markedIndices_infinite_of_certificates
    {D : Digraph V} {E : Set (V × V)}
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) {extra : ∀ s, Occurrence Y s → Prop}
    (hclosed : ColouredSafeHammockOmegaClosure.FilteredOmegaClosed Y extra rho X)
    (hcert : ∀ {x y}, (x, y) ∈ E → (x, y) ∈ familyEdges W ∨
      ∃ R : OutsideRoute W Y X x y, extra x (toAmbient R.occurrence))
    (r : Ray D) (hr : r.edgeSet ⊆ E) :
    {n : ℕ | IsMarked Y rho extra (r n) (r (n + 1))}.Infinite := by
  apply LinkageBlueprint.edgePredicateIndices_infinite_of_complement_common_finite_owner
    (IsMarked Y rho extra) hW hfinite (E := E) ?_ r hr
  intro x y he hnot
  rcases hcert he with hrow | ⟨R, hextra⟩
  · simp only [familyEdges, Set.mem_iUnion] at hrow
    obtain ⟨p, hp, hep⟩ := hrow
    exact ⟨p, hp, p.edgeSet_subset_support_prod hep⟩
  · exact R.common_owner_of_not_marked hW hfinite hY hclosed hextra hnot

/-- Retag an actual outside-fractured occurrence by its original uncut row.
The two cut endpoint memberships remain explicit geometric requirements. -/
def OutsideRoute.of_fractured
    (F : LinkageBlueprint.OutsideFracturedWarp W X)
    (A : CurrentSafeOccurrence F.holes.edgeWarp Y s)
    (hend : A.terminal? = some t) (hne : s ≠ t) (hsX : s ∈ X) (htX : t ∈ X)
    (hs : s ∉ Gamma.vertexSet Y) (ht : t ∉ Gamma.vertexSet Y)
    (hcap : A.vertexSet ∩ X ⊆ {s, t}) (hout : ¬A.vertexSet ⊆ X) :
    OutsideRoute W Y X s t where
  occurrence := A.retypeForward (F.occurrence_forwardEdges_subset_original A)
  terminal_eq := by simpa using hend
  distinct := hne
  source_mem := hsX
  terminal_mem := htX
  source_off := hs
  terminal_off := ht
  cut_intersection := by simpa using hcap
  outside := by simpa using hout

#print axioms OutsideRoute.common_owner_of_not_strong
#print axioms strongIndices_infinite
#print axioms markedIndices_infinite_of_certificates

end Erdos599.Blueprint.ColouredSafeShortcutGraph
