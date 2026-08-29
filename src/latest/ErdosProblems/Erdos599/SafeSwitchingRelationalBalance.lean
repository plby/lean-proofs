/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitchingRelationalRealization
import ErdosProblems.Erdos599.ReducingBoundary

/-!
# Balanced interval switches and exact augmentation of the boundary

The local incidence certificates below construct biuniqueness; it is not
assumed of the output. Together with interval convexity and the exact edge
balance delta, they construct a finite-character warp with one new initial
and one new terminal. They deliberately do not assert that these two
vertices belong to the same output path: that is the separate degeneracy
question. No existence of an actual balanced safe route is asserted here.
-/

namespace Erdos599.Alternating.SwitchingCore.RelationalInterval

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Removing every reference incidence which conflicts with an inserted
incidence is sufficient for local biuniqueness of the mixed relation. -/
theorem biUnique_of_incident_reference_edges_removed
    {W Y : Set Gamma.DPath} {R F : Set (V × V)}
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hF : F ⊆ familyEdges W)
    (hin : ∀ {a b x : V}, (a, x) ∈ F →
      (b, x) ∈ familyEdges Y → (b, x) ∈ R)
    (hout : ∀ {x a b : V}, (x, a) ∈ F →
      (x, b) ∈ familyEdges Y → (x, b) ∈ R) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ (familyEdges Y \ R) ∪ F) := by
  constructor
  · intro a b x ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact (IsWarp.familyEdges_biUnique hY).1 ha.1 hb.1
    · exact (ha.2 (hin hb ha.1)).elim
    · exact (hb.2 (hin ha hb.1)).elim
    · exact (IsWarp.familyEdges_biUnique hW).1 (hF ha) (hF hb)
  · intro x a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact (IsWarp.familyEdges_biUnique hY).2 ha.1 hb.1
    · exact (ha.2 (hout hb ha.1)).elim
    · exact (hb.2 (hout ha hb.1)).elim
    · exact (IsWarp.familyEdges_biUnique hW).2 (hF ha) (hF hb)

/-- The exact balance of a locally compatible removal/insertion. -/
theorem edgeBalance_eq_of_incidence
    {W Y : Set Gamma.DPath} {R F : Set (V × V)}
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hR : R ⊆ familyEdges Y) (hF : F ⊆ familyEdges W)
    (hin : ∀ {a b x : V}, (a, x) ∈ F →
      (b, x) ∈ familyEdges Y → (b, x) ∈ R)
    (hout : ∀ {x a b : V}, (x, a) ∈ F →
      (x, b) ∈ familyEdges Y → (x, b) ∈ R) (x : V) :
    edgeBalance ((familyEdges Y \ R) ∪ F) x =
      edgeBalance (familyEdges Y) x + edgeBalance F x - edgeBalance R x := by
  have hbi := biUnique_of_incident_reference_edges_removed hW hY hF hin hout
  exact edgeBalance_sdiff_union_eq_add_sub hR (IsWarp.familyEdges_biUnique hY).2
    (IsWarp.familyEdges_biUnique hY).1 hbi.2 hbi.1
    (retained_disjoint_inserted_of_incidence hin) x

/-- Backwards-compatible interface; direct incidence removal is enough,
so disjointness from the entire old reference is no longer needed. -/
theorem edgeBalance_eq_of_incident_reference_edges_removed
    {W Y : Set Gamma.DPath} {R F : Set (V × V)}
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hR : R ⊆ familyEdges Y) (hF : F ⊆ familyEdges W)
    (_hdisj : Disjoint F (familyEdges Y))
    (hin : ∀ {a b x : V}, (a, x) ∈ F →
      (b, x) ∈ familyEdges Y → (b, x) ∈ R)
    (hout : ∀ {x a b : V}, (x, a) ∈ F →
      (x, b) ∈ familyEdges Y → (x, b) ∈ R) (x : V) :
    edgeBalance ((familyEdges Y \ R) ∪ F) x =
      edgeBalance (familyEdges Y) x + edgeBalance F x - edgeBalance R x :=
  edgeBalance_eq_of_incidence hW hY hR hF hin hout x

private theorem edgeBalance_zero_of_not_mem_vertexSet
    {Y : Set Gamma.DPath} {x : V} (hx : x ∉ Gamma.vertexSet Y) :
    edgeBalance (familyEdges Y) x = 0 := by
  have hout : ¬HasOutgoing (familyEdges Y) x := by
    rintro ⟨y, hy⟩
    exact hx (familyEdges_subset_vertexSet_prod Y hy).1
  have hin : ¬HasIncoming (familyEdges Y) x := by
    rintro ⟨y, hy⟩
    exact hx (familyEdges_subset_vertexSet_prod Y hy).2
  simp [edgeBalance, propInt, hout, hin]

/-- A finite-character realization with the augmentation balance has the
exact old initial and terminal sets with the exposed endpoints adjoined.
The output pairing is intentionally unrestricted. -/
theorem boundary_eq_of_augmenting_balance
    {Y U : Set Gamma.DPath} (hY : Gamma.IsWarp Y) (hU : Gamma.IsWarp U)
    (hYfin : Gamma.HasFiniteCharacter Y) (hUfin : Gamma.HasFiniteCharacter U)
    (hiso : isolatedVertices U = isolatedVertices Y)
    {s t : V} (hst : s ≠ t)
    (hs : s ∉ Gamma.vertexSet Y) (ht : t ∉ Gamma.vertexSet Y)
    (hbal : ∀ x, edgeBalance (familyEdges U) x =
      edgeBalance (familyEdges Y) x + propInt (x = s) - propInt (x = t)) :
    Gamma.initialSet U = Gamma.initialSet Y ∪ {s} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier Y ∪ {t} := by
  have hsbal := edgeBalance_zero_of_not_mem_vertexSet hs
  have htbal := edgeBalance_zero_of_not_mem_vertexSet ht
  have hsiso : s ∉ isolatedVertices Y :=
    fun h ↦ hs (isolatedVertices_subset_vertexSet Y h)
  have htiso : t ∉ isolatedVertices Y :=
    fun h ↦ ht (isolatedVertices_subset_vertexSet Y h)
  constructor
  · ext x
    rw [mem_initialSet_iff_isolated_or_edgeBalance_eq_one hU hUfin,
      Set.mem_union, Set.mem_singleton_iff,
      mem_initialSet_iff_isolated_or_edgeBalance_eq_one hY hYfin, hiso, hbal]
    by_cases hxs : x = s
    · subst x
      simp [hsbal, propInt, hst]
    by_cases hxt : x = t
    · subst x
      simp [htbal, htiso, propInt, hxs]
    simp [propInt, hxs, hxt]
  · ext x
    rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one hU hUfin,
      Set.mem_union, Set.mem_singleton_iff,
      mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one hY hYfin,
      hiso, hbal]
    by_cases hxs : x = s
    · subst x
      simp [hsbal, hsiso, propInt, hst]
    by_cases hxt : x = t
    · subst x
      simp [htbal, propInt, hxs]
    simp [propInt, hxs, hxt]

/-- An interval-convex balanced switch constructs an augmenting warp, not
just a relation. The endpoints may lie on different output members. -/
theorem exists_finiteWarp_augmenting_of_incidence_balanced_intervalSwitch
    {W Y : Set Gamma.DPath} {R F : Set (V × V)}
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hR : R ⊆ familyEdges Y) (hF : F ⊆ familyEdges W)
    (hin : ∀ {a b x : V}, (a, x) ∈ F →
      (b, x) ∈ familyEdges Y → (b, x) ∈ R)
    (hout : ∀ {x a b : V}, (x, a) ∈ F →
      (x, b) ∈ familyEdges Y → (x, b) ∈ R)
    (hinterval : ∀ p ∈ Y, IsEdgeInterval (R ∩ p.edgeSet) p)
    (hpure : ∀ {x y : V}, (x, y) ∈ F →
      y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y)
    {s t : V} (hst : s ≠ t)
    (hs : s ∉ Gamma.vertexSet Y) (ht : t ∉ Gamma.vertexSet Y)
    (hdelta : ∀ x, edgeBalance F x - edgeBalance R x =
      propInt (x = s) - propInt (x = t)) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = (familyEdges Y \ R) ∪ F ∧
      isolatedVertices U = isolatedVertices Y ∧
      Gamma.initialSet U = Gamma.initialSet Y ∪ {s} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier Y ∪ {t} := by
  have hbi := biUnique_of_incident_reference_edges_removed hW hY hF hin hout
  have hiso : ∀ x ∈ isolatedVertices Y, ∀ y,
      (x, y) ∉ (familyEdges Y \ R) ∪ F ∧
      (y, x) ∉ (familyEdges Y \ R) ∪ F := by
    intro x hx y
    have hxInitial : x ∈ Gamma.initialSet Y := ⟨Gamma.trivialPath x, hx, by simp⟩
    have hxTerminal : x ∈ Gamma.terminalFrontier Y :=
      ⟨Gamma.trivialPath x, hx, by simp⟩
    constructor
    · rintro (he | he)
      · exact not_isolated_of_hasOutgoing hY ⟨y, he.1⟩ hx
      · exact (hpure he).2 hxTerminal
    · rintro (he | he)
      · exact not_isolated_of_hasIncoming hY ⟨y, he.1⟩ hx
      · exact (hpure he).1 hxInitial
  obtain ⟨U, hU, hUE, hUI, hUfin⟩ :=
    exists_finiteWarp_realizing_incidence_intervalSwitch hW hY hWfin hYfin
      hF hin hout rfl hbi hinterval hpure (isolatedVertices Y) hiso
  have hbalance : ∀ x, edgeBalance (familyEdges U) x =
      edgeBalance (familyEdges Y) x + propInt (x = s) - propInt (x = t) := by
    intro x
    rw [hUE, edgeBalance_eq_of_incidence hW hY hR hF hin hout]
    have hd := hdelta x
    omega
  have hboundary := boundary_eq_of_augmenting_balance hY hU hYfin hUfin
    hUI hst hs ht hbalance
  exact ⟨U, hU, hUfin, hUE, hUI, hboundary⟩

/-- The original disjoint-edge augmentation interface remains available. -/
theorem exists_finiteWarp_augmenting_of_balanced_intervalSwitch
    {W Y : Set Gamma.DPath} {R F : Set (V × V)}
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hR : R ⊆ familyEdges Y) (hF : F ⊆ familyEdges W)
    (_hdisj : Disjoint F (familyEdges Y))
    (hin : ∀ {a b x : V}, (a, x) ∈ F →
      (b, x) ∈ familyEdges Y → (b, x) ∈ R)
    (hout : ∀ {x a b : V}, (x, a) ∈ F →
      (x, b) ∈ familyEdges Y → (x, b) ∈ R)
    (hinterval : ∀ p ∈ Y, IsEdgeInterval (R ∩ p.edgeSet) p)
    (hpure : ∀ {x y : V}, (x, y) ∈ F →
      y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y)
    {s t : V} (hst : s ≠ t)
    (hs : s ∉ Gamma.vertexSet Y) (ht : t ∉ Gamma.vertexSet Y)
    (hdelta : ∀ x, edgeBalance F x - edgeBalance R x =
      propInt (x = s) - propInt (x = t)) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = (familyEdges Y \ R) ∪ F ∧
      isolatedVertices U = isolatedVertices Y ∧
      Gamma.initialSet U = Gamma.initialSet Y ∪ {s} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier Y ∪ {t} :=
  exists_finiteWarp_augmenting_of_incidence_balanced_intervalSwitch
    hW hY hWfin hYfin hR hF hin hout hinterval hpure hst hs ht hdelta

#print axioms biUnique_of_incident_reference_edges_removed
#print axioms boundary_eq_of_augmenting_balance
#print axioms exists_finiteWarp_augmenting_of_incidence_balanced_intervalSwitch
#print axioms exists_finiteWarp_augmenting_of_balanced_intervalSwitch

end Erdos599.Alternating.SwitchingCore.RelationalInterval
