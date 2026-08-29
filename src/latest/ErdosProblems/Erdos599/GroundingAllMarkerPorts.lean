/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitching
import ErdosProblems.Erdos599.GroundingSuccessorTransport

/-!
# The uncontracted all-marker auxiliary and its roof barrier

These are the sending and receiving ports of the informal grounding repair.
The reference matching consists of warp edges and identities strictly
outside the warp's vertex set. In particular, an isolated warp member has
two unmatched ports: its identity is not put into the matching. Every
nonmatching original or identity edge is directed from sending to receiving;
reference edges are directed backwards.

The barrier theorem keeps sending ports in a strict roof and receiving ports
in its full roof. It requires the precise incoming-reference-edge reflection
property and coverage of the essential boundary by the reference warp.
Neither of these geometric inputs is replaced by a path-confinement premise.
The theorem applies to arbitrary finite residual walks, including those
ending at a hanging marker, without the old essential-marker restriction.
-/

namespace Erdos599.GroundingAllMarkerPorts

open Set DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Sending (`inl`) and receiving (`inr`) copies of an original vertex. -/
abbrev Port (V : Type u) := Sum V V

/-- The exact reference matching, with identities only off the whole warp. -/
def referenceMatching (Y : Set Gamma.DPath) (x y : V) : Prop :=
  (x, y) ∈ familyEdges Y ∨ (x = y ∧ x ∉ Gamma.vertexSet Y)

/-- The directed, uncontracted residual graph of the reference matching. -/
def Step (Y : Set Gamma.DPath) : Port V → Port V → Prop
  | .inl x, .inr y =>
      (Gamma.graph.Adj x y ∨ x = y) ∧ ¬ referenceMatching Y x y
  | .inr y, .inl x => referenceMatching Y x y
  | _, _ => False

/-- The reference relation really is a matching, including isolated members. -/
theorem referenceMatching_biUnique {Y : Set Gamma.DPath}
    (hY : Gamma.IsWarp Y) : Relator.BiUnique (referenceMatching Y) := by
  have hE := IsWarp.familyEdges_biUnique hY
  constructor
  · intro x y z hx hy
    rcases hx with hx | ⟨hxz, hx⟩
    · rcases hy with hy | ⟨hyz, hy⟩
      · exact hE.1 hx hy
      · exact (hy (hyz.symm ▸ (familyEdges_subset_vertexSet_prod Y hx).2)).elim
    · rcases hy with hy | ⟨hyz, _hy⟩
      · exact (hx (hxz.symm ▸ (familyEdges_subset_vertexSet_prod Y hy).2)).elim
      · exact hxz.trans hyz.symm
  · intro x y z hy hz
    rcases hy with hy | ⟨hxy, hy⟩
    · rcases hz with hz | ⟨_hxz, hz⟩
      · exact hE.2 hy hz
      · exact (hz (familyEdges_subset_vertexSet_prod Y hy).1).elim
    · rcases hz with hz | ⟨hxz, _hz⟩
      · exact (hy (familyEdges_subset_vertexSet_prod Y hz).1).elim
      · exact hxy.symm.trans hxz

/-- The two different roof requirements for the two port types. -/
def RoofPort (S : Set V) : Port V → Prop
  | .inl x => x ∈ Gamma.strictRoof S
  | .inr x => x ∈ Gamma.roof S

/-- One residual step preserves the two-sided roof barrier. Identities on
the essential frontier cannot be reverse steps, because that frontier is
already on the reference warp. -/
theorem step_preserves_roof
    {Y : Set Gamma.DPath} {S : Set V}
    (hessential : Gamma.essential S = S)
    (hboundary : S ⊆ Gamma.vertexSet Y)
    (hincoming : ∀ {x y : V}, (x, y) ∈ familyEdges Y →
      y ∈ Gamma.roof S → x ∈ Gamma.strictRoof S)
    {p q : Port V} (hpq : Step Y p q) (hp : RoofPort (Gamma := Gamma) S p) :
    RoofPort (Gamma := Gamma) S q := by
  rcases p with x | y
  · rcases q with z | z
    · exact hpq.elim
    · rcases hpq.1 with hxy | rfl
      · exact Gamma.adj_mem_roof_of_mem_strictRoof_of_essential hessential hxy hp
      · exact hp.1
  · rcases q with x | z
    · rcases hpq with hxy | ⟨rfl, hx⟩
      · exact hincoming hxy hp
      · refine ⟨hp, ?_⟩
        intro hxEss
        exact hx (hboundary (hessential ▸ hxEss))
    · exact hpq.elim

/-- The barrier holds for any finite residual walk; no simplicity or
target-purity assumption is needed. -/
theorem reachable_preserves_roof
    {Y : Set Gamma.DPath} {S : Set V}
    (hessential : Gamma.essential S = S)
    (hboundary : S ⊆ Gamma.vertexSet Y)
    (hincoming : ∀ {x y : V}, (x, y) ∈ familyEdges Y →
      y ∈ Gamma.roof S → x ∈ Gamma.strictRoof S)
    {p q : Port V} (hpq : Relation.ReflTransGen (Step Y) p q)
    (hp : RoofPort (Gamma := Gamma) S p) :
    RoofPort (Gamma := Gamma) S q := by
  induction hpq with
  | refl => exact hp
  | tail _ hstep ih =>
      exact step_preserves_roof hessential hboundary hincoming hstep ih

/-- In particular a recorded finite terminal cannot reach any unroofed
marker's receiving port, whether the marker is grounded or hanging. -/
theorem not_reachable_unroofed_marker
    {Y : Set Gamma.DPath} {S : Set V}
    (hessential : Gamma.essential S = S)
    (hboundary : S ⊆ Gamma.vertexSet Y)
    (hincoming : ∀ {x y : V}, (x, y) ∈ familyEdges Y →
      y ∈ Gamma.roof S → x ∈ Gamma.strictRoof S)
    {x y : V} (hx : x ∈ Gamma.strictRoof S) (hy : y ∉ Gamma.roof S) :
    ¬ Relation.ReflTransGen (Step Y) (.inl x) (.inr y) := by
  intro hpath
  exact hy (reachable_preserves_roof hessential hboundary hincoming hpath hx)

/-- A ray proxy may start with any original edge leaving its record.
After that first edge the same receiving-port barrier applies. -/
theorem not_reachable_unroofed_marker_after_proxy_edge
    {Y : Set Gamma.DPath} {S : Set V}
    (hessential : Gamma.essential S = S)
    (hboundary : S ⊆ Gamma.vertexSet Y)
    (hincoming : ∀ {x y : V}, (x, y) ∈ familyEdges Y →
      y ∈ Gamma.roof S → x ∈ Gamma.strictRoof S)
    {x z y : V} (hx : x ∈ Gamma.strictRoof S)
    (hxz : Gamma.graph.Adj x z) (hy : y ∉ Gamma.roof S) :
    ¬ Relation.ReflTransGen (Step Y) (.inr z) (.inr y) := by
  intro hpath
  exact hy (reachable_preserves_roof hessential hboundary hincoming hpath
    (Gamma.adj_mem_roof_of_mem_strictRoof_of_essential hessential hxz hx))

/-- Birth-index form of the all-marker chronology barrier. The hypothesis
about future markers is the unroofed insertion rule plus increasing roofs. -/
theorem marker_index_lt_of_reachable
    {I : Type*} [LinearOrder I]
    {Y : Set Gamma.DPath} {S : Set V}
    (hessential : Gamma.essential S = S)
    (hboundary : S ⊆ Gamma.vertexSet Y)
    (hincoming : ∀ {x y : V}, (x, y) ∈ familyEdges Y →
      y ∈ Gamma.roof S → x ∈ Gamma.strictRoof S)
    (marker : I → V) (a : I)
    (hfuture : ∀ b, a ≤ b → marker b ∉ Gamma.roof S)
    {x : V} (hx : x ∈ Gamma.strictRoof S) {b : I}
    (hpath : Relation.ReflTransGen (Step Y) (.inl x) (.inr (marker b))) :
    b < a := by
  by_contra hba
  exact not_reachable_unroofed_marker hessential hboundary hincoming hx
    (hfuture b (le_of_not_gt hba)) hpath

#print axioms referenceMatching_biUnique
#print axioms reachable_preserves_roof
#print axioms not_reachable_unroofed_marker_after_proxy_edge
#print axioms marker_index_lt_of_reachable

end Erdos599.GroundingAllMarkerPorts
