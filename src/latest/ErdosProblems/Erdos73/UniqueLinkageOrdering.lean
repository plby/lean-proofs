/-
Adapted from the Apache-2.0-licensed polynomial-grid-minor-theorem development,
https://github.com/EdouardBonnet/polynomial-grid-minor-theorem,
commit fe2848173913a00d85c64d2a17af63f2cf0d4fbf,
proofs/Lax17Proofs/Source/{PseudoGridSlicingDefs,PseudoGridSlicing,UniqueLinkageOrdering}.lean.
Local changes: isolate the unique-linkage dependency chain, namespace and import
paths, and Lean 4.33 compatibility. The paper's current arXiv numbering is
Lemma 4.6 (the source comments refer to Lemma 4.5).
-/
import Mathlib.Order.Extension.Well
import Mathlib.Order.RelSeries
import Mathlib.Algebra.Group.Fin.Basic
import ErdosProblems.Erdos73.UniqueLinkageDefs

namespace Erdos73Infrastructure

universe u v w

/-!
# Linkage orderings from unique linkages

This file formalizes the missing generic part of Chuzhoy--Tan Lemma 4.5.
The row-support ordering used for pseudo-grids is already self-contained in
`PseudoGridSlicing`; here we build the paper's Robertson--Seymour ordering for
an arbitrary unique linkage.

The proof is organized around the auxiliary directed dependency relation from
Appendix B.  First we record the finite topological-order construction for an
acyclic directed relation.  The subsequent sections specialize it to
`PathSlicing.LinkageDependency`.
-/

namespace SimpleGraph

/-- A reducible record constructor for concatenating paths at their only
common vertex. Its walk and simplicity proof are the checked path operations. -/
noncomputable abbrev GraphPath.appendClean {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter : ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target) :
    GraphPath G where
  source := P.source
  target := Q.target
  walk := P.walk.append (Q.walk.copy h.symm rfl)
  isPath := P.appendWithEq_isPath_of_inter_subset_target Q h hinter

namespace PathSlicing

open Relation
open scoped SetRel

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}

theorem fin_addRight_one_apply_of_lt {n : ℕ} [NeZero n]
    (i : Fin n) (h : i.1 + 1 < n) :
    Equiv.addRight (1 : Fin n) i = ⟨i.1 + 1, h⟩ := by
  ext
  have hlt : i.1 + (1 : Fin n).1 < n := by
    rw [Fin.val_one']
    rw [Nat.mod_eq_of_lt (by omega)]
    exact h
  rw [Equiv.coe_addRight]
  rw [Fin.val_add_eq_of_add_lt hlt]
  rw [Fin.val_one']
  rw [Nat.mod_eq_of_lt (by omega)]

theorem fin_addRight_one_apply_of_not_lt {n : ℕ} [NeZero n]
    (i : Fin n) (h : ¬ i.1 + 1 < n) :
    Equiv.addRight (1 : Fin n) i = 0 := by
  ext
  have hi : i.1 + 1 = n := by omega
  simp [Equiv.coe_addRight, Fin.val_add, hi]

namespace GraphPath

/-- The one-edge path associated to an adjacency. -/
def edgePath {u v : V} (huv : G.Adj u v) : GraphPath G where
  source := u
  target := v
  walk := _root_.SimpleGraph.Walk.cons huv _root_.SimpleGraph.Walk.nil
  isPath := by
    simpa [_root_.SimpleGraph.Path.singleton] using
      (_root_.SimpleGraph.Path.singleton huv).property

omit [Fintype V] [DecidableEq V] in
@[simp] theorem edgePath_source {u v : V} (huv : G.Adj u v) :
    (edgePath huv).source = u := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem edgePath_target {u v : V} (huv : G.Adj u v) :
    (edgePath huv).target = v := rfl

omit [Fintype V] in
@[simp] theorem edgePath_vertexSet {u v : V} (huv : G.Adj u v) :
    (edgePath huv).vertexSet = {u, v} := by
  classical
  simp [edgePath, GraphPath.vertexSet]

omit [Fintype V] in
@[simp] theorem edgePath_edgeSet {u v : V} (huv : G.Adj u v) :
    (edgePath huv).edgeSet = {s(u, v)} := by
  classical
  simp [edgePath, GraphPath.edgeSet]

omit [Fintype V] in
theorem appendWithEq_right_edgeSet_subset (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    Q.edgeSet ⊆ (P.appendWithEq Q h hpath).edgeSet := by
  classical
  intro e he
  have heWalk : e ∈ Q.walk.edges := by
    exact List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using he)
  have : e ∈ (P.walk.append (Q.walk.copy h.symm rfl)).edges := by
    simp [heWalk]
  exact List.mem_toFinset.2 (by simpa [GraphPath.appendWithEq, GraphPath.edgeSet] using this)

omit [Fintype V] in
theorem appendWithEq_left_edgeSet_subset (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    P.edgeSet ⊆ (P.appendWithEq Q h hpath).edgeSet := by
  classical
  intro e he
  have heWalk : e ∈ P.walk.edges := by
    exact List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using he)
  have : e ∈ (P.walk.append (Q.walk.copy h.symm rfl)).edges := by
    simp [heWalk]
  exact List.mem_toFinset.2 (by simpa [GraphPath.appendWithEq, GraphPath.edgeSet] using this)

/-- Shortcut a path by replacing the segment from `u` to `v` with an ambient
edge `uv`.  The hypotheses `u < x < v` along the original path guarantee that
the resulting concatenation is simple. -/
noncomputable def shortcutAround
    (Prow : GraphPath G) {u x v : V}
    (hux : Prow.Before u x) (hxv : Prow.Before x v)
    (hux_ne : u ≠ x) (huv : G.Adj u v) : GraphPath G := by
  classical
  have hu : u ∈ Prow.vertexSet := ((Prow.before_iff_vertexIndex_le).1 hux).1
  have hv : v ∈ Prow.vertexSet := ((Prow.before_iff_vertexIndex_le).1 hxv).2.1
  have huvBefore : Prow.Before u v := Prow.before_trans hux hxv
  have huv_ne : u ≠ v := by
    intro huv_eq
    have hx_u : Prow.Before x u := by simpa [huv_eq] using hxv
    exact hux_ne (Prow.before_antisymm hux hx_u)
  let pref := Prow.takeUntil hu
  let edge := edgePath huv
  have hprefix_edge :
      ∀ ⦃z : V⦄, z ∈ pref.vertexSet → z ∈ edge.vertexSet → z = pref.target := by
    intro z hzPrefix hzEdge
    have hzu : Prow.Before z u := by
      simpa [pref] using Prow.before_of_mem_takeUntil hu hzPrefix
    have hzEdge' : z = u ∨ z = v := by
      simpa [edge] using hzEdge
    rcases hzEdge' with hzu_eq | hzv_eq
    · subst z
      simp [pref]
    · subst z
      have hvu : Prow.Before v u := by simpa using hzu
      exact False.elim (huv_ne (Prow.before_antisymm huvBefore hvu))
  let first :=
    pref.appendClean edge (by simp [pref, edge])
      hprefix_edge
  let suffix := Prow.dropUntil hv
  have hfirst_suffix :
      ∀ ⦃z : V⦄, z ∈ first.vertexSet → z ∈ suffix.vertexSet → z = first.target := by
    intro z hzFirst hzSuffix
    have hzFirstSplit :=
      GraphPath.appendWithEq_vertexSet_subset pref edge (by simp [pref, edge])
        (pref.appendWithEq_isPath_of_inter_subset_target edge
          (by simp [pref, edge]) hprefix_edge) hzFirst
    have hvz : Prow.Before v z := by
      exact ⟨hv, by simpa [suffix] using hzSuffix⟩
    rcases Finset.mem_union.1 hzFirstSplit with hzPrefix | hzEdge
    · have hzu : Prow.Before z u := by
        simpa [pref] using Prow.before_of_mem_takeUntil hu hzPrefix
      have hvu : Prow.Before v u := Prow.before_trans hvz hzu
      exact False.elim (huv_ne (Prow.before_antisymm huvBefore hvu))
    · have hzEdge' : z = u ∨ z = v := by
        simpa [edge] using hzEdge
      rcases hzEdge' with hzu_eq | hzv_eq
      · subst z
        have hvu : Prow.Before v u := by simpa using hvz
        exact False.elim (huv_ne (Prow.before_antisymm huvBefore hvu))
      · subst z
        simp [first, edge]
  exact first.appendClean suffix (by simp [first, suffix, edge])
    hfirst_suffix

omit [Fintype V] in
@[simp] theorem shortcutAround_source
    (Prow : GraphPath G) {u x v : V}
    (hux : Prow.Before u x) (hxv : Prow.Before x v)
    (hux_ne : u ≠ x) (huv : G.Adj u v) :
    (shortcutAround Prow hux hxv hux_ne huv).source = Prow.source := by
  classical
  simp [shortcutAround]

omit [Fintype V] in
@[simp] theorem shortcutAround_target
    (Prow : GraphPath G) {u x v : V}
    (hux : Prow.Before u x) (hxv : Prow.Before x v)
    (hux_ne : u ≠ x) (huv : G.Adj u v) :
    (shortcutAround Prow hux hxv hux_ne huv).target = Prow.target := by
  classical
  simp [shortcutAround]

omit [Fintype V] in
/-- The shortcut construction together with the facts needed to replace one
row of a linkage. -/
theorem exists_shortcutAround
    (Prow : GraphPath G) {u x v : V}
    (hux : Prow.Before u x) (hxv : Prow.Before x v)
    (hux_ne : u ≠ x) (huv : G.Adj u v) :
    ∃ Q : GraphPath G,
      Q.source = Prow.source ∧
        Q.target = Prow.target ∧
          Q.vertexSet ⊆ Prow.vertexSet ∧
            s(u, v) ∈ Q.edgeSet := by
  classical
  have hu : u ∈ Prow.vertexSet := ((Prow.before_iff_vertexIndex_le).1 hux).1
  have hv : v ∈ Prow.vertexSet := ((Prow.before_iff_vertexIndex_le).1 hxv).2.1
  have huvBefore : Prow.Before u v := Prow.before_trans hux hxv
  have huv_ne : u ≠ v := by
    intro huv_eq
    have hx_u : Prow.Before x u := by simpa [huv_eq] using hxv
    exact hux_ne (Prow.before_antisymm hux hx_u)
  let pref := Prow.takeUntil hu
  let edge := edgePath huv
  have hprefix_edge :
      ∀ ⦃z : V⦄, z ∈ pref.vertexSet → z ∈ edge.vertexSet → z = pref.target := by
    intro z hzPrefix hzEdge
    have hzu : Prow.Before z u := by
      simpa [pref] using Prow.before_of_mem_takeUntil hu hzPrefix
    have hzEdge' : z = u ∨ z = v := by
      simpa [edge] using hzEdge
    rcases hzEdge' with hzu_eq | hzv_eq
    · subst z
      simp [pref]
    · subst z
      have hvu : Prow.Before v u := by simpa using hzu
      exact False.elim (huv_ne (Prow.before_antisymm huvBefore hvu))
  let first :=
    pref.appendClean edge (by simp [pref, edge])
      hprefix_edge
  let suffix := Prow.dropUntil hv
  have hfirst_suffix :
      ∀ ⦃z : V⦄, z ∈ first.vertexSet → z ∈ suffix.vertexSet → z = first.target := by
    intro z hzFirst hzSuffix
    have hzFirstSplit :=
      GraphPath.appendWithEq_vertexSet_subset pref edge (by simp [pref, edge])
        (pref.appendWithEq_isPath_of_inter_subset_target edge
          (by simp [pref, edge]) hprefix_edge) hzFirst
    have hvz : Prow.Before v z := by
      exact ⟨hv, by simpa [suffix] using hzSuffix⟩
    rcases Finset.mem_union.1 hzFirstSplit with hzPrefix | hzEdge
    · have hzu : Prow.Before z u := by
        simpa [pref] using Prow.before_of_mem_takeUntil hu hzPrefix
      have hvu : Prow.Before v u := Prow.before_trans hvz hzu
      exact False.elim (huv_ne (Prow.before_antisymm huvBefore hvu))
    · have hzEdge' : z = u ∨ z = v := by
        simpa [edge] using hzEdge
      rcases hzEdge' with hzu_eq | hzv_eq
      · subst z
        have hvu : Prow.Before v u := by simpa using hvz
        exact False.elim (huv_ne (Prow.before_antisymm huvBefore hvu))
      · subst z
        simp [first, edge]
  let Q := first.appendClean suffix (by simp [first, suffix, edge])
    hfirst_suffix
  refine ⟨Q, by simp [Q, first, pref], by simp [Q, first, suffix, edge], ?_, ?_⟩
  · intro z hzQ
    have hzSplit :=
      GraphPath.appendWithEq_vertexSet_subset first suffix (by simp [first, suffix, edge])
        (first.appendWithEq_isPath_of_inter_subset_target suffix
          (by simp [first, suffix, edge]) hfirst_suffix) hzQ
    rcases Finset.mem_union.1 hzSplit with hzFirst | hzSuffix
    · have hzFirstSplit :=
        GraphPath.appendWithEq_vertexSet_subset pref edge (by simp [pref, edge])
          (pref.appendWithEq_isPath_of_inter_subset_target edge
            (by simp [pref, edge]) hprefix_edge) hzFirst
      rcases Finset.mem_union.1 hzFirstSplit with hzPref | hzEdge
      · exact Prow.takeUntil_vertexSet_subset hu hzPref
      · have hzEdge' : z = u ∨ z = v := by
          simpa [edge] using hzEdge
        rcases hzEdge' with rfl | rfl
        · exact hu
        · exact hv
    · exact Prow.dropUntil_vertexSet_subset hv hzSuffix
  · have hedgeEdge : s(u, v) ∈ edge.edgeSet := by
      simp [edge]
    have hedgeFirst : s(u, v) ∈ first.edgeSet := by
      exact
        (GraphPath.appendWithEq_right_edgeSet_subset pref edge
          (by simp [pref, edge])
          (pref.appendWithEq_isPath_of_inter_subset_target edge
            (by simp [pref, edge]) hprefix_edge) hedgeEdge)
    exact
      (GraphPath.appendWithEq_left_edgeSet_subset first suffix
        (by simp [first, suffix, edge])
        (first.appendWithEq_isPath_of_inter_subset_target suffix
          (by simp [first, suffix, edge]) hfirst_suffix) hedgeFirst)

/-- A cross-row rerouting path: take the prefix of `Pi` ending at `vi`, the
ambient edge `vi--uj`, and the suffix of the disjoint row `Pj` starting at
`uj`.  This is the path used in the cyclic rerouting contradiction in
Appendix B, Claim B.2. -/
noncomputable def crossPrefixSuffix
    (Pi Pj : GraphPath G) {vi uj : V}
    (hvi : vi ∈ Pi.vertexSet) (huj : uj ∈ Pj.vertexSet)
    (hdisj : Disjoint Pi.vertexSet Pj.vertexSet)
    (hvu : G.Adj vi uj) : GraphPath G := by
  classical
  let pref := Pi.takeUntil hvi
  let edge := edgePath hvu
  let suffix := Pj.dropUntil huj
  have hprefix_edge :
      ∀ ⦃z : V⦄, z ∈ pref.vertexSet → z ∈ edge.vertexSet → z = pref.target := by
    intro z hzPrefix hzEdge
    have hzEdge' : z = vi ∨ z = uj := by
      simpa [edge] using hzEdge
    rcases hzEdge' with hz_eq_vi | hz_eq_uj
    · simp [pref, hz_eq_vi]
    · have hzPi : z ∈ Pi.vertexSet := Pi.takeUntil_vertexSet_subset hvi hzPrefix
      have hzPj : z ∈ Pj.vertexSet := by simpa [hz_eq_uj] using huj
      exact False.elim (Finset.disjoint_left.mp hdisj hzPi hzPj)
  let first :=
    pref.appendClean edge (by simp [pref, edge])
      hprefix_edge
  have hfirst_suffix :
      ∀ ⦃z : V⦄, z ∈ first.vertexSet → z ∈ suffix.vertexSet → z = first.target := by
    intro z hzFirst hzSuffix
    have hzFirstSplit :=
      GraphPath.appendWithEq_vertexSet_subset pref edge (by simp [pref, edge])
        (pref.appendWithEq_isPath_of_inter_subset_target edge
          (by simp [pref, edge]) hprefix_edge) hzFirst
    have hzPj : z ∈ Pj.vertexSet := Pj.dropUntil_vertexSet_subset huj hzSuffix
    rcases Finset.mem_union.1 hzFirstSplit with hzPrefix | hzEdge
    · have hzPi : z ∈ Pi.vertexSet := Pi.takeUntil_vertexSet_subset hvi hzPrefix
      exact False.elim (Finset.disjoint_left.mp hdisj hzPi hzPj)
    · have hzEdge' : z = vi ∨ z = uj := by
        simpa [edge] using hzEdge
      rcases hzEdge' with rfl | rfl
      · exact False.elim (Finset.disjoint_left.mp hdisj hvi hzPj)
      · simp [first, edge]
  exact first.appendClean suffix
    (by simp [first, suffix, edge]) hfirst_suffix

omit [Fintype V] in
@[simp] theorem crossPrefixSuffix_source
    (Pi Pj : GraphPath G) {vi uj : V}
    (hvi : vi ∈ Pi.vertexSet) (huj : uj ∈ Pj.vertexSet)
    (hdisj : Disjoint Pi.vertexSet Pj.vertexSet)
    (hvu : G.Adj vi uj) :
    (crossPrefixSuffix Pi Pj hvi huj hdisj hvu).source = Pi.source := by
  classical
  simp [crossPrefixSuffix]

omit [Fintype V] in
@[simp] theorem crossPrefixSuffix_target
    (Pi Pj : GraphPath G) {vi uj : V}
    (hvi : vi ∈ Pi.vertexSet) (huj : uj ∈ Pj.vertexSet)
    (hdisj : Disjoint Pi.vertexSet Pj.vertexSet)
    (hvu : G.Adj vi uj) :
    (crossPrefixSuffix Pi Pj hvi huj hdisj hvu).target = Pj.target := by
  classical
  simp [crossPrefixSuffix]

omit [Fintype V] in
theorem exists_crossPrefixSuffix
    (Pi Pj : GraphPath G) {vi uj : V}
    (hvi : vi ∈ Pi.vertexSet) (huj : uj ∈ Pj.vertexSet)
    (hdisj : Disjoint Pi.vertexSet Pj.vertexSet)
    (hvu : G.Adj vi uj) :
    ∃ Q : GraphPath G,
      Q.source = Pi.source ∧
        Q.target = Pj.target ∧
          Q.vertexSet ⊆ Pi.vertexSet ∪ Pj.vertexSet ∧
            s(vi, uj) ∈ Q.edgeSet := by
  classical
  let pref := Pi.takeUntil hvi
  let edge := edgePath hvu
  let suffix := Pj.dropUntil huj
  have hprefix_edge :
      ∀ ⦃z : V⦄, z ∈ pref.vertexSet → z ∈ edge.vertexSet → z = pref.target := by
    intro z hzPrefix hzEdge
    have hzEdge' : z = vi ∨ z = uj := by
      simpa [edge] using hzEdge
    rcases hzEdge' with hz_eq_vi | hz_eq_uj
    · simp [pref, hz_eq_vi]
    · have hzPi : z ∈ Pi.vertexSet := Pi.takeUntil_vertexSet_subset hvi hzPrefix
      have hzPj : z ∈ Pj.vertexSet := by simpa [hz_eq_uj] using huj
      exact False.elim (Finset.disjoint_left.mp hdisj hzPi hzPj)
  let first :=
    pref.appendClean edge (by simp [pref, edge])
      hprefix_edge
  have hfirst_suffix :
      ∀ ⦃z : V⦄, z ∈ first.vertexSet → z ∈ suffix.vertexSet → z = first.target := by
    intro z hzFirst hzSuffix
    have hzFirstSplit :=
      GraphPath.appendWithEq_vertexSet_subset pref edge (by simp [pref, edge])
        (pref.appendWithEq_isPath_of_inter_subset_target edge
          (by simp [pref, edge]) hprefix_edge) hzFirst
    have hzPj : z ∈ Pj.vertexSet := Pj.dropUntil_vertexSet_subset huj hzSuffix
    rcases Finset.mem_union.1 hzFirstSplit with hzPrefix | hzEdge
    · have hzPi : z ∈ Pi.vertexSet := Pi.takeUntil_vertexSet_subset hvi hzPrefix
      exact False.elim (Finset.disjoint_left.mp hdisj hzPi hzPj)
    · have hzEdge' : z = vi ∨ z = uj := by
        simpa [edge] using hzEdge
      rcases hzEdge' with rfl | rfl
      · exact False.elim (Finset.disjoint_left.mp hdisj hvi hzPj)
      · simp [first, edge]
  let Q := first.appendClean suffix
    (by simp [first, suffix, edge]) hfirst_suffix
  refine ⟨Q, by simp [Q, first, pref], by simp [Q, first, suffix, edge], ?_, ?_⟩
  · intro z hzQ
    have hzSplit :=
      GraphPath.appendWithEq_vertexSet_subset first suffix
        (by simp [first, suffix, edge])
        (first.appendWithEq_isPath_of_inter_subset_target suffix
          (by simp [first, suffix, edge]) hfirst_suffix) hzQ
    rcases Finset.mem_union.1 hzSplit with hzFirst | hzSuffix
    · have hzFirstSplit :=
        GraphPath.appendWithEq_vertexSet_subset pref edge (by simp [pref, edge])
          (pref.appendWithEq_isPath_of_inter_subset_target edge
            (by simp [pref, edge]) hprefix_edge) hzFirst
      rcases Finset.mem_union.1 hzFirstSplit with hzPref | hzEdge
      · exact Finset.mem_union_left _
          (Pi.takeUntil_vertexSet_subset hvi hzPref)
      · have hzEdge' : z = vi ∨ z = uj := by
          simpa [edge] using hzEdge
        rcases hzEdge' with rfl | rfl
        · exact Finset.mem_union_left _ hvi
        · exact Finset.mem_union_right _ huj
    · exact Finset.mem_union_right _
        (Pj.dropUntil_vertexSet_subset huj hzSuffix)
  · have hedgeEdge : s(vi, uj) ∈ edge.edgeSet := by
      simp [edge]
    have hedgeFirst : s(vi, uj) ∈ first.edgeSet := by
      exact
        (GraphPath.appendWithEq_right_edgeSet_subset pref edge
          (by simp [pref, edge])
          (pref.appendWithEq_isPath_of_inter_subset_target edge
            (by simp [pref, edge]) hprefix_edge) hedgeEdge)
    exact
      (GraphPath.appendWithEq_left_edgeSet_subset first suffix
        (by simp [first, suffix, edge])
        (first.appendWithEq_isPath_of_inter_subset_target suffix
          (by simp [first, suffix, edge]) hfirst_suffix) hedgeFirst)

omit [Fintype V] in
/-- A strict prefix ending at `a` and the suffix beginning at a later vertex
`b` of the same simple path are disjoint. -/
theorem takeUntil_disjoint_dropUntil_of_before_ne
    (P : GraphPath G) {a b : V}
    (ha : a ∈ P.vertexSet) (hb : b ∈ P.vertexSet)
    (hab : P.Before a b) (hne : a ≠ b) :
    Disjoint (P.takeUntil ha).vertexSet (P.dropUntil hb).vertexSet := by
  rw [Finset.disjoint_left]
  intro z hzPrefix hzSuffix
  have hza : P.Before z a := P.before_of_mem_takeUntil ha hzPrefix
  have hbz : P.Before b z := ⟨hb, hzSuffix⟩
  have hba : P.Before b a := P.before_trans hbz hza
  exact hne (P.before_antisymm hab hba)

omit [Fintype V] in
theorem crossPrefixSuffix_vertexSet_subset_parts
    (Pi Pj : GraphPath G) {vi uj : V}
    (hvi : vi ∈ Pi.vertexSet) (huj : uj ∈ Pj.vertexSet)
    (hdisj : Disjoint Pi.vertexSet Pj.vertexSet)
    (hvu : G.Adj vi uj) :
    (crossPrefixSuffix Pi Pj hvi huj hdisj hvu).vertexSet ⊆
      (Pi.takeUntil hvi).vertexSet ∪ (Pj.dropUntil huj).vertexSet := by
  classical
  let pref := Pi.takeUntil hvi
  let edge := edgePath hvu
  let suffix := Pj.dropUntil huj
  have hprefix_edge :
      ∀ ⦃z : V⦄, z ∈ pref.vertexSet → z ∈ edge.vertexSet → z = pref.target := by
    intro z hzPrefix hzEdge
    have hzEdge' : z = vi ∨ z = uj := by
      simpa [edge] using hzEdge
    rcases hzEdge' with hz_eq_vi | hz_eq_uj
    · simp [pref, hz_eq_vi]
    · have hzPi : z ∈ Pi.vertexSet := Pi.takeUntil_vertexSet_subset hvi hzPrefix
      have hzPj : z ∈ Pj.vertexSet := by simpa [hz_eq_uj] using huj
      exact False.elim (Finset.disjoint_left.mp hdisj hzPi hzPj)
  let first :=
    pref.appendClean edge (by simp [pref, edge])
      hprefix_edge
  have hfirst_suffix :
      ∀ ⦃z : V⦄, z ∈ first.vertexSet → z ∈ suffix.vertexSet → z = first.target := by
    intro z hzFirst hzSuffix
    have hzFirstSplit :=
      GraphPath.appendWithEq_vertexSet_subset pref edge (by simp [pref, edge])
        (pref.appendWithEq_isPath_of_inter_subset_target edge
          (by simp [pref, edge]) hprefix_edge) hzFirst
    have hzPj : z ∈ Pj.vertexSet := Pj.dropUntil_vertexSet_subset huj hzSuffix
    rcases Finset.mem_union.1 hzFirstSplit with hzPrefix | hzEdge
    · have hzPi : z ∈ Pi.vertexSet := Pi.takeUntil_vertexSet_subset hvi hzPrefix
      exact False.elim (Finset.disjoint_left.mp hdisj hzPi hzPj)
    · have hzEdge' : z = vi ∨ z = uj := by
        simpa [edge] using hzEdge
      rcases hzEdge' with rfl | rfl
      · exact False.elim (Finset.disjoint_left.mp hdisj hvi hzPj)
      · simp [first, edge]
  intro z hz
  change z ∈
      (first.appendClean suffix
        (by simp [first, suffix, edge]) hfirst_suffix).vertexSet at hz
  have hzSplit :=
    GraphPath.appendWithEq_vertexSet_subset first suffix
      (by simp [first, suffix, edge])
      (first.appendWithEq_isPath_of_inter_subset_target suffix
        (by simp [first, suffix, edge]) hfirst_suffix) hz
  rcases Finset.mem_union.1 hzSplit with hzFirst | hzSuffix
  · have hzFirstSplit :=
      GraphPath.appendWithEq_vertexSet_subset pref edge (by simp [pref, edge])
        (pref.appendWithEq_isPath_of_inter_subset_target edge
          (by simp [pref, edge]) hprefix_edge) hzFirst
    rcases Finset.mem_union.1 hzFirstSplit with hzPref | hzEdge
    · exact Finset.mem_union_left _ (by simpa [pref] using hzPref)
    · have hzEdge' : z = vi ∨ z = uj := by
        simpa [edge] using hzEdge
      rcases hzEdge' with rfl | rfl
      · exact Finset.mem_union_left _
          (by simpa [pref] using GraphPath.target_mem_vertexSet pref)
      · exact Finset.mem_union_right _
          (by simpa [suffix] using GraphPath.source_mem_vertexSet suffix)
  · exact Finset.mem_union_right _ (by simpa [suffix] using hzSuffix)

/-- If a path contains vertices on both sides of a rank threshold, then some
edge of the path crosses the threshold from the lower side to the upper side.

The proof orients the relevant subpath from a lower vertex to an upper vertex,
takes the prefix ending at the first upper vertex, and uses its last edge. -/
theorem exists_adjacent_rank_crossing
    (rank : V → ℕ) (t : ℕ) (P : GraphPath G)
    (hcross : GraphPathCrossesRankThreshold rank t P) :
    ∃ u v : V,
      u ∈ P.vertexSet ∧ v ∈ P.vertexSet ∧
        rank u < t ∧ t ≤ rank v ∧ G.Adj u v := by
  classical
  rcases hcross with ⟨y, hyP, z, hzP, hyRank, hzRank⟩
  have horder : P.Before y z ∨ P.Before z y := by
    rcases le_total (P.vertexIndex y) (P.vertexIndex z) with hyz | hzy
    · exact Or.inl ((P.before_iff_vertexIndex_le).2 ⟨hyP, hzP, hyz⟩)
    · exact Or.inr ((P.before_iff_vertexIndex_le).2 ⟨hzP, hyP, hzy⟩)
  have aux :
      ∀ (Q : GraphPath G),
        Q.source ∈ P.vertexSet →
        Q.target ∈ P.vertexSet →
        Q.vertexSet ⊆ P.vertexSet →
        rank Q.source < t →
        t ≤ rank Q.target →
          ∃ u v : V,
            u ∈ P.vertexSet ∧ v ∈ P.vertexSet ∧
              rank u < t ∧ t ≤ rank v ∧ G.Adj u v := by
    intro Q hsrcP htgtP hQP hsrcRank htgtRank
    let U : Finset V := Finset.univ.filter fun v : V => t ≤ rank v
    have hne : (Q.vertexSet ∩ U).Nonempty := by
      exact ⟨Q.target, Finset.mem_inter.2
        ⟨GraphPath.target_mem_vertexSet Q, by simp [U, htgtRank]⟩⟩
    let C := Q.cleanPrefixToSet U hne
    have htargetU : C.target ∈ U := by
      simpa [C] using Q.cleanPrefixToSet_target_mem U hne
    have hsource_ne_target : C.source ≠ C.target := by
      intro hst
      have hsrcU : Q.source ∈ U := by
        have hsrcUC : C.source ∈ U := by
          simpa [hst] using htargetU
        simpa [C] using hsrcUC
      have : t ≤ rank Q.source := by simpa [U] using hsrcU
      omega
    let u : V := C.penultimate
    let v : V := C.target
    have huCdrop : u ∈ C.dropLast.vertexSet := by
      simpa [u] using GraphPath.target_mem_vertexSet C.dropLast
    have huC : u ∈ C.vertexSet := C.dropLast_vertexSet_subset huCdrop
    have hvC : v ∈ C.vertexSet := by
      simp [v]
    have huQ : u ∈ Q.vertexSet := by
      have hsub : C.vertexSet ⊆ Q.vertexSet := by
        simpa [C] using Q.cleanPrefixToSet_vertexSet_subset U hne
      exact hsub huC
    have hvQ : v ∈ Q.vertexSet := by
      have hsub : C.vertexSet ⊆ Q.vertexSet := by
        simpa [C] using Q.cleanPrefixToSet_vertexSet_subset U hne
      exact hsub hvC
    have hvRank : t ≤ rank v := by
      simpa [v, U] using htargetU
    have huRank : rank u < t := by
      by_contra hnot
      have huU : u ∈ U := by
        simp [U, le_of_not_gt hnot]
      have hu_eq_target :
          u = Q.firstHitVertex U hne := by
        exact Q.eq_firstHitVertex_of_mem_takeUntil_of_mem_set U hne
          (by exact huC) huU
      have hu_eq_Ctarget : u = C.target := by
        simpa [C] using hu_eq_target
      exact C.target_not_mem_dropLast_vertexSet hsource_ne_target
        (by simpa [hu_eq_Ctarget] using huCdrop)
    refine ⟨u, v, hQP huQ, hQP hvQ, huRank, hvRank, ?_⟩
    simpa [u, v] using C.penultimate_adj_target hsource_ne_target
  rcases horder with hyz | hzy
  · let Q := P.segmentOfBefore hyz
    exact aux Q
      (by simpa [Q] using hyP)
      (by simpa [Q] using hzP)
      (P.segmentOfBefore_vertexSet_subset hyz)
      (by simpa [Q] using hyRank)
      (by simpa [Q] using hzRank)
  · let ZY := P.segmentOfBefore hzy
    let Q := ZY.reverse
    have hsub : Q.vertexSet ⊆ P.vertexSet := by
      intro v hv
      have hvZY : v ∈ ZY.vertexSet := by simpa [Q] using hv
      exact P.segmentOfBefore_vertexSet_subset hzy hvZY
    exact aux Q
      (by simpa [Q, ZY] using hyP)
      (by simpa [Q, ZY] using hzP)
      hsub
      (by simpa [Q, ZY] using hyRank)
      (by simpa [Q, ZY] using hzRank)

end GraphPath

/-- A zero-based finite topological ranking of a directed relation. -/
structure TopologicalRank (rel : V → V → Prop) where
  /-- The assigned zero-based rank. -/
  rank : V → ℕ
  /-- The rank is injective. -/
  rank_injective : Function.Injective rank
  /-- Ranks are bounded by the finite vertex count. -/
  rank_lt_card : ∀ v : V, rank v < Fintype.card V
  /-- Every directed edge strictly increases the rank. -/
  rel_lt : ∀ ⦃u v : V⦄, rel u v → rank u < rank v

/-- A finite acyclic relation admits an injective zero-based topological
ranking.  Acyclicity is expressed as irreflexivity of the transitive closure,
which is exactly the form produced by the dependency-cycle argument in
Appendix B. -/
noncomputable def topologicalRankOfAcyclicRelation
    (rel : V → V → Prop)
    (hacyc : ∀ v : V, ¬ Relation.TransGen rel v v) :
    TopologicalRank rel := by
  classical
  let tr : V → V → Prop := Relation.TransGen rel
  haveI htrans : IsTrans V tr := inferInstance
  haveI hirrefl : Std.Irrefl tr := ⟨hacyc⟩
  haveI hwf : IsWellFounded V tr :=
    ⟨Finite.wellFounded_of_trans_of_irrefl tr⟩
  letI : LinearOrder V := IsWellFounded.wellOrderExtension tr
  refine
    { rank := rankByKey (fun v : V => v) (fun _ _ h => h)
      rank_injective := rankByKey_injective (fun v : V => v) (fun _ _ h => h)
      rank_lt_card := rankByKey_lt_card (fun v : V => v) (fun _ _ h => h)
      rel_lt := ?_ }
  intro u v huv
  have huvTr : tr u v := Relation.TransGen.single huv
  have huvLt : u < v := by
    exact Prod.Lex.left _ _ (IsWellFounded.rank_lt_of_rel huvTr)
  exact rankByKey_lt_of_key_lt (fun v : V => v) (fun _ _ h => h) huvLt

theorem topologicalRankOfAcyclicRelation_rel_lt
    (rel : V → V → Prop)
    (hacyc : ∀ v : V, ¬ Relation.TransGen rel v v)
    {u v : V} (huv : rel u v) :
    (topologicalRankOfAcyclicRelation rel hacyc).rank u <
      (topologicalRankOfAcyclicRelation rel hacyc).rank v :=
  (topologicalRankOfAcyclicRelation rel hacyc).rel_lt huv

/-- The `SetRel` wrapper for an ordinary binary relation, used by
`RelSeries`. -/
abbrev relationSetRel {α : Type*} (rel : α → α → Prop) : SetRel α α :=
  {p | rel p.1 p.2}

namespace RelationSeries

variable {α : Type*} {rel : α → α → Prop}

/-- A nontrivial closed relation series. -/
def Closed (p : RelSeries (relationSetRel rel)) : Prop :=
  p.head = p.last ∧ 0 < p.length

theorem exists_of_transGen {a b : α} (h : TransGen rel a b) :
    ∃ p : RelSeries (relationSetRel rel),
      p.head = a ∧ p.last = b ∧ 0 < p.length := by
  induction h using Relation.TransGen.head_induction_on with
  | single hab =>
      let p :=
        (RelSeries.singleton (relationSetRel rel) _).snoc _
          (by simpa [relationSetRel] using hab)
      refine ⟨p, ?_, ?_, ?_⟩
      · simp [p]
      · simp [p]
      · simp [p]
  | head hac hcb ih =>
      rcases ih with ⟨p, hphead, hplast, hplen⟩
      let q := p.cons _ (by simpa [relationSetRel, hphead] using hac)
      refine ⟨q, ?_, ?_, ?_⟩
      · simp [q]
      · simpa [q] using hplast
      · simp [q]

theorem exists_closed_of_transGen_cycle {a : α}
    (h : TransGen rel a a) :
    ∃ p : RelSeries (relationSetRel rel), Closed (rel := rel) p := by
  rcases exists_of_transGen h with ⟨p, hphead, hplast, hplen⟩
  exact ⟨p, ⟨hphead.trans hplast.symm, hplen⟩⟩

theorem exists_closed_length
    (hex : ∃ p : RelSeries (relationSetRel rel), Closed (rel := rel) p) :
    ∃ n : ℕ, ∃ p : RelSeries (relationSetRel rel),
      Closed (rel := rel) p ∧ p.length = n := by
  rcases hex with ⟨p, hp⟩
  exact ⟨p.length, p, hp, rfl⟩

/-- The length of a shortest nontrivial closed relation series. -/
noncomputable def minimalClosedLength
    (hex : ∃ p : RelSeries (relationSetRel rel), Closed (rel := rel) p) : ℕ :=
  by
    classical
    exact Nat.find (exists_closed_length (rel := rel) hex)

/-- A shortest nontrivial closed relation series. -/
noncomputable def minimalClosedSeries
    (hex : ∃ p : RelSeries (relationSetRel rel), Closed (rel := rel) p) :
    RelSeries (relationSetRel rel) :=
  by
    classical
    exact Classical.choose (Nat.find_spec (exists_closed_length (rel := rel) hex))

theorem minimalClosedSeries_closed
    (hex : ∃ p : RelSeries (relationSetRel rel), Closed (rel := rel) p) :
    Closed (rel := rel) (minimalClosedSeries (rel := rel) hex) :=
  by
  classical
  exact
  (Classical.choose_spec
    (Nat.find_spec (exists_closed_length (rel := rel) hex))).1

theorem minimalClosedSeries_length
    (hex : ∃ p : RelSeries (relationSetRel rel), Closed (rel := rel) p) :
    (minimalClosedSeries (rel := rel) hex).length =
      minimalClosedLength (rel := rel) hex :=
  by
  classical
  exact
  (Classical.choose_spec
    (Nat.find_spec (exists_closed_length (rel := rel) hex))).2

theorem minimalClosedSeries_min
    (hex : ∃ p : RelSeries (relationSetRel rel), Closed (rel := rel) p)
    {p : RelSeries (relationSetRel rel)} (hp : Closed (rel := rel) p) :
    (minimalClosedSeries (rel := rel) hex).length ≤ p.length := by
  classical
  rw [minimalClosedSeries_length (rel := rel) hex]
  exact Nat.find_min' (exists_closed_length (rel := rel) hex) ⟨p, hp, rfl⟩

/-- Rotate a closed series so that the old position `i` becomes the head.

For a closed series `a₀ -> ... -> aₙ = a₀`, this is the same cyclic series
`aᵢ -> ... -> aₙ = a₀ -> ... -> aᵢ`. -/
noncomputable def rotateClosed
    (p : RelSeries (relationSetRel rel)) (hp : Closed (rel := rel) p)
    (i : Fin p.length) : RelSeries (relationSetRel rel) :=
  (p.drop i.castSucc).smash (p.take i.castSucc) (by
    simpa using hp.1.symm)

@[simp] theorem rotateClosed_length
    (p : RelSeries (relationSetRel rel)) (hp : Closed (rel := rel) p)
    (i : Fin p.length) :
    (rotateClosed (rel := rel) p hp i).length = p.length := by
  simp [rotateClosed]

theorem rotateClosed_closed
    (p : RelSeries (relationSetRel rel)) (hp : Closed (rel := rel) p)
    (i : Fin p.length) :
    Closed (rel := rel) (rotateClosed (rel := rel) p hp i) := by
  constructor
  · simp [rotateClosed]
  · simpa [rotateClosed_length (rel := rel) p hp i] using hp.2

@[simp] theorem rotateClosed_head
    (p : RelSeries (relationSetRel rel)) (hp : Closed (rel := rel) p)
    (i : Fin p.length) :
    (rotateClosed (rel := rel) p hp i).head = p i.castSucc := by
  simp [rotateClosed]

theorem rotateClosed_one
    (p : RelSeries (relationSetRel rel)) (hp : Closed (rel := rel) p)
    (i : Fin p.length) :
    (rotateClosed (rel := rel) p hp i)
        ⟨1, by
          rw [rotateClosed_length (rel := rel) p hp i]
          exact Nat.succ_lt_succ hp.2⟩ =
      p i.succ := by
  classical
  simp [rotateClosed, RelSeries.smash, RelSeries.drop, Fin.addCases]
  by_cases h : 1 < p.length - i.1
  · simp [h]
    apply congrArg p.toFun
    ext
    simp [Nat.add_comm]
  · simp [h]
    have hi_last : i.1 + 1 = p.length := by omega
    have hi_succ : i.succ = (Fin.last p.length) := by
      ext
      simpa [Fin.val_succ] using hi_last
    simp [RelSeries.take]
    change p ⟨1 - (p.length - i.1), by omega⟩ = p i.succ
    rw [show (⟨1 - (p.length - i.1), by omega⟩ : Fin (p.length + 1)) =
        (0 : Fin (p.length + 1)) by
      ext
      simp
      omega]
    rw [hi_succ]
    change p.head = p.last
    exact hp.1

theorem rotateClosed_apply_forward
    (p : RelSeries (relationSetRel rel)) (hp : Closed (rel := rel) p)
    {i j : Fin p.length} (hij : i.1 ≤ j.1) :
    (rotateClosed (rel := rel) p hp i)
        ⟨j.1 - i.1, by
          rw [rotateClosed_length (rel := rel) p hp i]
          omega⟩ =
      p j.castSucc := by
  classical
  simp [rotateClosed, RelSeries.smash, RelSeries.drop, Fin.addCases]
  have hif : j.1 - i.1 < p.length - i.1 := by omega
  simp [hif]
  apply congrArg p.toFun
  ext
  simp
  omega

theorem rotateClosed_apply_wrapped
    (p : RelSeries (relationSetRel rel)) (hp : Closed (rel := rel) p)
    {i j : Fin p.length} (hji : j.1 ≤ i.1) :
    (rotateClosed (rel := rel) p hp i)
        ⟨p.length - i.1 + j.1, by
          rw [rotateClosed_length (rel := rel) p hp i]
          omega⟩ =
      p j.castSucc := by
  classical
  simp [rotateClosed, RelSeries.smash, RelSeries.drop, RelSeries.take, Fin.addCases]
  apply congrArg p.toFun
  ext
  simp

end RelationSeries

omit [Fintype V] in
theorem linkageDependency_irrefl
    (R : PerfectPathPacking G A B) (v : V) :
    ¬ LinkageDependency R v v := by
  classical
  intro hvv
  rcases hvv with hvvRow | hvvCross
  · rcases hvvRow with ⟨_r, _hv₁, _hv₂, _hbefore, hne⟩
    exact hne rfl
  · rcases hvvCross with
      ⟨r, r', hrr', hv_r, hv_r', _w, _hw, _hbefore, _hne, _hadj⟩
    exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hrr') hv_r hv_r'

omit [Fintype V] in
/-- Iterated form of Appendix B, Observation B.1.  If `x` is strictly before
`y` on a linkage row, then every dependency path starting at `y` can instead
start at `x`. -/
theorem transGen_linkageDependency_of_before
    {R : PerfectPathPacking G A B} {x y z : V} {r : R.Index}
    (hxy : (R.path r).Before x y) (hxy_ne : x ≠ y)
    (hyz : Relation.TransGen (LinkageDependency R) y z) :
    Relation.TransGen (LinkageDependency R) x z := by
  induction hyz with
  | single hyz =>
      exact Relation.TransGen.single
        (linkageDependency_of_before_of_linkageDependency hxy hxy_ne hyz)
  | tail hyw hwz ih =>
      exact Relation.TransGen.tail ih hwz

omit [Fintype V] in
theorem transGen_cycle_of_before_of_reflTransGen
    {R : PerfectPathPacking G A B} {x y : V} {r : R.Index}
    (hxy : (R.path r).Before x y) (hxy_ne : x ≠ y)
    (hyx : Relation.ReflTransGen (LinkageDependency R) y x) :
    Relation.TransGen (LinkageDependency R) x x := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hyx with hyx_eq | hyx_tr
  · exact False.elim (hxy_ne hyx_eq)
  · exact transGen_linkageDependency_of_before hxy hxy_ne hyx_tr

omit [Fintype V] in
/-- Data carried by a type-2 edge of the dependency digraph. -/
structure Type2DependencyData
    (R : PerfectPathPacking G A B) (u v : V) where
  row : R.Index
  row' : R.Index
  row_ne : row ≠ row'
  u_mem : u ∈ (R.path row).vertexSet
  v_mem : v ∈ (R.path row').vertexSet
  witness : V
  witness_mem : witness ∈ (R.path row).vertexSet
  before_witness : (R.path row).Before u witness
  u_ne_witness : u ≠ witness
  adj : G.Adj witness v

namespace Type2DependencyData

variable {R : PerfectPathPacking G A B} {u v : V}

omit [Fintype V] in
theorem exists_of_dependency_of_not_type1
    (huv : LinkageDependency R u v)
    (hnot :
      ¬ ∃ r : R.Index,
        u ∈ (R.path r).vertexSet ∧
          v ∈ (R.path r).vertexSet ∧
            (R.path r).Before u v ∧ u ≠ v) :
    Nonempty (Type2DependencyData R u v) := by
  rcases huv with htype1 | htype2
  · exact False.elim (hnot htype1)
  · rcases htype2 with
      ⟨r, r', hrr', hu, hv, w, hw, huw, hne, hadj⟩
    exact ⟨{
      row := r
      row' := r'
      row_ne := hrr'
      u_mem := hu
      v_mem := hv
      witness := w
      witness_mem := hw
      before_witness := huw
      u_ne_witness := hne
      adj := hadj
    }⟩

end Type2DependencyData

omit [Fintype V] in
/-- A shortest closed dependency series cannot start with a type-1 edge.  This
is the formal first-shortcut step of Appendix B: if the first edge only advances
on a row, Observation B.1 skips the next vertex and gives a shorter closed
series. -/
theorem closed_dependency_series_not_first_type1_of_minimal
    {R : PerfectPathPacking G A B}
    (p : RelSeries (relationSetRel (LinkageDependency R)))
    (hpclosed : RelationSeries.Closed (rel := LinkageDependency R) p)
    (hmin :
      ∀ q : RelSeries (relationSetRel (LinkageDependency R)),
        RelationSeries.Closed (rel := LinkageDependency R) q →
          p.length ≤ q.length) :
    ¬ ∃ r : R.Index,
      p.head ∈ (R.path r).vertexSet ∧
        p ⟨1, Nat.succ_lt_succ hpclosed.2⟩ ∈ (R.path r).vertexSet ∧
          (R.path r).Before p.head
            (p ⟨1, Nat.succ_lt_succ hpclosed.2⟩) ∧
            p.head ≠ p ⟨1, Nat.succ_lt_succ hpclosed.2⟩ := by
  classical
  rintro ⟨r, hhead, hnext, hbefore, hne⟩
  have hpos : 0 < p.length := hpclosed.2
  have htwo : 2 ≤ p.length := by
    by_contra hnot
    have hle : p.length ≤ 1 := by omega
    have hlen : p.length = 1 := by omega
    have hnext_last :
        p ⟨1, by omega⟩ = p.last := by
      apply congrArg p
      apply Fin.ext
      simp [hlen]
    have hhead_eq_next : p.head = p ⟨1, by omega⟩ := by
      rw [hnext_last]
      exact hpclosed.1
    exact hne hhead_eq_next
  have hstep1 :
      LinkageDependency R (p ⟨1, by omega⟩) (p ⟨2, by omega⟩) := by
    exact p.step ⟨1, by omega⟩
  have hshortcut :
      LinkageDependency R p.head (p ⟨2, by omega⟩) :=
    linkageDependency_of_before_of_linkageDependency hbefore hne hstep1
  let tail := p.drop ⟨2, by omega⟩
  let q := tail.cons p.head (by simpa [tail, relationSetRel] using hshortcut)
  have hqclosed :
      RelationSeries.Closed (rel := LinkageDependency R) q := by
    constructor
    · simp [q, tail, hpclosed.1]
    · simp [q]
  have hq_lt : q.length < p.length := by
    have hq_len : q.length = p.length - 1 := by
      simp [q, tail]
      omega
    rw [hq_len]
    omega
  have hp_le_q := hmin q hqclosed
  omega

omit [Fintype V] in
/-- No edge of a shortest closed dependency series is a type-1 edge.
Rotating the closed series turns an arbitrary edge into the first edge, where
`closed_dependency_series_not_first_type1_of_minimal` applies. -/
theorem closed_dependency_series_no_type1_edge_of_minimal
    {R : PerfectPathPacking G A B}
    (p : RelSeries (relationSetRel (LinkageDependency R)))
    (hpclosed : RelationSeries.Closed (rel := LinkageDependency R) p)
    (hmin :
      ∀ q : RelSeries (relationSetRel (LinkageDependency R)),
        RelationSeries.Closed (rel := LinkageDependency R) q →
          p.length ≤ q.length)
    (i : Fin p.length) :
    ¬ ∃ r : R.Index,
      p i.castSucc ∈ (R.path r).vertexSet ∧
        p i.succ ∈ (R.path r).vertexSet ∧
          (R.path r).Before (p i.castSucc) (p i.succ) ∧
            p i.castSucc ≠ p i.succ := by
  classical
  let rot :=
    RelationSeries.rotateClosed (rel := LinkageDependency R) p hpclosed i
  have hrotclosed :
      RelationSeries.Closed (rel := LinkageDependency R) rot :=
    RelationSeries.rotateClosed_closed (rel := LinkageDependency R) p hpclosed i
  have hrotmin :
      ∀ q : RelSeries (relationSetRel (LinkageDependency R)),
        RelationSeries.Closed (rel := LinkageDependency R) q →
          rot.length ≤ q.length := by
    intro q hq
    simpa [rot, RelationSeries.rotateClosed_length (rel := LinkageDependency R) p hpclosed i]
      using hmin q hq
  have hnotFirst :=
    closed_dependency_series_not_first_type1_of_minimal
      (R := R) rot hrotclosed hrotmin
  intro htype
  apply hnotFirst
  simpa [rot, RelationSeries.rotateClosed_head,
    RelationSeries.rotateClosed_one (rel := LinkageDependency R) p hpclosed i] using htype

omit [Fintype V] in
/-- In a shortest closed dependency series, the head cannot be strictly before
any later non-final vertex of the same linkage row.  Otherwise Observation B.1
shortcuts from the head to the successor of that later vertex, deleting a
nonempty prefix of the closed series. -/
theorem closed_dependency_series_not_head_before_later_same_row_of_minimal
    {R : PerfectPathPacking G A B}
    (p : RelSeries (relationSetRel (LinkageDependency R)))
    (hpclosed : RelationSeries.Closed (rel := LinkageDependency R) p)
    (hmin :
      ∀ q : RelSeries (relationSetRel (LinkageDependency R)),
        RelationSeries.Closed (rel := LinkageDependency R) q →
          p.length ≤ q.length)
    (i : Fin p.length) (hi_pos : 0 < i.1) :
    ¬ ∃ r : R.Index,
      p.head ∈ (R.path r).vertexSet ∧
        p i.castSucc ∈ (R.path r).vertexSet ∧
          (R.path r).Before p.head (p i.castSucc) ∧
            p.head ≠ p i.castSucc := by
  classical
  rintro ⟨r, hhead, hi, hbefore, hne⟩
  have hstep :
      LinkageDependency R (p i.castSucc) (p i.succ) := by
    simpa [relationSetRel] using p.step i
  have hshortcut :
      LinkageDependency R p.head (p i.succ) :=
    linkageDependency_of_before_of_linkageDependency hbefore hne hstep
  let tail := p.drop i.succ
  let q := tail.cons p.head (by simpa [tail, relationSetRel] using hshortcut)
  have hqclosed :
      RelationSeries.Closed (rel := LinkageDependency R) q := by
    constructor
    · simp [q, tail, hpclosed.1]
    · simp [q, tail]
  have hq_lt : q.length < p.length := by
    have hq_len : q.length = p.length - i.1 := by
      simp [q, tail]
      omega
    rw [hq_len]
    omega
  have hp_le_q := hmin q hqclosed
  omega

omit [Fintype V] in
/-- A shortest closed dependency series has no repeated non-final vertex.
If positions `i < j < length` carried the same vertex, rotating at `i` and
taking the prefix ending at `j` would give a shorter nontrivial closed series. -/
theorem closed_dependency_series_no_repeated_forward_of_minimal
    {R : PerfectPathPacking G A B}
    (p : RelSeries (relationSetRel (LinkageDependency R)))
    (hpclosed : RelationSeries.Closed (rel := LinkageDependency R) p)
    (hmin :
      ∀ q : RelSeries (relationSetRel (LinkageDependency R)),
        RelationSeries.Closed (rel := LinkageDependency R) q →
          p.length ≤ q.length)
    {i j : Fin p.length} (hij : i.1 < j.1) :
    p i.castSucc ≠ p j.castSucc := by
  classical
  intro heq
  let rot :=
    RelationSeries.rotateClosed (rel := LinkageDependency R) p hpclosed i
  let k : Fin (rot.length + 1) :=
    ⟨j.1 - i.1, by
      simp [rot]
      omega⟩
  let q := rot.take k
  have hrotHead : rot.head = p i.castSucc := by
    simp [rot]
  have hrotK : rot k = p j.castSucc := by
    simpa [rot, k] using
      RelationSeries.rotateClosed_apply_forward
        (rel := LinkageDependency R) p hpclosed (i := i) (j := j) hij.le
  have hqclosed :
      RelationSeries.Closed (rel := LinkageDependency R) q := by
    constructor
    · simp [q, hrotHead, hrotK, heq]
    · simp [q, k, rot]
      omega
  have hq_lt : q.length < p.length := by
    simp [q, k, rot]
    omega
  have hp_le_q := hmin q hqclosed
  omega

omit [Fintype V] in
/-- The type-2 source rows of a shortest closed dependency series are
pairwise distinct.  If two cycle vertices lay on the same row, the path order
between them and Observation B.1 would shortcut a nonempty arc of the cycle. -/
theorem closed_dependency_series_type2_rows_injective_of_minimal
    {R : PerfectPathPacking G A B}
    (p : RelSeries (relationSetRel (LinkageDependency R)))
    (hpclosed : RelationSeries.Closed (rel := LinkageDependency R) p)
    (hmin :
      ∀ q : RelSeries (relationSetRel (LinkageDependency R)),
        RelationSeries.Closed (rel := LinkageDependency R) q →
          p.length ≤ q.length)
    (D : ∀ i : Fin p.length,
      Type2DependencyData R (p i.castSucc) (p i.succ)) :
    Function.Injective fun i : Fin p.length => (D i).row := by
  classical
  have no_lt :
      ∀ {a b : Fin p.length}, a.1 < b.1 →
        (D a).row = (D b).row → False := by
    intro a b hab hrow
    have hne :
        p a.castSucc ≠ p b.castSucc :=
      closed_dependency_series_no_repeated_forward_of_minimal
        (R := R) p hpclosed hmin hab
    let Prow := R.path (D a).row
    have ha_mem : p a.castSucc ∈ Prow.vertexSet := by
      simpa [Prow] using (D a).u_mem
    have hb_mem : p b.castSucc ∈ Prow.vertexSet := by
      simpa [Prow, hrow] using (D b).u_mem
    have horder :
        Prow.Before (p a.castSucc) (p b.castSucc) ∨
          Prow.Before (p b.castSucc) (p a.castSucc) := by
      rcases le_total (Prow.vertexIndex (p a.castSucc))
          (Prow.vertexIndex (p b.castSucc)) with hle | hle
      · exact Or.inl ((Prow.before_iff_vertexIndex_le).2
          ⟨ha_mem, hb_mem, hle⟩)
      · exact Or.inr ((Prow.before_iff_vertexIndex_le).2
          ⟨hb_mem, ha_mem, hle⟩)
    rcases horder with hab_before | hba_before
    · let rot :=
        RelationSeries.rotateClosed (rel := LinkageDependency R) p hpclosed a
      have hrotclosed :
          RelationSeries.Closed (rel := LinkageDependency R) rot :=
        RelationSeries.rotateClosed_closed
          (rel := LinkageDependency R) p hpclosed a
      have hrotmin :
          ∀ q : RelSeries (relationSetRel (LinkageDependency R)),
            RelationSeries.Closed (rel := LinkageDependency R) q →
              rot.length ≤ q.length := by
        intro q hq
        simpa [rot,
          RelationSeries.rotateClosed_length
            (rel := LinkageDependency R) p hpclosed a] using hmin q hq
      let k : Fin rot.length :=
        ⟨b.1 - a.1, by
          simp [rot]
          omega⟩
      have hk_pos : 0 < k.1 := by
        simp [k]
        exact hab
      have hnot :=
        closed_dependency_series_not_head_before_later_same_row_of_minimal
          (R := R) rot hrotclosed hrotmin k hk_pos
      have hrotHead : rot.head = p a.castSucc := by
        simp [rot]
      have hrotK : rot k.castSucc = p b.castSucc := by
        simpa [rot, k] using
          RelationSeries.rotateClosed_apply_forward
            (rel := LinkageDependency R) p hpclosed (i := a) (j := b) hab.le
      apply hnot
      refine ⟨(D a).row, ?_, ?_, ?_, ?_⟩
      · simpa [hrotHead, Prow] using ha_mem
      · simpa [hrotK, Prow] using hb_mem
      · simpa [hrotHead, hrotK, Prow] using hab_before
      · simpa [hrotHead, hrotK] using hne
    · let rot :=
        RelationSeries.rotateClosed (rel := LinkageDependency R) p hpclosed b
      have hrotclosed :
          RelationSeries.Closed (rel := LinkageDependency R) rot :=
        RelationSeries.rotateClosed_closed
          (rel := LinkageDependency R) p hpclosed b
      have hrotmin :
          ∀ q : RelSeries (relationSetRel (LinkageDependency R)),
            RelationSeries.Closed (rel := LinkageDependency R) q →
              rot.length ≤ q.length := by
        intro q hq
        simpa [rot,
          RelationSeries.rotateClosed_length
            (rel := LinkageDependency R) p hpclosed b] using hmin q hq
      let k : Fin rot.length :=
        ⟨p.length - b.1 + a.1, by
          simp [rot]
          omega⟩
      have hk_pos : 0 < k.1 := by
        simp [k]
      have hnot :=
        closed_dependency_series_not_head_before_later_same_row_of_minimal
          (R := R) rot hrotclosed hrotmin k hk_pos
      have hrotHead : rot.head = p b.castSucc := by
        simp [rot]
      have hrotK : rot k.castSucc = p a.castSucc := by
        simpa [rot, k] using
          RelationSeries.rotateClosed_apply_wrapped
            (rel := LinkageDependency R) p hpclosed
            (i := b) (j := a) (le_of_lt hab)
      apply hnot
      refine ⟨(D b).row, ?_, ?_, ?_, ?_⟩
      · simpa [hrotHead] using (D b).u_mem
      · simpa [hrotK, hrow] using (D a).u_mem
      · simpa [hrotHead, hrotK, Prow, hrow] using hba_before
      · exact fun h => hne (by simpa [hrotHead, hrotK] using h.symm)
  intro i j hrow
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact no_lt hij hrow
  · exact no_lt hji hrow.symm

/-- A finite cyclic list of type-2 dependency edges in a linkage.

The index set is abstract rather than `Fin n`: the permutation `next` records
the cyclic successor.  This is the exact data used in Appendix B after
Observation B.3 has shown that a minimal directed dependency cycle has one
vertex on each of several distinct linkage rows, so every cycle edge is type 2.
-/
structure LinkageDependencyCycle (R : PerfectPathPacking G A B) where
  /-- The finite set of positions of the cycle. -/
  Index : Type
  /-- The cycle is nonempty. -/
  [indexNonempty : Nonempty Index]
  /-- The cycle index type is finite. -/
  [indexFintype : Fintype Index]
  /-- Decidable equality for cycle indices. -/
  [indexDecidableEq : DecidableEq Index]
  /-- The cyclic successor permutation. -/
  next : Equiv.Perm Index
  /-- The dependency-cycle vertex at a position. -/
  vertex : Index → V
  /-- The linkage row containing that vertex. -/
  row : Index → R.Index
  /-- Distinct cycle positions lie on distinct rows. -/
  row_injective : Function.Injective row
  /-- The cycle vertex lies on its row. -/
  vertex_mem : ∀ i, vertex i ∈ (R.path (row i)).vertexSet
  /-- The type-2 witness on the same row as `vertex i`. -/
  witness : Index → V
  /-- The witness lies on the same row. -/
  witness_mem : ∀ i, witness i ∈ (R.path (row i)).vertexSet
  /-- The witness is strictly after the cycle vertex on the row. -/
  before_witness : ∀ i, (R.path (row i)).Before (vertex i) (witness i)
  /-- Strictness of `before_witness`. -/
  vertex_ne_witness : ∀ i, vertex i ≠ witness i
  /-- A type-2 edge goes from each cycle position to the next row. -/
  row_next_ne : ∀ i, row i ≠ row (next i)
  /-- The ambient edge witnessing the type-2 dependency to the next vertex. -/
  adj_next : ∀ i, G.Adj (witness i) (vertex (next i))

namespace LinkageDependencyCycle

variable {R : PerfectPathPacking G A B}

instance (C : LinkageDependencyCycle R) : Nonempty C.Index := C.indexNonempty
instance (C : LinkageDependencyCycle R) : Fintype C.Index := C.indexFintype
instance (C : LinkageDependencyCycle R) : DecidableEq C.Index := C.indexDecidableEq

omit [Fintype V] in
/-- Package a cyclic family of type-2 dependency data as the abstract
dependency-cycle object used by the rerouting proof. -/
noncomputable def ofType2Family
    {ι : Type} [Nonempty ι] [Fintype ι] [DecidableEq ι]
    (next : Equiv.Perm ι) (vertex : ι → V)
    (D : ∀ i : ι, Type2DependencyData R (vertex i) (vertex (next i)))
    (hrowinj : Function.Injective fun i : ι => (D i).row) :
    LinkageDependencyCycle R where
  Index := ι
  next := next
  vertex := vertex
  row := fun i => (D i).row
  row_injective := hrowinj
  vertex_mem := fun i => (D i).u_mem
  witness := fun i => (D i).witness
  witness_mem := fun i => (D i).witness_mem
  before_witness := fun i => (D i).before_witness
  vertex_ne_witness := fun i => (D i).u_ne_witness
  row_next_ne := by
    intro i
    have htarget : (D i).row' = (D (next i)).row := by
      by_contra hne
      exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hne)
        (D i).v_mem (D (next i)).u_mem
    simpa [htarget] using (D i).row_ne
  adj_next := fun i => (D i).adj

/-- The rows used by a dependency cycle. -/
noncomputable def rowSet (C : LinkageDependencyCycle R) : Finset R.Index := by
  classical
  exact Finset.univ.image C.row

omit [Fintype V] in
theorem row_mem_rowSet (C : LinkageDependencyCycle R) (i : C.Index) :
    C.row i ∈ C.rowSet := by
  classical
  rw [rowSet]
  exact Finset.mem_image.2 ⟨i, by simp, rfl⟩

omit [Fintype V] in
theorem row_not_mem_complement {C : LinkageDependencyCycle R}
    {j : R.Index} (hj : j ∉ C.rowSet) (i : C.Index) :
    j ≠ C.row i := by
  intro h
  exact hj (by simpa [h] using C.row_mem_rowSet i)

/-- The predecessor of a cycle index. -/
abbrev pred (C : LinkageDependencyCycle R) (i : C.Index) : C.Index :=
  C.next.symm i

omit [Fintype V] in
theorem next_pred (C : LinkageDependencyCycle R) (i : C.Index) :
    C.next (C.pred i) = i := by
  simp [pred]

omit [Fintype V] in
theorem row_ne_pred (C : LinkageDependencyCycle R) (i : C.Index) :
    C.row i ≠ C.row (C.pred i) := by
  intro h
  exact C.row_next_ne (C.pred i) (by simpa [C.next_pred i] using h.symm)

/-- The rerouted path beginning on row `i` and ending on the predecessor row.
It follows the prefix of row `i`, crosses the witness edge from the predecessor
row, and then follows the predecessor suffix to its terminal vertex. -/
noncomputable def reroutedPath (C : LinkageDependencyCycle R)
    (i : C.Index) : GraphPath G := by
  classical
  let p := C.pred i
  have hrow_ne : C.row i ≠ C.row p := by
    simpa [p] using C.row_ne_pred i
  have hdisj :
      Disjoint (R.path (C.row i)).vertexSet (R.path (C.row p)).vertexSet :=
    R.toPathPacking.node_disjoint hrow_ne
  have hadj : G.Adj (C.vertex i) (C.witness p) := by
    have h := C.adj_next p
    simpa [p, C.next_pred i] using h.symm
  exact GraphPath.crossPrefixSuffix
    (R.path (C.row i)) (R.path (C.row p))
    (C.vertex_mem i) (C.witness_mem p) hdisj hadj

omit [Fintype V] in
@[simp] theorem reroutedPath_source (C : LinkageDependencyCycle R)
    (i : C.Index) :
    (C.reroutedPath i).source = (R.path (C.row i)).source := by
  rfl

omit [Fintype V] in
@[simp] theorem reroutedPath_target (C : LinkageDependencyCycle R)
    (i : C.Index) :
    (C.reroutedPath i).target = (R.path (C.row (C.pred i))).target := by
  rfl

omit [Fintype V] in
theorem reroutedPath_vertexSet_subset_parts (C : LinkageDependencyCycle R)
    (i : C.Index) :
    (C.reroutedPath i).vertexSet ⊆
      ((R.path (C.row i)).takeUntil (C.vertex_mem i)).vertexSet ∪
        ((R.path (C.row (C.pred i))).dropUntil (C.witness_mem (C.pred i))).vertexSet := by
  classical
  let p := C.pred i
  have hrow_ne : C.row i ≠ C.row p := by
    simpa [p] using C.row_ne_pred i
  have hdisj :
      Disjoint (R.path (C.row i)).vertexSet (R.path (C.row p)).vertexSet :=
    R.toPathPacking.node_disjoint hrow_ne
  have hadj : G.Adj (C.vertex i) (C.witness p) := by
    have h := C.adj_next p
    simpa [p, C.next_pred i] using h.symm
  simpa [reroutedPath, p] using
    (GraphPath.crossPrefixSuffix_vertexSet_subset_parts
      (R.path (C.row i)) (R.path (C.row p))
      (C.vertex_mem i) (C.witness_mem p) hdisj hadj)

omit [Fintype V] in
theorem reroutedPath_cross_edge_mem (C : LinkageDependencyCycle R)
    (i : C.Index) :
    s(C.vertex i, C.witness (C.pred i)) ∈ (C.reroutedPath i).edgeSet := by
  classical
  let p := C.pred i
  have hrow_ne : C.row i ≠ C.row p := by
    simpa [p] using C.row_ne_pred i
  have hdisj :
      Disjoint (R.path (C.row i)).vertexSet (R.path (C.row p)).vertexSet :=
    R.toPathPacking.node_disjoint hrow_ne
  have hadj : G.Adj (C.vertex i) (C.witness p) := by
    have h := C.adj_next p
    simpa [p, C.next_pred i] using h.symm
  rcases GraphPath.exists_crossPrefixSuffix
      (R.path (C.row i)) (R.path (C.row p))
      (C.vertex_mem i) (C.witness_mem p) hdisj hadj with
    ⟨Q, hQsource, hQtarget, hQsubset, hQedge⟩
  -- The concrete rerouted path is the same construction used in
  -- `exists_crossPrefixSuffix`; unfold it to recover the edge membership.
  simpa [reroutedPath, p, hrow_ne, hdisj, hadj] using
    (by
      let pref := (R.path (C.row i)).takeUntil (C.vertex_mem i)
      let edge := GraphPath.edgePath hadj
      let suffix := (R.path (C.row p)).dropUntil (C.witness_mem p)
      have hprefix_edge :
          ∀ ⦃z : V⦄, z ∈ pref.vertexSet → z ∈ edge.vertexSet → z = pref.target := by
        intro z hzPrefix hzEdge
        have hzEdge' : z = C.vertex i ∨ z = C.witness p := by
          simpa [edge] using hzEdge
        rcases hzEdge' with hz_eq_v | hz_eq_w
        · simp [pref, hz_eq_v]
        · have hzRowI : z ∈ (R.path (C.row i)).vertexSet :=
            (R.path (C.row i)).takeUntil_vertexSet_subset (C.vertex_mem i) hzPrefix
          have hzRowP : z ∈ (R.path (C.row p)).vertexSet := by
            simpa [hz_eq_w] using C.witness_mem p
          exact False.elim (Finset.disjoint_left.mp hdisj hzRowI hzRowP)
      let first :=
        pref.appendClean edge (by simp [pref, edge])
          hprefix_edge
      have hedgeEdge : s(C.vertex i, C.witness p) ∈ edge.edgeSet := by
        simp [edge]
      have hedgeFirst : s(C.vertex i, C.witness p) ∈ first.edgeSet := by
        exact
          (GraphPath.appendWithEq_right_edgeSet_subset pref edge
            (by simp [pref, edge])
            (pref.appendWithEq_isPath_of_inter_subset_target edge
              (by simp [pref, edge]) hprefix_edge) hedgeEdge)
      have hfirst_suffix :
          ∀ ⦃z : V⦄, z ∈ first.vertexSet → z ∈ suffix.vertexSet → z = first.target := by
        intro z hzFirst hzSuffix
        have hzFirstSplit :=
          GraphPath.appendWithEq_vertexSet_subset pref edge (by simp [pref, edge])
            (pref.appendWithEq_isPath_of_inter_subset_target edge
              (by simp [pref, edge]) hprefix_edge) hzFirst
        have hzRowP : z ∈ (R.path (C.row p)).vertexSet :=
          (R.path (C.row p)).dropUntil_vertexSet_subset (C.witness_mem p) hzSuffix
        rcases Finset.mem_union.1 hzFirstSplit with hzPrefix | hzEdge
        · have hzRowI : z ∈ (R.path (C.row i)).vertexSet :=
            (R.path (C.row i)).takeUntil_vertexSet_subset (C.vertex_mem i) hzPrefix
          exact False.elim (Finset.disjoint_left.mp hdisj hzRowI hzRowP)
        · have hzEdge' : z = C.vertex i ∨ z = C.witness p := by
            simpa [edge] using hzEdge
          rcases hzEdge' with rfl | rfl
          · exact False.elim
              (Finset.disjoint_left.mp hdisj (C.vertex_mem i) hzRowP)
          · simp [first, edge]
      exact
        (GraphPath.appendWithEq_left_edgeSet_subset first suffix
          (by simp [first, suffix, edge])
          (first.appendWithEq_isPath_of_inter_subset_target suffix
            (by simp [first, suffix, edge]) hfirst_suffix) hedgeFirst))

omit [Fintype V] in
theorem reroutedPath_nodeDisjoint_original
    (C : LinkageDependencyCycle R) (i : C.Index)
    {j : R.Index} (hj : j ∉ C.rowSet) :
    GraphPath.NodeDisjoint (C.reroutedPath i) (R.path j) := by
  classical
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro z hzCycle hzOrig
  have hzSplit := C.reroutedPath_vertexSet_subset_parts i hzCycle
  rcases Finset.mem_union.1 hzSplit with hzPrefix | hzSuffix
  · have hzRow : z ∈ (R.path (C.row i)).vertexSet :=
      (R.path (C.row i)).takeUntil_vertexSet_subset (C.vertex_mem i) hzPrefix
    have hne : C.row i ≠ j := by
      intro h
      exact hj (by simpa [← h] using C.row_mem_rowSet i)
    exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hne) hzRow hzOrig
  · have hzRow : z ∈ (R.path (C.row (C.pred i))).vertexSet :=
      (R.path (C.row (C.pred i))).dropUntil_vertexSet_subset
        (C.witness_mem (C.pred i)) hzSuffix
    have hne : C.row (C.pred i) ≠ j := by
      intro h
      exact hj (by simpa [← h] using C.row_mem_rowSet (C.pred i))
    exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hne) hzRow hzOrig

omit [Fintype V] in
theorem reroutedPath_nodeDisjoint
    (C : LinkageDependencyCycle R) {i j : C.Index} (hij : i ≠ j) :
    GraphPath.NodeDisjoint (C.reroutedPath i) (C.reroutedPath j) := by
  classical
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro z hzi hzj
  have hziSplit := C.reroutedPath_vertexSet_subset_parts i hzi
  have hzjSplit := C.reroutedPath_vertexSet_subset_parts j hzj
  rcases Finset.mem_union.1 hziSplit with hziPrefix | hziSuffix
  · rcases Finset.mem_union.1 hzjSplit with hzjPrefix | hzjSuffix
    · have hrow_ne : C.row i ≠ C.row j := by
        intro hrow
        exact hij (C.row_injective hrow)
      exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hrow_ne)
        ((R.path (C.row i)).takeUntil_vertexSet_subset (C.vertex_mem i) hziPrefix)
        ((R.path (C.row j)).takeUntil_vertexSet_subset (C.vertex_mem j) hzjPrefix)
    · by_cases hpj : C.pred j = i
      · have hzjSuffix' :
            z ∈ ((R.path (C.row i)).dropUntil (C.witness_mem i)).vertexSet := by
          simpa [hpj] using hzjSuffix
        have hdisj :=
          GraphPath.takeUntil_disjoint_dropUntil_of_before_ne
            (R.path (C.row i)) (C.vertex_mem i) (C.witness_mem i)
            (C.before_witness i) (C.vertex_ne_witness i)
        exact Finset.disjoint_left.mp hdisj hziPrefix hzjSuffix'
      · have hrow_ne : C.row i ≠ C.row (C.pred j) := by
          intro hrow
          exact hpj (C.row_injective hrow.symm)
        exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hrow_ne)
          ((R.path (C.row i)).takeUntil_vertexSet_subset (C.vertex_mem i) hziPrefix)
          ((R.path (C.row (C.pred j))).dropUntil_vertexSet_subset
            (C.witness_mem (C.pred j)) hzjSuffix)
  · rcases Finset.mem_union.1 hzjSplit with hzjPrefix | hzjSuffix
    · by_cases hpi : C.pred i = j
      · have hziSuffix' :
            z ∈ ((R.path (C.row j)).dropUntil (C.witness_mem j)).vertexSet := by
          simpa [hpi] using hziSuffix
        have hdisj :=
          GraphPath.takeUntil_disjoint_dropUntil_of_before_ne
            (R.path (C.row j)) (C.vertex_mem j) (C.witness_mem j)
            (C.before_witness j) (C.vertex_ne_witness j)
        exact Finset.disjoint_left.mp hdisj.symm hziSuffix' hzjPrefix
      · have hrow_ne : C.row (C.pred i) ≠ C.row j := by
          intro hrow
          exact hpi (C.row_injective hrow)
        exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hrow_ne)
          ((R.path (C.row (C.pred i))).dropUntil_vertexSet_subset
            (C.witness_mem (C.pred i)) hziSuffix)
          ((R.path (C.row j)).takeUntil_vertexSet_subset (C.vertex_mem j) hzjPrefix)
    · have hpred_ne : C.pred i ≠ C.pred j := by
        intro hpred
        apply hij
        have hnext := congrArg C.next hpred
        simpa [C.next_pred i, C.next_pred j] using hnext
      have hrow_ne : C.row (C.pred i) ≠ C.row (C.pred j) := by
        intro hrow
        exact hpred_ne (C.row_injective hrow)
      exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hrow_ne)
        ((R.path (C.row (C.pred i))).dropUntil_vertexSet_subset
          (C.witness_mem (C.pred i)) hziSuffix)
        ((R.path (C.row (C.pred j))).dropUntil_vertexSet_subset
          (C.witness_mem (C.pred j)) hzjSuffix)

/-- The index type of the linkage obtained by rerouting a dependency cycle.
Cycle rows are indexed by the cycle positions; all rows outside the cycle are
kept with their original row index. -/
abbrev RerouteIndex (C : LinkageDependencyCycle R) :=
  C.Index ⊕ {j : R.Index // j ∉ C.rowSet}

/-- The original row that supplies the source endpoint of a rerouted path. -/
def sourceRow (C : LinkageDependencyCycle R) : C.RerouteIndex → R.Index
  | Sum.inl i => C.row i
  | Sum.inr j => j.1

/-- The original row that supplies the target endpoint of a rerouted path. -/
def targetRow (C : LinkageDependencyCycle R) : C.RerouteIndex → R.Index
  | Sum.inl i => C.row (C.pred i)
  | Sum.inr j => j.1

omit [Fintype V] in
theorem sourceRow_injective (C : LinkageDependencyCycle R) :
    Function.Injective C.sourceRow := by
  classical
  intro x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          exact congrArg Sum.inl (C.row_injective hxy)
      | inr j =>
          have hj : j.1 = C.row i := by simpa [sourceRow] using hxy.symm
          exact False.elim (j.2 (by rw [hj]; exact C.row_mem_rowSet i))
  | inr i =>
      cases y with
      | inl j =>
          have hi : i.1 = C.row j := by simpa [sourceRow] using hxy
          exact False.elim (i.2 (by rw [hi]; exact C.row_mem_rowSet j))
      | inr j =>
          exact congrArg Sum.inr (Subtype.ext hxy)

omit [Fintype V] in
theorem sourceRow_surjective (C : LinkageDependencyCycle R) :
    Function.Surjective C.sourceRow := by
  classical
  intro r
  by_cases hr : r ∈ C.rowSet
  · rw [rowSet] at hr
    rcases Finset.mem_image.1 hr with ⟨i, _hi, hi⟩
    exact ⟨Sum.inl i, by simpa [sourceRow] using hi⟩
  · exact ⟨Sum.inr ⟨r, hr⟩, rfl⟩

omit [Fintype V] in
theorem sourceRow_bijective (C : LinkageDependencyCycle R) :
    Function.Bijective C.sourceRow :=
  ⟨C.sourceRow_injective, C.sourceRow_surjective⟩

omit [Fintype V] in
theorem targetRow_injective (C : LinkageDependencyCycle R) :
    Function.Injective C.targetRow := by
  classical
  intro x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          have hpred : C.pred i = C.pred j := C.row_injective hxy
          apply congrArg Sum.inl
          have hnext := congrArg C.next hpred
          simpa [C.next_pred i, C.next_pred j] using hnext
      | inr j =>
          have hj : j.1 = C.row (C.pred i) := by simpa [targetRow] using hxy.symm
          exact False.elim
            (j.2 (by rw [hj]; exact C.row_mem_rowSet (C.pred i)))
  | inr i =>
      cases y with
      | inl j =>
          have hi : i.1 = C.row (C.pred j) := by simpa [targetRow] using hxy
          exact False.elim
            (i.2 (by rw [hi]; exact C.row_mem_rowSet (C.pred j)))
      | inr j =>
          exact congrArg Sum.inr (Subtype.ext hxy)

omit [Fintype V] in
theorem targetRow_surjective (C : LinkageDependencyCycle R) :
    Function.Surjective C.targetRow := by
  classical
  intro r
  by_cases hr : r ∈ C.rowSet
  · rw [rowSet] at hr
    rcases Finset.mem_image.1 hr with ⟨i, _hi, hi⟩
    refine ⟨Sum.inl (C.next i), ?_⟩
    have hpred_next : C.pred (C.next i) = i := by simp [pred]
    simpa [targetRow, hpred_next] using hi
  · exact ⟨Sum.inr ⟨r, hr⟩, rfl⟩

omit [Fintype V] in
theorem targetRow_bijective (C : LinkageDependencyCycle R) :
    Function.Bijective C.targetRow :=
  ⟨C.targetRow_injective, C.targetRow_surjective⟩

/-- The path family obtained by rerouting every cycle row and leaving all other
linkage rows unchanged. -/
noncomputable abbrev reroutedPathPacking
    (C : LinkageDependencyCycle R) : PathPacking G A B where
  Index := C.RerouteIndex
  path := fun x =>
    match x with
    | Sum.inl i => C.reroutedPath i
    | Sum.inr j => R.path j.1
  connects := by
    intro x
    cases x with
    | inl i =>
        exact Or.inl
          ⟨by simpa [sourceRow] using R.source_mem (C.row i),
            by simpa [targetRow] using R.target_mem (C.row (C.pred i))⟩
    | inr j =>
        exact Or.inl ⟨R.source_mem j.1, R.target_mem j.1⟩
  node_disjoint := by
    intro x y hxy
    cases x with
    | inl i =>
        cases y with
        | inl j =>
            exact C.reroutedPath_nodeDisjoint (by
              intro hij
              exact hxy (by simp [hij]))
        | inr j =>
            exact C.reroutedPath_nodeDisjoint_original i j.2
    | inr i =>
        cases y with
        | inl j =>
            simpa [GraphPath.NodeDisjoint] using
              (C.reroutedPath_nodeDisjoint_original j i.2).symm
        | inr j =>
            have hij : i.1 ≠ j.1 := by
              intro hij'
              exact hxy (congrArg Sum.inr (Subtype.ext hij'))
            exact R.toPathPacking.node_disjoint hij

omit [Fintype V] in
@[simp] theorem reroutedPathPacking_card
    (C : LinkageDependencyCycle R) :
    C.reroutedPathPacking.card = R.card := by
  classical
  dsimp [reroutedPathPacking, PathPacking.card, PerfectPathPacking.card]
  have hbij := C.sourceRow_bijective
  exact Fintype.card_congr (Equiv.ofBijective C.sourceRow hbij)

omit [Fintype V] in
@[simp] theorem reroutedPathPacking_path_inl
    (C : LinkageDependencyCycle R) (i : C.Index) :
    C.reroutedPathPacking.path (Sum.inl i) = C.reroutedPath i := rfl

omit [Fintype V] in
@[simp] theorem reroutedPathPacking_path_inr
    (C : LinkageDependencyCycle R) (j : {j : R.Index // j ∉ C.rowSet}) :
    C.reroutedPathPacking.path (Sum.inr j) = R.path j.1 := rfl

/-- The rerouted path packing is again perfect: sources are indexed by
`sourceRow`, targets by `targetRow`, and both row maps are bijective. -/
noncomputable def reroutedPerfectPathPacking
    (C : LinkageDependencyCycle R) : PerfectPathPacking G A B where
  toPathPacking := C.reroutedPathPacking
  source_mem := by
    intro x
    cases x with
    | inl i =>
        simpa [reroutedPathPacking] using R.source_mem (C.row i)
    | inr j =>
        simpa [reroutedPathPacking] using R.source_mem j.1
  target_mem := by
    intro x
    cases x with
    | inl i =>
        simpa [reroutedPathPacking] using R.target_mem (C.row (C.pred i))
    | inr j =>
        simpa [reroutedPathPacking] using R.target_mem j.1
  source_bijective := by
    classical
    have hcomp :
        Function.Bijective
          ((fun r : R.Index =>
              (⟨(R.path r).source, R.source_mem r⟩ : {v // v ∈ A})) ∘
            C.sourceRow) :=
      R.source_bijective.comp C.sourceRow_bijective
    convert hcomp using 1
    funext x
    apply Subtype.ext
    cases x with
    | inl i =>
        simp [reroutedPathPacking, sourceRow]
    | inr j =>
        simp [reroutedPathPacking, sourceRow]
  target_bijective := by
    classical
    have hcomp :
        Function.Bijective
          ((fun r : R.Index =>
              (⟨(R.path r).target, R.target_mem r⟩ : {v // v ∈ B})) ∘
            C.targetRow) :=
      R.target_bijective.comp C.targetRow_bijective
    convert hcomp using 1
    funext x
    apply Subtype.ext
    cases x with
    | inl i =>
        simp [reroutedPathPacking, targetRow]
    | inr j =>
        simp [reroutedPathPacking, targetRow]

omit [Fintype V] in
theorem reroutedPerfectPathPacking_cross_edge_mem
    (C : LinkageDependencyCycle R) (i : C.Index) :
    s(C.vertex i, C.witness (C.pred i)) ∈
      C.reroutedPerfectPathPacking.toPathPacking.edgeSet := by
  classical
  apply (C.reroutedPerfectPathPacking.toPathPacking.mem_edgeSet).2
  refine ⟨Sum.inl i, ?_⟩
  simpa [reroutedPerfectPathPacking, reroutedPathPacking] using
    C.reroutedPath_cross_edge_mem i

omit [Fintype V] in
theorem cross_edge_not_mem_original
    (C : LinkageDependencyCycle R) (i : C.Index) :
    s(C.vertex i, C.witness (C.pred i)) ∉ R.toPathPacking.edgeSet := by
  classical
  intro he
  rcases (R.toPathPacking.mem_edgeSet).1 he with ⟨r, her⟩
  have heWalk :
      s(C.vertex i, C.witness (C.pred i)) ∈ (R.path r).walk.edges := by
    exact List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using her)
  have hvertex_r : C.vertex i ∈ (R.path r).vertexSet := by
    have hsupport :
        C.vertex i ∈ (R.path r).walk.support :=
      (R.path r).walk.fst_mem_support_of_mem_edges heWalk
    simpa [GraphPath.vertexSet] using hsupport
  have hwitness_r : C.witness (C.pred i) ∈ (R.path r).vertexSet := by
    have hsupport :
        C.witness (C.pred i) ∈ (R.path r).walk.support :=
      (R.path r).walk.snd_mem_support_of_mem_edges heWalk
    simpa [GraphPath.vertexSet] using hsupport
  have hr_i : r = C.row i := by
    by_contra hne
    exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hne)
      hvertex_r (C.vertex_mem i)
  have hr_pred : r = C.row (C.pred i) := by
    by_contra hne
    exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hne)
      hwitness_r (C.witness_mem (C.pred i))
  exact C.row_ne_pred i (by rw [← hr_i, ← hr_pred])

omit [Fintype V] in
theorem false_of_unique (C : LinkageDependencyCycle R)
    (hunique : R.IsUniqueLinkage) : False := by
  classical
  let i0 : C.Index := Classical.choice inferInstance
  let R' : PerfectPathPacking G A B := C.reroutedPerfectPathPacking
  have hR'edge :
      s(C.vertex i0, C.witness (C.pred i0)) ∈ R'.toPathPacking.edgeSet := by
    simpa [R'] using C.reroutedPerfectPathPacking_cross_edge_mem i0
  have hEq := hunique.2 R'
  have hRedge :
      s(C.vertex i0, C.witness (C.pred i0)) ∈ R.toPathPacking.edgeSet := by
    simpa [hEq] using hR'edge
  exact C.cross_edge_not_mem_original i0 hRedge

omit [Fintype V] in
theorem not_nonempty_of_unique (hunique : R.IsUniqueLinkage) :
    ¬ Nonempty (LinkageDependencyCycle R) := by
  rintro ⟨C⟩
  exact C.false_of_unique hunique

end LinkageDependencyCycle

omit [Fintype V] in
/-- Appendix B's acyclicity conclusion for the dependency digraph of a unique
linkage.  A directed dependency cycle has a shortest closed relation series.
Minimality rules out type-1 edges and repeated source rows, so the series is a
type-2 dependency cycle; rerouting that cycle contradicts uniqueness. -/
theorem linkageDependency_acyclic_of_unique
    {R : PerfectPathPacking G A B} (hunique : R.IsUniqueLinkage) :
    ∀ v : V, ¬ Relation.TransGen (LinkageDependency R) v v := by
  classical
  intro v hvv
  have hex :
      ∃ p : RelSeries (relationSetRel (LinkageDependency R)),
        RelationSeries.Closed (rel := LinkageDependency R) p :=
    RelationSeries.exists_closed_of_transGen_cycle
      (rel := LinkageDependency R) hvv
  let p :=
    RelationSeries.minimalClosedSeries
      (rel := LinkageDependency R) hex
  have hpclosed :
      RelationSeries.Closed (rel := LinkageDependency R) p := by
    simpa [p] using
      RelationSeries.minimalClosedSeries_closed
        (rel := LinkageDependency R) hex
  have hmin :
      ∀ q : RelSeries (relationSetRel (LinkageDependency R)),
        RelationSeries.Closed (rel := LinkageDependency R) q →
          p.length ≤ q.length := by
    intro q hq
    simpa [p] using
      RelationSeries.minimalClosedSeries_min
        (rel := LinkageDependency R) hex hq
  have hnotype1 :=
    closed_dependency_series_no_type1_edge_of_minimal
      (R := R) p hpclosed hmin
  have : NeZero p.length := ⟨Nat.pos_iff_ne_zero.mp hpclosed.2⟩
  let next : Equiv.Perm (Fin p.length) :=
    Equiv.addRight (1 : Fin p.length)
  let vertex : Fin p.length → V := fun i => p i.castSucc
  have hvertex_next : ∀ i : Fin p.length, vertex (next i) = p i.succ := by
    intro i
    by_cases hi : i.1 + 1 < p.length
    · have hnext : next i = ⟨i.1 + 1, hi⟩ := by
        simpa [next] using fin_addRight_one_apply_of_lt i hi
      simp [vertex, hnext]
      apply congrArg p.toFun
      ext
      simp [Fin.val_succ]
    · have hnext : next i = 0 := by
        simpa [next] using fin_addRight_one_apply_of_not_lt i hi
      have hisucc : i.succ = (Fin.last p.length) := by
        ext
        simp [Fin.val_succ]
        omega
      calc
        vertex (next i) = p.head := by simp [vertex, hnext, RelSeries.head]
        _ = p.last := hpclosed.1
        _ = p i.succ := by simp [RelSeries.last, hisucc]
  let Dp : ∀ i : Fin p.length,
      Type2DependencyData R (p i.castSucc) (p i.succ) := fun i =>
    Classical.choice
      (Type2DependencyData.exists_of_dependency_of_not_type1
        (R := R)
        (u := p i.castSucc) (v := p i.succ)
        (by simpa [relationSetRel] using p.step i)
        (hnotype1 i))
  have hrowinjp :
      Function.Injective fun i : Fin p.length => (Dp i).row :=
    closed_dependency_series_type2_rows_injective_of_minimal
      (R := R) p hpclosed hmin Dp
  let D : ∀ i : Fin p.length,
      Type2DependencyData R (vertex i) (vertex (next i)) := fun i =>
    { row := (Dp i).row
      row' := (Dp i).row'
      row_ne := (Dp i).row_ne
      u_mem := by simpa [vertex] using (Dp i).u_mem
      v_mem := by simpa [hvertex_next i] using (Dp i).v_mem
      witness := (Dp i).witness
      witness_mem := (Dp i).witness_mem
      before_witness := by simpa [vertex] using (Dp i).before_witness
      u_ne_witness := by simpa [vertex] using (Dp i).u_ne_witness
      adj := by simpa [hvertex_next i] using (Dp i).adj }
  have hrowinj : Function.Injective fun i : Fin p.length => (D i).row := by
    intro i j hij
    apply hrowinjp
    simpa [D] using hij
  let C : LinkageDependencyCycle R :=
    LinkageDependencyCycle.ofType2Family
      (R := R) next vertex D hrowinj
  exact LinkageDependencyCycle.not_nonempty_of_unique
    (R := R) hunique ⟨C⟩

namespace TopologicalRank

variable {R : PerfectPathPacking G A B}

omit [Fintype V] in
theorem shortcut_edge_not_mem_row
    (Prow : GraphPath G) {u x v : V}
    (hux : Prow.Before u x) (hxv : Prow.Before x v)
    (hux_ne : u ≠ x) (hxv_ne : x ≠ v) :
    s(u, v) ∉ Prow.edgeSet := by
  classical
  intro he
  have huxData := (Prow.before_iff_vertexIndex_le).1 hux
  have hxvData := (Prow.before_iff_vertexIndex_le).1 hxv
  have hxu_not : Prow.vertexIndex x ≠ Prow.vertexIndex u := by
    intro hidx
    have hxu : Prow.Before x u :=
      (Prow.before_iff_vertexIndex_le).2
        ⟨huxData.2.1, huxData.1, hidx.le⟩
    exact hux_ne (Prow.before_antisymm hux hxu)
  have huv_not : Prow.vertexIndex v ≠ Prow.vertexIndex x := by
    intro hidx
    have hvx : Prow.Before v x :=
      (Prow.before_iff_vertexIndex_le).2
        ⟨hxvData.2.1, hxvData.1, hidx.le⟩
    exact hxv_ne (Prow.before_antisymm hxv hvx)
  have hux_lt : Prow.vertexIndex u < Prow.vertexIndex x :=
    lt_of_le_of_ne huxData.2.2 hxu_not.symm
  have hxv_lt : Prow.vertexIndex x < Prow.vertexIndex v :=
    lt_of_le_of_ne hxvData.2.2 huv_not.symm
  have hedge := Prow.edge_vertexIndex_le_succ he
  omega

/-- Vertices whose dependency-topological rank is at or above a threshold. -/
noncomputable def aboveSet (rho : TopologicalRank (LinkageDependency R))
    (t : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => t ≤ rho.rank v

@[simp] theorem mem_aboveSet
    (rho : TopologicalRank (LinkageDependency R)) (t : ℕ) (v : V) :
    v ∈ rho.aboveSet t ↔ t ≤ rho.rank v := by
  classical
  simp [aboveSet]

/-- On one linkage row, the threshold vertex is the first vertex whose
topological rank is at least `t`, or the row target if the row has no such
vertex. -/
noncomputable def separatorVertex
    (rho : TopologicalRank (LinkageDependency R))
    (t : ℕ) (r : R.Index) : V := by
  classical
  let Prow := R.path r
  let U := rho.aboveSet t
  exact
    if hne : (Prow.vertexSet ∩ U).Nonempty then
      Prow.firstHitVertex U hne
    else
      Prow.target

theorem separatorVertex_mem
    (rho : TopologicalRank (LinkageDependency R))
    (t : ℕ) (r : R.Index) :
    rho.separatorVertex t r ∈ (R.path r).vertexSet := by
  classical
  let Prow := R.path r
  let U := rho.aboveSet t
  by_cases hne : (Prow.vertexSet ∩ U).Nonempty
  · simp [separatorVertex, Prow, U, hne, GraphPath.firstHitVertex_mem_vertexSet]
  · simp [separatorVertex, Prow, U, hne]

theorem separatorVertex_above_of_exists
    (rho : TopologicalRank (LinkageDependency R))
    {t : ℕ} {r : R.Index}
    (hne : ((R.path r).vertexSet ∩ rho.aboveSet t).Nonempty) :
    t ≤ rho.rank (rho.separatorVertex t r) := by
  classical
  let Prow := R.path r
  let U := rho.aboveSet t
  have hmem : Prow.firstHitVertex U (by simpa [Prow, U] using hne) ∈ U :=
    Prow.firstHitVertex_mem_set U (by simpa [Prow, U] using hne)
  simpa [separatorVertex, Prow, U, hne] using hmem

theorem separatorVertex_zero
    (rho : TopologicalRank (LinkageDependency R)) (r : R.Index) :
    rho.separatorVertex 0 r = (R.path r).source := by
  classical
  let Prow := R.path r
  let U := rho.aboveSet 0
  have hne : (Prow.vertexSet ∩ U).Nonempty := by
    exact ⟨Prow.source, by simp [Prow, U]⟩
  have hfirst_le_source :
      Prow.vertexIndex (Prow.firstHitVertex U hne) ≤
        Prow.vertexIndex Prow.source :=
    (Prow.firstHitVertex_spec U hne).2 Prow.source (by simp [Prow, U])
  have hidx0 :
      Prow.vertexIndex (Prow.firstHitVertex U hne) = 0 := by
    simpa [GraphPath.source_vertexIndex] using hfirst_le_source
  have hfirst_mem : Prow.firstHitVertex U hne ∈ Prow.vertexSet :=
    Prow.firstHitVertex_mem_vertexSet U hne
  have hbefore_source :
      Prow.Before (Prow.firstHitVertex U hne) Prow.source :=
    (Prow.before_iff_vertexIndex_le).2
      ⟨hfirst_mem, GraphPath.source_mem_vertexSet Prow, by simp [hidx0]⟩
  have hsource_before :
      Prow.Before Prow.source (Prow.firstHitVertex U hne) :=
    Prow.source_before_of_mem hfirst_mem
  have hfirst_eq :
      Prow.firstHitVertex U hne = Prow.source :=
    Prow.before_antisymm hbefore_source hsource_before
  simpa [separatorVertex, Prow, U, hne] using hfirst_eq

theorem separatorVertex_card
    (rho : TopologicalRank (LinkageDependency R)) (r : R.Index) :
    rho.separatorVertex (Fintype.card V) r = (R.path r).target := by
  classical
  let Prow := R.path r
  let U := rho.aboveSet (Fintype.card V)
  have hne : ¬ (Prow.vertexSet ∩ U).Nonempty := by
    rintro ⟨v, hv⟩
    have hvU : Fintype.card V ≤ rho.rank v := by
      simpa [U] using (Finset.mem_inter.1 hv).2
    have hvRank := rho.rank_lt_card v
    omega
  change
      (if h : (Prow.vertexSet ∩ U).Nonempty then
        Prow.firstHitVertex U h
      else
        Prow.target) = Prow.target
  rw [dif_neg hne]

theorem row_rank_lt_of_before
    (rho : TopologicalRank (LinkageDependency R))
    (r : R.Index) {u v : V}
    (hu : u ∈ (R.path r).vertexSet)
    (hv : v ∈ (R.path r).vertexSet)
    (huv : (R.path r).Before u v) (hne : u ≠ v) :
    rho.rank u < rho.rank v :=
  rho.rel_lt (Or.inl ⟨r, hu, hv, huv, hne⟩)

theorem below_before_separator
    (rho : TopologicalRank (LinkageDependency R))
    (t : ℕ) (r : R.Index) {v : V}
    (hv : v ∈ (R.path r).vertexSet) (hbelow : rho.rank v < t) :
    (R.path r).Before v (rho.separatorVertex t r) := by
  classical
  let Prow := R.path r
  let U := rho.aboveSet t
  by_cases hne : (Prow.vertexSet ∩ U).Nonempty
  · let s := Prow.firstHitVertex U hne
    have hs_mem : s ∈ Prow.vertexSet := Prow.firstHitVertex_mem_vertexSet U hne
    have hs_above : t ≤ rho.rank s := by
      have hsU : s ∈ U := Prow.firstHitVertex_mem_set U hne
      simpa [U] using hsU
    have hidx_not : ¬ Prow.vertexIndex s < Prow.vertexIndex v := by
      intro hlt
      have hsv : Prow.Before s v :=
        (Prow.before_iff_vertexIndex_le).2 ⟨hs_mem, hv, hlt.le⟩
      have hs_ne_v : s ≠ v := by
        intro hsv_eq
        have hs_rank_eq : rho.rank s = rho.rank v := congrArg rho.rank hsv_eq
        omega
      have hrank_lt : rho.rank s < rho.rank v :=
        rho.row_rank_lt_of_before r hs_mem hv hsv hs_ne_v
      omega
    have hbefore : Prow.Before v s :=
      (Prow.before_iff_vertexIndex_le).2
        ⟨hv, hs_mem, Nat.le_of_not_gt hidx_not⟩
    simpa [separatorVertex, Prow, U, hne, s] using hbefore
  · have hbefore_target : Prow.Before v Prow.target :=
      ⟨hv, by
        simpa [GraphPath.dropUntil_target] using
          GraphPath.target_mem_vertexSet (Prow.dropUntil hv)⟩
    simpa [separatorVertex, Prow, U, hne] using hbefore_target

theorem separator_before_above
    (rho : TopologicalRank (LinkageDependency R))
    (t : ℕ) (r : R.Index) {v : V}
    (hv : v ∈ (R.path r).vertexSet) (habove : t ≤ rho.rank v) :
    (R.path r).Before (rho.separatorVertex t r) v := by
  classical
  let Prow := R.path r
  let U := rho.aboveSet t
  have hne : (Prow.vertexSet ∩ U).Nonempty := by
    exact ⟨v, Finset.mem_inter.2 ⟨hv, by simpa [U] using habove⟩⟩
  have hbefore :
      Prow.Before (Prow.firstHitVertex U hne) v :=
    Prow.firstHitVertex_before_of_mem_set U hne hv (by simpa [U] using habove)
  simpa [separatorVertex, Prow, U, hne] using hbefore

theorem separatorVertex_monotone
    (rho : TopologicalRank (LinkageDependency R))
    (r : R.Index) {s t : ℕ} (hst : s ≤ t) :
    (R.path r).Before (rho.separatorVertex s r) (rho.separatorVertex t r) := by
  classical
  let Prow := R.path r
  let Ut := rho.aboveSet t
  by_cases htne : (Prow.vertexSet ∩ Ut).Nonempty
  · have ht_above : t ≤ rho.rank (rho.separatorVertex t r) :=
      rho.separatorVertex_above_of_exists (by simpa [Prow, Ut] using htne)
    exact rho.separator_before_above s r
      (rho.separatorVertex_mem t r) (hst.trans ht_above)
  · have htarget : rho.separatorVertex t r = Prow.target := by
      simp [separatorVertex, Prow, Ut, htne]
    rw [htarget]
    exact
      ⟨rho.separatorVertex_mem s r, by
        simpa [GraphPath.dropUntil_target] using
          GraphPath.target_mem_vertexSet
            (Prow.dropUntil (rho.separatorVertex_mem s r))⟩

/-- The finite threshold separator associated to a dependency-topological
rank. -/
noncomputable def separatorSet
    (rho : TopologicalRank (LinkageDependency R)) (t : ℕ) :
    Finset V := by
  classical
  exact Finset.univ.image fun r : R.Index => rho.separatorVertex t r

theorem separatorSet_eq
    (rho : TopologicalRank (LinkageDependency R)) (t : ℕ) :
    rho.separatorSet t =
      Finset.univ.image fun r : R.Index => rho.separatorVertex t r := rfl

theorem separatorVertex_mem_separatorSet
    (rho : TopologicalRank (LinkageDependency R))
    (t : ℕ) (r : R.Index) :
    rho.separatorVertex t r ∈ rho.separatorSet t := by
  classical
  rw [rho.separatorSet_eq t]
  exact Finset.mem_image.2 ⟨r, by simp, rfl⟩

theorem separatorSet_card_le
    (rho : TopologicalRank (LinkageDependency R)) (t : ℕ) :
    (rho.separatorSet t).card ≤ R.card := by
  classical
  rw [rho.separatorSet_eq t]
  calc
    (Finset.univ.image fun r : R.Index => rho.separatorVertex t r).card
        ≤ (Finset.univ : Finset R.Index).card := Finset.card_image_le
    _ = R.card := rfl

theorem separatorVertex_rank_ge_or_eq
    (rho : TopologicalRank (LinkageDependency R))
    {s t : ℕ} (hst : s ≤ t) (r : R.Index)
    (hne : rho.separatorVertex t r ≠ rho.separatorVertex s r) :
    s ≤ rho.rank (rho.separatorVertex t r) := by
  classical
  let Prow := R.path r
  let Us := rho.aboveSet s
  by_cases hsne : (Prow.vertexSet ∩ Us).Nonempty
  · have hs_above : s ≤ rho.rank (rho.separatorVertex s r) :=
      rho.separatorVertex_above_of_exists (by simpa [Prow, Us] using hsne)
    have hbefore := rho.separatorVertex_monotone r hst
    have hlt :
        rho.rank (rho.separatorVertex s r) <
          rho.rank (rho.separatorVertex t r) :=
      rho.row_rank_lt_of_before r
        (rho.separatorVertex_mem s r)
        (rho.separatorVertex_mem t r)
        hbefore hne.symm
    exact hs_above.trans hlt.le
  · have hsep_s : rho.separatorVertex s r = Prow.target := by
      simp [separatorVertex, Prow, Us, hsne]
    have ht_no : ¬ (Prow.vertexSet ∩ rho.aboveSet t).Nonempty := by
      intro htne
      apply hsne
      rcases htne with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      rcases Finset.mem_inter.1 hv with ⟨hvP, hvU⟩
      exact Finset.mem_inter.2
        ⟨hvP, by
          have htv : t ≤ rho.rank v := by simpa using hvU
          simpa [Us] using hst.trans htv⟩
    have hsep_t : rho.separatorVertex t r = Prow.target := by
      simp [separatorVertex, Prow, ht_no]
    exact False.elim (hne (hsep_t.trans hsep_s.symm))

theorem separatorSet_subset_separator_union_above
    (rho : TopologicalRank (LinkageDependency R))
    {s t : ℕ} (hst : s ≤ t) :
    rho.separatorSet t ⊆
      rho.separatorSet s ∪ (Finset.univ.filter fun v : V => s ≤ rho.rank v) := by
  classical
  intro v hv
  rw [rho.separatorSet_eq t] at hv
  rcases Finset.mem_image.1 hv with ⟨r, _hr, rfl⟩
  by_cases hsame : rho.separatorVertex t r = rho.separatorVertex s r
  · exact Finset.mem_union_left _
      (by
        rw [hsame]
        exact rho.separatorVertex_mem_separatorSet s r)
  · exact Finset.mem_union_right _
      (by simp [rho.separatorVertex_rank_ge_or_eq hst r hsame])

theorem separatorSet_sdiff_succ_subset_rankLevel
    (rho : TopologicalRank (LinkageDependency R))
    {t : ℕ} (_ht : t < Fintype.card V) :
    rho.separatorSet t \ rho.separatorSet (t + 1) ⊆
      (Finset.univ.filter fun v : V => rho.rank v = t) := by
  classical
  intro v hv
  rcases Finset.mem_sdiff.1 hv with ⟨hvSep, hvNotSucc⟩
  rw [rho.separatorSet_eq t] at hvSep
  rcases Finset.mem_image.1 hvSep with ⟨r, _hr, rfl⟩
  have hge : t ≤ rho.rank (rho.separatorVertex t r) := by
    by_contra hnot
    have hno : ¬ ((R.path r).vertexSet ∩ rho.aboveSet t).Nonempty := by
      intro hne
      exact hnot (rho.separatorVertex_above_of_exists hne)
    have hsep_t : rho.separatorVertex t r = (R.path r).target := by
      simp [separatorVertex, hno]
    have hnoSucc : ¬ ((R.path r).vertexSet ∩ rho.aboveSet (t + 1)).Nonempty := by
      rintro ⟨x, hx⟩
      have hxAboveSucc : t + 1 ≤ rho.rank x := by
        simpa using (Finset.mem_inter.1 hx).2
      apply hno
      exact ⟨x, Finset.mem_inter.2
        ⟨(Finset.mem_inter.1 hx).1,
          by
            have hxAbove : t ≤ rho.rank x :=
              (Nat.le_succ t).trans hxAboveSucc
            simpa using hxAbove⟩⟩
    have hsep_succ :
        rho.separatorVertex (t + 1) r = (R.path r).target := by
      simp [separatorVertex, hnoSucc]
    have hmemSucc := rho.separatorVertex_mem_separatorSet (t + 1) r
    rw [hsep_succ, ← hsep_t] at hmemSucc
    exact hvNotSucc hmemSucc
  have hle : rho.rank (rho.separatorVertex t r) ≤ t := by
    by_contra hnot
    have hsucc : t + 1 ≤ rho.rank (rho.separatorVertex t r) := by omega
    have hbefore1 := rho.separatorVertex_monotone r (Nat.le_succ t)
    have hbefore2 :
        (R.path r).Before (rho.separatorVertex (t + 1) r)
          (rho.separatorVertex t r) :=
      rho.separator_before_above (t + 1) r
        (rho.separatorVertex_mem t r) hsucc
    have heq :
        rho.separatorVertex t r = rho.separatorVertex (t + 1) r :=
      (R.path r).before_antisymm hbefore1 hbefore2
    have hmemSucc := rho.separatorVertex_mem_separatorSet (t + 1) r
    rw [← heq] at hmemSucc
    exact hvNotSucc hmemSucc
  simp [le_antisymm hle hge]

/-- Same-row crossing edges are impossible in a unique linkage: replacing the
row segment between the lower and upper endpoint by the crossing edge gives a
perfect linkage with a different edge set. -/
theorem no_same_row_crossing_of_unique
    (rho : TopologicalRank (LinkageDependency R))
    (hunique : R.IsUniqueLinkage)
    (t : ℕ) (r : R.Index) (u v : V)
    (hu : u ∈ (R.path r).vertexSet)
    (hv : v ∈ (R.path r).vertexSet)
    (huRank : rho.rank u < t) (hvRank : t ≤ rho.rank v)
    (huNotSep : u ∉ rho.separatorSet t)
    (hvNotSep : v ∉ rho.separatorSet t)
    (huv : G.Adj u v) :
    False := by
  classical
  let x := rho.separatorVertex t r
  have hxSep : x ∈ rho.separatorSet t := rho.separatorVertex_mem_separatorSet t r
  have hux : (R.path r).Before u x :=
    rho.below_before_separator t r hu huRank
  have hxv : (R.path r).Before x v :=
    rho.separator_before_above t r hv hvRank
  have hux_ne : u ≠ x := by
    intro h
    exact huNotSep (by simpa [x, h] using hxSep)
  have hxv_ne : x ≠ v := by
    intro h
    exact hvNotSep (by simpa [x, h] using hxSep)
  have hshortcutNotRow :
      s(u, v) ∉ (R.path r).edgeSet :=
    shortcut_edge_not_mem_row (R.path r) hux hxv hux_ne hxv_ne
  have hshortcutNotR :
      s(u, v) ∉ R.toPathPacking.edgeSet := by
    intro he
    rcases (R.toPathPacking.mem_edgeSet).1 he with ⟨i, hei⟩
    by_cases hir : i = r
    · subst i
      exact hshortcutNotRow hei
    · have heWalk : s(u, v) ∈ (R.path i).walk.edges := by
        exact List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using hei)
      have hu_i : u ∈ (R.path i).vertexSet := by
        have huSupport : u ∈ (R.path i).walk.support :=
          (R.path i).walk.fst_mem_support_of_mem_edges heWalk
        simpa [GraphPath.vertexSet] using huSupport
      exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hir)
        hu_i hu
  rcases GraphPath.exists_shortcutAround (R.path r) hux hxv hux_ne huv with
    ⟨Q, hQsource, hQtarget, hQsubset, hQedge⟩
  let newPath : R.Index → GraphPath G := fun i =>
    if i = r then Q else R.path i
  have newPath_source_mem : ∀ i : R.Index, (newPath i).source ∈ A := by
    intro i
    by_cases hir : i = r
    · subst i
      simpa [newPath, hQsource] using R.source_mem r
    · simpa [newPath, hir] using R.source_mem i
  have newPath_target_mem : ∀ i : R.Index, (newPath i).target ∈ B := by
    intro i
    by_cases hir : i = r
    · subst i
      simpa [newPath, hQtarget] using R.target_mem r
    · simpa [newPath, hir] using R.target_mem i
  let R' : PerfectPathPacking G A B := {
    toPathPacking := {
      Index := R.Index
      path := newPath
      connects := by
        intro i
        exact Or.inl ⟨newPath_source_mem i, newPath_target_mem i⟩
      node_disjoint := by
        intro i j hij
        by_cases hir : i = r
        · by_cases hjr : j = r
          · exact False.elim (hij (hir.trans hjr.symm))
          · subst i
            dsimp [newPath]
            rw [if_pos rfl, if_neg hjr]
            exact Finset.disjoint_of_subset_left hQsubset
              (R.toPathPacking.node_disjoint (by
                intro hrj
                exact hjr hrj.symm))
        · by_cases hjr : j = r
          · subst j
            dsimp [newPath]
            rw [if_neg hir, if_pos rfl]
            exact Finset.disjoint_of_subset_right hQsubset
              (R.toPathPacking.node_disjoint (by
                intro hir'
                exact hir hir'))
          · dsimp [newPath]
            rw [if_neg hir, if_neg hjr]
            exact R.toPathPacking.node_disjoint hij
    }
    source_mem := newPath_source_mem
    target_mem := newPath_target_mem
    source_bijective := by
      have hfun :
          (fun i : R.Index =>
            (⟨(newPath i).source, newPath_source_mem i⟩ : {w // w ∈ A})) =
          (fun i : R.Index =>
            (⟨(R.path i).source, R.source_mem i⟩ : {w // w ∈ A})) := by
        funext i
        apply Subtype.ext
        by_cases hir : i = r
        · subst i
          simp [newPath, hQsource]
        · simp [newPath, hir]
      simpa [hfun] using R.source_bijective
    target_bijective := by
      have hfun :
          (fun i : R.Index =>
            (⟨(newPath i).target, newPath_target_mem i⟩ : {w // w ∈ B})) =
          (fun i : R.Index =>
            (⟨(R.path i).target, R.target_mem i⟩ : {w // w ∈ B})) := by
        funext i
        apply Subtype.ext
        by_cases hir : i = r
        · subst i
          simp [newPath, hQtarget]
        · simp [newPath, hir]
      simpa [hfun] using R.target_bijective
  }
  have hR'edge : s(u, v) ∈ R'.toPathPacking.edgeSet := by
    apply (R'.toPathPacking.mem_edgeSet).2
    refine ⟨r, ?_⟩
    simpa [R', newPath] using hQedge
  have hEq := hunique.2 R'
  have hRedge : s(u, v) ∈ R.toPathPacking.edgeSet := by
    simpa [hEq] using hR'edge
  exact hshortcutNotR hRedge

/-- Separator blocking follows from the topological ordering once same-row
crossing edges are ruled out by a rerouting argument.  The different-row case
is the type-2 dependency argument from Appendix B. -/
theorem separator_blocks_of_no_same_row_crossing
    (rho : TopologicalRank (LinkageDependency R))
    (hspan : R.SpansVertices)
    (hsame :
      ∀ (t : ℕ) (r : R.Index) (u v : V),
        u ∈ (R.path r).vertexSet →
          v ∈ (R.path r).vertexSet →
            rho.rank u < t →
              t ≤ rho.rank v →
                u ∉ rho.separatorSet t →
                  v ∉ rho.separatorSet t →
                    G.Adj u v →
                      False)
    (t : ℕ) (P : GraphPath G)
    (hcross : GraphPathCrossesRankThreshold rho.rank t P) :
    ∃ v ∈ P.vertexSet, v ∈ rho.separatorSet t := by
  classical
  by_contra hno
  push Not at hno
  rcases GraphPath.exists_adjacent_rank_crossing rho.rank t P hcross with
    ⟨u, v, huP, hvP, huRank, hvRank, huv⟩
  rcases (R.toPathPacking.mem_vertexSet).1 (hspan u) with ⟨ru, huRow⟩
  rcases (R.toPathPacking.mem_vertexSet).1 (hspan v) with ⟨rv, hvRow⟩
  have huNotSep : u ∉ rho.separatorSet t := fun huSep => hno u huP huSep
  have hvNotSep : v ∉ rho.separatorSet t := fun hvSep => hno v hvP hvSep
  by_cases hsameRow : ru = rv
  · subst rv
    exact hsame t ru u v huRow hvRow huRank hvRank huNotSep hvNotSep huv
  · let x := rho.separatorVertex t rv
    have hxMem : x ∈ (R.path rv).vertexSet := rho.separatorVertex_mem t rv
    have hxSep : x ∈ rho.separatorSet t := rho.separatorVertex_mem_separatorSet t rv
    have hx_ne_v : x ≠ v := by
      intro hxv
      exact hvNotSep (by simpa [x, hxv] using hxSep)
    have hxBeforeV : (R.path rv).Before x v :=
      rho.separator_before_above t rv hvRow hvRank
    have hxAbove : t ≤ rho.rank x := by
      have hne : ((R.path rv).vertexSet ∩ rho.aboveSet t).Nonempty := by
        exact ⟨v, Finset.mem_inter.2 ⟨hvRow, by simpa using hvRank⟩⟩
      simpa [x] using rho.separatorVertex_above_of_exists hne
    have hdep : LinkageDependency R x u := by
      refine Or.inr ⟨rv, ru, ?_, hxMem, huRow, v, hvRow, hxBeforeV, hx_ne_v, huv.symm⟩
      exact fun h => hsameRow h.symm
    have hlt := rho.rel_lt hdep
    omega

/-- The full separator-blocking property for a unique linkage, assuming a
topological ranking of the dependency relation. -/
theorem separator_blocks_of_unique
    (rho : TopologicalRank (LinkageDependency R))
    (hunique : R.IsUniqueLinkage)
    (t : ℕ) (P : GraphPath G)
    (hcross : GraphPathCrossesRankThreshold rho.rank t P) :
    ∃ v ∈ P.vertexSet, v ∈ rho.separatorSet t :=
  rho.separator_blocks_of_no_same_row_crossing hunique.1
    (fun t r u v hu hv huRank hvRank huNotSep hvNotSep huv =>
      rho.no_same_row_crossing_of_unique hunique t r u v
        hu hv huRank hvRank huNotSep hvNotSep huv)
    t P hcross

/-- Package a dependency-topological rank and its separator-blocking property
as the formal `LinkageOrdering` used by Theorem 4.6. -/
noncomputable def toLinkageOrdering
    (rho : TopologicalRank (LinkageDependency R))
    (hblocks :
      ∀ (t : ℕ) (P : GraphPath G),
        GraphPathCrossesRankThreshold rho.rank t P →
          ∃ v ∈ P.vertexSet, v ∈ rho.separatorSet t) :
    LinkageOrdering R where
  rank := rho.rank
  rank_injective := rho.rank_injective
  rank_lt_card := rho.rank_lt_card
  row_strict := by
    intro r u v hu hv huv hne
    exact rho.row_rank_lt_of_before r hu hv huv hne
  separatorVertex := rho.separatorVertex
  separatorVertex_mem := rho.separatorVertex_mem
  separatorVertex_zero := rho.separatorVertex_zero
  separatorVertex_card := rho.separatorVertex_card
  below_before_separator := rho.below_before_separator
  separator_before_above := rho.separator_before_above
  separatorVertex_monotone := by
    intro r s t hst
    exact rho.separatorVertex_monotone r hst
  separatorSet := rho.separatorSet
  separatorSet_eq := rho.separatorSet_eq
  separatorSet_subset_separator_union_above := by
    intro s t hst
    exact rho.separatorSet_subset_separator_union_above hst
  separatorSet_sdiff_succ_subset_rankLevel := by
    intro t ht
    exact rho.separatorSet_sdiff_succ_subset_rankLevel ht
  separator_card_le := rho.separatorSet_card_le
  separator_blocks := hblocks

/-- A dependency-topological rank of a unique linkage is exactly the
Robertson--Seymour linkage ordering needed in Lemma 4.5. -/
noncomputable def linkageOrderingOfTopologicalRank
    (rho : TopologicalRank (LinkageDependency R))
    (hunique : R.IsUniqueLinkage) :
    LinkageOrdering R :=
  rho.toLinkageOrdering (rho.separator_blocks_of_unique hunique)

/-- Lemma 4.5 reduced to Appendix B's acyclicity claim for the dependency
digraph.  The remaining theorem in this file proves the separator construction
and rerouting argument once the dependency relation has been shown acyclic. -/
noncomputable def linkageOrderingOfUniqueOfDependencyAcyclic
    (hunique : R.IsUniqueLinkage)
    (hacyc : ∀ v : V, ¬ Relation.TransGen (LinkageDependency R) v v) :
    LinkageOrdering R :=
  let rho := topologicalRankOfAcyclicRelation (LinkageDependency R) hacyc
  rho.linkageOrderingOfTopologicalRank hunique

end TopologicalRank

/-- Chuzhoy--Tan Lemma 4.5: every unique linkage admits a
Robertson--Seymour linkage ordering whose threshold separators have size at
most the number of linkage paths and block every path crossing the threshold. -/
noncomputable def linkageOrderingOfUnique
    {R : PerfectPathPacking G A B} (hunique : R.IsUniqueLinkage) :
    LinkageOrdering R :=
  TopologicalRank.linkageOrderingOfUniqueOfDependencyAcyclic
    hunique (linkageDependency_acyclic_of_unique hunique)

end PathSlicing

end SimpleGraph

end Erdos73Infrastructure

#print axioms Erdos73Infrastructure.SimpleGraph.PathSlicing.linkageOrderingOfUnique
