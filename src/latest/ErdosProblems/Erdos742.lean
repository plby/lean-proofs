/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 742.
https://www.erdosproblems.com/forum/thread/742

Informal authors:
- Zoltán Füredi

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos742.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/742.lean
-/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 742

Füredi's sufficiently-large resolution of the Murty--Simon conjecture for
diameter-two edge-critical graphs.

The detailed mathematical proof and a Leanization map are in `tex/742.tex`.
-/

open scoped ENat
open SimpleGraph

namespace Erdos742

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A finite greedy-selection lemma in the cardinal form used to linearize
the family of light critical paths. -/
lemma exists_large_pairwise_subset {α : Type*} [DecidableEq α]
    (s : Finset α) (R : α → α → Prop) [DecidableRel R]
    (hR : Std.Symm R) (D : ℕ)
    (hdeg : ∀ x ∈ s, (s.filter fun y => y = x ∨ R x y).card ≤ D + 1) :
    ∃ t ⊆ s, (t : Set α).Pairwise (fun x y => ¬ R x y) ∧
      s.card ≤ (D + 1) * t.card := by
  classical
  let : Std.Symm R := hR
  let good : Finset (Finset α) :=
    s.powerset.filter fun t => (t : Set α).Pairwise (fun x y => ¬ R x y)
  have hgood : good.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [good]
  obtain ⟨t, htgood, htmax⟩ := good.exists_max_image Finset.card hgood
  have hts : t ⊆ s := (Finset.mem_filter.mp htgood).1 |> Finset.mem_powerset.mp
  have htpair : (t : Set α).Pairwise (fun x y => ¬ R x y) :=
    (Finset.mem_filter.mp htgood).2
  refine ⟨t, hts, htpair, ?_⟩
  have hcover : s ⊆ t.biUnion (fun x => s.filter fun y => y = x ∨ R x y) := by
    intro x hxs
    by_cases hxt : x ∈ t
    · rw [Finset.mem_biUnion]
      exact ⟨x, hxt, by simp [hxs]⟩
    · by_contra hxcover
      simp only [Finset.mem_biUnion, not_exists, not_and] at hxcover
      have hxR : ∀ y ∈ t, ¬ R x y := by
        intro y hyt hxy
        exact hxcover y hyt (by simp [hxs, Std.Symm.symm _ _ hxy])
      have hins_pair : ((insert x t : Finset α) : Set α).Pairwise
          (fun a b => ¬ R a b) := by
        let : Std.Symm (fun a b => ¬ R a b) :=
          ⟨fun _ _ hab hba => hab (Std.Symm.symm _ _ hba)⟩
        rw [Finset.coe_insert, Set.pairwise_insert_of_symm]
        exact ⟨htpair, fun y hyt _ => hxR y hyt⟩
      have hins_good : insert x t ∈ good := by
        simp only [good, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.insert_subset hxs hts, hins_pair⟩
      have hle := htmax (insert x t) hins_good
      simp [hxt] at hle
  calc
    s.card ≤ (t.biUnion (fun x => s.filter fun y => y = x ∨ R x y)).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ x ∈ t, (s.filter fun y => y = x ∨ R x y).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ t, (D + 1) := Finset.sum_le_sum fun x hx => hdeg x (hts hx)
    _ = (D + 1) * t.card := by simp [mul_comm]

/-- A graph is diameter-2-critical if it has diameter `2` and removing any edge
destroys diameter `2`.  This is exactly the upstream Formal Conjectures
definition. -/
def IsDiameter2Critical (G : SimpleGraph V) : Prop :=
  G.diam = 2 ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).diam ≠ 2

section CriticalPaths

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A type-I critical path: the edge `xy` is the unique path of length at most
two between its endpoints. -/
def IsTypeI (x y : V) : Prop :=
  G.Adj x y ∧ G.commonNeighbors x y = ∅

/-- A type-II critical path `x-z-y`: `z` is the unique common neighbor of the
nonadjacent endpoints `x,y`. -/
def IsTypeII (x z y : V) : Prop :=
  x ≠ y ∧ ¬G.Adj x y ∧ G.commonNeighbors x y = {z}

/-- `x,y` form a critical pair: there is a unique path of length at most two
between them. -/
def IsCriticalPair (x y : V) : Prop :=
  IsTypeI G x y ∨ ∃ z, IsTypeII G x z y

/-- An edge lies on the unique short path belonging to the critical pair
`x,y`. -/
def CriticalPathContains (x y : V) (e : Sym2 V) : Prop :=
  (IsTypeI G x y ∧ e = s(x, y)) ∨
    ∃ z, IsTypeII G x z y ∧ (e = s(x, z) ∨ e = s(z, y))

noncomputable instance criticalPathContains.instDecidable (x y : V) (e : Sym2 V) :
    Decidable (CriticalPathContains G x y e) := Classical.propDecidable _

lemma isTypeI_symm {x y : V} : IsTypeI G x y ↔ IsTypeI G y x := by
  simp only [IsTypeI, adj_comm, G.commonNeighbors_symm]

lemma isTypeII_symm {x z y : V} : IsTypeII G x z y ↔ IsTypeII G y z x := by
  simp only [IsTypeII, ne_comm, adj_comm, G.commonNeighbors_symm]

lemma isCriticalPair_symm {x y : V} : IsCriticalPair G x y ↔ IsCriticalPair G y x := by
  simp only [IsCriticalPair, isTypeI_symm (G := G), isTypeII_symm (G := G)]

lemma criticalPathContains_symm {x y : V} {e : Sym2 V} :
    CriticalPathContains G x y e ↔ CriticalPathContains G y x e := by
  constructor
  · rintro (⟨hI, rfl⟩ | ⟨z, hII, rfl | rfl⟩)
    · exact Or.inl ⟨(isTypeI_symm (G := G)).mp hI, Sym2.eq_swap⟩
    · exact Or.inr ⟨z, (isTypeII_symm (G := G)).mp hII, Or.inr Sym2.eq_swap⟩
    · exact Or.inr ⟨z, (isTypeII_symm (G := G)).mp hII, Or.inl Sym2.eq_swap⟩
  · rintro (⟨hI, rfl⟩ | ⟨z, hII, rfl | rfl⟩)
    · exact Or.inl ⟨(isTypeI_symm (G := G)).mpr hI, Sym2.eq_swap⟩
    · exact Or.inr ⟨z, (isTypeII_symm (G := G)).mpr hII, Or.inr Sym2.eq_swap⟩
    · exact Or.inr ⟨z, (isTypeII_symm (G := G)).mpr hII, Or.inl Sym2.eq_swap⟩

lemma isTypeI_ne {x y : V} (h : IsTypeI G x y) : x ≠ y :=
  h.1.ne

lemma isTypeII_ne_left {x z y : V} (h : IsTypeII G x z y) : x ≠ z := by
  intro hxz
  have hz : z ∈ G.commonNeighbors x y := by simp [h.2.2]
  exact G.loopless.irrefl x (hxz ▸ (G.mem_commonNeighbors.mp hz).1)

lemma isTypeII_ne_right {x z y : V} (h : IsTypeII G x z y) : z ≠ y := by
  intro hzy
  have hz : z ∈ G.commonNeighbors x y := by simp [h.2.2]
  exact G.loopless.irrefl y (hzy ▸ (G.mem_commonNeighbors.mp hz).2)

lemma isTypeII_endpoints_ne {x z y : V} (h : IsTypeII G x z y) : x ≠ y := by
  exact h.1

lemma criticalPathContains_edge {x y : V} {e : Sym2 V}
    (h : CriticalPathContains G x y e) : e ∈ G.edgeSet := by
  rcases h with ⟨hI, rfl⟩ | ⟨z, hII, rfl | rfl⟩
  · simpa using hI.1
  · have hz : z ∈ G.commonNeighbors x y := by simp [hII.2.2]
    simpa using (G.mem_commonNeighbors.mp hz).1
  · have hz : z ∈ G.commonNeighbors x y := by simp [hII.2.2]
    simpa [adj_comm] using (G.mem_commonNeighbors.mp hz).2

lemma ediam_eq_two_of_diam_eq_two (h : G.diam = 2) : G.ediam = 2 := by
  exact (ENat.toNat_eq_iff (by norm_num : (2 : ℕ) ≠ 0)).mp (by simpa [SimpleGraph.diam] using h)

/-- If deleting an edge destroys diameter two, some pair has extended distance
strictly greater than two in the deletion.  This formulation uniformly covers
the connected and disconnected cases. -/
lemma exists_two_lt_edist_deleteEdge (hdiam : G.diam = 2) {e : Sym2 V}
    (hcritical : (G.deleteEdges {e}).diam ≠ 2) :
    ∃ x y, 2 < (G.deleteEdges {e}).edist x y := by
  let H := G.deleteEdges {e}
  have hG : G.ediam = 2 := ediam_eq_two_of_diam_eq_two (G := G) hdiam
  have hGH : G.ediam ≤ H.ediam := SimpleGraph.ediam_anti (G.deleteEdges_le {e})
  have hnle : ¬H.ediam ≤ 2 := by
    intro hle
    have heq : H.ediam = 2 := le_antisymm hle (by simpa [hG] using hGH)
    apply hcritical
    change H.diam = 2
    rw [SimpleGraph.diam, heq]
    rfl
  rw [SimpleGraph.ediam_le_iff] at hnle
  push_neg at hnle
  exact hnle

/-- If the deletion of `e` removes a common neighbor `z` of `x,y`, one of
the two incident path edges is `e`. -/
lemma eq_deletedEdge_left_or_right {e : Sym2 V} {x y z : V}
    (hz : z ∈ G.commonNeighbors x y)
    (hz' : z ∉ (G.deleteEdges {e}).commonNeighbors x y) :
    s(x, z) = e ∨ s(y, z) = e := by
  rw [G.mem_commonNeighbors] at hz
  rw [(G.deleteEdges {e}).mem_commonNeighbors] at hz'
  simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at hz'
  tauto

/-- One deleted edge can destroy at most one common neighbor of a nonadjacent
pair. -/
lemma commonNeighbor_unique_of_deleteEdge {e : Sym2 V} {x y z w : V}
    (hxy : x ≠ y) (hnadj : ¬G.Adj x y)
    (hz : z ∈ G.commonNeighbors x y) (hw : w ∈ G.commonNeighbors x y)
    (hz' : z ∉ (G.deleteEdges {e}).commonNeighbors x y)
    (hw' : w ∉ (G.deleteEdges {e}).commonNeighbors x y) : z = w := by
  have hzdel := eq_deletedEdge_left_or_right (G := G) hz hz'
  have hwdel := eq_deletedEdge_left_or_right (G := G) hw hw'
  have hzx : z ≠ x := by
    exact ((G.mem_commonNeighbors.mp hz).1.ne).symm
  have hzy : z ≠ y := by
    exact ((G.mem_commonNeighbors.mp hz).2.ne).symm
  have hwx : w ≠ x := by
    exact ((G.mem_commonNeighbors.mp hw).1.ne).symm
  have hwy : w ≠ y := by
    exact ((G.mem_commonNeighbors.mp hw).2.ne).symm
  rcases hzdel with hzdel | hzdel <;> rcases hwdel with hwdel | hwdel
  · have h : s(x, z) = s(x, w) := hzdel.trans hwdel.symm
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact h.2
    · exact (hzx h.2).elim
  · have h : s(x, z) = s(y, w) := hzdel.trans hwdel.symm
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact (hxy h.1).elim
    · exact (hwx h.1.symm).elim
  · have h : s(y, z) = s(x, w) := hzdel.trans hwdel.symm
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact (hxy h.1.symm).elim
    · exact (hwy h.1.symm).elim
  · have h : s(y, z) = s(y, w) := hzdel.trans hwdel.symm
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact h.2
    · exact (hzy h.2).elim

/-- If `xy` survives as an edge of `G` but not after deleting the same edge,
then no two-edge `x-y` path exists when the deletion has distance greater than
two. -/
lemma commonNeighbors_eq_empty_of_adj_deleteEdge {e : Sym2 V} {x y : V}
    (hxy : G.Adj x y)
    (hxy' : ¬(G.deleteEdges {e}).Adj x y)
    (hcommon' : (G.deleteEdges {e}).commonNeighbors x y = ∅) :
    G.commonNeighbors x y = ∅ := by
  have he : s(x, y) = e := by
    by_contra hne
    exact hxy' (SimpleGraph.deleteEdges_adj.mpr ⟨hxy, by simpa using hne⟩)
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hz
  have hz' : z ∉ (G.deleteEdges {e}).commonNeighbors x y := by simp [hcommon']
  have hdel := eq_deletedEdge_left_or_right (G := G) hz hz'
  have hzx : z ≠ x := ((G.mem_commonNeighbors.mp hz).1.ne).symm
  have hzy : z ≠ y := ((G.mem_commonNeighbors.mp hz).2.ne).symm
  rcases hdel with hdel | hdel
  · have h : s(x, z) = s(x, y) := hdel.trans he.symm
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact hzy h.2
    · exact hzx h.2
  · have h : s(y, z) = s(x, y) := hdel.trans he.symm
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact hzy h.2
    · exact hzx h.2

/-- Diameter criticality covers every graph edge by a unique short path. -/
lemma exists_criticalPathContains_of_diameter2Critical
    (hG : IsDiameter2Critical G) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ∃ x y, CriticalPathContains G x y e := by
  obtain ⟨x, y, hfar⟩ :=
    exists_two_lt_edist_deleteEdge (G := G) hG.1 (hG.2 e he)
  have hfar' := (SimpleGraph.two_lt_edist_iff.mp hfar)
  have hxy : x ≠ y := hfar'.1
  have hHnadj : ¬(G.deleteEdges {e}).Adj x y := hfar'.2.1
  have hHcommon : (G.deleteEdges {e}).commonNeighbors x y = ∅ := hfar'.2.2
  have hGedi : G.ediam = 2 := ediam_eq_two_of_diam_eq_two (G := G) hG.1
  have hdist : G.edist x y ≤ 2 := by simpa [hGedi] using (G.edist_le_ediam (u := x) (v := y))
  by_cases hadj : G.Adj x y
  · have heq : s(x, y) = e := by
      simpa [SimpleGraph.deleteEdges_adj, hadj] using hHnadj
    refine ⟨x, y, Or.inl ⟨?_, heq.symm⟩⟩
    exact ⟨hadj, commonNeighbors_eq_empty_of_adj_deleteEdge (G := G)
      hadj hHnadj hHcommon⟩
  · have hnonempty : (G.commonNeighbors x y).Nonempty := by
      have hnotlt : ¬2 < G.edist x y := not_lt.mpr hdist
      by_contra hempty
      have := SimpleGraph.two_lt_edist_iff.mpr ⟨hxy, hadj, Set.not_nonempty_iff_eq_empty.mp hempty⟩
      exact hnotlt this
    obtain ⟨z, hz⟩ := hnonempty
    have hzH : z ∉ (G.deleteEdges {e}).commonNeighbors x y := by simp [hHcommon]
    have hdel := eq_deletedEdge_left_or_right (G := G) hz hzH
    have hsingleton : G.commonNeighbors x y = {z} := by
      ext w
      constructor
      · intro hw
        have hwH : w ∉ (G.deleteEdges {e}).commonNeighbors x y := by simp [hHcommon]
        simpa using commonNeighbor_unique_of_deleteEdge (G := G) hxy hadj hw hz hwH hzH
      · simp_all
    refine ⟨x, y, Or.inr ⟨z, ⟨hxy, hadj, hsingleton⟩, ?_⟩⟩
    rcases hdel with hdel | hdel
    · exact Or.inl hdel.symm
    · exact Or.inr (hdel.symm.trans Sym2.eq_swap)

end CriticalPaths

section AuxiliaryGraphs

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The graph whose edges are the critical pairs of `G`. -/
noncomputable def criticalGraph : SimpleGraph V where
  Adj := IsCriticalPair G
  symm.symm _ _ := (isCriticalPair_symm (G := G)).mp
  loopless.irrefl x := by
    simp [IsCriticalPair, IsTypeI, IsTypeII]

noncomputable instance criticalGraph.instDecidableRel : DecidableRel (criticalGraph G).Adj :=
  Classical.decRel _

@[simp] lemma criticalGraph_adj {x y : V} : (criticalGraph G).Adj x y ↔
    IsCriticalPair G x y := Iff.rfl

/-- The graph joining two distinct vertices exactly when their neighborhoods
in `H` are disjoint. -/
noncomputable def disjointNeighborhoodGraph (H : SimpleGraph V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ H.commonNeighbors x y = ∅
  symm.symm x y h := ⟨h.1.symm, by simpa [H.commonNeighbors_symm] using h.2⟩
  loopless.irrefl x h := h.1 rfl

noncomputable instance disjointNeighborhoodGraph.instDecidableRel (H : SimpleGraph V) :
    DecidableRel (disjointNeighborhoodGraph H).Adj := Classical.decRel _

@[simp] lemma disjointNeighborhoodGraph_adj {H : SimpleGraph V} {x y : V} :
    (disjointNeighborhoodGraph H).Adj x y ↔ x ≠ y ∧ H.commonNeighbors x y = ∅ := Iff.rfl

/-- A finite set of pairwise vertex-disjoint edges of `H`.  We use this
elementary representation instead of the subgraph matching API because the
maximality argument is entirely finitary. -/
def EdgeMatching (H : SimpleGraph V) [DecidableRel H.Adj]
    (M : Finset (Sym2 V)) : Prop :=
  M ⊆ H.edgeFinset ∧
    (M : Set (Sym2 V)).Pairwise fun e f ↦ Disjoint (e : Set V) (f : Set V)

/-- A maximum-cardinality matching is maximal: every edge outside it meets
one of its edges. -/
lemma exists_maximal_edgeMatching (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∃ M : Finset (Sym2 V), EdgeMatching H M ∧
      ∀ e ∈ H.edgeFinset, e ∉ M →
        ∃ m ∈ M, ¬ Disjoint (e : Set V) (m : Set V) := by
  classical
  let good := H.edgeFinset.powerset.filter fun (M : Finset (Sym2 V)) ↦
    (M : Set (Sym2 V)).Pairwise fun e f ↦ Disjoint (e : Set V) (f : Set V)
  have hgood : good.Nonempty := ⟨∅, by simp [good]⟩
  obtain ⟨M, hMgood, hMmax⟩ := good.exists_max_image Finset.card hgood
  have hMsub : M ⊆ H.edgeFinset :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hMgood).1
  have hMpair : (M : Set (Sym2 V)).Pairwise
      (fun e f ↦ Disjoint (e : Set V) (f : Set V)) :=
    (Finset.mem_filter.mp hMgood).2
  refine ⟨M, ⟨hMsub, hMpair⟩, ?_⟩
  intro e heH heM
  by_contra hdisj
  push Not at hdisj
  have hpairInsert : ((insert e M : Finset (Sym2 V)) : Set (Sym2 V)).Pairwise
      (fun p q ↦ Disjoint (p : Set V) (q : Set V)) := by
    rw [Finset.coe_insert, Set.pairwise_insert]
    refine ⟨hMpair, ?_⟩
    intro m hm hem
    exact ⟨hdisj m hm, (hdisj m hm).symm⟩
  have hinsGood : insert e M ∈ good := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr ?_, hpairInsert⟩
    intro f hf
    rw [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact heH
    · exact hMsub hf
  have hle := hMmax (insert e M) hinsGood
  rw [Finset.card_insert_of_notMem heM] at hle
  omega

/-- A vertex is saturated by the finite matching `M`. -/
def IsMatched (M : Finset (Sym2 V)) (v : V) : Prop :=
  ∃ e ∈ M, v ∈ e

/-- The unique matching edge through a saturated vertex. -/
noncomputable def matchingEdge (M : Finset (Sym2 V)) (v : V)
    (hv : IsMatched M v) : M :=
  ⟨hv.choose, hv.choose_spec.1⟩

lemma matchingEdge_contains (M : Finset (Sym2 V)) (v : V)
    (hv : IsMatched M v) : v ∈ (matchingEdge M v hv : Sym2 V) :=
  hv.choose_spec.2

lemma matchingEdge_unique {M : Finset (Sym2 V)}
    (hpair : (M : Set (Sym2 V)).Pairwise
      (fun e f ↦ Disjoint (e : Set V) (f : Set V)))
    {v : V} (hv : IsMatched M v) (m : M) (hvm : v ∈ (m : Sym2 V)) :
    matchingEdge M v hv = m := by
  apply Subtype.ext
  by_contra hne
  have hd := hpair (matchingEdge M v hv).property m.property hne
  exact (Set.disjoint_left.mp hd) (matchingEdge_contains M v hv) hvm

/-- Rank of the matching edge through `v`, with unmatched vertices placed
after all matching edges. -/
noncomputable def matchingRank (M : Finset (Sym2 V)) (v : V) : ℕ :=
  by
    classical
    exact if hv : IsMatched M v then
      (Fintype.equivFin M (matchingEdge M v hv)).val else M.card

lemma matchingRank_lt_card {M : Finset (Sym2 V)} {v : V} (hv : IsMatched M v) :
    matchingRank M v < M.card := by
  simp only [matchingRank, dif_pos hv]
  simpa using (Fintype.equivFin M (matchingEdge M v hv)).isLt

lemma matchingRank_eq_card {M : Finset (Sym2 V)} {v : V} (hv : ¬ IsMatched M v) :
    matchingRank M v = M.card := by simp [matchingRank, hv]

lemma matchingEdge_eq_of_rank_eq {M : Finset (Sym2 V)}
    {v w : V} (hv : IsMatched M v) (hw : IsMatched M w)
    (hrank : matchingRank M v = matchingRank M w) :
    matchingEdge M v hv = matchingEdge M w hw := by
  simp only [matchingRank, dif_pos hv, dif_pos hw] at hrank
  apply (Fintype.equivFin M).injective
  apply Fin.ext
  exact hrank

private lemma sym2_out_mk (e : Sym2 V) : s(e.out.1, e.out.2) = e := by
  rw [Sym2.mk, e.out_eq]

/-- Orient a nonmatching edge towards the endpoint incident with the
lower-ranked matching edge. -/
noncomputable def selectedVertex (M : Finset (Sym2 V)) (e : Sym2 V) : V :=
  if matchingRank M e.out.1 ≤ matchingRank M e.out.2 then e.out.1 else e.out.2

noncomputable def otherVertex (M : Finset (Sym2 V)) (e : Sym2 V) : V :=
  if matchingRank M e.out.1 ≤ matchingRank M e.out.2 then e.out.2 else e.out.1

lemma selected_other_mk (M : Finset (Sym2 V)) (e : Sym2 V) :
    s(selectedVertex M e, otherVertex M e) = e := by
  by_cases h : matchingRank M e.out.1 ≤ matchingRank M e.out.2
  · simpa [selectedVertex, otherVertex, h] using sym2_out_mk e
  · rw [selectedVertex, otherVertex, if_neg h, if_neg h, Sym2.eq_swap]
    exact sym2_out_mk e

lemma selectedVertex_mem (M : Finset (Sym2 V)) (e : Sym2 V) : selectedVertex M e ∈ e := by
  have h := Sym2.mem_mk_left (selectedVertex M e) (otherVertex M e)
  rwa [selected_other_mk M e] at h

lemma otherVertex_mem (M : Finset (Sym2 V)) (e : Sym2 V) : otherVertex M e ∈ e := by
  have h := Sym2.mem_mk_right (selectedVertex M e) (otherVertex M e)
  rwa [selected_other_mk M e] at h

lemma selectedVertex_ne_otherVertex {H : SimpleGraph V} [DecidableRel H.Adj]
    (M : Finset (Sym2 V)) {e : Sym2 V} (he : e ∈ H.edgeFinset) :
    selectedVertex M e ≠ otherVertex M e := by
  have hadj : H.Adj (selectedVertex M e) (otherVertex M e) := by
    rw [← H.mem_edgeSet, selected_other_mk]
    exact SimpleGraph.mem_edgeFinset.mp he
  exact hadj.ne

lemma selectedVertex_isMatched {H : SimpleGraph V} [DecidableRel H.Adj]
    {M : Finset (Sym2 V)}
    (hcover : ∀ e ∈ H.edgeFinset, e ∉ M →
      ∃ m ∈ M, ¬ Disjoint (e : Set V) (m : Set V))
    {e : Sym2 V} (heH : e ∈ H.edgeFinset) (heM : e ∉ M) :
    IsMatched M (selectedVertex M e) := by
  obtain ⟨m, hmM, hm⟩ := hcover e heH heM
  obtain ⟨z, hze, hzm⟩ := Set.not_disjoint_iff.mp hm
  have hz : z = e.out.1 ∨ z = e.out.2 := by
    rw [← sym2_out_mk e] at hze
    simpa using hze
  have hsome : IsMatched M e.out.1 ∨ IsMatched M e.out.2 := by
    rcases hz with rfl | rfl
    · exact Or.inl ⟨m, hmM, hzm⟩
    · exact Or.inr ⟨m, hmM, hzm⟩
  by_cases hle : matchingRank M e.out.1 ≤ matchingRank M e.out.2
  · rw [selectedVertex, if_pos hle]
    rcases hsome with h | h
    · exact h
    · by_contra hn
      rw [matchingRank_eq_card hn] at hle
      exact (not_le_of_gt (matchingRank_lt_card h)) hle
  · rw [selectedVertex, if_neg hle]
    rcases hsome with h | h
    · by_contra hn
      have hlt := matchingRank_lt_card h
      apply hle
      rw [matchingRank_eq_card hn]
      exact hlt.le
    · exact h

lemma matchingEdges_ne_of_nonmatching_edge
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {M : Finset (Sym2 V)}
    (hpair : (M : Set (Sym2 V)).Pairwise
      (fun e f ↦ Disjoint (e : Set V) (f : Set V)))
    {e : Sym2 V} (heH : e ∈ H.edgeFinset) (heM : e ∉ M)
    (hs : IsMatched M (selectedVertex M e))
    (ho : IsMatched M (otherVertex M e)) :
    matchingEdge M (selectedVertex M e) hs ≠
      matchingEdge M (otherVertex M e) ho := by
  intro heq
  have hsMem := matchingEdge_contains M (selectedVertex M e) hs
  have hoMem : otherVertex M e ∈
      (matchingEdge M (selectedVertex M e) hs : Sym2 V) := by
    rw [heq]
    exact matchingEdge_contains M (otherVertex M e) ho
  have hedgeEq : (matchingEdge M (selectedVertex M e) hs : Sym2 V) = e := by
    have hpair' : (matchingEdge M (selectedVertex M e) hs : Sym2 V) =
        s(selectedVertex M e, otherVertex M e) :=
      (Sym2.mem_and_mem_iff (selectedVertex_ne_otherVertex M heH)).mp ⟨hsMem, hoMem⟩
    exact hpair'.trans (selected_other_mk M e)
  exact heM (hedgeEq ▸ (matchingEdge M (selectedVertex M e) hs).property)

lemma selectedVertex_rank_lt_other
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {M : Finset (Sym2 V)}
    (hpair : (M : Set (Sym2 V)).Pairwise
      (fun e f ↦ Disjoint (e : Set V) (f : Set V)))
    {e : Sym2 V} (heH : e ∈ H.edgeFinset) (heM : e ∉ M)
    (hs : IsMatched M (selectedVertex M e))
    (ho : IsMatched M (otherVertex M e)) :
    matchingRank M (selectedVertex M e) < matchingRank M (otherVertex M e) := by
  have hne := matchingEdges_ne_of_nonmatching_edge hpair heH heM hs ho
  have hrankne : matchingRank M (selectedVertex M e) ≠
      matchingRank M (otherVertex M e) := by
    intro h
    exact hne (matchingEdge_eq_of_rank_eq hs ho h)
  by_cases hle : matchingRank M e.out.1 ≤ matchingRank M e.out.2
  · have hrankne' : matchingRank M e.out.1 ≠ matchingRank M e.out.2 := by
      simpa [selectedVertex, otherVertex, hle] using hrankne
    simpa [selectedVertex, otherVertex, hle] using lt_of_le_of_ne hle hrankne'
  · have hlt : matchingRank M e.out.2 < matchingRank M e.out.1 := lt_of_not_ge hle
    simpa [selectedVertex, otherVertex, hle] using hlt

/-- The other endpoint of the matching edge through `v`. -/
noncomputable def matchingMate (M : Finset (Sym2 V)) (v : V) (hv : IsMatched M v) : V :=
  Sym2.Mem.other (matchingEdge_contains M v hv)

lemma matchingMate_spec (M : Finset (Sym2 V)) (v : V) (hv : IsMatched M v) :
    s(v, matchingMate M v hv) = (matchingEdge M v hv : Sym2 V) :=
  by simpa [matchingMate] using Sym2.other_spec (matchingEdge_contains M v hv)

lemma matchingMate_mem (M : Finset (Sym2 V)) (v : V) (hv : IsMatched M v) :
    matchingMate M v hv ∈ (matchingEdge M v hv : Sym2 V) := by
  simpa [matchingMate] using Sym2.other_mem (matchingEdge_contains M v hv)

lemma matchingRank_eq_of_matchingEdge_eq {M : Finset (Sym2 V)}
    {v w : V} (hv : IsMatched M v) (hw : IsMatched M w)
    (h : matchingEdge M v hv = matchingEdge M w hw) :
    matchingRank M v = matchingRank M w := by
  simp only [matchingRank, dif_pos hv, dif_pos hw]
  rw [h]

lemma adj_matchingMate {H : SimpleGraph V} [DecidableRel H.Adj]
    {M : Finset (Sym2 V)} (hsub : M ⊆ H.edgeFinset)
    {v : V} (hv : IsMatched M v) : H.Adj v (matchingMate M v hv) := by
  rw [← H.mem_edgeSet, matchingMate_spec]
  exact SimpleGraph.mem_edgeFinset.mp (hsub (matchingEdge M v hv).property)

lemma matchingMate_ne_otherVertex {H : SimpleGraph V} [DecidableRel H.Adj]
    {M : Finset (Sym2 V)} (hsub : M ⊆ H.edgeFinset)
    (hpair : (M : Set (Sym2 V)).Pairwise
      (fun e f ↦ Disjoint (e : Set V) (f : Set V)))
    {e : Sym2 V} (heH : e ∈ H.edgeFinset) (heM : e ∉ M)
    (hs : IsMatched M (selectedVertex M e)) :
    matchingMate M (selectedVertex M e) hs ≠ otherVertex M e := by
  intro hmate
  have hsMem := matchingEdge_contains M (selectedVertex M e) hs
  have hoMem : otherVertex M e ∈
      (matchingEdge M (selectedVertex M e) hs : Sym2 V) := by
    rw [← hmate]
    exact matchingMate_mem M (selectedVertex M e) hs
  have hpairEq : (matchingEdge M (selectedVertex M e) hs : Sym2 V) =
      s(selectedVertex M e, otherVertex M e) :=
    (Sym2.mem_and_mem_iff (selectedVertex_ne_otherVertex M heH)).mp ⟨hsMem, hoMem⟩
  have hedgeEq : (matchingEdge M (selectedVertex M e) hs : Sym2 V) = e :=
    hpairEq.trans (selected_other_mk M e)
  exact heM (hedgeEq ▸ (matchingEdge M (selectedVertex M e) hs).property)

/-- The nonmatching edges of a maximal matching inject into unordered pairs
with a common neighbor.  The lower-ranked matched endpoint is used to make
the injection canonical; a crossed collision would force two opposite strict
rank inequalities. -/
lemma nonmatching_edges_inject_commonPairs
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {M : Finset (Sym2 V)} (hM : EdgeMatching H M)
    (hcover : ∀ e ∈ H.edgeFinset, e ∉ M →
      ∃ m ∈ M, ¬ Disjoint (e : Set V) (m : Set V)) :
    (H.edgeFinset \ M).card ≤
      ((⊤ : SimpleGraph V).edgeFinset \ (disjointNeighborhoodGraph H).edgeFinset).card := by
  classical
  let source := H.edgeFinset \ M
  let target := (⊤ : SimpleGraph V).edgeFinset \
    (disjointNeighborhoodGraph H).edgeFinset
  let hit : source → target := fun e ↦ by
    have heH : e.1 ∈ H.edgeFinset := (Finset.mem_sdiff.mp e.2).1
    have heM : e.1 ∉ M := (Finset.mem_sdiff.mp e.2).2
    have hs : IsMatched M (selectedVertex M e.1) :=
      selectedVertex_isMatched hcover heH heM
    let p := s(matchingMate M (selectedVertex M e.1) hs, otherVertex M e.1)
    have hne : matchingMate M (selectedVertex M e.1) hs ≠ otherVertex M e.1 :=
      matchingMate_ne_otherVertex hM.1 hM.2 heH heM hs
    have hpTop : p ∈ (⊤ : SimpleGraph V).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      simpa using hne
    have hselOther : H.Adj (selectedVertex M e.1) (otherVertex M e.1) := by
      rw [← H.mem_edgeSet, selected_other_mk]
      exact SimpleGraph.mem_edgeFinset.mp heH
    have hcommon : selectedVertex M e.1 ∈
        H.commonNeighbors (matchingMate M (selectedVertex M e.1) hs)
          (otherVertex M e.1) := by
      rw [H.mem_commonNeighbors]
      exact ⟨(adj_matchingMate hM.1 hs).symm, hselOther.symm⟩
    have hpNot : p ∉ (disjointNeighborhoodGraph H).edgeFinset := by
      intro hp
      have hp' := (SimpleGraph.mem_edgeFinset.mp hp :
        (disjointNeighborhoodGraph H).Adj _ _)
      simpa [hp'.2] using hcommon
    exact ⟨p, Finset.mem_sdiff.mpr ⟨hpTop, hpNot⟩⟩
  have hinj : Function.Injective hit := by
    intro e f hef
    have heH : e.1 ∈ H.edgeFinset := (Finset.mem_sdiff.mp e.2).1
    have heM : e.1 ∉ M := (Finset.mem_sdiff.mp e.2).2
    have hfH : f.1 ∈ H.edgeFinset := (Finset.mem_sdiff.mp f.2).1
    have hfM : f.1 ∉ M := (Finset.mem_sdiff.mp f.2).2
    have hse : IsMatched M (selectedVertex M e.1) :=
      selectedVertex_isMatched hcover heH heM
    have hsf : IsMatched M (selectedVertex M f.1) :=
      selectedVertex_isMatched hcover hfH hfM
    have hpairs :
        s(matchingMate M (selectedVertex M e.1) hse, otherVertex M e.1) =
        s(matchingMate M (selectedVertex M f.1) hsf, otherVertex M f.1) :=
      congr_arg Subtype.val hef
    rw [Sym2.eq_iff] at hpairs
    apply Subtype.ext
    rcases hpairs with hdirect | hcross
    · have heMateMem := matchingMate_mem M (selectedVertex M e.1) hse
      have hfMateMem : matchingMate M (selectedVertex M e.1) hse ∈
          (matchingEdge M (selectedVertex M f.1) hsf : Sym2 V) := by
        rw [hdirect.1]
        exact matchingMate_mem M (selectedVertex M f.1) hsf
      have hedges : matchingEdge M (selectedVertex M e.1) hse =
          matchingEdge M (selectedVertex M f.1) hsf := by
        apply Subtype.ext
        by_contra hne
        have hd := hM.2 (matchingEdge M (selectedVertex M e.1) hse).property
          (matchingEdge M (selectedVertex M f.1) hsf).property hne
        exact (Set.disjoint_left.mp hd) heMateMem hfMateMem
      have hedgePairs :
          s(selectedVertex M e.1, matchingMate M (selectedVertex M e.1) hse) =
          s(selectedVertex M f.1, matchingMate M (selectedVertex M f.1) hsf) := by
        rw [matchingMate_spec, matchingMate_spec, hedges]
      rw [Sym2.eq_iff] at hedgePairs
      have hsel : selectedVertex M e.1 = selectedVertex M f.1 := by
        rcases hedgePairs with h | h
        · exact h.1
        · exact ((adj_matchingMate hM.1 hse).ne
            (h.1.trans hdirect.1.symm)).elim
      rw [← selected_other_mk M e.1, ← selected_other_mk M f.1, hsel, hdirect.2]
    · have heMateMem := matchingMate_mem M (selectedVertex M e.1) hse
      have hfMateMem := matchingMate_mem M (selectedVertex M f.1) hsf
      have hoe : IsMatched M (otherVertex M e.1) := by
        refine ⟨matchingEdge M (selectedVertex M f.1) hsf,
          (matchingEdge M (selectedVertex M f.1) hsf).property, ?_⟩
        rw [hcross.2]
        exact hfMateMem
      have hof : IsMatched M (otherVertex M f.1) := by
        refine ⟨matchingEdge M (selectedVertex M e.1) hse,
          (matchingEdge M (selectedVertex M e.1) hse).property, ?_⟩
        rw [← hcross.1]
        exact heMateMem
      have heEdges : matchingEdge M (selectedVertex M e.1) hse =
          matchingEdge M (otherVertex M f.1) hof := by
        symm
        apply matchingEdge_unique hM.2 hof
        rw [← hcross.1]
        exact heMateMem
      have hfEdges : matchingEdge M (selectedVertex M f.1) hsf =
          matchingEdge M (otherVertex M e.1) hoe := by
        symm
        apply matchingEdge_unique hM.2 hoe
        rw [hcross.2]
        exact hfMateMem
      have hre : matchingRank M (selectedVertex M e.1) =
          matchingRank M (otherVertex M f.1) :=
        matchingRank_eq_of_matchingEdge_eq hse hof heEdges
      have hrf : matchingRank M (selectedVertex M f.1) =
          matchingRank M (otherVertex M e.1) :=
        matchingRank_eq_of_matchingEdge_eq hsf hoe hfEdges
      have hltE := selectedVertex_rank_lt_other hM.2 heH heM hse hoe
      have hltF := selectedVertex_rank_lt_other hM.2 hfH hfM hsf hof
      omega
  simpa [source, target] using Finset.card_le_card_of_injective (f := hit) hinj

/-- A matching has at most half as many edges as the ambient graph has
vertices. -/
lemma edgeMatching_card_le_half
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {M : Finset (Sym2 V)} (hM : EdgeMatching H M) :
    M.card ≤ Fintype.card V / 2 := by
  classical
  let endpoint : M × Bool → V := fun p ↦
    if p.2 then p.1.1.out.1 else p.1.1.out.2
  have hinj : Function.Injective endpoint := by
    rintro ⟨e, i⟩ ⟨f, j⟩ hij
    have hei : endpoint (e, i) ∈ (e.1 : Sym2 V) := by
      cases i <;> simp [endpoint, Sym2.out_fst_mem, Sym2.out_snd_mem]
    have hfj : endpoint (f, j) ∈ (f.1 : Sym2 V) := by
      cases j <;> simp [endpoint, Sym2.out_fst_mem, Sym2.out_snd_mem]
    have hef : e = f := by
      apply Subtype.ext
      by_contra hne
      have hd := hM.2 e.property f.property hne
      exact (Set.disjoint_left.mp hd) hei (hij ▸ hfj)
    subst f
    have heH : e.1 ∈ H.edgeFinset := hM.1 e.property
    have hadj : H.Adj e.1.out.1 e.1.out.2 := by
      rw [← H.mem_edgeSet, sym2_out_mk]
      exact SimpleGraph.mem_edgeFinset.mp heH
    have hne := hadj.ne
    cases i <;> cases j <;> simp_all [endpoint]
  have hcard := Fintype.card_le_of_injective endpoint hinj
  have htwo : M.card * 2 ≤ Fintype.card V := by
    simpa using hcard
  exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr htwo

private lemma choose_two_add_half_eq_half_square (n : ℕ) :
    n.choose 2 + n / 2 = n ^ 2 / 2 := by
  rw [Nat.choose_two_right]
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst n
    cases k with
    | zero => decide
    | succ k =>
      have hp : ((k + 1 + (k + 1)) * (k + 1 + (k + 1) - 1)) =
          2 * ((k + 1) * (k + 1 + (k + 1) - 1)) := by ring
      have hs : (k + 1 + (k + 1)) ^ 2 = 2 * (2 * (k + 1) ^ 2) := by ring
      have hpred : k + 1 + (k + 1) - 1 = 2 * k + 1 := by omega
      rw [hp, hs]
      have heven : k + 1 + (k + 1) = 2 * (k + 1) := by ring
      rw [hpred, heven]
      simp
      ring
  · subst n
    have hp : (2 * k + 1) * (2 * k + 1 - 1) = 2 * (k * (2 * k + 1)) := by
      simp
      ring
    have hs : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
    rw [hp, hs]
    simp [Nat.mul_add_div]
    ring

/-- For every finite graph `H`, the number of its edges plus the number of
pairs with disjoint `H`-neighborhoods is at most `n² / 2`. -/
lemma card_edges_add_disjointNeighborhood_le
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    H.edgeFinset.card + (disjointNeighborhoodGraph H).edgeFinset.card ≤
      Fintype.card V ^ 2 / 2 := by
  classical
  obtain ⟨M, hM, hcover⟩ := exists_maximal_edgeMatching H
  have hinj := nonmatching_edges_inject_commonPairs H hM hcover
  have hMcard := edgeMatching_card_le_half H hM
  have hMsub := hM.1
  have hDsub : (disjointNeighborhoodGraph H).edgeFinset ⊆
      (⊤ : SimpleGraph V).edgeFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact SimpleGraph.edgeSet_mono
      (show disjointNeighborhoodGraph H ≤ (⊤ : SimpleGraph V) from le_top) he
  have hHsplit := Finset.card_sdiff_add_card_eq_card hMsub
  have hTsplit := Finset.card_sdiff_add_card_eq_card hDsub
  have htop : (⊤ : SimpleGraph V).edgeFinset.card = (Fintype.card V).choose 2 :=
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two
  rw [htop] at hTsplit
  rw [← choose_two_add_half_eq_half_square (Fintype.card V)]
  omega

/-- If no type-II critical path survives completely in `H`, then every
critical pair of `G` has disjoint neighborhoods in `H`. -/
lemma criticalGraph_le_disjointNeighborhoodGraph {H : SimpleGraph V} (hHG : H ≤ G)
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y)) :
    criticalGraph G ≤ disjointNeighborhoodGraph H := by
  intro x y hxy
  refine ⟨?_, ?_⟩
  · rcases hxy with hI | ⟨z, hII'⟩
    · exact hI.1.ne
    · exact hII'.1
  · ext w
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hw
    have hwG : w ∈ G.commonNeighbors x y := by
      rw [G.mem_commonNeighbors]
      exact ⟨hHG (H.mem_commonNeighbors.mp hw).1, hHG (H.mem_commonNeighbors.mp hw).2⟩
    rcases hxy with hI | ⟨z, hII'⟩
    · simpa [hI.2] using hwG
    · have hwz : w = z := by simpa [hII'.2.2] using hwG
      exact hII x z y hII' (by
        have h := H.mem_commonNeighbors.mp hw
        exact ⟨by simpa [hwz] using h.1, by simpa [hwz] using h.2.symm⟩)

/-- Under the same pruning hypothesis, one critical path contains at most
one edge of `H`. -/
lemma criticalPathContains_unique_edge {H : SimpleGraph V}
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y))
    {x y : V} {e f : Sym2 V} (heH : e ∈ H.edgeSet) (hfH : f ∈ H.edgeSet)
    (he : CriticalPathContains G x y e) (hf : CriticalPathContains G x y f) : e = f := by
  rcases he with ⟨heI, rfl⟩ | ⟨z, heII, rfl | rfl⟩
  · rcases hf with ⟨-, rfl⟩ | ⟨w, hwII, -⟩
    · rfl
    · exact (hwII.2.1 heI.1).elim
  · rcases hf with ⟨hfI, -⟩ | ⟨w, hwII, rfl | rfl⟩
    · exact (heII.2.1 hfI.1).elim
    · have hwz : w = z := (by simpa [heII.2.2] using hwII.2.2 : z = w).symm
      simp [hwz]
    · have hwz : w = z := (by simpa [heII.2.2] using hwII.2.2 : z = w).symm
      subst w
      exact (hII x z y heII ⟨by simpa using heH, by simpa [adj_comm] using hfH⟩).elim
  · rcases hf with ⟨hfI, -⟩ | ⟨w, hwII, rfl | rfl⟩
    · exact (heII.2.1 hfI.1).elim
    · have hwz : w = z := (by simpa [heII.2.2] using hwII.2.2 : z = w).symm
      subst w
      exact (hII x z y heII ⟨by simpa using hfH, by simpa [adj_comm] using heH⟩).elim
    · have hwz : w = z := (by simpa [heII.2.2] using hwII.2.2 : z = w).symm
      simp [hwz]

/-- The surviving edges inject into the critical pairs. -/
lemma card_edgeFinset_le_card_criticalGraph {H : SimpleGraph V} [DecidableRel H.Adj]
    (hHG : H ≤ G) (hG : IsDiameter2Critical G)
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y)) :
    H.edgeFinset.card ≤ (criticalGraph G).edgeFinset.card := by
  classical
  choose x y hpath using fun e : H.edgeFinset ↦
    exists_criticalPathContains_of_diameter2Critical (G := G) hG
      ((SimpleGraph.edgeSet_mono hHG) (SimpleGraph.mem_edgeFinset.mp e.2))
  let target : H.edgeFinset → (criticalGraph G).edgeFinset := fun e ↦
    ⟨s(x e, y e), by
      rw [SimpleGraph.mem_edgeFinset]
      exact (hpath e).elim
        (fun hI ↦ Or.inl hI.1) (fun hII' ↦ Or.inr ⟨hII'.choose, hII'.choose_spec.1⟩)⟩
  refine Finset.card_le_card_of_injective (f := target) ?_
  intro e f hef
  apply Subtype.ext
  apply criticalPathContains_unique_edge (G := G) hII
    (SimpleGraph.mem_edgeFinset.mp e.2) (SimpleGraph.mem_edgeFinset.mp f.2)
  · exact hpath e
  · have hpairs : s(x e, y e) = s(x f, y f) := congr_arg Subtype.val hef
    rw [Sym2.eq_iff] at hpairs
    rcases hpairs with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · simpa [hx, hy] using hpath f
    · simpa [hx, hy] using (criticalPathContains_symm (G := G)).mp (hpath f)

/-- Restricting the original graph can only create new pairs with disjoint
neighborhoods. -/
lemma induce_disjointNeighborhoodGraph_le (H : SimpleGraph V) (S : Set V) :
    (disjointNeighborhoodGraph H).induce S ≤ disjointNeighborhoodGraph (H.induce S) := by
  intro a b hab
  refine ⟨fun h ↦ hab.1 (congr_arg Subtype.val h), ?_⟩
  ext w
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hw
  have hw' := (H.induce S).mem_commonNeighbors.mp hw
  have hwH : (w : V) ∈ H.commonNeighbors (a : V) (b : V) := by
    rw [H.mem_commonNeighbors]
    exact hw'
  have : (w : V) ∈ (∅ : Set V) := hab.2 ▸ hwH
  exact this

private lemma half_square_step (n : ℕ) :
    (n - 1) ^ 2 / 2 + (n - 1) ≤ n ^ 2 / 2 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst n
    cases k with
    | zero => norm_num
    | succ k =>
      simp [pow_two, Nat.add_mul, Nat.mul_add]
      omega
  · subst n
    simp [pow_two, Nat.add_mul, Nat.mul_add]
    omega

private lemma choose_two_le_half_square (n : ℕ) : n.choose 2 ≤ n ^ 2 / 2 := by
  rw [Nat.choose_two_right]
  exact Nat.div_le_div_right (by simpa [pow_two] using
    (Nat.mul_le_mul_left n (Nat.sub_le n 1)))

/-- Unless `H` is empty, a neighbor of a maximum-degree vertex has total
degree in `H` and `disj H` at most `n`. -/
lemma exists_degree_add_disjoint_degree_le_card (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : H ≠ ⊥) :
    ∃ y, H.degree y + (disjointNeighborhoodGraph H).degree y ≤ Fintype.card V := by
  have : Nonempty V := by
    by_contra h
    have : IsEmpty V := not_nonempty_iff.mp h
    exact hH (Subsingleton.elim _ _)
  obtain ⟨x, hx⟩ := H.exists_maximal_degree_vertex
  have hxpos : 0 < H.degree x := by
    rw [← hx]
    exact Nat.pos_of_ne_zero (by simpa using hH)
  obtain ⟨y, hxy⟩ := H.degree_pos_iff_exists_adj x |>.mp hxpos
  refine ⟨y, ?_⟩
  have hdeg : H.degree y ≤ H.degree x := (H.degree_le_maxDegree y).trans_eq hx
  let A := H.neighborFinset x \ {y}
  let B := (disjointNeighborhoodGraph H).neighborFinset y
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    have hzA' : z ∈ H.neighborFinset x \ {y} := by simpa [A] using hzA
    have hxz : H.Adj x z := by simpa using (Finset.mem_sdiff.mp hzA').1
    have hyz : (disjointNeighborhoodGraph H).Adj y z := by simpa [B] using hzB
    have hcommon : x ∈ H.commonNeighbors y z := by
      rw [H.mem_commonNeighbors]
      exact ⟨hxy.symm, hxz.symm⟩
    simpa [hyz.2] using hcommon
  have hunion : A ∪ B ⊆ Finset.univ.erase y := by
    intro z hz
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ z⟩
    rcases Finset.mem_union.mp hz with hzA | hzB
    · have hzA' : z ∈ H.neighborFinset x \ {y} := by simpa [A] using hzA
      simpa using (Finset.mem_sdiff.mp hzA').2
    · exact ((disjointNeighborhoodGraph H).ne_of_adj (by simpa [B] using hzB)).symm
  have hcard_union : A.card + B.card ≤ Fintype.card V - 1 := by
    rw [← Finset.card_union_of_disjoint hAB]
    exact (Finset.card_le_card hunion).trans_eq (by simp)
  have hcardA : A.card = H.degree x - 1 := by
    dsimp [A]
    simp [Finset.card_sdiff, H.card_neighborFinset_eq_degree, hxy]
  have hcardB : B.card = (disjointNeighborhoodGraph H).degree y := by
    exact (disjointNeighborhoodGraph H).card_neighborFinset_eq_degree y
  have hdegree_pred : H.degree x - 1 + 1 = H.degree x :=
    Nat.sub_add_cancel hxpos
  have hcard_pred : Fintype.card V - 1 + 1 = Fintype.card V :=
    Nat.sub_add_cancel Fintype.card_pos
  omega

/-- Mantel's theorem in precisely the natural-number form used by Problem
742. -/
lemma card_edgeFinset_le_quarter_of_cliqueFree_three {H : SimpleGraph V}
    [DecidableRel H.Adj] (hH : H.CliqueFree 3) :
    H.edgeFinset.card ≤ Fintype.card V ^ 2 / 4 := by
  let n := Fintype.card V
  have heq : (n ^ 2 - (n % 2) ^ 2) / 4 + (n % 2).choose 2 = n ^ 2 / 4 := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk]
      have hs : (k + k) ^ 2 = 4 * (k * k) := by ring
      have hm : (k + k) % 2 = 0 := by omega
      rw [hs, hm]
      simp
    · rw [hk]
      have hs : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
      have hm : (2 * k + 1) % 2 = 1 := by omega
      rw [hs, hm]
      simp
      omega
  rw [← heq]
  simpa only [Nat.mul_one, Nat.reduceSub, Nat.reduceMul] using
    hH.card_edgeFinset_le (r := 2)

end AuxiliaryGraphs

section Multiplicity

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Number of ordered critical pairs whose critical path contains `e`.
Using ordered pairs only changes the inessential factor two and makes the
finite double count especially direct. -/
noncomputable def edgeMultiplicity (e : Sym2 V) : ℕ :=
  ((Finset.univ : Finset (V × V)).filter fun (p : V × V) ↦
    CriticalPathContains G p.1 p.2 e).card

/-- Canonically oriented type-II critical paths whose two edges both have
ordered multiplicity below `M`.  The endpoint order removes the duplicate
obtained by reversing a path. -/
noncomputable def lightTriples [LinearOrder V] (M : ℕ) : Finset (V × V × V) :=
  by
    classical
    exact (Finset.univ : Finset (V × V × V)).filter fun p ↦
      p.1 < p.2.2 ∧ IsTypeII G p.1 p.2.1 p.2.2 ∧
        edgeMultiplicity G s(p.1, p.2.1) < M ∧
        edgeMultiplicity G s(p.2.1, p.2.2) < M

@[simp] lemma mem_lightTriples [LinearOrder V] {M : ℕ} {x z y : V} :
    (x, z, y) ∈ lightTriples G M ↔
      x < y ∧ IsTypeII G x z y ∧
        edgeMultiplicity G s(x, z) < M ∧ edgeMultiplicity G s(z, y) < M := by
  simp [lightTriples]

/-- Two oriented triples conflict when they share two corresponding
coordinates. -/
def TripleConflict (p q : V × V × V) : Prop :=
  (p.1 = q.1 ∧ p.2.1 = q.2.1) ∨
    (p.1 = q.1 ∧ p.2.2 = q.2.2) ∨
    (p.2.1 = q.2.1 ∧ p.2.2 = q.2.2)

instance tripleConflict.instDecidableRel : DecidableRel (TripleConflict (V := V)) :=
  by
    intro p q
    unfold TripleConflict
    infer_instance

lemma tripleConflict_symm : Std.Symm (TripleConflict (V := V)) := by
  constructor
  intro p q h
  rcases h with h | h | h
  · exact Or.inl ⟨h.1.symm, h.2.symm⟩
  · exact Or.inr (Or.inl ⟨h.1.symm, h.2.symm⟩)
  · exact Or.inr (Or.inr ⟨h.1.symm, h.2.symm⟩)

/-- The center of a type-II critical path is determined by its endpoints. -/
lemma isTypeII_center_unique {x z z' y : V}
    (hz : IsTypeII G x z y) (hz' : IsTypeII G x z' y) : z = z' := by
  simpa [hz.2.2] using hz'.2.2

/-- Among light triples, a conflict is already witnessed by equality of one
of the two path edges (the endpoint-pair alternative forces equality). -/
lemma tripleConflict_of_lightTriples_imp_pathEdge
    [LinearOrder V] {M : ℕ} {p q : V × V × V}
    (hp : p ∈ lightTriples G M) (hq : q ∈ lightTriples G M)
    (h : p = q ∨ TripleConflict p q) :
    (p.1 = q.1 ∧ p.2.1 = q.2.1) ∨
      (p.2.1 = q.2.1 ∧ p.2.2 = q.2.2) := by
  rcases h with rfl | h
  · exact Or.inl ⟨rfl, rfl⟩
  rcases h with h | h | h
  · exact Or.inl h
  · have hpII : IsTypeII G p.1 p.2.1 p.2.2 :=
      (mem_lightTriples (G := G)).mp hp |>.2.1
    have hqII : IsTypeII G q.1 q.2.1 q.2.2 :=
      (mem_lightTriples (G := G)).mp hq |>.2.1
    have hc : p.2.1 = q.2.1 := by
      apply isTypeII_center_unique (G := G) hpII
      simpa [h.1, h.2] using hqII
    exact Or.inl ⟨h.1, hc⟩
  · exact Or.inr h

private lemma lightTriples_firstEdge_fiber_card_le [LinearOrder V]
    {M : ℕ} {p : V × V × V} (hp : p ∈ lightTriples G M) :
    ((lightTriples G M).filter fun q ↦ q.1 = p.1 ∧ q.2.1 = p.2.1).card ≤
      edgeMultiplicity G s(p.1, p.2.1) := by
  classical
  let source := (lightTriples G M).filter fun q ↦ q.1 = p.1 ∧ q.2.1 = p.2.1
  let target := (Finset.univ : Finset (V × V)).filter fun q ↦
    CriticalPathContains G q.1 q.2 s(p.1, p.2.1)
  let f : source → target := fun q ↦
    ⟨(q.1.1, q.1.2.2), by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hqmem : q.1 ∈ lightTriples G M := (Finset.mem_filter.mp q.2).1
      have hqeq := (Finset.mem_filter.mp q.2).2
      have hqII : IsTypeII G q.1.1 q.1.2.1 q.1.2.2 :=
        ((mem_lightTriples (G := G)).mp hqmem).2.1
      exact Or.inr ⟨q.1.2.1, hqII, Or.inl (by simp [hqeq.1, hqeq.2])⟩⟩
  have hinj : Function.Injective f := by
    intro q r hqr
    apply Subtype.ext
    have hend : q.1.2.2 = r.1.2.2 := congr_arg (fun x => x.2) (congr_arg Subtype.val hqr)
    have hqeq := (Finset.mem_filter.mp q.2).2
    have hreq := (Finset.mem_filter.mp r.2).2
    apply Prod.ext
    · exact hqeq.1.trans hreq.1.symm
    · apply Prod.ext
      · exact hqeq.2.trans hreq.2.symm
      · exact hend
  simpa [source, target, edgeMultiplicity] using
    (Finset.card_le_card_of_injective (f := f) hinj)

private lemma lightTriples_secondEdge_fiber_card_le [LinearOrder V]
    {M : ℕ} {p : V × V × V} (hp : p ∈ lightTriples G M) :
    ((lightTriples G M).filter fun q ↦ q.2.1 = p.2.1 ∧ q.2.2 = p.2.2).card ≤
      edgeMultiplicity G s(p.2.1, p.2.2) := by
  classical
  let source := (lightTriples G M).filter fun q ↦ q.2.1 = p.2.1 ∧ q.2.2 = p.2.2
  let target := (Finset.univ : Finset (V × V)).filter fun q ↦
    CriticalPathContains G q.1 q.2 s(p.2.1, p.2.2)
  let f : source → target := fun q ↦
    ⟨(q.1.1, q.1.2.2), by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hqmem : q.1 ∈ lightTriples G M := (Finset.mem_filter.mp q.2).1
      have hqeq := (Finset.mem_filter.mp q.2).2
      have hqII : IsTypeII G q.1.1 q.1.2.1 q.1.2.2 :=
        ((mem_lightTriples (G := G)).mp hqmem).2.1
      exact Or.inr ⟨q.1.2.1, hqII, Or.inr (by simp [hqeq.1, hqeq.2])⟩⟩
  have hinj : Function.Injective f := by
    intro q r hqr
    apply Subtype.ext
    have hfirst : q.1.1 = r.1.1 := congr_arg (fun x => x.1) (congr_arg Subtype.val hqr)
    have hqeq := (Finset.mem_filter.mp q.2).2
    have hreq := (Finset.mem_filter.mp r.2).2
    apply Prod.ext
    · exact hfirst
    · apply Prod.ext
      · exact hqeq.1.trans hreq.1.symm
      · exact hqeq.2.trans hreq.2.symm
  simpa [source, target, edgeMultiplicity] using
    (Finset.card_le_card_of_injective (f := f) hinj)

private lemma lightTriples_closedConflict_card_le [LinearOrder V]
    {M : ℕ} {p : V × V × V} (hp : p ∈ lightTriples G M) :
    ((lightTriples G M).filter fun q ↦ q = p ∨ TripleConflict p q).card ≤ 2 * M := by
  classical
  let A := (lightTriples G M).filter fun q ↦ q.1 = p.1 ∧ q.2.1 = p.2.1
  let B := (lightTriples G M).filter fun q ↦ q.2.1 = p.2.1 ∧ q.2.2 = p.2.2
  have hsub : (lightTriples G M).filter (fun q ↦ q = p ∨ TripleConflict p q) ⊆ A ∪ B := by
    intro q hq
    have hqL : q ∈ lightTriples G M := (Finset.mem_filter.mp hq).1
    have hclosed := (Finset.mem_filter.mp hq).2
    have hedge := tripleConflict_of_lightTriples_imp_pathEdge (G := G) hp hqL
      (hclosed.elim (fun h ↦ Or.inl h.symm) Or.inr)
    rw [Finset.mem_union]
    rcases hedge with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨hqL, ⟨h.1.symm, h.2.symm⟩⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hqL, ⟨h.1.symm, h.2.symm⟩⟩)
  have hA : A.card ≤ edgeMultiplicity G s(p.1, p.2.1) := by
    simpa [A] using lightTriples_firstEdge_fiber_card_le (G := G) hp
  have hB : B.card ≤ edgeMultiplicity G s(p.2.1, p.2.2) := by
    simpa [B] using lightTriples_secondEdge_fiber_card_le (G := G) hp
  have hmult := (mem_lightTriples (G := G)).mp hp
  calc
    _ ≤ (A ∪ B).card := Finset.card_le_card hsub
    _ ≤ A.card + B.card := Finset.card_union_le A B
    _ ≤ edgeMultiplicity G s(p.1, p.2.1) + edgeMultiplicity G s(p.2.1, p.2.2) :=
      Nat.add_le_add hA hB
    _ ≤ 2 * M := by
      have h1 : edgeMultiplicity G s(p.1, p.2.1) < M := hmult.2.2.1
      have h2 : edgeMultiplicity G s(p.2.1, p.2.2) < M := hmult.2.2.2
      omega

/-- A light-path family contains a large subfamily whose tripartite shadow is
locally linear.  Mathlib's `TripartiteFromTriangles` construction packages
both edge-disjointness and the absence of accidental triangles. -/
lemma exists_locallyLinear_lightTriples [LinearOrder V] (M : ℕ) :
    ∃ t ⊆ lightTriples G M,
      (lightTriples G M).card ≤ (2 * M + 1) * t.card ∧
      (SimpleGraph.TripartiteFromTriangles.graph t).LocallyLinear := by
  classical
  obtain ⟨t, hts, hpair, hcard⟩ :=
    exists_large_pairwise_subset (lightTriples G M) (TripleConflict (V := V))
      tripleConflict_symm (2 * M) (fun p hp ↦
        (lightTriples_closedConflict_card_le (G := G) hp).trans (Nat.le_succ _))
  have hExplicit : SimpleGraph.TripartiteFromTriangles.ExplicitDisjoint t := by
    constructor
    · intro a b c a' h h'
      by_contra hne
      have hneq : (a, b, c) ≠ (a', b, c) := by
        intro heq
        exact hne (congr_arg (fun p : V × V × V => p.1) heq)
      exact (hpair h h' hneq) (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · intro a b c b' h h'
      by_contra hne
      have hneq : (a, b, c) ≠ (a, b', c) := by
        intro heq
        exact hne (congr_arg (fun p : V × V × V => p.2.1) heq)
      exact (hpair h h' hneq) (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · intro a b c c' h h'
      by_contra hne
      have hneq : (a, b, c) ≠ (a, b, c') := by
        intro heq
        exact hne (congr_arg (fun p : V × V × V => p.2.2) heq)
      exact (hpair h h' hneq) (Or.inl ⟨rfl, rfl⟩)
  have hNoAccidental : SimpleGraph.TripartiteFromTriangles.NoAccidental t := by
    constructor
    intro a a' b b' c c' ha hb hc
    by_contra hnone
    push Not at hnone
    have haL : (a', b, c) ∈ lightTriples G M := hts ha
    have hbL : (a, b', c) ∈ lightTriples G M := hts hb
    have hcL : (a, b, c') ∈ lightTriples G M := hts hc
    have haII : IsTypeII G a' b c := ((mem_lightTriples (G := G)).mp haL).2.1
    have hbII : IsTypeII G a b' c := ((mem_lightTriples (G := G)).mp hbL).2.1
    have hcII : IsTypeII G a b c' := ((mem_lightTriples (G := G)).mp hcL).2.1
    have hab : G.Adj a b := by
      have hbmem : b ∈ G.commonNeighbors a c' := by simp [hcII.2.2]
      exact (G.mem_commonNeighbors.mp hbmem).1
    have hbc : G.Adj b c := by
      have hbmem : b ∈ G.commonNeighbors a' c := by simp [haII.2.2]
      exact (G.mem_commonNeighbors.mp hbmem).2.symm
    have hbmem : b ∈ G.commonNeighbors a c := by
      rw [G.mem_commonNeighbors]
      exact ⟨hab, hbc.symm⟩
    have hbb' : b = b' := by simpa [hbII.2.2] using hbmem
    exact hnone.2.1 hbb'
  let := hExplicit
  let := hNoAccidental
  exact ⟨t, hts, hcard, SimpleGraph.TripartiteFromTriangles.locallyLinear t⟩

lemma card_le_tripartite_cliqueFinset (t : Finset (V × V × V)) :
    t.card ≤ ((SimpleGraph.TripartiteFromTriangles.graph t).cliqueFinset 3).card := by
  classical
  rw [← Finset.card_map SimpleGraph.TripartiteFromTriangles.toTriangle]
  apply Finset.card_le_card
  intro s hs
  rw [Finset.mem_map] at hs
  obtain ⟨p, hp, rfl⟩ := hs
  rw [SimpleGraph.mem_cliqueFinset_iff]
  exact SimpleGraph.TripartiteFromTriangles.toTriangle_is3Clique hp

/-- Edges of ordered multiplicity at least `M`. -/
noncomputable def heavyEdges (M : ℕ) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ M ≤ edgeMultiplicity G e

private lemma criticalPath_edge_fiber_card_le_two (x y : V) :
    ((G.edgeFinset.filter fun e ↦ CriticalPathContains G x y e).card) ≤ 2 := by
  classical
  by_cases hI : IsTypeI G x y
  · have hsub : G.edgeFinset.filter (fun e ↦ CriticalPathContains G x y e) ⊆ {s(x, y)} := by
      intro e he
      rw [Finset.mem_singleton]
      rcases (Finset.mem_filter.mp he).2 with ⟨-, he⟩ | ⟨z, hII, -⟩
      · exact he
      · exact (hII.2.1 hI.1).elim
    exact (Finset.card_le_card hsub).trans (by simp)
  · by_cases hIIex : ∃ z, IsTypeII G x z y
    · obtain ⟨z, hz⟩ := hIIex
      have hsub : G.edgeFinset.filter (fun e ↦ CriticalPathContains G x y e) ⊆
          {s(x, z), s(z, y)} := by
        intro e he
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases (Finset.mem_filter.mp he).2 with ⟨hI', -⟩ | ⟨w, hw, hew⟩
        · exact (hI hI').elim
        · have hwz : w = z := by
            have : ({w} : Set V) = {z} := hw.2.2.symm.trans hz.2.2
            simpa using Set.singleton_injective this
          subst w
          exact hew
      exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _ |>.trans (by simp))
    · have hempty : G.edgeFinset.filter (fun e ↦ CriticalPathContains G x y e) = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨e, he⟩
        rcases (Finset.mem_filter.mp he).2 with ⟨hI', -⟩ | ⟨z, hII, -⟩
        · exact hI hI'
        · exact hIIex ⟨z, hII⟩
      simp [hempty]

/-- Heavy edges are few: this is the critical-path incidence double count. -/
lemma heavyEdges_card_mul_le (M : ℕ) :
    (heavyEdges G M).card * M ≤ 2 * Fintype.card V ^ 2 := by
  classical
  let r : Sym2 V → V × V → Prop := fun e p ↦ CriticalPathContains G p.1 p.2 e
  have hdouble := Finset.card_mul_le_card_mul (r := r)
    (s := heavyEdges G M) (t := (Finset.univ : Finset (V × V)))
    (m := M) (n := 2) (fun e he ↦ ?_) (fun p hp ↦ ?_)
  · calc
      (heavyEdges G M).card * M ≤ (Finset.univ : Finset (V × V)).card * 2 := hdouble
      _ = 2 * Fintype.card V ^ 2 := by
        simp [Fintype.card_prod, pow_two]
        ring
  · simpa [Finset.bipartiteAbove, r, heavyEdges, edgeMultiplicity] using
      (Finset.mem_filter.mp he).2
  · calc
      ((heavyEdges G M).bipartiteBelow r p).card ≤
          (G.edgeFinset.filter fun e ↦ CriticalPathContains G p.1 p.2 e).card := by
        apply Finset.card_le_card
        intro e he
        simp only [Finset.mem_bipartiteBelow] at he
        rw [Finset.mem_filter]
        exact ⟨(Finset.mem_filter.mp he.1).1, he.2⟩
      _ ≤ 2 := criticalPath_edge_fiber_card_le_two (G := G) p.1 p.2

/-- Edges appearing in a type-II critical path whose two edges both have
ordered multiplicity below `M`. -/
noncomputable def lightPathEdges (M : ℕ) : Finset (Sym2 V) :=
  by
    classical
    exact G.edgeFinset.filter fun e ↦ ∃ x z y,
      IsTypeII G x z y ∧ edgeMultiplicity G s(x, z) < M ∧
        edgeMultiplicity G s(z, y) < M ∧ (e = s(x, z) ∨ e = s(z, y))

lemma lightPathEdges_card_le_two_mul_lightTriples [LinearOrder V] (M : ℕ) :
    (lightPathEdges G M).card ≤ 2 * (lightTriples G M).card := by
  classical
  let U := (lightTriples G M).biUnion fun p ↦
    ({s(p.1, p.2.1), s(p.2.1, p.2.2)} : Finset (Sym2 V))
  have hsub : lightPathEdges G M ⊆ U := by
    intro e he
    obtain ⟨heG, x, z, y, hII, hxz, hzy, hepath⟩ := by
      simpa [lightPathEdges] using he
    have hxy : x ≠ y := isTypeII_endpoints_ne (G := G) hII
    by_cases hlt : x < y
    · have ht : (x, z, y) ∈ lightTriples G M := by
        exact (mem_lightTriples (G := G)).mpr ⟨hlt, hII, hxz, hzy⟩
      rw [Finset.mem_biUnion]
      refine ⟨(x, z, y), ht, ?_⟩
      simpa using hepath
    · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hlt) hxy.symm
      have ht : (y, z, x) ∈ lightTriples G M := by
        apply (mem_lightTriples (G := G)).mpr
        refine ⟨hyx, isTypeII_symm (G := G) |>.mpr hII, ?_, ?_⟩
        · rw [Sym2.eq_swap]
          exact hzy
        · rw [Sym2.eq_swap]
          exact hxz
      rw [Finset.mem_biUnion]
      refine ⟨(y, z, x), ht, ?_⟩
      rcases hepath with rfl | rfl <;> simp
  calc
    (lightPathEdges G M).card ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ lightTriples G M,
        ({s(p.1, p.2.1), s(p.2.1, p.2.2)} : Finset (Sym2 V)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ lightTriples G M, 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact (Finset.card_insert_le _ _).trans (by simp)
    _ = 2 * (lightTriples G M).card := by simp [Nat.mul_comm]

/-- Füredi's pruned spanning graph: remove heavy edges and all edges of
light type-II critical paths. -/
noncomputable def prunedGraph (M : ℕ) : SimpleGraph V :=
  G.deleteEdges (↑(heavyEdges G M ∪ lightPathEdges G M) : Set (Sym2 V))

noncomputable instance prunedGraph.instDecidableRel (M : ℕ) :
    DecidableRel (prunedGraph G M).Adj := Classical.decRel _

lemma prunedGraph_le (M : ℕ) : prunedGraph G M ≤ G :=
  G.deleteEdges_le _

/-- Every type-II critical path loses at least one edge during pruning. -/
lemma prunedGraph_no_typeII (M : ℕ) (x z y : V) (hII : IsTypeII G x z y) :
    ¬((prunedGraph G M).Adj x z ∧ (prunedGraph G M).Adj z y) := by
  classical
  have hz : z ∈ G.commonNeighbors x y := by simp [hII.2.2]
  have hxzG : G.Adj x z := (G.mem_commonNeighbors.mp hz).1
  have hzyG : G.Adj z y := (G.mem_commonNeighbors.mp hz).2.symm
  intro hsurvive
  have hxz_not_removed : s(x, z) ∉ (↑(heavyEdges G M ∪ lightPathEdges G M) : Set (Sym2 V)) :=
    (SimpleGraph.deleteEdges_adj.mp hsurvive.1).2
  have hzy_not_removed : s(z, y) ∉ (↑(heavyEdges G M ∪ lightPathEdges G M) : Set (Sym2 V)) :=
    (SimpleGraph.deleteEdges_adj.mp hsurvive.2).2
  have hxz_light : edgeMultiplicity G s(x, z) < M := by
    by_contra h
    have hheavy : s(x, z) ∈ heavyEdges G M := by
      rw [heavyEdges, Finset.mem_filter]
      exact ⟨by simpa using hxzG, by omega⟩
    exact hxz_not_removed (by simp [hheavy])
  have hzy_light : edgeMultiplicity G s(z, y) < M := by
    by_contra h
    have hheavy : s(z, y) ∈ heavyEdges G M := by
      rw [heavyEdges, Finset.mem_filter]
      exact ⟨by simpa using hzyG, by omega⟩
    exact hzy_not_removed (by simp [hheavy])
  have hlight : s(x, z) ∈ lightPathEdges G M := by
    rw [lightPathEdges, Finset.mem_filter]
    exact ⟨by simpa using hxzG, x, z, y, hII, hxz_light, hzy_light, Or.inl rfl⟩
  exact hxz_not_removed (by simp [hlight])

private lemma two_mul_le_half_square_imp_le_quarter (n k : ℕ)
    (h : 2 * k ≤ n ^ 2 / 2) : k ≤ n ^ 2 / 4 := by
  rcases Nat.even_or_odd n with ⟨a, ha⟩ | ⟨a, ha⟩
  · rw [ha] at h ⊢
    have hs : (a + a) ^ 2 = 4 * (a * a) := by ring
    rw [hs] at h ⊢
    omega
  · rw [ha] at h ⊢
    have hs : (2 * a + 1) ^ 2 = 4 * (a * a + a) + 1 := by ring
    rw [hs] at h ⊢
    omega

/-- The critical-pair injection and the sharp disjoint-neighborhood inequality
give the exact quarter bound for the pruned graph. -/
lemma prunedGraph_card_le_quarter (M : ℕ)
    (hG : IsDiameter2Critical G) :
    (prunedGraph G M).edgeFinset.card ≤ Fintype.card V ^ 2 / 4 := by
  have hbound := card_edges_add_disjointNeighborhood_le (prunedGraph G M)
  have hHC : (prunedGraph G M).edgeFinset.card ≤ (criticalGraph G).edgeFinset.card :=
    card_edgeFinset_le_card_criticalGraph (G := G) (prunedGraph_le G M) hG
      (prunedGraph_no_typeII G M)
  have hCD : (criticalGraph G).edgeFinset.card ≤
      (disjointNeighborhoodGraph (prunedGraph G M)).edgeFinset.card := by
    apply Finset.card_le_card
    apply SimpleGraph.edgeFinset_mono
    exact criticalGraph_le_disjointNeighborhoodGraph (G := G) (prunedGraph_le G M)
      (prunedGraph_no_typeII G M)
  apply two_mul_le_half_square_imp_le_quarter
  omega

end Multiplicity

section TriangleRemoval

/-- Fixed-error Ruzsa--Szemerédi consequence.  In a locally linear graph all
triangles are edge-disjoint and every edge belongs to one; the triangle
removal lemma therefore forces the triangle count to be `o(n²)`. -/
theorem eventually_locallyLinear_card_cliqueFinset_lt (eps : ℝ) (heps : 0 < eps) :
    ∃ n₀ : ℕ, ∀ (α : Type*) [Fintype α] [DecidableEq α]
      (G : SimpleGraph α) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card α → G.LocallyLinear →
        (G.cliqueFinset 3).card < eps * (Fintype.card α : ℝ) ^ 2 := by
  let delta := SimpleGraph.triangleRemovalBound eps
  have hdelta : 0 < delta := SimpleGraph.triangleRemovalBound_pos heps
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max 1 (1 / (6 * delta)))
  refine ⟨n₀, ?_⟩
  intro α _ _ G _ hn hlin
  let n := Fintype.card α
  have hnreal : max 1 (1 / (6 * delta)) < (n : ℝ) :=
    hn₀.trans_le (by exact_mod_cast hn)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (lt_max_of_lt_left zero_lt_one) hnreal.le
  by_contra hnot
  have hbig : eps * (n ^ 2 : ℕ) ≤ ((G.cliqueFinset 3).card : ℝ) := by
    push Not at hnot
    simpa using hnot
  have hfar : G.FarFromTriangleFree eps := hlin.1.farFromTriangleFree hbig
  have hlow := hfar.le_card_cliqueFinset
  have hthree : 3 * (G.cliqueFinset 3).card ≤ n.choose 2 :=
    hlin.1.card_edgeFinset_le.trans G.card_edgeFinset_le_card_choose_two
  have hthreeR : (3 : ℝ) * (G.cliqueFinset 3).card ≤ (n.choose 2 : ℝ) := by
    exact_mod_cast hthree
  have hchoose : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith
  have hnlarge : 1 / (6 * delta) < (n : ℝ) :=
    (le_max_right _ _).trans_lt hnreal
  have hstrict : (n : ℝ) ^ 2 / 6 < delta * (n : ℝ) ^ 3 := by
    have hmul := mul_lt_mul_of_pos_left hnlarge
      (show 0 < 6 * delta * (n : ℝ) ^ 2 by positivity)
    field_simp at hmul ⊢
    nlinarith
  have hupper : delta * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 / 6 := by
    calc
      _ ≤ ((G.cliqueFinset 3).card : ℝ) := by simpa [delta, n] using hlow
      _ ≤ (n : ℝ) ^ 2 / 6 := by nlinarith [hthreeR, hchoose]
  exact (not_le_of_gt hstrict) hupper

/-- For fixed multiplicity threshold, the number of canonically oriented
light type-II critical paths is `o(n²)`, in the fixed-error form needed for
the eventual theorem. -/
theorem eventually_lightTriples_card_lt (M : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ n₀ : ℕ, ∀ (α : Type*) [Fintype α] [DecidableEq α] [LinearOrder α]
      (G : SimpleGraph α) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card α →
        ((lightTriples G M).card : ℝ) < eps * (Fintype.card α : ℝ) ^ 2 := by
  let K : ℝ := 2 * M + 1
  have hK : 0 < K := by
    dsimp [K]
    positivity
  let eps' : ℝ := eps / (9 * K)
  have heps' : 0 < eps' := div_pos heps (mul_pos (by norm_num) hK)
  obtain ⟨n₀, hn₀⟩ := eventually_locallyLinear_card_cliqueFinset_lt eps' heps'
  refine ⟨n₀, ?_⟩
  intro α _ _ _ G _ hn
  obtain ⟨t, -, hselect, hlinear⟩ := exists_locallyLinear_lightTriples G M
  have hshadowCard : Fintype.card (α ⊕ α ⊕ α) = 3 * Fintype.card α := by
    simp
    omega
  have hnshadow : n₀ ≤ Fintype.card (α ⊕ α ⊕ α) := by
    rw [hshadowCard]
    omega
  have htri := hn₀ (α ⊕ α ⊕ α)
    (SimpleGraph.TripartiteFromTriangles.graph t) hnshadow hlinear
  have htNat : t.card ≤
      ((SimpleGraph.TripartiteFromTriangles.graph t).cliqueFinset 3).card :=
    card_le_tripartite_cliqueFinset t
  have htReal : (t.card : ℝ) ≤
      (((SimpleGraph.TripartiteFromTriangles.graph t).cliqueFinset 3).card : ℝ) := by
    exact_mod_cast htNat
  have hselectReal : ((lightTriples G M).card : ℝ) ≤ K * (t.card : ℝ) := by
    have hc : ((lightTriples G M).card : ℝ) ≤
        (((2 * M + 1) * t.card : ℕ) : ℝ) := by
      exact_mod_cast hselect
    simpa [K] using hc
  rw [hshadowCard] at htri
  dsimp [eps'] at htri
  have hbound : K * (t.card : ℝ) < eps * (Fintype.card α : ℝ) ^ 2 := by
    calc
      K * (t.card : ℝ) ≤ K *
          (((SimpleGraph.TripartiteFromTriangles.graph t).cliqueFinset 3).card : ℝ) :=
        mul_le_mul_of_nonneg_left htReal hK.le
      _ < K * (eps / (9 * K) * ((3 * Fintype.card α : ℕ) : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_left htri hK
      _ = eps * (Fintype.card α : ℝ) ^ 2 := by
        push_cast
        field_simp
        ring
  exact hselectReal.trans_lt hbound

end TriangleRemoval

section Exactification

/-! The remaining lemmas are the finite stability and exact-counting part of
Füredi's argument (Sections 4--6 of the paper). -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The graph formed by the type-I critical pairs. -/
noncomputable def typeIGraph : SimpleGraph V where
  Adj x y := IsTypeI G x y
  symm.symm _ _ h := (isTypeI_symm (G := G)).mp h
  loopless.irrefl x h := h.1.ne rfl

noncomputable instance typeIGraph.instDecidableRel : DecidableRel (typeIGraph G).Adj :=
  Classical.decRel _

@[simp] lemma typeIGraph_adj {x y : V} : (typeIGraph G).Adj x y ↔ IsTypeI G x y :=
  Iff.rfl

lemma typeIGraph_le : typeIGraph G ≤ G := fun _ _ h ↦ h.1

lemma typeIGraph_le_criticalGraph : typeIGraph G ≤ criticalGraph G :=
  fun _ _ h ↦ Or.inl h

/-- Degree of a vertex into a specified finite vertex set. -/
def degreeInto (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) (S : Finset V) : ℕ :=
  (H.neighborFinset v ∩ S).card

@[simp] lemma degreeInto_empty (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) :
    degreeInto H v ∅ = 0 := by simp [degreeInto]

lemma degreeInto_le_card (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) (S : Finset V) :
    degreeInto H v S ≤ S.card := by
  exact Finset.card_le_card Finset.inter_subset_right

lemma degreeInto_le_degree (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) (S : Finset V) :
    degreeInto H v S ≤ H.degree v := by
  simpa [degreeInto, H.card_neighborFinset_eq_degree] using
    Finset.card_le_card (Finset.inter_subset_left : H.neighborFinset v ∩ S ⊆ H.neighborFinset v)

lemma degreeInto_eq_degree_of_subset (H : SimpleGraph V) [DecidableRel H.Adj]
    (v : V) {S : Finset V} (hsub : H.neighborFinset v ⊆ S) :
    degreeInto H v S = H.degree v := by
  rw [degreeInto, Finset.inter_eq_left.mpr hsub, H.card_neighborFinset_eq_degree]

lemma degreeInto_mono {H K : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hHK : H ≤ K) (v : V) (S : Finset V) : degreeInto H v S ≤ degreeInto K v S := by
  apply Finset.card_le_card
  intro w hw
  rw [Finset.mem_inter] at hw ⊢
  exact ⟨by simpa using hHK (by simpa using hw.1), hw.2⟩

lemma degreeInto_union_of_disjoint (H : SimpleGraph V) [DecidableRel H.Adj]
    (v : V) {S T : Finset V} (hST : Disjoint S T) :
    degreeInto H v (S ∪ T) = degreeInto H v S + degreeInto H v T := by
  rw [degreeInto, Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right
      (Finset.inter_subset_right) (Finset.disjoint_of_subset_left
        Finset.inter_subset_right hST))]
  rfl

lemma degreeInto_univ (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) :
    degreeInto H v Finset.univ = H.degree v := by
  simp [degreeInto, H.card_neighborFinset_eq_degree]

lemma degreeInto_eq_sum (H : SimpleGraph V) [DecidableRel H.Adj]
    (v : V) (S : Finset V) :
    degreeInto H v S = ∑ w ∈ S, if H.Adj v w then 1 else 0 := by
  have heq : H.neighborFinset v ∩ S = S.filter fun w ↦ H.Adj v w := by
    ext w
    simp [and_comm]
  rw [degreeInto, heq]
  simpa using (Finset.sum_boole (fun w ↦ H.Adj v w) S).symm

/-- Double-counting the edges between two finite vertex sets. -/
lemma sum_degreeInto_comm (H : SimpleGraph V) [DecidableRel H.Adj]
    (S T : Finset V) :
    ∑ v ∈ S, degreeInto H v T = ∑ w ∈ T, degreeInto H w S := by
  simp_rw [degreeInto_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro v hv
  simp only [adj_comm]

lemma exists_mem_inter_of_card_lt_add {S A B : Finset V}
    (hA : A ⊆ S) (hB : B ⊆ S) (hcard : S.card < A.card + B.card) :
    ∃ x, x ∈ A ∧ x ∈ B := by
  by_contra h
  push Not at h
  have hdisj : Disjoint A B := Finset.disjoint_left.mpr h
  have hunion : A ∪ B ⊆ S := Finset.union_subset hA hB
  have := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj] at this
  omega

lemma card_add_sub_le_card_inter {S A B : Finset V}
    (hA : A ⊆ S) (hB : B ⊆ S) :
    A.card + B.card - S.card ≤ (A ∩ B).card := by
  have hunion : (A ∪ B).card ≤ S.card := Finset.card_le_card (Finset.union_subset hA hB)
  have hcard := Finset.card_union_add_card_inter A B
  omega

private lemma sum_const_sub (S : Finset V) (a : ℕ) (f : V → ℕ)
    (hf : ∀ x ∈ S, f x ≤ a) :
    ∑ x ∈ S, (a - f x) = S.card * a - ∑ x ∈ S, f x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
    have hfx := hf x (by simp)
    have hfS : ∀ y ∈ S, f y ≤ a := fun y hy ↦ hf y (by simp [hy])
    rw [Finset.sum_insert hx, Finset.sum_insert hx, Finset.card_insert_of_notMem hx, ih hfS]
    have hsum : ∑ y ∈ S, f y ≤ S.card * a := by
      calc
        _ ≤ ∑ _y ∈ S, a := Finset.sum_le_sum fun y hy ↦ hfS y hy
        _ = S.card * a := by simp
    simp only [Nat.add_mul, one_mul]
    omega

/-- Edges of `H` whose two endpoints lie in `S`. -/
def edgesInside (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) :
    Finset (Sym2 V) := H.edgeFinset.filter fun e ↦ e.toFinset ⊆ S

lemma card_edgesInside (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) :
    (edgesInside H S).card = (H.induce (↑S : Set V)).edgeFinset.card := by
  simpa [edgesInside] using H.card_filter_edgeFinset_toFinset_subset S

lemma sum_degreeInto_self (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) :
    ∑ v ∈ S, degreeInto H v S = 2 * (edgesInside H S).card := by
  classical
  let K : SimpleGraph V := (H.induce (↑S : Set V)).spanningCoe
  let : DecidableRel K.Adj := Classical.decRel _
  have hneighbor (v : V) : K.neighborFinset v =
      if v ∈ S then H.neighborFinset v ∩ S else ∅ := by
    ext w
    by_cases hv : v ∈ S <;> simp [K, hv]
  have hdegree (v : V) : K.degree v =
      if v ∈ S then degreeInto H v S else 0 := by
    rw [← K.card_neighborFinset_eq_degree, hneighbor]
    by_cases hv : v ∈ S <;> simp [hv, degreeInto]
  have hedge : K.edgeFinset = edgesInside H S := by
    ext e
    obtain ⟨x, y⟩ := e
    simp [K, edgesInside, Sym2.toFinset_mk_eq, Finset.insert_subset_iff]
  have hsum : (∑ v : V, K.degree v) = ∑ v ∈ S, degreeInto H v S := by
    calc
      _ = ∑ v : V, if v ∈ S then degreeInto H v S else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hdegree v
      _ = _ := by
        rw [← Finset.sum_filter]
        simp
  calc
    _ = ∑ v : V, K.degree v := hsum.symm
    _ = 2 * K.edgeFinset.card := K.sum_degrees_eq_twice_card_edges
    _ = 2 * (edgesInside H S).card := by rw [hedge]

private lemma card_darts_fst_mem (H : SimpleGraph V) [DecidableRel H.Adj]
    (B : Finset V) :
    ((Finset.univ : Finset H.Dart).filter fun d ↦ d.fst ∈ B).card =
      ∑ v ∈ B, H.degree v := by
  classical
  calc
    _ = ∑ d : H.Dart, if d.fst ∈ B then 1 else 0 := by
      simpa using (Finset.sum_boole (fun d : H.Dart ↦ d.fst ∈ B) Finset.univ).symm
    _ = ∑ v ∈ B, ∑ d : H.Dart, if d.fst = v then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d.fst ∈ B
      · simp [hd]
      · simp [hd]
    _ = ∑ v ∈ B, H.degree v := by
      apply Finset.sum_congr rfl
      intro v _
      rw [← H.dart_fst_fiber_card_eq_degree v]
      simpa using (Finset.sum_boole (fun d : H.Dart ↦ d.fst = v) Finset.univ)

/-- Deleting a finite vertex set removes at most the sum of its original
degrees.  Internal edges of the deleted set are deliberately overcounted. -/
lemma card_edgeFinset_le_card_edgesInside_add_sum_degree
    (H : SimpleGraph V) [DecidableRel H.Adj] (B : Finset V) :
    H.edgeFinset.card ≤ (edgesInside H (Finset.univ \ B)).card +
      ∑ v ∈ B, H.degree v := by
  classical
  let outside := H.edgeFinset \ edgesInside H (Finset.univ \ B)
  let target := (Finset.univ : Finset H.Dart).filter fun d ↦ d.fst ∈ B
  let orient : outside → target := fun e ↦ by
    have heH : e.1 ∈ H.edgeFinset := (Finset.mem_sdiff.mp e.2).1
    have heNot : e.1 ∉ edgesInside H (Finset.univ \ B) :=
      (Finset.mem_sdiff.mp e.2).2
    have hendpoint : e.1.out.1 ∈ B ∨ e.1.out.2 ∈ B := by
      by_contra h
      push Not at h
      apply heNot
      rw [edgesInside, Finset.mem_filter]
      refine ⟨heH, ?_⟩
      intro x hx
      have hx' : x = e.1.out.1 ∨ x = e.1.out.2 := by
        rw [← Sym2.mem_iff, sym2_out_mk]
        exact Sym2.mem_toFinset.mp hx
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hx' with rfl | rfl
      · exact h.1
      · exact h.2
    by_cases hfirst : e.1.out.1 ∈ B
    · let d : H.Dart := ⟨(e.1.out.1, e.1.out.2), by
          rw [← H.mem_edgeSet, sym2_out_mk]
          exact SimpleGraph.mem_edgeFinset.mp heH⟩
      exact ⟨d, by simp [target, d, hfirst]⟩
    · let d : H.Dart := ⟨(e.1.out.2, e.1.out.1), by
          rw [adj_comm, ← H.mem_edgeSet, sym2_out_mk]
          exact SimpleGraph.mem_edgeFinset.mp heH⟩
      exact ⟨d, by simp [target, d, hendpoint.resolve_left hfirst]⟩
  have horient_edge (e : outside) : (orient e).1.edge = e.1 := by
    simp only [orient]
    split
    · simp [SimpleGraph.Dart.edge, sym2_out_mk]
    · simp only [SimpleGraph.Dart.edge]
      rw [Sym2.eq_swap, sym2_out_mk]
  have hinj : Function.Injective orient := by
    intro e f hef
    apply Subtype.ext
    rw [← horient_edge e, ← horient_edge f, congr_arg Subtype.val hef]
  have hout : outside.card ≤ target.card :=
    Finset.card_le_card_of_injective (f := orient) hinj
  have hinside : edgesInside H (Finset.univ \ B) ⊆ H.edgeFinset := by
    intro e he
    exact (Finset.mem_filter.mp he).1
  have hsplit := Finset.card_sdiff_add_card_eq_card hinside
  rw [← hsplit, add_comm]
  exact Nat.add_le_add_left (hout.trans_eq (card_darts_fst_mem H B)) _

/-- Stability form of the disjoint-neighborhood inequality.  If
`e(H)+e(disj H)` is within `q²/2` of its maximum, fewer than `q` vertices
can have degree sum at most `n-q`. -/
lemma card_low_degreeSum_lt
    (H : SimpleGraph V) [DecidableRel H.Adj] (q : ℕ)
    (hq : q ≤ Fintype.card V)
    (hdense : (((Fintype.card V : ℝ) ^ 2 - q ^ 2) / 2) <
      (H.edgeFinset.card : ℝ) +
        ((disjointNeighborhoodGraph H).edgeFinset.card : ℝ)) :
    ((Finset.univ : Finset V).filter fun v ↦
      H.degree v + (disjointNeighborhoodGraph H).degree v ≤
        Fintype.card V - q).card < q := by
  classical
  let Dg := disjointNeighborhoodGraph H
  let bad := (Finset.univ : Finset V).filter fun v ↦
    H.degree v + Dg.degree v ≤ Fintype.card V - q
  by_contra hnot
  have hqbad : q ≤ bad.card := by simpa [bad] using hnot
  obtain ⟨B, hBbad, hBcard⟩ := Finset.exists_subset_card_eq hqbad
  let S := Finset.univ \ B
  have hBuniv : B ⊆ (Finset.univ : Finset V) := Finset.subset_univ B
  have hScard : S.card = Fintype.card V - q := by
    dsimp [S]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBuniv, hBcard, Finset.card_univ]
  have hHdel := card_edgeFinset_le_card_edgesInside_add_sum_degree H B
  have hDdel := card_edgeFinset_le_card_edgesInside_add_sum_degree Dg B
  have hInduced : (Dg.induce (↑S : Set V)).edgeFinset.card ≤
      (disjointNeighborhoodGraph (H.induce (↑S : Set V))).edgeFinset.card := by
    apply Finset.card_le_card
    apply SimpleGraph.edgeFinset_mono
    exact induce_disjointNeighborhoodGraph_le H (↑S : Set V)
  have hsmall := card_edges_add_disjointNeighborhood_le (H.induce (↑S : Set V))
  have hInside : (edgesInside H S).card + (edgesInside Dg S).card ≤ S.card ^ 2 / 2 := by
    rw [card_edgesInside, card_edgesInside]
    simpa using (Nat.add_le_add_left hInduced _ |>.trans hsmall)
  have hdeg : ∑ v ∈ B, (H.degree v + Dg.degree v) ≤ q * (Fintype.card V - q) := by
    calc
      _ ≤ ∑ _v ∈ B, (Fintype.card V - q) := by
        apply Finset.sum_le_sum
        intro v hv
        have hvbad := hBbad hv
        exact (Finset.mem_filter.mp hvbad).2
      _ = B.card * (Fintype.card V - q) := by simp
      _ = q * (Fintype.card V - q) := by rw [hBcard]
  have hNat : H.edgeFinset.card + Dg.edgeFinset.card ≤
      S.card ^ 2 / 2 + q * (Fintype.card V - q) := by
    calc
      _ ≤ ((edgesInside H S).card + ∑ v ∈ B, H.degree v) +
          ((edgesInside Dg S).card + ∑ v ∈ B, Dg.degree v) :=
        Nat.add_le_add hHdel hDdel
      _ = ((edgesInside H S).card + (edgesInside Dg S).card) +
          ∑ v ∈ B, (H.degree v + Dg.degree v) := by
        rw [Finset.sum_add_distrib]
        omega
      _ ≤ S.card ^ 2 / 2 + q * (Fintype.card V - q) :=
        Nat.add_le_add hInside hdeg
  have hReal : (H.edgeFinset.card : ℝ) + (Dg.edgeFinset.card : ℝ) ≤
      ((Fintype.card V : ℝ) ^ 2 - q ^ 2) / 2 := by
    have hcast : (H.edgeFinset.card : ℝ) + (Dg.edgeFinset.card : ℝ) ≤
        ((S.card ^ 2 / 2 + q * (Fintype.card V - q) : ℕ) : ℝ) := by
      exact_mod_cast hNat
    have hdiv : ((S.card ^ 2 / 2 : ℕ) : ℝ) ≤ (S.card : ℝ) ^ 2 / 2 := by
      calc
        _ ≤ ((S.card ^ 2 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) :=
          Nat.cast_div_le
        _ = (S.card : ℝ) ^ 2 / 2 := by norm_num
    rw [Nat.cast_add, Nat.cast_mul, hScard] at hcast
    push_cast at hcast hdiv
    have hqR : (q : ℝ) ≤ Fintype.card V := by exact_mod_cast hq
    rw [hScard] at hdiv
    push_cast at hdiv
    have hsubcast : ((Fintype.card V - q : ℕ) : ℝ) =
        Fintype.card V - q := by rw [Nat.cast_sub hq]
    rw [hsubcast] at hcast hdiv
    nlinarith
  exact (not_le_of_gt hdense) (by simpa [Dg] using hReal)

/-- Handshake bound for the vertices of degree at least `q`. -/
lemma card_highDegree_mul_le_twice_edges
    (H : SimpleGraph V) [DecidableRel H.Adj] (q : ℕ) :
    ((Finset.univ : Finset V).filter fun v ↦ q ≤ H.degree v).card * q ≤
      2 * H.edgeFinset.card := by
  let A := (Finset.univ : Finset V).filter fun v ↦ q ≤ H.degree v
  calc
    A.card * q = ∑ _v ∈ A, q := by simp
    _ ≤ ∑ v ∈ A, H.degree v := by
      apply Finset.sum_le_sum
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    _ ≤ ∑ v : V, H.degree v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
      simp
    _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges

lemma card_highDegree_lt
    (H : SimpleGraph V) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q)
    (hedges : 2 * H.edgeFinset.card < q ^ 2) :
    ((Finset.univ : Finset V).filter fun v ↦ q ≤ H.degree v).card < q := by
  have h := card_highDegree_mul_le_twice_edges H q
  nlinarith

/-- Near equality leaves fewer than `q²/2` exceptional
`disj(H) \ critical(G)` edges. -/
lemma twice_exception_edges_lt
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (hHG : H ≤ G) (hG : IsDiameter2Critical G)
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y))
    {q : ℕ}
    (hdense : (((Fintype.card V : ℝ) ^ 2 - q ^ 2) / 4) <
      (H.edgeFinset.card : ℝ)) :
    2 * ((disjointNeighborhoodGraph H \ criticalGraph G).edgeFinset.card) < q ^ 2 := by
  classical
  let Dg := disjointNeighborhoodGraph H
  let Cg := criticalGraph G
  have hHC : H.edgeFinset.card ≤ Cg.edgeFinset.card :=
    card_edgeFinset_le_card_criticalGraph (G := G) hHG hG hII
  have hCDgraph : Cg ≤ Dg := criticalGraph_le_disjointNeighborhoodGraph (G := G) hHG hII
  have hCD : Cg.edgeFinset.card ≤ Dg.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hCDgraph)
  have hsum := card_edges_add_disjointNeighborhood_le H
  have hsumR : (H.edgeFinset.card : ℝ) + (Dg.edgeFinset.card : ℝ) ≤
      (Fintype.card V : ℝ) ^ 2 / 2 := by
    have hcast : (H.edgeFinset.card : ℝ) + (Dg.edgeFinset.card : ℝ) ≤
        ((Fintype.card V ^ 2 / 2 : ℕ) : ℝ) := by exact_mod_cast hsum
    refine hcast.trans ?_
    calc
      (((Fintype.card V ^ 2 / 2 : ℕ) : ℝ)) ≤
          ((Fintype.card V ^ 2 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) := Nat.cast_div_le
      _ = (Fintype.card V : ℝ) ^ 2 / 2 := by norm_num
  have hedge : (Dg \ Cg).edgeFinset = Dg.edgeFinset \ Cg.edgeFinset := by
    ext e
    simp [Dg, Cg, SimpleGraph.sdiff_adj]
  have hcard : (Dg \ Cg).edgeFinset.card =
      Dg.edgeFinset.card - Cg.edgeFinset.card := by
    rw [hedge, Finset.card_sdiff_of_subset (SimpleGraph.edgeFinset_mono hCDgraph)]
  have hsubcast : (((Dg \ Cg).edgeFinset.card : ℕ) : ℝ) =
      (Dg.edgeFinset.card : ℝ) - Cg.edgeFinset.card := by
    rw [hcard, Nat.cast_sub hCD]
  have hltR : (2 : ℝ) * (Dg \ Cg).edgeFinset.card < q ^ 2 := by
    rw [hsubcast]
    have hHC' : (H.edgeFinset.card : ℝ) ≤ Cg.edgeFinset.card := by exact_mod_cast hHC
    nlinarith
  exact_mod_cast hltR

/-- The output of the first stability stage.  `D` is the neighborhood of a
maximum-degree vertex, `C` its complement, and `A4,A5,A6` are Füredi's three
exceptional sets. -/
structure InitialCore (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (q : ℕ) where
  u : V
  D : Finset V
  C : Finset V
  A4 : Finset V
  A5 : Finset V
  A6 : Finset V
  D_eq : D = H.neighborFinset u
  C_eq : C = Finset.univ \ D
  partition : C ∪ D = Finset.univ
  disjoint : Disjoint C D
  maxDegree : ∀ v, H.degree v ≤ D.card
  card_A4 : A4.card < q
  card_A5 : A5.card < q
  card_A6 : A6.card < 5 * q
  good_H_degree : ∀ y ∈ D, y ∉ A5 → D.card < H.degree y + q
  good_critical_cross : ∀ y ∈ D, y ∉ A4 → y ∉ A5 →
    C.card < degreeInto (criticalGraph G) y C + 2 * q
  outside_A6 : ∀ x ∈ C, x ∉ A6 → 20 * q < degreeInto (criticalGraph G) x D

/-- Quantitative Section 4 of Füredi's proof, with `q` playing the role of
`ε n`.  The scale assumptions `1000q ≤ n ≤ 1001q` absorb all floor errors. -/
lemma exists_initialCore
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (hHG : H ≤ G) (hG : IsDiameter2Critical G)
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y))
    {q : ℕ} (hq : 0 < q)
    (hscale_lo : 1000 * q ≤ Fintype.card V)
    (hscale_hi : Fintype.card V ≤ 1001 * q)
    (hdense : (((Fintype.card V : ℝ) ^ 2 - q ^ 2) / 4) <
      (H.edgeFinset.card : ℝ)) :
    Nonempty (InitialCore G H q) := by
  classical
  let n := Fintype.card V
  let Dg := disjointNeighborhoodGraph H
  let Cg := criticalGraph G
  let X := Dg \ Cg
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity : 0 < 1000 * q) hscale_lo
  let : Nonempty V := Fintype.card_pos_iff.mp hnpos
  obtain ⟨u, hu⟩ := H.exists_maximal_degree_vertex
  let D := H.neighborFinset u
  let C := Finset.univ \ D
  let A4 := (Finset.univ : Finset V).filter fun v ↦ q ≤ X.degree v
  let A5 := (Finset.univ : Finset V).filter fun v ↦
    H.degree v + Dg.degree v ≤ n - q
  let A6 := C.filter fun x ↦ degreeInto Cg x D ≤ 20 * q
  have hCDgraph : Cg ≤ Dg := criticalGraph_le_disjointNeighborhoodGraph (G := G) hHG hII
  have hHC : H.edgeFinset.card ≤ Cg.edgeFinset.card :=
    card_edgeFinset_le_card_criticalGraph (G := G) hHG hG hII
  have hsum := card_edges_add_disjointNeighborhood_le H
  have hsumDense : (((n : ℝ) ^ 2 - q ^ 2) / 2) <
      (H.edgeFinset.card : ℝ) + (Dg.edgeFinset.card : ℝ) := by
    have hHD : H.edgeFinset.card ≤ Dg.edgeFinset.card :=
      hHC.trans (Finset.card_le_card (SimpleGraph.edgeFinset_mono hCDgraph))
    have hHDR : (H.edgeFinset.card : ℝ) ≤ Dg.edgeFinset.card := by exact_mod_cast hHD
    dsimp [n] at hdense ⊢
    nlinarith
  have hA5 : A5.card < q := by
    have hqn : q ≤ Fintype.card V := (by omega : q ≤ 1000 * q).trans hscale_lo
    simpa [A5, Dg, n] using card_low_degreeSum_lt H q
      hqn hsumDense
  have hXsmall : 2 * X.edgeFinset.card < q ^ 2 := by
    change 2 * ((Dg \ Cg).edgeFinset.card) < q ^ 2
    exact twice_exception_edges_lt (G := G) hHG hG hII hdense
  have hA4 : A4.card < q := by
    change ((Finset.univ : Finset V).filter fun v ↦ q ≤ X.degree v).card < q
    apply card_highDegree_lt X hq
    convert hXsmall
  have hDcard : D.card = H.degree u := by
    simp [D, H.card_neighborFinset_eq_degree]
  have hmax : ∀ v, H.degree v ≤ D.card := by
    intro v
    rw [hDcard]
    exact (H.degree_le_maxDegree v).trans_eq hu
  have hCcard : C.card = n - D.card := by
    dsimp [C, n]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ D),
      Finset.card_univ]
  have hpart : C ∪ D = Finset.univ := by
    ext v
    simp [C]
  have hdisj : Disjoint C D := by
    rw [Finset.disjoint_left]
    intro v hvC hvD
    exact (Finset.mem_sdiff.mp hvC).2 hvD
  have hDC : D.card + C.card = n := by
    have hc := congr_arg Finset.card hpart
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_univ] at hc
    simpa [n, add_comm] using hc
  have hDgOutside {y : V} (hyD : y ∈ D) : Dg.neighborFinset y ⊆ C := by
    intro z hyz
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hzD
    have huy : H.Adj u y := by simpa [D] using hyD
    have huz : H.Adj u z := by simpa [D] using hzD
    have hyzD : Dg.Adj y z := by simpa using hyz
    have hucommon : u ∈ H.commonNeighbors y z := by
      rw [H.mem_commonNeighbors]
      exact ⟨huy.symm, huz.symm⟩
    simpa [Dg, hyzD.2] using hucommon
  have hCgOutside {y : V} (hyD : y ∈ D) : Cg.neighborFinset y ⊆ C := by
    intro z hyz
    exact hDgOutside hyD (by
      simpa using hCDgraph (by simpa using hyz))
  have hgoodH : ∀ y ∈ D, y ∉ A5 → D.card < H.degree y + q := by
    intro y hyD hyA5
    have hySum : n - q < H.degree y + Dg.degree y := by
      have : ¬(H.degree y + Dg.degree y ≤ n - q) := by
        simpa [A5] using hyA5
      omega
    have hyDg : Dg.degree y ≤ C.card := by
      rw [← degreeInto_eq_degree_of_subset Dg y (hDgOutside hyD)]
      exact degreeInto_le_card Dg y C
    omega
  have hDgDecomp (y : V) : Cg.degree y + X.degree y = Dg.degree y := by
    have hsub : Cg.neighborFinset y ⊆ Dg.neighborFinset y := by
      intro z hz
      simpa using hCDgraph (by simpa using hz)
    have hxfin : X.neighborFinset y = Dg.neighborFinset y \ Cg.neighborFinset y := by
      simp [X, Dg, Cg]
    rw [← Cg.card_neighborFinset_eq_degree, ← X.card_neighborFinset_eq_degree,
      ← Dg.card_neighborFinset_eq_degree, hxfin]
    have hs := Finset.card_sdiff_add_card_eq_card hsub
    omega
  have hgoodCrit : ∀ y ∈ D, y ∉ A4 → y ∉ A5 →
      C.card < degreeInto Cg y C + 2 * q := by
    intro y hyD hyA4 hyA5
    have hySum : n - q < H.degree y + Dg.degree y := by
      have : ¬(H.degree y + Dg.degree y ≤ n - q) := by
        simpa [A5] using hyA5
      omega
    have hyH : H.degree y ≤ D.card := hmax y
    have hyX : X.degree y < q := by
      have : ¬q ≤ X.degree y := by simpa [A4] using hyA4
      omega
    have hyCg : Cg.degree y + X.degree y = Dg.degree y := hDgDecomp y
    have hyInto : degreeInto Cg y C = Cg.degree y :=
      degreeInto_eq_degree_of_subset Cg y (hCgOutside hyD)
    omega
  have hmaxEdge : 2 * H.edgeFinset.card ≤ n * D.card := by
    rw [← H.sum_degrees_eq_twice_card_edges]
    calc
      _ ≤ ∑ _v : V, D.card := Finset.sum_le_sum fun v _ ↦ hmax v
      _ = n * D.card := by simp [n]
  have hDlargeR : ((n : ℝ) ^ 2 - q ^ 2) / 2 < (n : ℝ) * D.card := by
    have hmaxR : (2 : ℝ) * H.edgeFinset.card ≤ (n : ℝ) * D.card := by
      exact_mod_cast hmaxEdge
    nlinarith
  have hMissing : ∑ x ∈ C, (D.card - degreeInto Cg x D) ≤ 2 * q * n := by
    have hcross := sum_degreeInto_comm Cg C D
    have hterm : ∀ y ∈ D,
        C.card - degreeInto Cg y C ≤ 2 * q + if y ∈ A4 ∪ A5 then C.card else 0 := by
      intro y hyD
      by_cases hy : y ∈ A4 ∪ A5
      · exact (degreeInto_le_card Cg y C) |> fun h ↦ by simp [hy]; omega
      · have hy4 : y ∉ A4 := fun h ↦ hy (Finset.mem_union_left _ h)
        have hy5 : y ∉ A5 := fun h ↦ hy (Finset.mem_union_right _ h)
        have := hgoodCrit y hyD hy4 hy5
        simp [hy]
        omega
    calc
      _ = D.card * C.card - ∑ x ∈ C, degreeInto Cg x D := by
        simpa [mul_comm] using sum_const_sub C D.card (fun x ↦ degreeInto Cg x D)
          (fun x hx ↦ degreeInto_le_card Cg x D)
      _ = D.card * C.card - ∑ y ∈ D, degreeInto Cg y C := by rw [hcross]
      _ = ∑ y ∈ D, (C.card - degreeInto Cg y C) := by
        symm
        rw [sum_const_sub D C.card (fun y ↦ degreeInto Cg y C)
          (fun y hy ↦ degreeInto_le_card Cg y C)]
      _ ≤ ∑ y ∈ D, (2 * q + if y ∈ A4 ∪ A5 then C.card else 0) := by
        apply Finset.sum_le_sum
        exact hterm
      _ ≤ 2 * q * D.card + (A4 ∪ A5).card * C.card := by
        rw [Finset.sum_add_distrib]
        have hfilter : ∑ y ∈ D, (if y ∈ A4 ∪ A5 then C.card else 0) ≤
            (A4 ∪ A5).card * C.card := by
          have heq : ∑ y ∈ D, (if y ∈ A4 ∪ A5 then C.card else 0) =
              (D.filter fun y ↦ y ∈ A4 ∪ A5).card * C.card := by
            rw [← Finset.sum_filter]
            simp
          rw [heq]
          exact Nat.mul_le_mul_right _ (Finset.card_le_card (by
            intro y hy
            exact (Finset.mem_filter.mp hy).2))
        simpa [mul_comm, mul_left_comm] using Nat.add_le_add_right hfilter (2 * q * D.card)
      _ ≤ 2 * q * D.card + (2 * q) * C.card := by
        gcongr
        exact (Finset.card_union_le A4 A5).trans (by omega)
      _ = 2 * q * n := by
        rw [← Nat.mul_add, hDC]
  have hA6mul : A6.card * (D.card - 20 * q) ≤ 2 * q * n := by
    calc
      _ = ∑ _x ∈ A6, (D.card - 20 * q) := by simp
      _ ≤ ∑ x ∈ A6, (D.card - degreeInto Cg x D) := by
        apply Finset.sum_le_sum
        intro x hx
        have hx' := (Finset.mem_filter.mp hx).2
        omega
      _ ≤ ∑ x ∈ C, (D.card - degreeInto Cg x D) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx ↦ (Finset.mem_filter.mp hx).1)
        simp
      _ ≤ 2 * q * n := hMissing
  have hA6 : A6.card < 5 * q := by
    by_contra h
    have h5q : 5 * q ≤ A6.card := by omega
    have hLower : 5 * q * (D.card - 20 * q) ≤ 2 * q * n :=
      (Nat.mul_le_mul_right _ h5q).trans hA6mul
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hscaleLoR : (1000 : ℝ) * q ≤ n := by exact_mod_cast hscale_lo
    have hscaleHiR : (n : ℝ) ≤ 1001 * q := by exact_mod_cast hscale_hi
    have hD20 : 20 * q ≤ D.card := by
      by_contra hsmall
      have hDR : (D.card : ℝ) < 20 * q := by exact_mod_cast (by omega : D.card < 20 * q)
      nlinarith [hDlargeR]
    have hLowerR : (5 : ℝ) * q * (D.card - 20 * q) ≤ 2 * q * n := by
      have hcast : ((5 * q * (D.card - 20 * q) : ℕ) : ℝ) ≤
          ((2 * q * n : ℕ) : ℝ) := by exact_mod_cast hLower
      norm_num [Nat.cast_sub hD20] at hcast ⊢
      exact hcast
    nlinarith [hDlargeR]
  refine ⟨{
    u := u
    D := D
    C := C
    A4 := A4
    A5 := A5
    A6 := A6
    D_eq := rfl
    C_eq := rfl
    partition := hpart
    disjoint := hdisj
    maxDegree := hmax
    card_A4 := hA4
    card_A5 := hA5
    card_A6 := hA6
    good_H_degree := hgoodH
    good_critical_cross := hgoodCrit
    outside_A6 := ?_ }⟩
  intro x hxC hxA6
  change 20 * q < degreeInto Cg x D
  have : ¬degreeInto Cg x D ≤ 20 * q := by simpa [A6, hxC] using hxA6
  omega

/-- A critical pair cannot have a common neighbor in a graph in which every
type-II critical path has been broken. -/
lemma not_commonNeighbor_of_critical
    {H : SimpleGraph V} [DecidableRel H.Adj] (hHG : H ≤ G)
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y))
    {x y z : V} (hcrit : (criticalGraph G).Adj x y) :
    ¬(H.Adj x z ∧ H.Adj z y) := by
  have hdisj := criticalGraph_le_disjointNeighborhoodGraph (G := G) hHG hII hcrit
  intro hz
  have : z ∈ H.commonNeighbors x y := by
    rw [H.mem_commonNeighbors]
    exact ⟨hz.1, hz.2.symm⟩
  simpa [hdisj.2] using this

/-- Degrees into the two cells of a finite partition add. -/
lemma degreeInto_add_of_partition (H : SimpleGraph V) [DecidableRel H.Adj]
    (v : V) {C D : Finset V} (hdisj : Disjoint C D)
    (hpart : C ∪ D = Finset.univ) :
    degreeInto H v C + degreeInto H v D = H.degree v := by
  rw [← degreeInto_union_of_disjoint H v hdisj, hpart, degreeInto_univ]

/-- If every edge surviving inside `S` can be assigned to a critical pair
with one endpoint in `S` and the other in `B`, then path uniqueness bounds
the number of those edges by `|S| |B|`. -/
lemma card_edgesInside_le_mul_of_critical_targets
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y))
    (S B : Finset V)
    (hTarget : ∀ e ∈ edgesInside H S,
      ∃ x ∈ S, ∃ y ∈ B, CriticalPathContains G x y e) :
    (edgesInside H S).card ≤ S.card * B.card := by
  classical
  let E := edgesInside H S
  choose x hxS y hyB hpath using fun e : E ↦ hTarget e.1 e.2
  let target : E → S × B := fun e ↦ ⟨⟨x e, hxS e⟩, ⟨y e, hyB e⟩⟩
  have hinj : Function.Injective target := by
    intro e f hef
    have hx : x e = x f := congr_arg (fun p : S × B ↦ (p.1 : V)) hef
    have hy : y e = y f := congr_arg (fun p : S × B ↦ (p.2 : V)) hef
    apply Subtype.ext
    apply criticalPathContains_unique_edge (G := G) hII
    · exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_filter.mp e.2).1
    · exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_filter.mp f.2).1
    · exact hpath e
    · simpa [hx, hy] using hpath f
  have hcard := Fintype.card_le_of_injective target hinj
  simpa [E, Fintype.card_prod] using hcard

/-- The same critical-path injection for an arbitrary finite family of
`G`-edges. -/
lemma card_edgeFamily_le_mul_of_critical_targets
    (E : Finset (Sym2 V)) (S B : Finset V)
    (hTarget : ∀ e ∈ E,
      ∃ x ∈ S, ∃ y ∈ B, CriticalPathContains G x y e)
    (hUnique : ∀ {e f : Sym2 V}, e ∈ E → f ∈ E →
      ∀ {x y : V}, CriticalPathContains G x y e →
        CriticalPathContains G x y f → e = f) :
    E.card ≤ S.card * B.card := by
  classical
  choose x hxS y hyB hpath using fun e : E ↦ hTarget e.1 e.2
  let target : E → S × B := fun e ↦ ⟨⟨x e, hxS e⟩, ⟨y e, hyB e⟩⟩
  have hinj : Function.Injective target := by
    intro e f hef
    have hx : x e = x f := congr_arg (fun p : S × B ↦ (p.1 : V)) hef
    have hy : y e = y f := congr_arg (fun p : S × B ↦ (p.2 : V)) hef
    apply Subtype.ext
    exact hUnique e.2 f.2 (hpath e) (by simpa [hx, hy] using hpath f)
  have hcard := Fintype.card_le_of_injective target hinj
  simpa [Fintype.card_prod] using hcard

/-- Existing cross-edges and internal edges charged to missing cross-pairs
together fit inside the full Cartesian product. -/
lemma card_interedges_add_edgeFamily_le_mul
    (C D : Finset V) (E : Finset (Sym2 V))
    (hTarget : ∀ e ∈ E,
      ∃ x ∈ C, ∃ y ∈ D, ¬G.Adj x y ∧ CriticalPathContains G x y e)
    (hUnique : ∀ {e f : Sym2 V}, e ∈ E → f ∈ E →
      ∀ {x y : V}, CriticalPathContains G x y e →
        CriticalPathContains G x y f → e = f) :
    (G.interedges C D).card + E.card ≤ C.card * D.card := by
  classical
  choose x hxC y hyD hnon hpath using fun e : E ↦ hTarget e.1 e.2
  let target : (G.interedges C D) ⊕ E → C × D
    | Sum.inl p => ⟨⟨p.1.1, (G.mem_interedges_iff.mp p.2).1⟩,
        ⟨p.1.2, (G.mem_interedges_iff.mp p.2).2.1⟩⟩
    | Sum.inr e => ⟨⟨x e, hxC e⟩, ⟨y e, hyD e⟩⟩
  have hinj : Function.Injective target := by
    intro a b hab
    rcases a with p | e <;> rcases b with r | f
    · apply congr_arg Sum.inl
      apply Subtype.ext
      exact Prod.ext
        (congr_arg (fun z : C × D ↦ (z.1 : V)) hab)
        (congr_arg (fun z : C × D ↦ (z.2 : V)) hab)
    · have hxy : (p.1.1 : V) = x f := congr_arg (fun z : C × D ↦ (z.1 : V)) hab
      have huv : (p.1.2 : V) = y f := congr_arg (fun z : C × D ↦ (z.2 : V)) hab
      have hpAdj := (G.mem_interedges_iff.mp p.2).2.2
      exact (hnon f) (by simpa [hxy, huv] using hpAdj) |> False.elim
    · have hxy : x e = (r.1.1 : V) := congr_arg (fun z : C × D ↦ (z.1 : V)) hab
      have huv : y e = (r.1.2 : V) := congr_arg (fun z : C × D ↦ (z.2 : V)) hab
      have hrAdj := (G.mem_interedges_iff.mp r.2).2.2
      exact (hnon e) (by simpa [hxy, huv] using hrAdj) |> False.elim
    · apply congr_arg Sum.inr
      apply Subtype.ext
      have hx : x e = x f := congr_arg (fun z : C × D ↦ (z.1 : V)) hab
      have hy : y e = y f := congr_arg (fun z : C × D ↦ (z.2 : V)) hab
      exact hUnique e.2 f.2 (hpath e) (by simpa [hx, hy] using hpath f)
  have hcard := Fintype.card_le_of_injective target hinj
  simpa [Fintype.card_sum, Fintype.card_prod] using hcard

/-- Decompose the edges induced by two disjoint cells into cross-edges and
the two internal edge families. -/
lemma card_edgesInside_union_le
    (C D : Finset V) (hCD : Disjoint C D) :
    (edgesInside G (C ∪ D)).card ≤ (G.interedges C D).card +
      (edgesInside G C ∪ edgesInside G D).card := by
  classical
  let X := G.edgeFinset.filter fun e ↦
    ∃ x ∈ C, ∃ y ∈ D, e = s(x, y)
  have hX : X.card ≤ (G.interedges C D).card := by
    choose x hxC y hyD heq using fun e : X ↦ (Finset.mem_filter.mp e.2).2
    let target : X → G.interedges C D := fun e ↦
      ⟨(x e, y e), G.mk_mem_interedges_iff.mpr
        ⟨hxC e, hyD e, by
          have heG := (Finset.mem_filter.mp e.2).1
          rw [SimpleGraph.mem_edgeFinset] at heG
          simpa [heq e] using heG⟩⟩
    have hinj : Function.Injective target := by
      intro e f hef
      apply Subtype.ext
      have hxy : x e = x f := congr_arg (fun p : G.interedges C D ↦ p.1.1) hef
      have huv : y e = y f := congr_arg (fun p : G.interedges C D ↦ p.1.2) hef
      exact (heq e).trans (by simpa [hxy, huv] using (heq f).symm)
    simpa using Fintype.card_le_of_injective target hinj
  have hcover : edgesInside G (C ∪ D) ⊆
      X ∪ (edgesInside G C ∪ edgesInside G D) := by
    intro e he
    have he' := Finset.mem_filter.mp he
    obtain ⟨a, b⟩ := e
    have hab : a ∈ C ∪ D ∧ b ∈ C ∪ D := by
      simpa [Sym2.toFinset_mk_eq, Finset.insert_subset_iff] using he'.2
    rcases Finset.mem_union.mp hab.1 with haC | haD <;>
      rcases Finset.mem_union.mp hab.2 with hbC | hbD
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨he'.1, by simpa [Sym2.toFinset_mk_eq,
          Finset.insert_subset_iff] using And.intro haC hbC⟩))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he'.1,
        ⟨a, haC, b, hbD, rfl⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he'.1,
        ⟨b, hbC, a, haD, Sym2.eq_swap⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨he'.1, by simpa [Sym2.toFinset_mk_eq,
          Finset.insert_subset_iff] using And.intro haD hbD⟩))
  calc
    (edgesInside G (C ∪ D)).card ≤
        (X ∪ (edgesInside G C ∪ edgesInside G D)).card := Finset.card_le_card hcover
    _ ≤ X.card + (edgesInside G C ∪ edgesInside G D).card := Finset.card_union_le _ _
    _ ≤ (G.interedges C D).card + (edgesInside G C ∪ edgesInside G D).card :=
      Nat.add_le_add_right hX _

private lemma mul_sub_le_quarter (n d : ℕ) (hd : d ≤ n) :
    d * (n - d) ≤ n ^ 2 / 4 := by
  have hcast : (4 : ℝ) * d * (n - d) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 2 * d)]
  have hnat' : 4 * d * (n - d) ≤ n ^ 2 := by exact_mod_cast hcast
  have hnat : 4 * (d * (n - d)) ≤ n ^ 2 := by simpa [Nat.mul_assoc] using hnat'
  omega

/-- The data needed for Füredi's last injection.  `C,D` are the enlarged
sides, `A` is the low-degree remainder, and `S` is the union of the two
small fringes. -/
structure FinalPartition (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) where
  C : Finset V
  D : Finset V
  A : Finset V
  S : Finset V
  partition : C ∪ D ∪ A = Finset.univ
  disjoint_CD : Disjoint C D
  disjoint_CA : Disjoint C A
  disjoint_DA : Disjoint D A
  card_S : S.card < 66 * q
  card_D : 494 * q < D.card
  degree_A : ∀ v ∈ A, G.degree v < 300 * q
  no_critical_C : ∀ {x y}, x ∈ C → y ∈ C → ¬(criticalGraph G).Adj x y
  no_critical_D : ∀ {x y}, x ∈ D → y ∈ D → ¬(criticalGraph G).Adj x y
  internal_target : ∀ e ∈ edgesInside G C ∪ edgesInside G D,
    (∃ x ∈ C, ∃ y ∈ D, ¬G.Adj x y ∧ CriticalPathContains G x y e) ∨
      ∃ x ∈ S, ∃ y ∈ A, CriticalPathContains G x y e
  internal_unique : ∀ {e f : Sym2 V},
    e ∈ edgesInside G C ∪ edgesInside G D →
    f ∈ edgesInside G C ∪ edgesInside G D →
    ∀ {x y : V}, CriticalPathContains G x y e →
      CriticalPathContains G x y f → e = f

/-- The last page of Füredi's proof, isolated from the construction of the
partition: existing cross-edges and internally charged missing cross-pairs
fit in `C × D`; the remaining internal edges and all low-degree edges fit in
the slack supplied by `A × D`. -/
lemma FinalPartition.card_edges_le_quarter
    (P : FinalPartition G q) :
    G.edgeFinset.card ≤ Fintype.card V ^ 2 / 4 := by
  classical
  let E := edgesInside G P.C ∪ edgesInside G P.D
  let CrossTarget : Sym2 V → Prop := fun e ↦
    ∃ x ∈ P.C, ∃ y ∈ P.D, ¬G.Adj x y ∧ CriticalPathContains G x y e
  let Ec := E.filter CrossTarget
  let Ea := E \ Ec
  have hEcsub : Ec ⊆ E := fun e he ↦ (Finset.mem_filter.mp he).1
  have hEasub : Ea ⊆ E := fun e he ↦ (Finset.mem_sdiff.mp he).1
  have hUnique : ∀ {e f : Sym2 V}, e ∈ E → f ∈ E →
      ∀ {x y : V}, CriticalPathContains G x y e →
        CriticalPathContains G x y f → e = f := by
    intro e f he hf x y hpe hpf
    exact P.internal_unique he hf hpe hpf
  have hEcTarget : ∀ e ∈ Ec,
      ∃ x ∈ P.C, ∃ y ∈ P.D, ¬G.Adj x y ∧ CriticalPathContains G x y e := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hEaTarget : ∀ e ∈ Ea,
      ∃ x ∈ P.S, ∃ y ∈ P.A, CriticalPathContains G x y e := by
    intro e he
    have heE := hEasub he
    have heNot : e ∉ Ec := (Finset.mem_sdiff.mp he).2
    rcases P.internal_target e heE with hcross | hA
    · exact (heNot (Finset.mem_filter.mpr ⟨heE, hcross⟩)).elim
    · exact hA
  have hcrossBound : (G.interedges P.C P.D).card + Ec.card ≤
      P.C.card * P.D.card :=
    card_interedges_add_edgeFamily_le_mul (G := G) P.C P.D Ec hEcTarget
      (by
        intro e f he hf x y hpe hpf
        exact hUnique (hEcsub he) (hEcsub hf) hpe hpf)
  have hABound : Ea.card ≤ P.S.card * P.A.card :=
    card_edgeFamily_le_mul_of_critical_targets (G := G) Ea P.S P.A hEaTarget
      (by
        intro e f he hf x y hpe hpf
        exact hUnique (hEasub he) (hEasub hf) hpe hpf)
  have hEcEa : Ec.card + Ea.card = E.card := by
    have hcard := Finset.card_sdiff_add_card_eq_card hEcsub
    change Ea.card + Ec.card = E.card at hcard
    omega
  have hinside : (edgesInside G (P.C ∪ P.D)).card ≤
      P.C.card * P.D.card + P.S.card * P.A.card := by
    have hdecomp := card_edgesInside_union_le (G := G) P.C P.D P.disjoint_CD
    change (edgesInside G (P.C ∪ P.D)).card ≤
      (G.interedges P.C P.D).card + E.card at hdecomp
    omega
  have hcompl : Finset.univ \ P.A = P.C ∪ P.D := by
    ext v
    constructor
    · intro hv
      have hv' := Finset.mem_sdiff.mp hv
      have hvPart : v ∈ P.C ∨ v ∈ P.D ∨ v ∈ P.A := by
        have : v ∈ P.C ∪ P.D ∪ P.A := P.partition.symm ▸ Finset.mem_univ v
        simpa [or_assoc] using this
      rcases hvPart with hvC | hvD | hvA
      · exact Finset.mem_union_left _ hvC
      · exact Finset.mem_union_right _ hvD
      · exact (hv'.2 hvA).elim
    · intro hv
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_union.mp hv with hvC | hvD
      · exact fun hvA ↦ Finset.disjoint_left.mp P.disjoint_CA hvC hvA
      · exact fun hvA ↦ Finset.disjoint_left.mp P.disjoint_DA hvD hvA
  have hdelete := card_edgeFinset_le_card_edgesInside_add_sum_degree G P.A
  rw [hcompl] at hdelete
  have hdegree : ∑ v ∈ P.A, G.degree v ≤ P.A.card * (300 * q) := by
    calc
      _ ≤ ∑ _v ∈ P.A, (300 * q) := by
        apply Finset.sum_le_sum
        intro v hv
        exact Nat.le_of_lt (P.degree_A v hv)
      _ = P.A.card * (300 * q) := by simp
  have hedge : G.edgeFinset.card ≤ P.C.card * P.D.card +
      P.S.card * P.A.card + P.A.card * (300 * q) := by
    exact hdelete.trans (Nat.add_le_add hinside hdegree)
  have hslack : P.S.card + 300 * q ≤ P.D.card := by
    have hS := P.card_S
    have hD := P.card_D
    omega
  have hedge' : G.edgeFinset.card ≤ P.D.card * (P.C.card + P.A.card) := by
    calc
      G.edgeFinset.card ≤ P.C.card * P.D.card +
          P.S.card * P.A.card + P.A.card * (300 * q) := hedge
      _ = P.C.card * P.D.card + P.A.card * (P.S.card + 300 * q) := by ring
      _ ≤ P.C.card * P.D.card + P.A.card * P.D.card := by gcongr
      _ = P.D.card * (P.C.card + P.A.card) := by ring
  have hcard : P.C.card + P.D.card + P.A.card = Fintype.card V := by
    have hCDA : Disjoint (P.C ∪ P.D) P.A :=
      Finset.disjoint_union_left.mpr ⟨P.disjoint_CA, P.disjoint_DA⟩
    have hc := congr_arg Finset.card P.partition
    rw [Finset.card_union_of_disjoint hCDA,
      Finset.card_union_of_disjoint P.disjoint_CD, Finset.card_univ] at hc
    exact hc
  have hDle : P.D.card ≤ Fintype.card V := by omega
  calc
    G.edgeFinset.card ≤ P.D.card * (P.C.card + P.A.card) := hedge'
    _ = P.D.card * (Fintype.card V - P.D.card) := by
      congr 1
      omega
    _ ≤ Fintype.card V ^ 2 / 4 := mul_sub_le_quarter _ _ hDle

/-- No vertex is simultaneously rich in `H`-neighbors on both sides of the
maximum-degree partition. -/
lemma InitialCore.not_large_both
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (I : InitialCore G H q)
    (hHG : H ≤ G)
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y))
    (hq : 0 < q) (v : V) :
    degreeInto H v I.C < 2 * q ∨ degreeInto H v I.D < 2 * q := by
  by_contra h
  push Not at h
  let ND := H.neighborFinset v ∩ I.D
  let NC := H.neighborFinset v ∩ I.C
  let bad := I.A4 ∪ I.A5
  have hsumBad : I.A4.card + I.A5.card < 2 * q := by
    simpa [two_mul] using Nat.add_lt_add I.card_A4 I.card_A5
  have hbad : bad.card < 2 * q :=
    (Finset.card_union_le I.A4 I.A5).trans_lt hsumBad
  have hND : 2 * q ≤ ND.card := by simpa [ND, degreeInto] using h.2
  have hnsub : ¬ND ⊆ bad := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨y, hyND, hybad⟩ := Finset.not_subset.mp hnsub
  have hyv : H.Adj v y := by
    have := (Finset.mem_inter.mp hyND).1
    simpa using this
  have hyD : y ∈ I.D := (Finset.mem_inter.mp hyND).2
  have hy4 : y ∉ I.A4 := fun hy ↦ hybad (Finset.mem_union_left _ hy)
  have hy5 : y ∉ I.A5 := fun hy ↦ hybad (Finset.mem_union_right _ hy)
  let A := H.neighborFinset v ∩ I.C
  let B := (criticalGraph G).neighborFinset y ∩ I.C
  have hAcard : 2 * q ≤ A.card := by simpa [A, degreeInto] using h.1
  have hBcard : I.C.card < B.card + 2 * q := by
    simpa [B, degreeInto] using I.good_critical_cross y hyD hy4 hy5
  have hsum : I.C.card < A.card + B.card := by omega
  obtain ⟨x, hxA, hxB⟩ := exists_mem_inter_of_card_lt_add
    (S := I.C) (A := A) (B := B) Finset.inter_subset_right Finset.inter_subset_right hsum
  have hvx : H.Adj v x := by
    have := (Finset.mem_inter.mp hxA).1
    simpa using this
  have hyx : (criticalGraph G).Adj y x := by
    have := (Finset.mem_inter.mp hxB).1
    simpa using this
  exact not_commonNeighbor_of_critical (G := G) hHG hII hyx ⟨hyv.symm, hvx⟩

/-- The first half of Section 5: if the set of vertices in `D` with many
neighbors back in `D` were large, it would occupy all but fewer than `12q`
vertices of `D` and would have minimum internal degree greater than
`|D₀|-3q`. -/
lemma InitialCore.wrongSide_consequences
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (I : InitialCore G H q)
    (hHG : H ≤ G)
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y))
    (hq : 0 < q)
    (hlarge : 3 * q ≤
      (I.D.filter fun y ↦ y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D).card) :
    let D0 := I.D.filter fun y ↦ y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D
    I.D.card - D0.card < 12 * q ∧
      ∀ y ∈ D0, D0.card < degreeInto H y D0 + 3 * q := by
  classical
  let D0 := I.D.filter fun y ↦ y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D
  change I.D.card - D0.card < 12 * q ∧
    ∀ y ∈ D0, D0.card < degreeInto H y D0 + 3 * q
  let R := I.D \ (D0 ∪ I.A5)
  have hD0sub : D0 ⊆ I.D := fun y hy ↦ (Finset.mem_filter.mp hy).1
  have hRsub : R ⊆ I.D := fun y hy ↦ (Finset.mem_sdiff.mp hy).1
  have hD0A5 : Disjoint D0 I.A5 := by
    rw [Finset.disjoint_left]
    intro y hy0 hy5
    exact (Finset.mem_filter.mp hy0).2.1 hy5
  have hD0Into : ∀ y ∈ D0, I.D.card < degreeInto H y I.D + 3 * q := by
    intro y hy0
    have hyD := hD0sub hy0
    have hy5 : y ∉ I.A5 := (Finset.mem_filter.mp hy0).2.1
    have hyType : 2 * q ≤ degreeInto H y I.D := (Finset.mem_filter.mp hy0).2.2
    have hsmallC := (InitialCore.not_large_both (G := G) I hHG hII hq y).resolve_right
      (by omega)
    have hsplit := degreeInto_add_of_partition H y I.disjoint I.partition
    have hdeg := I.good_H_degree y hyD hy5
    omega
  have hRInto : ∀ y ∈ R, degreeInto H y D0 < 2 * q := by
    intro y hyR
    have hyD := hRsub hyR
    have hyNot := (Finset.mem_sdiff.mp hyR).2
    have hy5 : y ∉ I.A5 := fun h ↦ hyNot (Finset.mem_union_right _ h)
    have hy0 : y ∉ D0 := fun h ↦ hyNot (Finset.mem_union_left _ h)
    have : ¬(y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D) := by
      simpa [D0, hyD] using hy0
    have hyDsmall : degreeInto H y I.D < 2 * q := by
      have hnle : ¬2 * q ≤ degreeInto H y I.D := fun hle ↦ this ⟨hy5, hle⟩
      omega
    have hsub : H.neighborFinset y ∩ D0 ⊆ H.neighborFinset y ∩ I.D :=
      Finset.inter_subset_inter (fun _ h ↦ h) hD0sub
    exact (Finset.card_le_card hsub).trans_lt hyDsmall
  have hDcover : I.D ⊆ D0 ∪ R ∪ I.A5 := by
    intro y hyD
    by_cases hy0 : y ∈ D0
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hy0)
    by_cases hy5 : y ∈ I.A5
    · exact Finset.mem_union_right _ hy5
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hyD, by simp [hy0, hy5]⟩))
  have hIntoR : ∀ y ∈ D0,
      I.D.card - D0.card - 4 * q ≤ degreeInto H y R := by
    intro y hy0
    have hsub : H.neighborFinset y ∩ I.D ⊆
        (H.neighborFinset y ∩ D0) ∪
          (H.neighborFinset y ∩ R) ∪ (H.neighborFinset y ∩ I.A5) := by
      intro z hz
      have hz' := Finset.mem_inter.mp hz
      have hzpart := hDcover hz'.2
      rcases Finset.mem_union.mp hzpart with hzpart | hz5
      · rcases Finset.mem_union.mp hzpart with hz0 | hzR
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_inter.mpr ⟨hz'.1, hz0⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_inter.mpr ⟨hz'.1, hzR⟩))
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hz'.1, hz5⟩)
    have hdecomp : degreeInto H y I.D ≤
        degreeInto H y D0 + degreeInto H y R + degreeInto H y I.A5 := by
      dsimp [degreeInto]
      calc
        (H.neighborFinset y ∩ I.D).card ≤
            (((H.neighborFinset y ∩ D0) ∪ (H.neighborFinset y ∩ R)) ∪
              (H.neighborFinset y ∩ I.A5)).card := Finset.card_le_card hsub
        _ ≤ ((H.neighborFinset y ∩ D0) ∪ (H.neighborFinset y ∩ R)).card +
              (H.neighborFinset y ∩ I.A5).card := Finset.card_union_le _ _
        _ ≤ ((H.neighborFinset y ∩ D0).card +
              (H.neighborFinset y ∩ R).card) +
              (H.neighborFinset y ∩ I.A5).card :=
            Nat.add_le_add_right (Finset.card_union_le _ _) _
    have h0 := degreeInto_le_card H y D0
    have h5 := degreeInto_le_card H y I.A5
    have hbig := hD0Into y hy0
    have htotal : degreeInto H y I.D < D0.card + degreeInto H y R + q := by
      calc
        degreeInto H y I.D ≤
            degreeInto H y D0 + degreeInto H y R + degreeInto H y I.A5 := hdecomp
        _ ≤ D0.card + degreeInto H y R + I.A5.card :=
          Nat.add_le_add (Nat.add_le_add h0 (le_refl _)) h5
        _ < D0.card + degreeInto H y R + q := Nat.add_lt_add_left I.card_A5 _
    omega
  have hcross := sum_degreeInto_comm H D0 R
  have ht : I.D.card - D0.card < 12 * q := by
    by_contra hnot
    have htwelve : 12 * q ≤ I.D.card - D0.card := by omega
    by_cases hRE : R = ∅
    · have hDsub : I.D ⊆ D0 ∪ I.A5 := by
        intro y hyD
        have := hDcover hyD
        simpa [hRE] using this
      have hc := Finset.card_le_card hDsub
      have hu := Finset.card_union_le D0 I.A5
      have hle : I.D.card ≤ D0.card + I.A5.card := hc.trans hu
      have hA5q := I.card_A5
      omega
    · have hRpos : 0 < R.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hRE)
      have hlower : D0.card * (I.D.card - D0.card - 4 * q) ≤
          ∑ y ∈ D0, degreeInto H y R := by
        calc
          _ = ∑ _y ∈ D0, (I.D.card - D0.card - 4 * q) := by simp
          _ ≤ _ := Finset.sum_le_sum hIntoR
      have hupper : ∑ y ∈ R, degreeInto H y D0 < R.card * (2 * q) := by
        have hle : ∑ y ∈ R, degreeInto H y D0 ≤ R.card * (2 * q - 1) := by
          calc
            _ ≤ ∑ _y ∈ R, (2 * q - 1) := by
              apply Finset.sum_le_sum
              intro y hy
              have := hRInto y hy
              omega
            _ = _ := by simp
        have hstrict : R.card * (2 * q - 1) < R.card * (2 * q) := by
          apply Nat.mul_lt_mul_of_pos_left
          · omega
          · exact hRpos
        exact hle.trans_lt hstrict
      have hRcard : R.card ≤ I.D.card - D0.card := by
        have hsub : D0 ∪ R ⊆ I.D := Finset.union_subset hD0sub hRsub
        have hd : Disjoint D0 R := by
          rw [Finset.disjoint_left]
          intro y hy0 hyR
          exact (Finset.mem_sdiff.mp hyR).2 (Finset.mem_union_left _ hy0)
        have hc := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hd] at hc
        omega
      rw [hcross] at hlower
      have hD0large : 3 * q ≤ D0.card := by simpa [D0] using hlarge
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have hchain := hlower.trans_lt hupper
      have hsub1 : 4 * q ≤ I.D.card - D0.card := by omega
      have hsub2 : D0.card ≤ I.D.card := Finset.card_le_card hD0sub
      have hchainR : ((D0.card * (I.D.card - D0.card - 4 * q) : ℕ) : ℝ) <
          ((R.card * (2 * q) : ℕ) : ℝ) := by exact_mod_cast hchain
      norm_num only [Nat.cast_mul] at hchainR
      rw [Nat.cast_sub hsub1, Nat.cast_sub hsub2] at hchainR
      norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hchainR
      have hRcardR : (R.card : ℝ) ≤ ((I.D.card - D0.card : ℕ) : ℝ) := by
        exact_mod_cast hRcard
      rw [Nat.cast_sub hsub2] at hRcardR
      have hD0largeR : (((3 * q : ℕ) : ℝ)) ≤ D0.card := by exact_mod_cast hD0large
      norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hD0largeR
      have htwelveR : (((12 * q : ℕ) : ℝ)) ≤ ((I.D.card - D0.card : ℕ) : ℝ) := by
        exact_mod_cast htwelve
      rw [Nat.cast_sub hsub2] at htwelveR
      norm_num only [Nat.cast_mul, Nat.cast_ofNat] at htwelveR
      have hprod1 : 0 ≤ ((D0.card : ℝ) - 3 * q) *
          ((I.D.card : ℝ) - D0.card - 4 * q) :=
        mul_nonneg (by linarith) (by linarith)
      have hprod2 : 0 ≤ (q : ℝ) *
          ((I.D.card : ℝ) - D0.card - 12 * q) :=
        mul_nonneg (le_of_lt hqR) (by linarith)
      nlinarith
  refine ⟨ht, ?_⟩
  intro y hy0
  have hbig := hD0Into y hy0
  have hDsplit : degreeInto H y I.D ≤
      degreeInto H y D0 + (I.D.card - D0.card) := by
    have hsub : H.neighborFinset y ∩ I.D ⊆
        (H.neighborFinset y ∩ D0) ∪ (I.D \ D0) := by
      intro z hz
      have hz' := Finset.mem_inter.mp hz
      by_cases hz0 : z ∈ D0
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz'.1, hz0⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz'.2, hz0⟩)
    have hc := Finset.card_le_card hsub
    have hu := Finset.card_union_le (H.neighborFinset y ∩ D0) (I.D \ D0)
    have hD0sub' := hD0sub
    rw [Finset.card_sdiff_of_subset hD0sub'] at hu
    dsimp [degreeInto] at hc ⊢
    omega
  have hD0card : D0.card ≤ I.D.card := Finset.card_le_card hD0sub
  omega

/-- Two different two-edge walks between a critical pair are impossible. -/
lemma criticalPair_commonNeighbor_unique {x y z w : V}
    (hcrit : (criticalGraph G).Adj x y)
    (hz : G.Adj x z ∧ G.Adj z y) (hw : G.Adj x w ∧ G.Adj w y) : z = w := by
  rcases hcrit with hI | ⟨c, hII⟩
  · have hzmem : z ∈ G.commonNeighbors x y := by
      rw [G.mem_commonNeighbors]
      exact ⟨hz.1, hz.2.symm⟩
    simpa [hI.2] using hzmem
  · have hzmem : z ∈ G.commonNeighbors x y := by
      rw [G.mem_commonNeighbors]
      exact ⟨hz.1, hz.2.symm⟩
    have hwmem : w ∈ G.commonNeighbors x y := by
      rw [G.mem_commonNeighbors]
      exact ⟨hw.1, hw.2.symm⟩
    have hzc : z = c := by simpa [hII.2.2] using hzmem
    have hwc : w = c := by simpa [hII.2.2] using hwmem
    exact hzc.trans hwc.symm

/-- More than one common neighbor rules out a critical pair. -/
lemma not_critical_of_two_commonNeighbors {x y : V} (S : Finset V)
    (hlarge : S.card + 1 < degreeInto G x S + degreeInto G y S) :
    ¬(criticalGraph G).Adj x y := by
  classical
  intro hcrit
  let A := G.neighborFinset x ∩ S
  let B := G.neighborFinset y ∩ S
  have hAsub : A ⊆ S := Finset.inter_subset_right
  have hBsub : B ⊆ S := Finset.inter_subset_right
  have hinter := card_add_sub_le_card_inter hAsub hBsub
  have htwo : 1 < (A ∩ B).card := by
    change S.card + 1 < A.card + B.card at hlarge
    omega
  let T := {z // z ∈ A ∩ B}
  have hT : 1 < Fintype.card T := by
    change 1 < Fintype.card ↥(A ∩ B)
    rw [Fintype.card_coe]
    exact htwo
  obtain ⟨z, w, hzw⟩ := Fintype.exists_pair_of_one_lt_card hT
  have hz := Finset.mem_inter.mp z.property
  have hw := Finset.mem_inter.mp w.property
  have hzx : G.Adj x z := by simpa [A] using (Finset.mem_inter.mp hz.1).1
  have hzy : G.Adj z y := by simpa [B, adj_comm] using (Finset.mem_inter.mp hz.2).1
  have hwx : G.Adj x w := by simpa [A] using (Finset.mem_inter.mp hw.1).1
  have hwy : G.Adj w y := by simpa [B, adj_comm] using (Finset.mem_inter.mp hw.2).1
  have heq := criticalPair_commonNeighbor_unique (G := G) hcrit ⟨hzx, hzy⟩ ⟨hwx, hwy⟩
  exact hzw (Subtype.ext heq)

/-- If neither side contains a critical pair, a critical path contains at
most one edge internal to the two disjoint sides. -/
lemma criticalPathContains_unique_internal
    (C D : Finset V) (hCD : Disjoint C D)
    (hNoC : ∀ {x y}, x ∈ C → y ∈ C → ¬(criticalGraph G).Adj x y)
    (hNoD : ∀ {x y}, x ∈ D → y ∈ D → ¬(criticalGraph G).Adj x y)
    {x y : V} {e f : Sym2 V}
    (he : e ∈ edgesInside G C ∪ edgesInside G D)
    (hf : f ∈ edgesInside G C ∪ edgesInside G D)
    (hpe : CriticalPathContains G x y e)
    (hpf : CriticalPathContains G x y f) : e = f := by
  classical
  rcases hpe with ⟨hI, rfl⟩ | ⟨z, hII, rfl | rfl⟩
  · rcases hpf with ⟨-, rfl⟩ | ⟨w, hw, -⟩
    · rfl
    · exact (hw.2.1 hI.1).elim
  · rcases hpf with ⟨hI, -⟩ | ⟨w, hw, rfl | rfl⟩
    · exact (hII.2.1 hI.1).elim
    · have hwz : w = z := (by simpa [hII.2.2] using hw.2.2 : z = w).symm
      simp [hwz]
    · have hwz : w = z := (by simpa [hII.2.2] using hw.2.2 : z = w).symm
      subst w
      have heSide := Finset.mem_union.mp he
      have hfSide := Finset.mem_union.mp hf
      rcases heSide with heC | heD <;> rcases hfSide with hfC | hfD
      · have heSub := (Finset.mem_filter.mp heC).2
        have hfSub := (Finset.mem_filter.mp hfC).2
        have hxC : x ∈ C := heSub (by simp)
        have hyC : y ∈ C := hfSub (by simp)
        exact (hNoC hxC hyC (Or.inr ⟨z, hII⟩)).elim
      · have heSub := (Finset.mem_filter.mp heC).2
        have hfSub := (Finset.mem_filter.mp hfD).2
        have hzC : z ∈ C := heSub (by simp)
        have hzD : z ∈ D := hfSub (by simp)
        exact (Finset.disjoint_left.mp hCD hzC hzD).elim
      · have heSub := (Finset.mem_filter.mp heD).2
        have hfSub := (Finset.mem_filter.mp hfC).2
        have hzD : z ∈ D := heSub (by simp)
        have hzC : z ∈ C := hfSub (by simp)
        exact (Finset.disjoint_left.mp hCD hzC hzD).elim
      · have heSub := (Finset.mem_filter.mp heD).2
        have hfSub := (Finset.mem_filter.mp hfD).2
        have hxD : x ∈ D := heSub (by simp)
        have hyD : y ∈ D := hfSub (by simp)
        exact (hNoD hxD hyD (Or.inr ⟨z, hII⟩)).elim
  · rcases hpf with ⟨hI, -⟩ | ⟨w, hw, rfl | rfl⟩
    · exact (hII.2.1 hI.1).elim
    · have hwz : w = z := (by simpa [hII.2.2] using hw.2.2 : z = w).symm
      subst w
      have heSide := Finset.mem_union.mp he
      have hfSide := Finset.mem_union.mp hf
      rcases heSide with heC | heD <;> rcases hfSide with hfC | hfD
      · have heSub := (Finset.mem_filter.mp heC).2
        have hfSub := (Finset.mem_filter.mp hfC).2
        have hyC : y ∈ C := heSub (by simp)
        have hxC : x ∈ C := hfSub (by simp)
        exact (hNoC hxC hyC (Or.inr ⟨z, hII⟩)).elim
      · have heSub := (Finset.mem_filter.mp heC).2
        have hfSub := (Finset.mem_filter.mp hfD).2
        have hzC : z ∈ C := heSub (by simp)
        have hzD : z ∈ D := hfSub (by simp)
        exact (Finset.disjoint_left.mp hCD hzC hzD).elim
      · have heSub := (Finset.mem_filter.mp heD).2
        have hfSub := (Finset.mem_filter.mp hfC).2
        have hzD : z ∈ D := heSub (by simp)
        have hzC : z ∈ C := hfSub (by simp)
        exact (Finset.disjoint_left.mp hCD hzC hzD).elim
      · have heSub := (Finset.mem_filter.mp heD).2
        have hfSub := (Finset.mem_filter.mp hfD).2
        have hyD : y ∈ D := heSub (by simp)
        have hxD : x ∈ D := hfSub (by simp)
        exact (hNoD hxD hyD (Or.inr ⟨z, hII⟩)).elim
    · have hwz : w = z := (by simpa [hII.2.2] using hw.2.2 : z = w).symm
      simp [hwz]

lemma isTypeI_of_critical_of_adj {x y : V}
    (hcrit : (criticalGraph G).Adj x y) (hxy : G.Adj x y) : IsTypeI G x y := by
  rcases hcrit with hI | ⟨z, hII⟩
  · exact hI
  · exact (hII.2.1 hxy).elim

/-- A finite set whose induced minimum degree is within `3q` of its order
has pairwise common neighbors once its order exceeds `6q`. -/
lemma exists_commonNeighbor_of_almost_complete
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) {q : ℕ} (hlarge : 6 * q < S.card)
    (hmin : ∀ y ∈ S, S.card < degreeInto H y S + 3 * q)
    {y z : V} (hy : y ∈ S) (hz : z ∈ S) :
    ∃ w ∈ S, H.Adj y w ∧ H.Adj w z := by
  let A := H.neighborFinset y ∩ S
  let B := H.neighborFinset z ∩ S
  have hA : A ⊆ S := Finset.inter_subset_right
  have hB : B ⊆ S := Finset.inter_subset_right
  have hAc : A.card = degreeInto H y S := rfl
  have hBc : B.card = degreeInto H z S := rfl
  have hsum : S.card < A.card + B.card := by
    have hy' := hmin y hy
    have hz' := hmin z hz
    omega
  obtain ⟨w, hwA, hwB⟩ := exists_mem_inter_of_card_lt_add hA hB hsum
  refine ⟨w, (Finset.mem_inter.mp hwA).2, ?_, ?_⟩
  · simpa [A] using (Finset.mem_inter.mp hwA).1
  · have := (Finset.mem_inter.mp hwB).1
    simpa [B, adj_comm] using this

/-- Section 5's key uniqueness consequence: outside `A6`, a vertex has at
most one `G`-neighbor in an almost-complete wrong-side set. -/
lemma InitialCore.degreeInto_wrongSide_le_one
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (I : InitialCore G H q) (hHG : H ≤ G)
    (D0 : Finset V) (hD0sub : D0 ⊆ I.D)
    (ht : I.D.card - D0.card < 12 * q)
    (hlarge : 6 * q < D0.card)
    (hmin : ∀ y ∈ D0, D0.card < degreeInto H y D0 + 3 * q)
    {x : V} (hxC : x ∈ I.C) (hx6 : x ∉ I.A6) :
    degreeInto G x D0 ≤ 1 := by
  classical
  by_contra hnot
  have htwo : 1 < (G.neighborFinset x ∩ D0).card := by
    change ¬degreeInto G x D0 ≤ 1 at hnot
    simpa [degreeInto] using Nat.lt_of_not_ge hnot
  let T := {y // y ∈ G.neighborFinset x ∩ D0}
  have hT : 1 < Fintype.card T := by
    change 1 < Fintype.card ↥(G.neighborFinset x ∩ D0)
    rw [Fintype.card_coe]
    exact htwo
  obtain ⟨y₁, y₂, hyne⟩ := Fintype.exists_pair_of_one_lt_card hT
  have hy₁mem := Finset.mem_inter.mp y₁.property
  have hy₂mem := Finset.mem_inter.mp y₂.property
  have hy₁D : (y₁ : V) ∈ D0 := hy₁mem.2
  have hy₂D : (y₂ : V) ∈ D0 := hy₂mem.2
  have hxy₁ : G.Adj x y₁ := by simpa using hy₁mem.1
  have hxy₂ : G.Adj x y₂ := by simpa using hy₂mem.1
  let A := (H.neighborFinset (y₁ : V) ∩ D0) ∩
    (H.neighborFinset (y₂ : V) ∩ D0)
  have hAcard : D0.card - 6 * q < A.card := by
    have hinter := card_add_sub_le_card_inter
      (S := D0) (A := H.neighborFinset (y₁ : V) ∩ D0)
      (B := H.neighborFinset (y₂ : V) ∩ D0)
      Finset.inter_subset_right Finset.inter_subset_right
    change (H.neighborFinset (y₁ : V) ∩ D0).card +
      (H.neighborFinset (y₂ : V) ∩ D0).card - D0.card ≤ A.card at hinter
    have h₁ := hmin y₁ hy₁D
    have h₂ := hmin y₂ hy₂D
    change D0.card - 6 * q < A.card
    dsimp [degreeInto] at h₁ h₂
    omega
  let B := (criticalGraph G).neighborFinset x ∩ I.D
  have hBcard : 20 * q < B.card := by
    simpa [B, degreeInto] using I.outside_A6 x hxC hx6
  have hAsub : A ⊆ I.D := by
    intro z hz
    exact hD0sub (Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).2
  have hBsub : B ⊆ I.D := Finset.inter_subset_right
  have hsum : I.D.card < A.card + B.card := by
    have hD0card := Finset.card_le_card hD0sub
    omega
  obtain ⟨z, hzA, hzB⟩ := exists_mem_inter_of_card_lt_add hAsub hBsub hsum
  have hzA' := Finset.mem_inter.mp hzA
  have hy₁z : H.Adj (y₁ : V) z := by
    simpa using (Finset.mem_inter.mp hzA'.1).1
  have hy₂z : H.Adj (y₂ : V) z := by
    simpa using (Finset.mem_inter.mp hzA'.2).1
  have hxz : (criticalGraph G).Adj x z := by
    simpa [B] using (Finset.mem_inter.mp hzB).1
  have heq : (y₁ : V) = y₂ := criticalPair_commonNeighbor_unique (G := G) hxz
    ⟨hxy₁, hHG hy₁z⟩ ⟨hxy₂, hHG hy₂z⟩
  exact hyne (Subtype.ext heq)

/-- Vertices of an almost-complete wrong-side set which have no neighbor in
`C \ A6` form a small exceptional set. -/
lemma InitialCore.card_isolated_wrongSide_lt
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (I : InitialCore G H q) (hHG : H ≤ G) (hG : IsDiameter2Critical G)
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y))
    (hq : 0 < q)
    (D0 : Finset V) (hD0sub : D0 ⊆ I.D)
    (ht : I.D.card - D0.card < 12 * q)
    (hlarge : 6 * q < D0.card)
    (hmin : ∀ y ∈ D0, D0.card < degreeInto H y D0 + 3 * q) :
    let F := D0.filter fun y ↦ degreeInto G y (I.C \ I.A6) = 0
    F.card < 37 * q := by
  classical
  let F := D0.filter fun y ↦ degreeInto G y (I.C \ I.A6) = 0
  change F.card < 37 * q
  let B := I.A6 ∪ (I.D \ D0)
  have hFsub : F ⊆ D0 := fun y hy ↦ (Finset.mem_filter.mp hy).1
  have hBcard : B.card < 17 * q := by
    have hdiff : (I.D \ D0).card = I.D.card - D0.card :=
      Finset.card_sdiff_of_subset hD0sub
    have hA6 := I.card_A6
    calc
      B.card ≤ I.A6.card + (I.D \ D0).card := Finset.card_union_le _ _
      _ < 5 * q + 12 * q := by rw [hdiff]; omega
      _ = 17 * q := by ring
  have hNoCrit : ∀ {a b : V}, a ∈ D0 → b ∈ D0 →
      ¬(criticalGraph G).Adj a b := by
    intro a b ha hb hab
    obtain ⟨w, -, haw, hwb⟩ := exists_commonNeighbor_of_almost_complete
      H D0 hlarge hmin ha hb
    exact not_commonNeighbor_of_critical (G := G) hHG hII hab ⟨haw, hwb⟩
  have hOutside {a b z : V} (hzF : z ∈ F)
      (hab : (criticalGraph G).Adj a b)
      (haD0 : a ∈ D0) (hzb : G.Adj z b) : b ∈ B := by
    have hbD0 : b ∉ D0 := fun hb ↦ hNoCrit haD0 hb hab
    have hbpart : b ∈ I.C ∨ b ∈ I.D := by
      have : b ∈ I.C ∪ I.D := I.partition.symm ▸ Finset.mem_univ b
      exact Finset.mem_union.mp this
    rcases hbpart with hbC | hbD
    · by_cases hb6 : b ∈ I.A6
      · exact Finset.mem_union_left _ hb6
      · have hbCA : b ∈ I.C \ I.A6 := Finset.mem_sdiff.mpr ⟨hbC, hb6⟩
        have hbN : b ∈ G.neighborFinset z ∩ (I.C \ I.A6) :=
          Finset.mem_inter.mpr ⟨by simpa using hzb, hbCA⟩
        have hpos : 0 < degreeInto G z (I.C \ I.A6) :=
          Finset.card_pos.mpr ⟨b, hbN⟩
        have hz0 := (Finset.mem_filter.mp hzF).2
        omega
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hbD, hbD0⟩)
  have hTarget : ∀ e ∈ edgesInside H F,
      ∃ x ∈ F, ∃ y ∈ B, CriticalPathContains G x y e := by
    intro e he
    have he' := Finset.mem_filter.mp he
    have heG : e ∈ G.edgeSet := SimpleGraph.edgeSet_mono hHG
      (SimpleGraph.mem_edgeFinset.mp he'.1)
    obtain ⟨a, b, hp⟩ := exists_criticalPathContains_of_diameter2Critical
      (G := G) hG heG
    rcases hp with ⟨hI, heq⟩ | ⟨z, hP, heq | heq⟩
    · have haF : a ∈ F := he'.2 (by simpa [heq])
      have hbF : b ∈ F := he'.2 (by simpa [heq])
      exact (hNoCrit (hFsub haF) (hFsub hbF) (Or.inl hI)).elim
    · have haF : a ∈ F := he'.2 (by simpa [heq])
      have hzF : z ∈ F := he'.2 (by simpa [heq])
      have hzmem : z ∈ G.commonNeighbors a b := by simp [hP.2.2]
      have hzb : G.Adj z b := (G.mem_commonNeighbors.mp hzmem).2.symm
      have hbB := hOutside hzF (Or.inr ⟨z, hP⟩) (hFsub haF) hzb
      exact ⟨a, haF, b, hbB, Or.inr ⟨z, hP, Or.inl heq⟩⟩
    · have hzF : z ∈ F := he'.2 (by simpa [heq])
      have hbF : b ∈ F := he'.2 (by simpa [heq])
      have hzmem : z ∈ G.commonNeighbors a b := by simp [hP.2.2]
      have hza : G.Adj z a := (G.mem_commonNeighbors.mp hzmem).1.symm
      have haB := hOutside (a := b) (b := a) hzF
        ((isCriticalPair_symm (G := G)).mpr (Or.inr ⟨z, hP⟩)) (hFsub hbF) hza
      refine ⟨b, hbF, a, haB, ?_⟩
      exact (criticalPathContains_symm (G := G)).mp
        (Or.inr ⟨z, hP, Or.inr heq⟩)
  have hupper : (edgesInside H F).card ≤ F.card * B.card :=
    card_edgesInside_le_mul_of_critical_targets (G := G) hII F B hTarget
  have hFmin : ∀ y ∈ F, F.card < degreeInto H y F + 3 * q := by
    intro y hyF
    have hy0 := hFsub hyF
    have hbig := hmin y hy0
    have hsplit : degreeInto H y D0 ≤
        degreeInto H y F + (D0.card - F.card) := by
      have hsub : H.neighborFinset y ∩ D0 ⊆
          (H.neighborFinset y ∩ F) ∪ (D0 \ F) := by
        intro z hz
        have hz' := Finset.mem_inter.mp hz
        by_cases hzF : z ∈ F
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz'.1, hzF⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz'.2, hzF⟩)
      have hc := Finset.card_le_card hsub
      have hu := Finset.card_union_le (H.neighborFinset y ∩ F) (D0 \ F)
      rw [Finset.card_sdiff_of_subset hFsub] at hu
      dsimp [degreeInto] at hc ⊢
      omega
    have hFcard := Finset.card_le_card hFsub
    omega
  have hlower : F.card * (F.card - 3 * q) ≤ 2 * (edgesInside H F).card := by
    calc
      _ = ∑ _y ∈ F, (F.card - 3 * q) := by simp
      _ ≤ ∑ y ∈ F, degreeInto H y F := by
        apply Finset.sum_le_sum
        intro y hy
        have := hFmin y hy
        omega
      _ = 2 * (edgesInside H F).card := sum_degreeInto_self H F
  by_contra hnot
  have h37 : 37 * q ≤ F.card := by omega
  have h3 : 3 * q ≤ F.card := by omega
  have hcomp : F.card * (F.card - 3 * q) ≤ 2 * (F.card * B.card) :=
    hlower.trans (Nat.mul_le_mul_left 2 hupper)
  have hcompR : (((F.card * (F.card - 3 * q) : ℕ) : ℝ)) ≤
      (((2 * (F.card * B.card) : ℕ) : ℝ)) := by exact_mod_cast hcomp
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcompR
  rw [Nat.cast_sub h3] at hcompR
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcompR
  have h37R : (37 : ℝ) * q ≤ F.card := by exact_mod_cast h37
  have hBR : (B.card : ℝ) < 17 * q := by exact_mod_cast hBcard
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hFposN : 0 < F.card := by omega
  have hFpos : (0 : ℝ) < F.card := by exact_mod_cast hFposN
  nlinarith

/-- Sum of the two internal degree sequences along the matching constructed
in Section 5.  Critical-pair uniqueness forces the two relevant neighbor
sets to overlap only at noncritical partners. -/
lemma matched_self_degree_sum_le
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (hHG : H ≤ G) (q : ℕ) (D1 C1 : Finset V) (f : V → V)
    (himage : C1 = D1.image f)
    (hinj : Set.InjOn f D1)
    (hmatch : ∀ y ∈ D1, G.Adj y (f y))
    (hcrit : ∀ y ∈ D1, D1.card < degreeInto (criticalGraph G) y C1 + 2 * q)
    (hseparate : ∀ y ∈ D1, ∀ z ∈ D1, f y ≠ z) :
    (∑ x ∈ C1, degreeInto H x C1) +
        ∑ y ∈ D1, degreeInto H y D1 ≤ D1.card * (D1.card + 2 * q) := by
  classical
  have hCcard : C1.card = D1.card := by
    rw [himage, Finset.card_image_of_injOn hinj]
  have hpoint : ∀ y ∈ D1,
      degreeInto H (f y) C1 + degreeInto H y D1 ≤ D1.card + 2 * q := by
    intro y hy
    let A := H.neighborFinset (f y) ∩ C1
    let B := (H.neighborFinset y ∩ D1).image f
    let K := (criticalGraph G).neighborFinset y ∩ C1
    have hBcard : B.card = degreeInto H y D1 := by
      calc
        B.card = (H.neighborFinset y ∩ D1).card := Finset.card_image_of_injOn
          (fun a ha b hb hab ↦
            hinj (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2 hab)
        _ = degreeInto H y D1 := rfl
    have hAsub : A ⊆ C1 := Finset.inter_subset_right
    have hBsub : B ⊆ C1 := by
      intro z hz
      change z ∈ (H.neighborFinset y ∩ D1).image f at hz
      rw [Finset.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rw [himage, Finset.mem_image]
      exact ⟨w, (Finset.mem_inter.mp hw).2, rfl⟩
    have hKsub : K ⊆ C1 := Finset.inter_subset_right
    have hinter : A ∩ B ⊆ C1 \ K := by
      intro z hz
      have hz' := Finset.mem_inter.mp hz
      refine Finset.mem_sdiff.mpr ⟨hAsub hz'.1, ?_⟩
      intro hzK
      have hzA := Finset.mem_inter.mp hz'.1
      have hzB := Finset.mem_image.mp hz'.2
      obtain ⟨w, hw, hwz⟩ := hzB
      have hw' := Finset.mem_inter.mp hw
      have hfyZ : G.Adj (f y) z := hHG (by simpa [A] using hzA.1)
      have hyW : G.Adj y w := hHG (by simpa using hw'.1)
      have hwZ : G.Adj w z := by simpa [← hwz] using hmatch w hw'.2
      have hyFy : G.Adj y (f y) := hmatch y hy
      have hyZ : (criticalGraph G).Adj y z := by
        simpa [K] using (Finset.mem_inter.mp hzK).1
      have heq : f y = w := criticalPair_commonNeighbor_unique (G := G) hyZ
        ⟨hyFy, hfyZ⟩ ⟨hyW, hwZ⟩
      exact hseparate y hy w hw'.2 heq
    have hInterCard : (A ∩ B).card ≤ C1.card - K.card := by
      have hc := Finset.card_le_card hinter
      rw [Finset.card_sdiff_of_subset hKsub] at hc
      exact hc
    have hUnionCard : (A ∪ B).card ≤ C1.card :=
      Finset.card_le_card (Finset.union_subset hAsub hBsub)
    have hIE := Finset.card_union_add_card_inter A B
    have hcritY := hcrit y hy
    change D1.card < K.card + 2 * q at hcritY
    change A.card + degreeInto H y D1 ≤ D1.card + 2 * q
    rw [← hBcard]
    omega
  have hsum : ∑ y ∈ D1,
      (degreeInto H (f y) C1 + degreeInto H y D1) ≤
      ∑ _y ∈ D1, (D1.card + 2 * q) := Finset.sum_le_sum hpoint
  have hreindex : ∑ x ∈ C1, degreeInto H x C1 =
      ∑ y ∈ D1, degreeInto H (f y) C1 := by
    rw [himage, Finset.sum_image]
    intro a ha b hb hab
    exact hinj ha hb hab
  rw [Finset.sum_add_distrib] at hsum
  rw [hreindex]
  simpa using hsum

/-- Count all edges after controlling the two internal degree sums on equal
matched cores.  Edges outside the cores are charged to the outside endpoint
and bounded by the maximum degree. -/
lemma InitialCore.twice_card_edges_le_of_matched_core
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (I : InitialCore G H q) (C1 D1 : Finset V)
    (hCsub : C1 ⊆ I.C) (hDsub : D1 ⊆ I.D)
    (hcard : C1.card = D1.card)
    (hself : (∑ x ∈ C1, degreeInto H x C1) +
      ∑ y ∈ D1, degreeInto H y D1 ≤ D1.card * (D1.card + 2 * q))
    (hcross : ∑ y ∈ D1, degreeInto H y C1 ≤ D1.card * (2 * q)) :
    2 * H.edgeFinset.card ≤ D1.card * (D1.card + 6 * q) +
      2 * (Fintype.card V - 2 * D1.card) * I.D.card := by
  classical
  have hdisj : Disjoint C1 D1 :=
    Finset.disjoint_of_subset_left hCsub (Finset.disjoint_of_subset_right hDsub I.disjoint)
  let U := C1 ∪ D1
  let O := Finset.univ \ U
  have hUcard : U.card = 2 * D1.card := by
    rw [show U = C1 ∪ D1 from rfl, Finset.card_union_of_disjoint hdisj, hcard]
    omega
  have hOcard : O.card = Fintype.card V - 2 * D1.card := by
    rw [show O = Finset.univ \ U from rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ, hUcard]
  have hsumU : ∑ v ∈ U, degreeInto H v U =
      ((∑ x ∈ C1, degreeInto H x C1) +
        ∑ y ∈ D1, degreeInto H y D1) +
        2 * ∑ y ∈ D1, degreeInto H y C1 := by
    have hcomm := sum_degreeInto_comm H C1 D1
    rw [show U = C1 ∪ D1 from rfl, Finset.sum_union hdisj]
    simp_rw [degreeInto_union_of_disjoint H _ hdisj]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    omega
  have hinside : 2 * (edgesInside H U).card ≤ D1.card * (D1.card + 6 * q) := by
    rw [← sum_degreeInto_self H U, hsumU]
    calc
      _ ≤ D1.card * (D1.card + 2 * q) + 2 * (D1.card * (2 * q)) :=
        Nat.add_le_add hself (Nat.mul_le_mul_left 2 hcross)
      _ = D1.card * (D1.card + 6 * q) := by ring
  have hcompl : Finset.univ \ O = U := by
    ext v
    simp [O, U]
  have hedge := card_edgeFinset_le_card_edgesInside_add_sum_degree H O
  rw [hcompl] at hedge
  have houtside : ∑ v ∈ O, H.degree v ≤ O.card * I.D.card := by
    calc
      _ ≤ ∑ _v ∈ O, I.D.card := by
        apply Finset.sum_le_sum
        intro v hv
        exact I.maxDegree v
      _ = O.card * I.D.card := by simp
  have htotal : H.edgeFinset.card ≤ (edgesInside H U).card + O.card * I.D.card :=
    hedge.trans (Nat.add_le_add_left houtside _)
  rw [hOcard] at htotal
  calc
    2 * H.edgeFinset.card ≤
        2 * ((edgesInside H U).card +
          (Fintype.card V - 2 * D1.card) * I.D.card) :=
      Nat.mul_le_mul_left 2 htotal
    _ = 2 * (edgesInside H U).card +
        2 * ((Fintype.card V - 2 * D1.card) * I.D.card) := by ring
    _ ≤ D1.card * (D1.card + 6 * q) +
        2 * (Fintype.card V - 2 * D1.card) * I.D.card := by
      exact Nat.add_le_add hinside (by rw [Nat.mul_assoc])
    _ = _ := by ring

/-- Section 5 of Füredi's proof: only fewer than `3q` vertices in `D` can
have at least `2q` surviving neighbors back in `D`. -/
lemma InitialCore.wrongSide_small
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (I : InitialCore G H q) (hHG : H ≤ G) (hG : IsDiameter2Critical G)
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y))
    (hq : 0 < q)
    (hscale_lo : 1000 * q ≤ Fintype.card V)
    (hscale_hi : Fintype.card V ≤ 1001 * q)
    (hdense : (((Fintype.card V : ℝ) ^ 2 - q ^ 2) / 4) <
      (H.edgeFinset.card : ℝ)) :
    (I.D.filter fun y ↦ y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D).card < 3 * q := by
  classical
  let D0 := I.D.filter fun y ↦ y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D
  change D0.card < 3 * q
  by_contra hnot
  have hlarge : 3 * q ≤ D0.card := by omega
  have hD0sub : D0 ⊆ I.D := fun y hy ↦ (Finset.mem_filter.mp hy).1
  have hcons := InitialCore.wrongSide_consequences (G := G) I hHG hII hq
    (by simpa [D0] using hlarge)
  change I.D.card - D0.card < 12 * q ∧
    ∀ y ∈ D0, D0.card < degreeInto H y D0 + 3 * q at hcons
  obtain ⟨ht, hmin⟩ := hcons
  have hmaxEdge : 2 * H.edgeFinset.card ≤ Fintype.card V * I.D.card := by
    rw [← H.sum_degrees_eq_twice_card_edges]
    calc
      _ ≤ ∑ _v : V, I.D.card := Finset.sum_le_sum fun v _ ↦ I.maxDegree v
      _ = Fintype.card V * I.D.card := by simp
  have hDlarge : 18 * q < I.D.card := by
    by_contra hnotD
    have hDle : I.D.card ≤ 18 * q := by omega
    have hmaxR : (2 : ℝ) * H.edgeFinset.card ≤
        (Fintype.card V : ℝ) * I.D.card := by exact_mod_cast hmaxEdge
    have hloR : (1000 : ℝ) * q ≤ Fintype.card V := by exact_mod_cast hscale_lo
    have hhiR : (Fintype.card V : ℝ) ≤ 1001 * q := by exact_mod_cast hscale_hi
    have hDleR : (I.D.card : ℝ) ≤ 18 * q := by exact_mod_cast hDle
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hprod : (Fintype.card V : ℝ) * I.D.card ≤
        (1001 * q) * (18 * q) :=
      mul_le_mul hhiR hDleR (by positivity) (by positivity)
    have hsquare : 0 ≤ ((Fintype.card V : ℝ) - 1000 * q) *
        ((Fintype.card V : ℝ) + 1000 * q) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith
  have hD0large : 6 * q < D0.card := by
    have hD0card := Finset.card_le_card hD0sub
    omega
  let F := D0.filter fun y ↦ degreeInto G y (I.C \ I.A6) = 0
  have hFsmall : F.card < 37 * q := by
    simpa [F] using InitialCore.card_isolated_wrongSide_lt (G := G) I hHG hG hII hq
      D0 hD0sub ht hD0large hmin
  let D1 := D0 \ (F ∪ I.A4)
  have hD1sub0 : D1 ⊆ D0 := fun y hy ↦ (Finset.mem_sdiff.mp hy).1
  have hD1sub : D1 ⊆ I.D := hD1sub0.trans hD0sub
  have hDcover : D0 ⊆ D1 ∪ F ∪ I.A4 := by
    intro y hy0
    by_cases hyF : y ∈ F
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hyF)
    by_cases hy4 : y ∈ I.A4
    · exact Finset.mem_union_right _ hy4
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hy0, by simp [hyF, hy4]⟩))
  have hD1near : I.D.card < D1.card + 50 * q := by
    have hc := Finset.card_le_card hDcover
    have hu1 := Finset.card_union_le (D1 ∪ F) I.A4
    have hu2 := Finset.card_union_le D1 F
    have hA4 := I.card_A4
    omega
  have hex : ∀ y ∈ D1, ∃ x, x ∈ I.C \ I.A6 ∧ G.Adj y x := by
    intro y hy1
    have hy0 := hD1sub0 hy1
    have hyNot := (Finset.mem_sdiff.mp hy1).2
    have hyF : y ∉ F := fun h ↦ hyNot (Finset.mem_union_left _ h)
    have hne : degreeInto G y (I.C \ I.A6) ≠ 0 := by
      intro heq
      exact hyF (Finset.mem_filter.mpr ⟨hy0, heq⟩)
    have hpos : 0 < degreeInto G y (I.C \ I.A6) := Nat.pos_of_ne_zero hne
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    have hx' := Finset.mem_inter.mp hx
    exact ⟨x, hx'.2, by simpa using hx'.1⟩
  have hex' : ∀ y : V, ∃ x : V,
      y ∈ D1 → x ∈ I.C \ I.A6 ∧ G.Adj y x := by
    intro y
    by_cases hy : y ∈ D1
    · obtain ⟨x, hx, hxy⟩ := hex y hy
      exact ⟨x, fun _ ↦ ⟨hx, hxy⟩⟩
    · exact ⟨y, fun h ↦ (hy h).elim⟩
  choose f hf using hex'
  have hfset : ∀ y ∈ D1, f y ∈ I.C \ I.A6 :=
    fun y hy ↦ (hf y hy).1
  have hfadj : ∀ y ∈ D1, G.Adj y (f y) :=
    fun y hy ↦ (hf y hy).2
  have hfinj : Set.InjOn f (↑D1 : Set V) := by
    intro y hy z hz heq
    have hy0 := hD1sub0 hy
    have hz0 := hD1sub0 hz
    have hle := InitialCore.degreeInto_wrongSide_le_one (G := G) I hHG
      D0 hD0sub ht hD0large hmin (Finset.mem_sdiff.mp (hfset y hy)).1
      (Finset.mem_sdiff.mp (hfset y hy)).2
    have hyMem : y ∈ G.neighborFinset (f y) ∩ D0 :=
      Finset.mem_inter.mpr ⟨by simpa [adj_comm] using hfadj y hy, hy0⟩
    have hzMem : z ∈ G.neighborFinset (f y) ∩ D0 :=
      Finset.mem_inter.mpr ⟨by simpa [heq, adj_comm] using hfadj z hz, hz0⟩
    by_contra hyz
    have hpair : ({y, z} : Finset V) ⊆ G.neighborFinset (f y) ∩ D0 := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hyMem
      · exact hzMem
    have hc := Finset.card_le_card hpair
    have hdeg : (G.neighborFinset (f y) ∩ D0).card = degreeInto G (f y) D0 := rfl
    simp [hyz] at hc
    omega
  let C1 := D1.image f
  have hCsub : C1 ⊆ I.C := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_sdiff.mp (hfset y hy)).1
  have hCcard : C1.card = D1.card := by
    rw [show C1 = D1.image f from rfl, Finset.card_image_of_injOn hfinj]
  have hseparate : ∀ y ∈ D1, ∀ z ∈ D1, f y ≠ z := by
    intro y hy z hz heq
    have hfyC1 : f y ∈ C1 := by
      rw [show C1 = D1.image f from rfl, Finset.mem_image]
      exact ⟨y, hy, rfl⟩
    have hfyC := hCsub hfyC1
    have hzD := hD1sub hz
    exact Finset.disjoint_left.mp I.disjoint hfyC (heq ▸ hzD)
  have hcritC1 : ∀ y ∈ D1,
      D1.card < degreeInto (criticalGraph G) y C1 + 2 * q := by
    intro y hy1
    have hy0 := hD1sub0 hy1
    have hyD := hD1sub hy1
    have hy5 : y ∉ I.A5 := (Finset.mem_filter.mp hy0).2.1
    have hyNot := (Finset.mem_sdiff.mp hy1).2
    have hy4 : y ∉ I.A4 := fun h ↦ hyNot (Finset.mem_union_right _ h)
    have hbig := I.good_critical_cross y hyD hy4 hy5
    have hC1le : C1.card ≤ I.C.card := Finset.card_le_card hCsub
    have hsplit : degreeInto (criticalGraph G) y I.C ≤
        degreeInto (criticalGraph G) y C1 + (I.C.card - C1.card) := by
      have hsub : (criticalGraph G).neighborFinset y ∩ I.C ⊆
          ((criticalGraph G).neighborFinset y ∩ C1) ∪ (I.C \ C1) := by
        intro z hz
        have hz' := Finset.mem_inter.mp hz
        by_cases hz1 : z ∈ C1
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz'.1, hz1⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz'.2, hz1⟩)
      have hc := Finset.card_le_card hsub
      have hu := Finset.card_union_le
        ((criticalGraph G).neighborFinset y ∩ C1) (I.C \ C1)
      rw [Finset.card_sdiff_of_subset hCsub] at hu
      dsimp [degreeInto] at hc ⊢
      omega
    omega
  have hself := matched_self_degree_sum_le (G := G) hHG q D1 C1 f rfl hfinj hfadj
    hcritC1 hseparate
  have hcross : ∑ y ∈ D1, degreeInto H y C1 ≤ D1.card * (2 * q) := by
    calc
      _ ≤ ∑ _y ∈ D1, (2 * q) := by
        apply Finset.sum_le_sum
        intro y hy1
        have hy0 := hD1sub0 hy1
        have hyType : 2 * q ≤ degreeInto H y I.D := (Finset.mem_filter.mp hy0).2.2
        have hsmallC := (InitialCore.not_large_both (G := G) I hHG hII hq y).resolve_right
          (by omega)
        have hsub : H.neighborFinset y ∩ C1 ⊆ H.neighborFinset y ∩ I.C :=
          Finset.inter_subset_inter (fun _ h ↦ h) hCsub
        have hc := Finset.card_le_card hsub
        change degreeInto H y C1 ≤ 2 * q
        change degreeInto H y C1 ≤ degreeInto H y I.C at hc
        exact hc.trans (Nat.le_of_lt hsmallC)
      _ = D1.card * (2 * q) := by simp
  have htwice := InitialCore.twice_card_edges_le_of_matched_core (G := G) I C1 D1
    hCsub hD1sub hCcard hself hcross
  have htwoD1 : 2 * D1.card ≤ Fintype.card V := by
    have hdisj : Disjoint C1 D1 :=
      Finset.disjoint_of_subset_left hCsub
        (Finset.disjoint_of_subset_right hD1sub I.disjoint)
    have hc := Finset.card_le_card (Finset.subset_univ (C1 ∪ D1))
    rw [Finset.card_union_of_disjoint hdisj, hCcard, Finset.card_univ] at hc
    omega
  have htwiceR : ((2 * H.edgeFinset.card : ℕ) : ℝ) ≤
      ((D1.card * (D1.card + 6 * q) +
        2 * (Fintype.card V - 2 * D1.card) * I.D.card : ℕ) : ℝ) := by
    exact_mod_cast htwice
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at htwiceR
  rw [Nat.cast_sub htwoD1] at htwiceR
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at htwiceR
  have hD1le : D1.card ≤ I.D.card := Finset.card_le_card hD1sub
  have hD1leR : (D1.card : ℝ) ≤ I.D.card := by exact_mod_cast hD1le
  have hnearR : (I.D.card : ℝ) < D1.card + 50 * q := by exact_mod_cast hD1near
  have hfactor : ((D1.card : ℝ) - I.D.card + 50 * q) *
      ((D1.card : ℝ) - 3 * I.D.card - 44 * q) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hquad : (2 : ℝ) * H.edgeFinset.card ≤
      -3 * (I.D.card : ℝ) ^ 2 +
        2 * Fintype.card V * I.D.card + 106 * q * I.D.card + 2200 * q ^ 2 := by
    nlinarith
  have hloR : (1000 : ℝ) * q ≤ Fintype.card V := by exact_mod_cast hscale_lo
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsquare : 0 ≤ ((6 : ℝ) * I.D.card - 2 * Fintype.card V - 106 * q) ^ 2 :=
    sq_nonneg _
  have hscaleSquare : 0 ≤ ((Fintype.card V : ℝ) - 1000 * q) *
      ((Fintype.card V : ℝ) + 1000 * q) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith

/-- The maximum-degree cell is already large under the near-extremal density
hypothesis.  The deliberately weak constant `18` is useful for selecting
vertices outside all Section 4 and Section 5 exceptional sets. -/
lemma InitialCore.card_D_gt_eighteen_mul
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (I : InitialCore G H q) (hq : 0 < q)
    (hscale_lo : 1000 * q ≤ Fintype.card V)
    (hscale_hi : Fintype.card V ≤ 1001 * q)
    (hdense : (((Fintype.card V : ℝ) ^ 2 - q ^ 2) / 4) <
      (H.edgeFinset.card : ℝ)) :
    18 * q < I.D.card := by
  have hmaxEdge : 2 * H.edgeFinset.card ≤ Fintype.card V * I.D.card := by
    rw [← H.sum_degrees_eq_twice_card_edges]
    calc
      _ ≤ ∑ _v : V, I.D.card := Finset.sum_le_sum fun v _ ↦ I.maxDegree v
      _ = Fintype.card V * I.D.card := by simp
  by_contra hnot
  have hDle : I.D.card ≤ 18 * q := by omega
  have hmaxR : (2 : ℝ) * H.edgeFinset.card ≤
      (Fintype.card V : ℝ) * I.D.card := by exact_mod_cast hmaxEdge
  have hloR : (1000 : ℝ) * q ≤ Fintype.card V := by exact_mod_cast hscale_lo
  have hhiR : (Fintype.card V : ℝ) ≤ 1001 * q := by exact_mod_cast hscale_hi
  have hDleR : (I.D.card : ℝ) ≤ 18 * q := by exact_mod_cast hDle
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hprod : (Fintype.card V : ℝ) * I.D.card ≤
      (1001 * q) * (18 * q) :=
    mul_le_mul hhiR hDleR (by positivity) (by positivity)
  have hsquare : 0 ≤ ((Fintype.card V : ℝ) - 1000 * q) *
      ((Fintype.card V : ℝ) + 1000 * q) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith

/-- Section 6 starts with an almost complete bipartite type-I core.  Removing
the three exceptional sets from `D` costs fewer than `5q` vertices; every
remaining vertex has type-I degree into `C` with fewer than `6q` omissions.
The two cells differ by at most the displayed additive errors. -/
lemma InitialCore.section6_typeI_core
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (I : InitialCore G H q) (hHG : H ≤ G) (hG : IsDiameter2Critical G)
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y))
    (hq : 0 < q)
    (hscale_lo : 1000 * q ≤ Fintype.card V)
    (hscale_hi : Fintype.card V ≤ 1001 * q)
    (hdense : (((Fintype.card V : ℝ) ^ 2 - q ^ 2) / 4) <
      (H.edgeFinset.card : ℝ)) :
    let D0 := I.D.filter fun y ↦ y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D
    let D7 := I.D \ (I.A4 ∪ I.A5 ∪ D0)
    I.C.card < I.D.card + q ∧
      I.D.card < I.C.card + 3 * q ∧
      I.D.card < D7.card + 5 * q ∧
      ∀ y ∈ D7, I.C.card < degreeInto (typeIGraph G) y I.C + 6 * q := by
  classical
  let n := Fintype.card V
  let D0 := I.D.filter fun y ↦ y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D
  let D7 := I.D \ (I.A4 ∪ I.A5 ∪ D0)
  change I.C.card < I.D.card + q ∧
    I.D.card < I.C.card + 3 * q ∧
    I.D.card < D7.card + 5 * q ∧
    ∀ y ∈ D7, I.C.card < degreeInto (typeIGraph G) y I.C + 6 * q
  have hDC : I.D.card + I.C.card = n := by
    have hc := congr_arg Finset.card I.partition
    rw [Finset.card_union_of_disjoint I.disjoint, Finset.card_univ] at hc
    simpa [n, add_comm] using hc
  have hmaxEdge : 2 * H.edgeFinset.card ≤ n * I.D.card := by
    rw [← H.sum_degrees_eq_twice_card_edges]
    calc
      _ ≤ ∑ _v : V, I.D.card := Finset.sum_le_sum fun v _ ↦ I.maxDegree v
      _ = n * I.D.card := by simp [n]
  have hCD : I.C.card < I.D.card + q := by
    by_contra hnot
    have hgap : I.D.card + q ≤ I.C.card := by omega
    have hmaxR : (2 : ℝ) * H.edgeFinset.card ≤ (n : ℝ) * I.D.card := by
      exact_mod_cast hmaxEdge
    have hnq : q ≤ n := (by omega : q ≤ 1000 * q).trans hscale_lo
    have hnqR : (q : ℝ) ≤ n := by exact_mod_cast hnq
    have hDCR : (I.D.card : ℝ) + I.C.card = n := by exact_mod_cast hDC
    have hgapR : (I.D.card : ℝ) + q ≤ I.C.card := by exact_mod_cast hgap
    nlinarith
  have hD0 : D0.card < 3 * q := by
    simpa [D0] using InitialCore.wrongSide_small (G := G) I hHG hG hII hq
      hscale_lo hscale_hi hdense
  let E := I.A4 ∪ I.A5 ∪ D0
  have hE : E.card < 5 * q := by
    have h4 := I.card_A4
    have h5 := I.card_A5
    calc
      E.card ≤ (I.A4 ∪ I.A5).card + D0.card := by
        simpa [E, Finset.union_assoc] using Finset.card_union_le (I.A4 ∪ I.A5) D0
      _ ≤ I.A4.card + I.A5.card + D0.card := by
        gcongr
        exact Finset.card_union_le _ _
      _ < q + q + 3 * q := by omega
      _ = 5 * q := by ring
  have hD7sub : D7 ⊆ I.D := fun y hy ↦ (Finset.mem_sdiff.mp hy).1
  have hDnear : I.D.card < D7.card + 5 * q := by
    have hcover : I.D ⊆ D7 ∪ E := by
      intro y hy
      by_cases hyE : y ∈ E
      · exact Finset.mem_union_right _ hyE
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hy, by simpa [E] using hyE⟩)
    have hc := Finset.card_le_card hcover
    have hu := Finset.card_union_le D7 E
    omega
  have hDlarge := InitialCore.card_D_gt_eighteen_mul (G := G) I hq hscale_lo
    hscale_hi hdense
  have hD7pos : 0 < D7.card := by omega
  obtain ⟨y, hy7⟩ := Finset.card_pos.mp hD7pos
  have hyD : y ∈ I.D := hD7sub hy7
  have hyE : y ∉ E := (Finset.mem_sdiff.mp hy7).2
  have hy4 : y ∉ I.A4 := fun h ↦ hyE (by simp [E, h])
  have hy5 : y ∉ I.A5 := fun h ↦ hyE (by simp [E, h])
  have hy0 : y ∉ D0 := fun h ↦ hyE (by simp [E, h])
  have hyInternal : degreeInto H y I.D < 2 * q := by
    have : ¬(y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D) := by
      simpa [D0, hyD] using hy0
    by_contra hnot
    exact this ⟨hy5, by omega⟩
  have hyDegree := I.good_H_degree y hyD hy5
  have hySplit := degreeInto_add_of_partition H y I.disjoint I.partition
  have hDCright : I.D.card < I.C.card + 3 * q := by
    have hIntoDegree : degreeInto H y I.C + degreeInto H y I.D = H.degree y := hySplit
    have hIntoCard := degreeInto_le_card H y I.C
    omega
  have hTypeI : ∀ z ∈ D7,
      I.C.card < degreeInto (typeIGraph G) z I.C + 6 * q := by
    intro z hz7
    have hzD : z ∈ I.D := hD7sub hz7
    have hzE : z ∉ E := (Finset.mem_sdiff.mp hz7).2
    have hz4 : z ∉ I.A4 := fun h ↦ hzE (by simp [E, h])
    have hz5 : z ∉ I.A5 := fun h ↦ hzE (by simp [E, h])
    have hz0 : z ∉ D0 := fun h ↦ hzE (by simp [E, h])
    have hzInternal : degreeInto H z I.D < 2 * q := by
      have : ¬(z ∉ I.A5 ∧ 2 * q ≤ degreeInto H z I.D) := by
        simpa [D0, hzD] using hz0
      by_contra hnot
      exact this ⟨hz5, by omega⟩
    have hzDegree := I.good_H_degree z hzD hz5
    have hzSplit := degreeInto_add_of_partition H z I.disjoint I.partition
    have hzH : I.C.card < degreeInto H z I.C + 4 * q := by
      have hzIntoCard := degreeInto_le_card H z I.C
      omega
    have hzCrit := I.good_critical_cross z hzD hz4 hz5
    let A := H.neighborFinset z ∩ I.C
    let B := (criticalGraph G).neighborFinset z ∩ I.C
    have hAsub : A ⊆ I.C := Finset.inter_subset_right
    have hBsub : B ⊆ I.C := Finset.inter_subset_right
    have hInter : A ∩ B ⊆ (typeIGraph G).neighborFinset z ∩ I.C := by
      intro w hw
      have hwA := Finset.mem_inter.mp (Finset.mem_inter.mp hw).1
      have hwB := Finset.mem_inter.mp (Finset.mem_inter.mp hw).2
      refine Finset.mem_inter.mpr ⟨?_, hwA.2⟩
      simpa using isTypeI_of_critical_of_adj (G := G) (by simpa using hwB.1)
        (hHG (by simpa using hwA.1))
    have hIE := Finset.card_union_add_card_inter A B
    have hUnion : (A ∪ B).card ≤ I.C.card :=
      Finset.card_le_card (Finset.union_subset hAsub hBsub)
    have hInterCard := Finset.card_le_card hInter
    change I.C.card < ((typeIGraph G).neighborFinset z ∩ I.C).card + 6 * q
    change I.C.card < A.card + 4 * q at hzH
    change I.C.card < B.card + 2 * q at hzCrit
    omega
  exact ⟨hCD, hDCright, hDnear, hTypeI⟩

/-- Double-counting the missing type-I pairs shows that all but fewer than
`61q` vertices of `C` see all but `100q` vertices of the Section 6 core
`D7`.  The relaxed constants keep every subsequent estimate integral. -/
lemma InitialCore.section6_other_core_small
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (I : InitialCore G H q) (hHG : H ≤ G) (hG : IsDiameter2Critical G)
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y))
    (hq : 0 < q)
    (hscale_lo : 1000 * q ≤ Fintype.card V)
    (hscale_hi : Fintype.card V ≤ 1001 * q)
    (hdense : (((Fintype.card V : ℝ) ^ 2 - q ^ 2) / 4) <
      (H.edgeFinset.card : ℝ)) :
    let D0 := I.D.filter fun y ↦ y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D
    let D7 := I.D \ (I.A4 ∪ I.A5 ∪ D0)
    let C7 := I.C.filter fun x ↦
      D7.card < degreeInto (typeIGraph G) x D7 + 100 * q
    I.C.card < C7.card + 61 * q := by
  classical
  let n := Fintype.card V
  let D0 := I.D.filter fun y ↦ y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D
  let D7 := I.D \ (I.A4 ∪ I.A5 ∪ D0)
  let C7 := I.C.filter fun x ↦
    D7.card < degreeInto (typeIGraph G) x D7 + 100 * q
  change I.C.card < C7.card + 61 * q
  have hcore := InitialCore.section6_typeI_core (G := G) I hHG hG hII hq
    hscale_lo hscale_hi hdense
  change I.C.card < I.D.card + q ∧
      I.D.card < I.C.card + 3 * q ∧
      I.D.card < D7.card + 5 * q ∧
      ∀ y ∈ D7, I.C.card < degreeInto (typeIGraph G) y I.C + 6 * q at hcore
  have hD7sub : D7 ⊆ I.D := fun y hy ↦ (Finset.mem_sdiff.mp hy).1
  have hD7univ : D7 ⊆ (Finset.univ : Finset V) := Finset.subset_univ D7
  have hD7card : D7.card ≤ n := by simpa [n] using Finset.card_le_card hD7univ
  have hD7pos : 0 < D7.card := by
    have hDlarge := InitialCore.card_D_gt_eighteen_mul (G := G) I hq hscale_lo
      hscale_hi hdense
    omega
  let F := I.C \ C7
  have hFsub : F ⊆ I.C := fun x hx ↦ (Finset.mem_sdiff.mp hx).1
  have hC7sub : C7 ⊆ I.C := fun x hx ↦ (Finset.mem_filter.mp hx).1
  have hmissingLower : F.card * (100 * q) ≤
      ∑ x ∈ F, (D7.card - degreeInto (typeIGraph G) x D7) := by
    calc
      _ = ∑ _x ∈ F, (100 * q) := by simp
      _ ≤ ∑ x ∈ F, (D7.card - degreeInto (typeIGraph G) x D7) := by
        apply Finset.sum_le_sum
        intro x hxF
        have hxC := hFsub hxF
        have hx7 : x ∉ C7 := (Finset.mem_sdiff.mp hxF).2
        have hnot : ¬D7.card < degreeInto (typeIGraph G) x D7 + 100 * q := by
          simpa [C7, hxC] using hx7
        have hle := degreeInto_le_card (typeIGraph G) x D7
        omega
  have hmissingMono :
      (∑ x ∈ F, (D7.card - degreeInto (typeIGraph G) x D7)) ≤
      ∑ x ∈ I.C, (D7.card - degreeInto (typeIGraph G) x D7) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hFsub
    simp
  have hcross := sum_degreeInto_comm (typeIGraph G) I.C D7
  have hmissingEq :
      (∑ x ∈ I.C, (D7.card - degreeInto (typeIGraph G) x D7)) =
      ∑ y ∈ D7, (I.C.card - degreeInto (typeIGraph G) y I.C) := by
    rw [sum_const_sub I.C D7.card
        (fun x ↦ degreeInto (typeIGraph G) x D7)
        (fun x _ ↦ degreeInto_le_card (typeIGraph G) x D7),
      sum_const_sub D7 I.C.card
        (fun y ↦ degreeInto (typeIGraph G) y I.C)
        (fun y _ ↦ degreeInto_le_card (typeIGraph G) y I.C), hcross]
    rw [Nat.mul_comm]
  have hmissingUpper :
      (∑ y ∈ D7, (I.C.card - degreeInto (typeIGraph G) y I.C)) <
      D7.card * (6 * q) := by
    have hle : ∑ y ∈ D7, (I.C.card - degreeInto (typeIGraph G) y I.C) ≤
        ∑ _y ∈ D7, (6 * q - 1) := by
      apply Finset.sum_le_sum
      intro y hy
      have hycore := hcore.2.2.2 y hy
      omega
    calc
      _ ≤ D7.card * (6 * q - 1) := by simpa using hle
      _ < D7.card * (6 * q) := by
        apply Nat.mul_lt_mul_of_pos_left
        · omega
        · exact hD7pos
  have hproduct : F.card * (100 * q) < D7.card * (6 * q) :=
    hmissingLower.trans_lt (hmissingMono.trans_eq hmissingEq |>.trans_lt hmissingUpper)
  have hFsmall : F.card < 61 * q := by
    by_contra hnot
    have hFlarge : 61 * q ≤ F.card := by omega
    have hprodR : (F.card : ℝ) * (100 * q) < (D7.card : ℝ) * (6 * q) := by
      exact_mod_cast hproduct
    have hFR : (61 : ℝ) * q ≤ F.card := by exact_mod_cast hFlarge
    have hD7R : (D7.card : ℝ) ≤ n := by exact_mod_cast hD7card
    have hnR : (n : ℝ) ≤ 1001 * q := by exact_mod_cast hscale_hi
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    nlinarith
  have hcover : I.C ⊆ C7 ∪ F := by
    intro x hxC
    by_cases hx7 : x ∈ C7
    · exact Finset.mem_union_left _ hx7
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxC, hx7⟩)
  have hc := Finset.card_le_card hcover
  have hu := Finset.card_union_le C7 F
  omega

/-- A vertex cannot have many `G`-neighbors on both sides: a neighbor in the
type-I core `D7` and more than `6q` neighbors in `C` would complete a triangle
through a type-I edge. -/
lemma InitialCore.section6_degree_dichotomy
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (I : InitialCore G H q) (hHG : H ≤ G) (hG : IsDiameter2Critical G)
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y))
    (hq : 0 < q)
    (hscale_lo : 1000 * q ≤ Fintype.card V)
    (hscale_hi : Fintype.card V ≤ 1001 * q)
    (hdense : (((Fintype.card V : ℝ) ^ 2 - q ^ 2) / 4) <
      (H.edgeFinset.card : ℝ)) :
    let D0 := I.D.filter fun y ↦ y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D
    let D7 := I.D \ (I.A4 ∪ I.A5 ∪ D0)
    ∀ v, degreeInto G v I.C ≤ 6 * q ∨ degreeInto G v I.D < 5 * q := by
  classical
  let D0 := I.D.filter fun y ↦ y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D
  let D7 := I.D \ (I.A4 ∪ I.A5 ∪ D0)
  change ∀ v, degreeInto G v I.C ≤ 6 * q ∨ degreeInto G v I.D < 5 * q
  have hcore := InitialCore.section6_typeI_core (G := G) I hHG hG hII hq
    hscale_lo hscale_hi hdense
  change I.C.card < I.D.card + q ∧
      I.D.card < I.C.card + 3 * q ∧
      I.D.card < D7.card + 5 * q ∧
      ∀ y ∈ D7, I.C.card < degreeInto (typeIGraph G) y I.C + 6 * q at hcore
  have hD7sub : D7 ⊆ I.D := fun y hy ↦ (Finset.mem_sdiff.mp hy).1
  intro v
  by_cases hvC : degreeInto G v I.C ≤ 6 * q
  · exact Or.inl hvC
  · right
    have hvCbig : 6 * q < degreeInto G v I.C := by omega
    have hnone : G.neighborFinset v ∩ D7 = ∅ := by
      ext y
      constructor
      · intro hy
        rw [Finset.mem_inter] at hy
        obtain ⟨hyN, hy7⟩ := hy
        have hyCore := hcore.2.2.2 y hy7
        let A := G.neighborFinset v ∩ I.C
        let B := (typeIGraph G).neighborFinset y ∩ I.C
        have hAsub : A ⊆ I.C := Finset.inter_subset_right
        have hBsub : B ⊆ I.C := Finset.inter_subset_right
        have hsum : I.C.card < A.card + B.card := by
          change I.C.card < degreeInto G v I.C + degreeInto (typeIGraph G) y I.C
          omega
        obtain ⟨x, hxA, hxB⟩ := exists_mem_inter_of_card_lt_add hAsub hBsub hsum
        have hvx : G.Adj v x := by simpa [A] using (Finset.mem_inter.mp hxA).1
        have hyxI : IsTypeI G y x := by
          simpa [B] using (Finset.mem_inter.mp hxB).1
        have hyv : G.Adj y v := by simpa [adj_comm] using hyN
        have hvCommon : v ∈ G.commonNeighbors y x := by
          rw [G.mem_commonNeighbors]
          exact ⟨hyv, hvx.symm⟩
        exact (by simpa [hyxI.2] using hvCommon)
      · simp
    have hsubset : G.neighborFinset v ∩ I.D ⊆ I.D \ D7 := by
      intro y hy
      have hy' := Finset.mem_inter.mp hy
      refine Finset.mem_sdiff.mpr ⟨hy'.2, ?_⟩
      intro hy7
      have : y ∈ G.neighborFinset v ∩ D7 := Finset.mem_inter.mpr ⟨hy'.1, hy7⟩
      simpa [hnone] using this
    have hc := Finset.card_le_card hsubset
    have hD7card : D7.card ≤ I.D.card := Finset.card_le_card hD7sub
    rw [Finset.card_sdiff_of_subset hD7sub] at hc
    change degreeInto G v I.D < 5 * q
    change degreeInto G v I.D ≤ I.D.card - D7.card at hc
    omega

/-- The two type-I cores cover all but fewer than `66q` vertices.  We also
record the coarse lower bounds needed by the common-neighbor arguments. -/
lemma InitialCore.section6_core_sizes
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (I : InitialCore G H q) (hHG : H ≤ G) (hG : IsDiameter2Critical G)
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y))
    (hq : 0 < q)
    (hscale_lo : 1000 * q ≤ Fintype.card V)
    (hscale_hi : Fintype.card V ≤ 1001 * q)
    (hdense : (((Fintype.card V : ℝ) ^ 2 - q ^ 2) / 4) <
      (H.edgeFinset.card : ℝ)) :
    let D0 := I.D.filter fun y ↦ y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D
    let D7 := I.D \ (I.A4 ∪ I.A5 ∪ D0)
    let C7 := I.C.filter fun x ↦
      D7.card < degreeInto (typeIGraph G) x D7 + 100 * q
    let A7 := Finset.univ \ (C7 ∪ D7)
    A7.card < 66 * q ∧ 494 * q < D7.card ∧ 437 * q < C7.card := by
  classical
  let n := Fintype.card V
  let D0 := I.D.filter fun y ↦ y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D
  let D7 := I.D \ (I.A4 ∪ I.A5 ∪ D0)
  let C7 := I.C.filter fun x ↦
    D7.card < degreeInto (typeIGraph G) x D7 + 100 * q
  let A7 := Finset.univ \ (C7 ∪ D7)
  change A7.card < 66 * q ∧ 494 * q < D7.card ∧ 437 * q < C7.card
  have hcore := InitialCore.section6_typeI_core (G := G) I hHG hG hII hq
    hscale_lo hscale_hi hdense
  change I.C.card < I.D.card + q ∧
      I.D.card < I.C.card + 3 * q ∧
      I.D.card < D7.card + 5 * q ∧
      ∀ y ∈ D7, I.C.card < degreeInto (typeIGraph G) y I.C + 6 * q at hcore
  have hCnear := InitialCore.section6_other_core_small (G := G) I hHG hG hII hq
    hscale_lo hscale_hi hdense
  change I.C.card < C7.card + 61 * q at hCnear
  have hD7sub : D7 ⊆ I.D := fun y hy ↦ (Finset.mem_sdiff.mp hy).1
  have hC7sub : C7 ⊆ I.C := fun x hx ↦ (Finset.mem_filter.mp hx).1
  have hdisj7 : Disjoint C7 D7 :=
    Finset.disjoint_of_subset_left hC7sub
      (Finset.disjoint_of_subset_right hD7sub I.disjoint)
  have hDC : I.D.card + I.C.card = n := by
    have hc := congr_arg Finset.card I.partition
    rw [Finset.card_union_of_disjoint I.disjoint, Finset.card_univ] at hc
    simpa [n, add_comm] using hc
  have hDlower : 499 * q < I.D.card := by
    by_contra hnot
    have hDle : I.D.card ≤ 499 * q := by omega
    omega
  have hClower : 498 * q < I.C.card := by
    by_contra hnot
    have hCle : I.C.card ≤ 498 * q := by omega
    omega
  have hD7lower : 494 * q < D7.card := by omega
  have hC7lower : 437 * q < C7.card := by omega
  have hA7sub : A7 ⊆ (I.C \ C7) ∪ (I.D \ D7) := by
    intro v hvA
    have hvNot := (Finset.mem_sdiff.mp hvA).2
    have hvPart : v ∈ I.C ∨ v ∈ I.D := by
      have : v ∈ I.C ∪ I.D := I.partition.symm ▸ Finset.mem_univ v
      exact Finset.mem_union.mp this
    rcases hvPart with hvC | hvD
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvC, fun hv7 ↦
        hvNot (Finset.mem_union_left _ hv7)⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvD, fun hv7 ↦
        hvNot (Finset.mem_union_right _ hv7)⟩)
  have hC7card : C7.card ≤ I.C.card := Finset.card_le_card hC7sub
  have hD7card : D7.card ≤ I.D.card := Finset.card_le_card hD7sub
  have hAupper : A7.card ≤ (I.C.card - C7.card) + (I.D.card - D7.card) := by
    calc
      A7.card ≤ ((I.C \ C7) ∪ (I.D \ D7)).card := Finset.card_le_card hA7sub
      _ ≤ (I.C \ C7).card + (I.D \ D7).card := Finset.card_union_le _ _
      _ = (I.C.card - C7.card) + (I.D.card - D7.card) := by
        rw [Finset.card_sdiff_of_subset hC7sub, Finset.card_sdiff_of_subset hD7sub]
  have hA7small : A7.card < 66 * q := by omega
  exact ⟨hA7small, hD7lower, hC7lower⟩

/-- The concrete enlarged bipartition produced in Section 6. -/
structure Section6Partition (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) where
  C7 : Finset V
  D7 : Finset V
  C8 : Finset V
  D8 : Finset V
  A : Finset V
  C : Finset V
  D : Finset V
  S : Finset V
  C_eq : C = C7 ∪ C8
  D_eq : D = D7 ∪ D8
  S_eq : S = C8 ∪ D8
  partition : C ∪ D ∪ A = Finset.univ
  disjoint_CD : Disjoint C D
  disjoint_CA : Disjoint C A
  disjoint_DA : Disjoint D A
  card_S : S.card < 66 * q
  card_D : 494 * q < D.card
  degree_A : ∀ v ∈ A, G.degree v < 300 * q
  no_critical_C : ∀ {x y}, x ∈ C → y ∈ C → ¬(criticalGraph G).Adj x y
  no_critical_D : ∀ {x y}, x ∈ D → y ∈ D → ¬(criticalGraph G).Adj x y
  no_edge_C7 : ∀ {x y}, x ∈ C7 → y ∈ C → ¬G.Adj x y
  no_edge_D7 : ∀ {x y}, x ∈ D7 → y ∈ D → ¬G.Adj x y

/-- Construction of the enlarged sides and the low-degree remainder in
Section 6. -/
lemma InitialCore.exists_section6Partition
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (I : InitialCore G H q) (hHG : H ≤ G) (hG : IsDiameter2Critical G)
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y))
    (hq : 0 < q)
    (hscale_lo : 1000 * q ≤ Fintype.card V)
    (hscale_hi : Fintype.card V ≤ 1001 * q)
    (hdense : (((Fintype.card V : ℝ) ^ 2 - q ^ 2) / 4) <
      (H.edgeFinset.card : ℝ)) :
    Nonempty (Section6Partition G q) := by
  classical
  let n := Fintype.card V
  let D0 := I.D.filter fun y ↦ y ∉ I.A5 ∧ 2 * q ≤ degreeInto H y I.D
  let D7 := I.D \ (I.A4 ∪ I.A5 ∪ D0)
  let C7 := I.C.filter fun x ↦
    D7.card < degreeInto (typeIGraph G) x D7 + 100 * q
  let A7 := Finset.univ \ (C7 ∪ D7)
  let A8 := A7.filter fun v ↦ G.degree v < 300 * q
  let R := A7 \ A8
  let C8 := R.filter fun v ↦ degreeInto G v I.C ≤ 6 * q
  let D8 := R \ C8
  let C' := C7 ∪ C8
  let D' := D7 ∪ D8
  let S := C8 ∪ D8
  have hcore := InitialCore.section6_typeI_core (G := G) I hHG hG hII hq
    hscale_lo hscale_hi hdense
  change I.C.card < I.D.card + q ∧
      I.D.card < I.C.card + 3 * q ∧
      I.D.card < D7.card + 5 * q ∧
      ∀ y ∈ D7, I.C.card < degreeInto (typeIGraph G) y I.C + 6 * q at hcore
  have hsizes := InitialCore.section6_core_sizes (G := G) I hHG hG hII hq
    hscale_lo hscale_hi hdense
  change A7.card < 66 * q ∧ 494 * q < D7.card ∧ 437 * q < C7.card at hsizes
  have hdich := InitialCore.section6_degree_dichotomy (G := G) I hHG hG hII hq
    hscale_lo hscale_hi hdense
  change ∀ v, degreeInto G v I.C ≤ 6 * q ∨ degreeInto G v I.D < 5 * q at hdich
  have hD7sub : D7 ⊆ I.D := fun y hy ↦ (Finset.mem_sdiff.mp hy).1
  have hC7sub : C7 ⊆ I.C := fun x hx ↦ (Finset.mem_filter.mp hx).1
  have hA8sub : A8 ⊆ A7 := fun x hx ↦ (Finset.mem_filter.mp hx).1
  have hRsub : R ⊆ A7 := fun x hx ↦ (Finset.mem_sdiff.mp hx).1
  have hC8subR : C8 ⊆ R := fun x hx ↦ (Finset.mem_filter.mp hx).1
  have hD8subR : D8 ⊆ R := fun x hx ↦ (Finset.mem_sdiff.mp hx).1
  have hC8subA : C8 ⊆ A7 := hC8subR.trans hRsub
  have hD8subA : D8 ⊆ A7 := hD8subR.trans hRsub
  have hCoreA : Disjoint (C7 ∪ D7) A7 := by
    rw [Finset.disjoint_left]
    intro x hx hxa
    exact (Finset.mem_sdiff.mp hxa).2 hx
  have hC7A : Disjoint C7 A7 := Finset.disjoint_of_subset_left
    (Finset.subset_union_left) hCoreA
  have hD7A : Disjoint D7 A7 := Finset.disjoint_of_subset_left
    (Finset.subset_union_right) hCoreA
  have hC8D8 : Disjoint C8 D8 := by
    rw [Finset.disjoint_left]
    intro x hx8 hxd
    exact (Finset.mem_sdiff.mp hxd).2 hx8
  have hC8A8 : Disjoint C8 A8 := by
    rw [Finset.disjoint_left]
    intro x hx8 hxa
    exact (Finset.mem_sdiff.mp (hC8subR hx8)).2 hxa
  have hD8A8 : Disjoint D8 A8 := by
    rw [Finset.disjoint_left]
    intro x hxd hxa
    exact (Finset.mem_sdiff.mp (hD8subR hxd)).2 hxa
  have hC'D' : Disjoint C' D' := by
    rw [Finset.disjoint_left]
    intro x hxc hxd
    rcases Finset.mem_union.mp hxc with hx7 | hx8 <;>
      rcases Finset.mem_union.mp hxd with hy7 | hy8
    · exact Finset.disjoint_left.mp I.disjoint (hC7sub hx7) (hD7sub hy7)
    · exact Finset.disjoint_left.mp hC7A hx7 (hD8subA hy8)
    · exact Finset.disjoint_left.mp hD7A hy7 (hC8subA hx8)
    · exact Finset.disjoint_left.mp hC8D8 hx8 hy8
  have hC'A8 : Disjoint C' A8 := by
    rw [Finset.disjoint_left]
    intro x hxc hxa
    rcases Finset.mem_union.mp hxc with hx7 | hx8
    · exact Finset.disjoint_left.mp hC7A hx7 (hA8sub hxa)
    · exact Finset.disjoint_left.mp hC8A8 hx8 hxa
  have hD'A8 : Disjoint D' A8 := by
    rw [Finset.disjoint_left]
    intro x hxd hxa
    rcases Finset.mem_union.mp hxd with hx7 | hx8
    · exact Finset.disjoint_left.mp hD7A hx7 (hA8sub hxa)
    · exact Finset.disjoint_left.mp hD8A8 hx8 hxa
  have hpart : C' ∪ D' ∪ A8 = Finset.univ := by
    ext x
    constructor
    · intro _
      exact Finset.mem_univ x
    · intro _
      by_cases hxcore : x ∈ C7 ∪ D7
      · rcases Finset.mem_union.mp hxcore with hxC | hxD
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ hxC))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_union_left _ hxD))
      · have hxA7 : x ∈ A7 := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxcore⟩
        by_cases hxA8 : x ∈ A8
        · exact Finset.mem_union_right _ hxA8
        · have hxR : x ∈ R := Finset.mem_sdiff.mpr ⟨hxA7, hxA8⟩
          by_cases hxsmall : degreeInto G x I.C ≤ 6 * q
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxR, hxsmall⟩)))
          · have hxC8 : x ∉ C8 := by simpa [C8, hxR] using hxsmall
            exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxR, hxC8⟩)))
  have hDC : I.D.card + I.C.card = n := by
    have hc := congr_arg Finset.card I.partition
    rw [Finset.card_union_of_disjoint I.disjoint, Finset.card_univ] at hc
    simpa [n, add_comm] using hc
  have hDupper : I.D.card < 504 * q := by omega
  have hCupper : I.C.card < 503 * q := by omega
  have hC8degree : ∀ x ∈ C8, 294 * q ≤ degreeInto G x I.D := by
    intro x hx8
    have hxR := hC8subR hx8
    have hxNotA : x ∉ A8 := (Finset.mem_sdiff.mp hxR).2
    have hxDeg : 300 * q ≤ G.degree x := by
      have : ¬G.degree x < 300 * q := by simpa [A8, hRsub hxR] using hxNotA
      omega
    have hxSmall := (Finset.mem_filter.mp hx8).2
    have hxSplit := degreeInto_add_of_partition G x I.disjoint I.partition
    omega
  have hD8degree : ∀ x ∈ D8, 295 * q < degreeInto G x I.C := by
    intro x hx8
    have hxR := hD8subR hx8
    have hxNotA : x ∉ A8 := (Finset.mem_sdiff.mp hxR).2
    have hxDeg : 300 * q ≤ G.degree x := by
      have : ¬G.degree x < 300 * q := by simpa [A8, hRsub hxR] using hxNotA
      omega
    have hxNotC : x ∉ C8 := (Finset.mem_sdiff.mp hx8).2
    have hxLargeC : 6 * q < degreeInto G x I.C := by
      have : ¬degreeInto G x I.C ≤ 6 * q := by simpa [C8, hxR] using hxNotC
      omega
    have hxSmallD := (hdich x).resolve_left (by omega)
    have hxSplit := degreeInto_add_of_partition G x I.disjoint I.partition
    omega
  have hC'degree : ∀ x ∈ C', 294 * q ≤ degreeInto G x I.D := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx7 | hx8
    · have hxDef := (Finset.mem_filter.mp hx7).2
      have hmono : degreeInto (typeIGraph G) x D7 ≤ degreeInto G x I.D := by
        apply Finset.card_le_card
        intro y hy
        have hy' := Finset.mem_inter.mp hy
        exact Finset.mem_inter.mpr ⟨by simpa using typeIGraph_le (G := G) (by simpa using hy'.1),
          hD7sub hy'.2⟩
      omega
    · exact hC8degree x hx8
  have hD'degree : ∀ x ∈ D', 295 * q ≤ degreeInto G x I.C := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx7 | hx8
    · have hxCore := hcore.2.2.2 x hx7
      have hmono := degreeInto_mono (typeIGraph_le (G := G)) x I.C
      omega
    · exact Nat.le_of_lt (hD8degree x hx8)
  have hNoC : ∀ {x y}, x ∈ C' → y ∈ C' → ¬(criticalGraph G).Adj x y := by
    intro x y hx hy
    apply not_critical_of_two_commonNeighbors (G := G) I.D
    have hxD := hC'degree x hx
    have hyD := hC'degree y hy
    omega
  have hNoD : ∀ {x y}, x ∈ D' → y ∈ D' → ¬(criticalGraph G).Adj x y := by
    intro x y hx hy
    apply not_critical_of_two_commonNeighbors (G := G) I.C
    have hxC := hD'degree x hx
    have hyC := hD'degree y hy
    omega
  have hNoEdgeC : ∀ {x y}, x ∈ C7 → y ∈ C' → ¬G.Adj x y := by
    intro x y hx7 hy hxy
    let TX := (typeIGraph G).neighborFinset x ∩ D7
    let NY := G.neighborFinset y ∩ I.D
    have hTXsub : TX ⊆ I.D := fun z hz ↦ hD7sub (Finset.mem_inter.mp hz).2
    have hNYsub : NY ⊆ I.D := Finset.inter_subset_right
    have hxDef := (Finset.mem_filter.mp hx7).2
    have hyDeg := hC'degree y hy
    have hsum : I.D.card < TX.card + NY.card := by
      change I.D.card < degreeInto (typeIGraph G) x D7 + degreeInto G y I.D
      omega
    obtain ⟨z, hzT, hzN⟩ := exists_mem_inter_of_card_lt_add hTXsub hNYsub hsum
    have hxz : IsTypeI G x z := by simpa [TX] using (Finset.mem_inter.mp hzT).1
    have hzy : G.Adj z y := by simpa [NY, adj_comm] using (Finset.mem_inter.mp hzN).1
    have hyCommon : y ∈ G.commonNeighbors x z := by
      rw [G.mem_commonNeighbors]
      exact ⟨hxy, hzy⟩
    simpa [hxz.2] using hyCommon
  have hNoEdgeD : ∀ {x y}, x ∈ D7 → y ∈ D' → ¬G.Adj x y := by
    intro x y hx7 hy hxy
    let TX := (typeIGraph G).neighborFinset x ∩ I.C
    let NY := G.neighborFinset y ∩ I.C
    have hTXsub : TX ⊆ I.C := Finset.inter_subset_right
    have hNYsub : NY ⊆ I.C := Finset.inter_subset_right
    have hxCore := hcore.2.2.2 x hx7
    have hyDeg := hD'degree y hy
    have hsum : I.C.card < TX.card + NY.card := by
      change I.C.card < degreeInto (typeIGraph G) x I.C + degreeInto G y I.C
      omega
    obtain ⟨z, hzT, hzN⟩ := exists_mem_inter_of_card_lt_add hTXsub hNYsub hsum
    have hxz : IsTypeI G x z := by simpa [TX] using (Finset.mem_inter.mp hzT).1
    have hzy : G.Adj z y := by simpa [NY, adj_comm] using (Finset.mem_inter.mp hzN).1
    have hyCommon : y ∈ G.commonNeighbors x z := by
      rw [G.mem_commonNeighbors]
      exact ⟨hxy, hzy⟩
    simpa [hxz.2] using hyCommon
  have hScard : S.card < 66 * q := by
    have hSsub : S ⊆ A7 := Finset.union_subset hC8subA hD8subA
    exact (Finset.card_le_card hSsub).trans_lt hsizes.1
  have hDcard : 494 * q < D'.card :=
    hsizes.2.1.trans_le (Finset.card_le_card Finset.subset_union_left)
  refine ⟨{
    C7 := C7, D7 := D7, C8 := C8, D8 := D8, A := A8,
    C := C', D := D', S := S,
    C_eq := rfl, D_eq := rfl, S_eq := rfl,
    partition := hpart, disjoint_CD := hC'D', disjoint_CA := hC'A8,
    disjoint_DA := hD'A8, card_S := hScard, card_D := hDcard,
    degree_A := fun v hv ↦ (Finset.mem_filter.mp hv).2,
    no_critical_C := hNoC, no_critical_D := hNoD,
    no_edge_C7 := hNoEdgeC, no_edge_D7 := hNoEdgeD }⟩

/-- Every edge internal to an enlarged side actually has both endpoints in
the corresponding small fringe. -/
lemma Section6Partition.internal_vertices
    (P : Section6Partition G q) {e : Sym2 V}
    (he : e ∈ edgesInside G P.C ∪ edgesInside G P.D) :
    e.toFinset ⊆ P.S := by
  classical
  obtain ⟨a, b⟩ := e
  have heSide := Finset.mem_union.mp he
  have heG : G.Adj a b := by
    rcases heSide with heC | heD
    · exact (by
        have := (Finset.mem_filter.mp heC).1
        rw [SimpleGraph.mem_edgeFinset] at this
        simpa using this)
    · exact (by
        have := (Finset.mem_filter.mp heD).1
        rw [SimpleGraph.mem_edgeFinset] at this
        simpa using this)
  have haS : a ∈ P.S := by
    rcases heSide with heC | heD
    · have hsub := (Finset.mem_filter.mp heC).2
      have haC : a ∈ P.C := hsub (by simp)
      rw [P.C_eq] at haC
      rcases Finset.mem_union.mp haC with ha7 | ha8
      · have hbC : b ∈ P.C := hsub (by simp)
        exact (P.no_edge_C7 ha7 hbC heG).elim
      · rw [P.S_eq]
        exact Finset.mem_union_left _ ha8
    · have hsub := (Finset.mem_filter.mp heD).2
      have haD : a ∈ P.D := hsub (by simp)
      rw [P.D_eq] at haD
      rcases Finset.mem_union.mp haD with ha7 | ha8
      · have hbD : b ∈ P.D := hsub (by simp)
        exact (P.no_edge_D7 ha7 hbD heG).elim
      · rw [P.S_eq]
        exact Finset.mem_union_right _ ha8
  have hbS : b ∈ P.S := by
    rcases heSide with heC | heD
    · have hsub := (Finset.mem_filter.mp heC).2
      have hbC : b ∈ P.C := hsub (by simp)
      rw [P.C_eq] at hbC
      rcases Finset.mem_union.mp hbC with hb7 | hb8
      · have haC : a ∈ P.C := hsub (by simp)
        exact (P.no_edge_C7 hb7 haC heG.symm).elim
      · rw [P.S_eq]
        exact Finset.mem_union_left _ hb8
    · have hsub := (Finset.mem_filter.mp heD).2
      have hbD : b ∈ P.D := hsub (by simp)
      rw [P.D_eq] at hbD
      rcases Finset.mem_union.mp hbD with hb7 | hb8
      · have haD : a ∈ P.D := hsub (by simp)
        exact (P.no_edge_D7 hb7 haD heG.symm).elim
      · rw [P.S_eq]
        exact Finset.mem_union_right _ hb8
  simpa [Sym2.toFinset_mk_eq, Finset.insert_subset_iff] using And.intro haS hbS

/-- The final charge associated with an internal edge. -/
lemma Section6Partition.internal_charge
    (P : Section6Partition G q) (hG : IsDiameter2Critical G)
    (e : Sym2 V) (he : e ∈ edgesInside G P.C ∪ edgesInside G P.D) :
    (∃ x ∈ P.C, ∃ y ∈ P.D, ¬G.Adj x y ∧ CriticalPathContains G x y e) ∨
      ∃ x ∈ P.S, ∃ y ∈ P.A, CriticalPathContains G x y e := by
  classical
  have heG : e ∈ G.edgeSet := by
    rcases Finset.mem_union.mp he with heC | heD
    · exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_filter.mp heC).1
    · exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_filter.mp heD).1
  obtain ⟨x, y, hp⟩ := exists_criticalPathContains_of_diameter2Critical (G := G) hG heG
  have hver := Section6Partition.internal_vertices (G := G) P he
  have hclassify : ∀ {a b : V}, a ∈ P.S → ¬G.Adj a b →
      CriticalPathContains G a b e →
      (∃ c ∈ P.C, ∃ d ∈ P.D, ¬G.Adj c d ∧ CriticalPathContains G c d e) ∨
        ∃ s ∈ P.S, ∃ z ∈ P.A, CriticalPathContains G s z e := by
    intro a b haS hnab hpab
    have haFringe : a ∈ P.C8 ∨ a ∈ P.D8 := by
      rw [P.S_eq] at haS
      exact Finset.mem_union.mp haS
    have hbPart : b ∈ P.C ∨ b ∈ P.D ∨ b ∈ P.A := by
      have : b ∈ P.C ∪ P.D ∪ P.A := P.partition.symm ▸ Finset.mem_univ b
      simpa [or_assoc] using this
    rcases haFringe with ha8 | ha8
    · have haC : a ∈ P.C := by
        rw [P.C_eq]
        exact Finset.mem_union_right _ ha8
      rcases hbPart with hbC | hbD | hbA
      · have hcrit : (criticalGraph G).Adj a b := by
          rcases hpab with ⟨hI, -⟩ | ⟨z, hII, -⟩
          · exact Or.inl hI
          · exact Or.inr ⟨z, hII⟩
        exact (P.no_critical_C haC hbC hcrit).elim
      · exact Or.inl ⟨a, haC, b, hbD, hnab, hpab⟩
      · exact Or.inr ⟨a, haS, b, hbA, hpab⟩
    · have haD : a ∈ P.D := by
        rw [P.D_eq]
        exact Finset.mem_union_right _ ha8
      rcases hbPart with hbC | hbD | hbA
      · refine Or.inl ⟨b, hbC, a, haD, ?_, ?_⟩
        · simpa [adj_comm] using hnab
        · exact (criticalPathContains_symm (G := G)).mp hpab
      · have hcrit : (criticalGraph G).Adj a b := by
          rcases hpab with ⟨hI, -⟩ | ⟨z, hII, -⟩
          · exact Or.inl hI
          · exact Or.inr ⟨z, hII⟩
        exact (P.no_critical_D haD hbD hcrit).elim
      · exact Or.inr ⟨a, haS, b, hbA, hpab⟩
  rcases hp with ⟨hI, heq⟩ | ⟨z, hII, heq | heq⟩
  · have heSide := Finset.mem_union.mp he
    rcases heSide with heC | heD
    · have hsub := (Finset.mem_filter.mp heC).2
      have hxC : x ∈ P.C := hsub (by simpa [heq])
      have hyC : y ∈ P.C := hsub (by simpa [heq])
      exact (P.no_critical_C hxC hyC (Or.inl hI)).elim
    · have hsub := (Finset.mem_filter.mp heD).2
      have hxD : x ∈ P.D := hsub (by simpa [heq])
      have hyD : y ∈ P.D := hsub (by simpa [heq])
      exact (P.no_critical_D hxD hyD (Or.inl hI)).elim
  · have hxS : x ∈ P.S := hver (by simpa [heq])
    exact hclassify hxS hII.2.1 (Or.inr ⟨z, hII, Or.inl heq⟩)
  · have hyS : y ∈ P.S := hver (by simpa [heq])
    exact hclassify hyS (by simpa [adj_comm] using hII.2.1)
      ((criticalPathContains_symm (G := G)).mp (Or.inr ⟨z, hII, Or.inr heq⟩))

/-- Exactification: a near-extremal pruned graph forces the original
diameter-two-critical graph to obey the sharp quarter bound. -/
lemma exact_bound_of_dense_pruned
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (hHG : H ≤ G) (hG : IsDiameter2Critical G)
    (hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y))
    {q : ℕ} (hq : 0 < q)
    (hscale_lo : 1000 * q ≤ Fintype.card V)
    (hscale_hi : Fintype.card V ≤ 1001 * q)
    (hdense : (((Fintype.card V : ℝ) ^ 2 - q ^ 2) / 4) <
      (H.edgeFinset.card : ℝ)) :
    G.edgeFinset.card ≤ Fintype.card V ^ 2 / 4 := by
  classical
  obtain ⟨I⟩ := exists_initialCore (G := G) hHG hG hII hq hscale_lo hscale_hi hdense
  obtain ⟨P⟩ := InitialCore.exists_section6Partition (G := G) I hHG hG hII hq
    hscale_lo hscale_hi hdense
  let Q : FinalPartition G q := {
    C := P.C
    D := P.D
    A := P.A
    S := P.S
    partition := P.partition
    disjoint_CD := P.disjoint_CD
    disjoint_CA := P.disjoint_CA
    disjoint_DA := P.disjoint_DA
    card_S := P.card_S
    card_D := P.card_D
    degree_A := P.degree_A
    no_critical_C := P.no_critical_C
    no_critical_D := P.no_critical_D
    internal_target := fun e he ↦
      Section6Partition.internal_charge (G := G) P hG e he
    internal_unique := by
      intro e f he hf x y hpe hpf
      exact criticalPathContains_unique_internal (G := G) P.C P.D P.disjoint_CD
        P.no_critical_C P.no_critical_D he hf hpe hpf }
  exact FinalPartition.card_edges_le_quarter (G := G) Q

end Exactification

section Final

/-- The real square divided by four lies below the successor of its natural
floor. -/
private lemma square_div_four_lt_succ_nat (n : ℕ) :
    (n : ℝ) ^ 2 / 4 < ((n ^ 2 / 4 + 1 : ℕ) : ℝ) := by
  have hr : n ^ 2 % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hd : n ^ 2 % 4 + 4 * (n ^ 2 / 4) = n ^ 2 := by
    simpa using Nat.mod_add_div (n ^ 2) 4
  have hrR : ((n ^ 2 % 4 : ℕ) : ℝ) < 4 := by exact_mod_cast hr
  have hdR : ((n ^ 2 % 4 : ℕ) : ℝ) + 4 * ((n ^ 2 / 4 : ℕ) : ℝ) =
      (n : ℝ) ^ 2 := by exact_mod_cast hd
  push_cast at hdR ⊢
  nlinarith

/-- Füredi's theorem, in exactly the form used by the Formal Conjectures
statement: the Murty--Simon bound holds for every sufficiently large finite
diameter-two edge-critical graph. -/
theorem erdos_742 : ∃ n₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V → IsDiameter2Critical G →
      G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 := by
  let M : ℕ := 100000000
  let eps : ℝ := 1 / 10000000000
  have heps : 0 < eps := by norm_num [eps]
  obtain ⟨nLight, hnLight⟩ := eventually_lightTriples_card_lt M eps heps
  refine ⟨max 1000000 nLight, ?_⟩
  intro W _ _ G _ hn hG
  classical
  let : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W)
    (Fintype.equivFin W).injective
  let n := Fintype.card W
  let q := n / 1000
  have hnMillion : 1000000 ≤ n := by
    exact (le_max_left _ _).trans (by simpa [n] using hn)
  have hnLight' : nLight ≤ n := by
    exact (le_max_right _ _).trans (by simpa [n] using hn)
  have hqThousand : 1000 ≤ q := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 1000)).2
    simpa [q, n] using hnMillion
  have hq : 0 < q := by omega
  have hscale_lo : 1000 * q ≤ n := by
    simpa [q, Nat.mul_comm] using Nat.div_mul_le_self n 1000
  have hmod : n % 1000 < 1000 := Nat.mod_lt _ (by norm_num)
  have hdecomp : n % 1000 + 1000 * q = n := by
    simpa [q] using Nat.mod_add_div n 1000
  have hscale_hi : n ≤ 1001 * q := by omega
  have hlight := hnLight W G (by simpa [n] using hnLight')
  change ((lightTriples G M).card : ℝ) < eps * (n : ℝ) ^ 2 at hlight
  have hheavyNat := heavyEdges_card_mul_le G M
  change (heavyEdges G M).card * M ≤ 2 * n ^ 2 at hheavyNat
  have hheavyR : (heavyEdges G M).card * (M : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
    exact_mod_cast hheavyNat
  have hpathNat := lightPathEdges_card_le_two_mul_lightTriples G M
  have hpathR : ((lightPathEdges G M).card : ℝ) ≤
      2 * (lightTriples G M).card := by exact_mod_cast hpathNat
  have hnR : (n : ℝ) ≤ 1001 * q := by exact_mod_cast hscale_hi
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnSquare : (n : ℝ) ^ 2 ≤ (1001 * (q : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg ((1001 : ℝ) * q - n)]
  have hheavySmall : ((heavyEdges G M).card : ℝ) < (q : ℝ) ^ 2 / 16 := by
    dsimp [M] at hheavyR
    nlinarith
  have hpathSmall : ((lightPathEdges G M).card : ℝ) < (q : ℝ) ^ 2 / 16 := by
    dsimp [eps] at hlight
    nlinarith
  let R := heavyEdges G M ∪ lightPathEdges G M
  have hRcard : R.card ≤ (heavyEdges G M).card + (lightPathEdges G M).card :=
    Finset.card_union_le _ _
  have hRsmall : (R.card : ℝ) < (q : ℝ) ^ 2 / 4 := by
    have hRcardR : (R.card : ℝ) ≤
        (heavyEdges G M).card + (lightPathEdges G M).card := by exact_mod_cast hRcard
    nlinarith
  let H := prunedGraph G M
  have hHG : H ≤ G := by simpa [H] using prunedGraph_le G M
  have hII : ∀ x z y, IsTypeII G x z y → ¬(H.Adj x z ∧ H.Adj z y) := by
    intro x z y h
    simpa [H] using prunedGraph_no_typeII G M x z y h
  by_contra hnot
  have hcounter : n ^ 2 / 4 < G.edgeFinset.card := by
    simpa [n] using Nat.lt_of_not_ge hnot
  have hGreal : (n : ℝ) ^ 2 / 4 < (G.edgeFinset.card : ℝ) := by
    have hsucc : n ^ 2 / 4 + 1 ≤ G.edgeFinset.card := by omega
    have hsuccR : (((n ^ 2 / 4 + 1 : ℕ) : ℝ)) ≤ G.edgeFinset.card := by
      exact_mod_cast hsucc
    exact (square_div_four_lt_succ_nat n).trans_le hsuccR
  have hRsub : R ⊆ G.edgeFinset := by
    intro e he
    rcases Finset.mem_union.mp he with hh | hl
    · exact (Finset.mem_filter.mp hh).1
    · exact (Finset.mem_filter.mp hl).1
  have hHedges : H.edgeFinset = G.edgeFinset \ R := by
    ext e
    rw [SimpleGraph.mem_edgeFinset, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
    simp [H, R, prunedGraph, SimpleGraph.deleteEdges_adj]
  have hHcard : H.edgeFinset.card = G.edgeFinset.card - R.card := by
    rw [hHedges, Finset.card_sdiff_of_subset hRsub]
  have hRle : R.card ≤ G.edgeFinset.card := Finset.card_le_card hRsub
  have hHreal : (H.edgeFinset.card : ℝ) =
      (G.edgeFinset.card : ℝ) - R.card := by
    rw [hHcard, Nat.cast_sub hRle]
  have hdense : (((n : ℝ) ^ 2 - q ^ 2) / 4) < (H.edgeFinset.card : ℝ) := by
    rw [hHreal]
    nlinarith
  exact hnot (exact_bound_of_dense_pruned (G := G) hHG hG hII hq
    (by simpa [n] using hscale_lo) (by simpa [n] using hscale_hi)
    (by simpa [n] using hdense))

end Final

end Erdos742

#print axioms Erdos742.erdos_742

alias _root_.Erdos742.furedi_bound := _root_.Erdos742.erdos_742
