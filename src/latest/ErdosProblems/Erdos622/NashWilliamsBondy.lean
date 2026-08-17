/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos622.LongestCycle
import ErdosProblems.Erdos622.ChvatalErdos
import ErdosProblems.Erdos58.Menger

/-!
# The Nash--Williams--Bondy alternative

This file proves the finite form of the theorem of Nash--Williams used in
the Dirac-stability argument.  If a graph of order `n > 3` has minimum
degree at least `k`, where `3 * k > n + 2`, then it is Hamiltonian, is not
two-connected, or contains an independent set of `k + 1` vertices.

The proof is Bondy's constructive proof of the Nash--Williams theorem.  Its
central assertion is that, at this degree scale, a cycle whose exterior
contains an edge can be enlarged.  For an exterior ear with two internal
vertices, the degrees of three selected vertices are split among the two
arcs of the cycle and its exterior.  One of the three regions has more
incidences than available vertices; a shifted-neighbour collision gives one
of the standard cycle splices.  A longest cycle therefore has independent
exterior.  Shifting the neighbours of one exterior vertex around the cycle
then gives the required independent set.

The separation predicate is kept local so this file stays below
`KSSStability` in the import graph.  It is definitionally the same witness
used there.
-/

open Finset Set
open scoped SimpleGraph

namespace Erdos622
namespace NashWilliamsBondy

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Deleting one vertex leaves two vertices in distinct components. -/
def IsCutVertexWitness (G : SimpleGraph V) (c : V) : Prop :=
  ∃ x y : {v : V // v ≠ c},
    ¬ (G.induce {v : V | v ≠ c}).Reachable x y

/-- The graph is disconnected, or has a cut vertex. -/
def HasSeparationWitness (G : SimpleGraph V) : Prop :=
  ¬ G.Preconnected ∨ ∃ c : V, IsCutVertexWitness G c

/-- Exact finite independent-set witness, stated without importing the KSS
assembly file. -/
def HasIndependentSetAt (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ A : Finset V, A.card = k ∧ G.IsIndepSet (A : Set V)

/-! ## From the finite separation witness to ordinary two-connectivity -/

private lemma connected_of_not_separated
    (hCard : 3 ≤ Fintype.card V)
    (hsep : ¬ HasSeparationWitness G) : G.Connected := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hpre : G.Preconnected := by
    by_contra h
    exact hsep (Or.inl h)
  exact ⟨hpre⟩

private lemma delete_connected_of_not_separated
    (hCard : 3 ≤ Fintype.card V)
    (hsep : ¬ HasSeparationWitness G) (c : V) :
    (G.induce ({c}ᶜ : Set V)).Connected := by
  let H : SimpleGraph {v : V // v ≠ c} := G.induce {v : V | v ≠ c}
  have hpre : H.Preconnected := by
    intro x y
    by_contra hxy
    apply hsep
    exact Or.inr ⟨c, x, y, hxy⟩
  have hcard : 0 < Fintype.card {v : V // v ≠ c} := by
    rw [Fintype.card_subtype_compl]
    have heq : Fintype.card {v : V // v = c} = 1 := Fintype.card_unique
    omega
  letI : Nonempty {v : V // v ≠ c} := Fintype.card_pos_iff.mp hcard
  have hH : H.Connected := ⟨hpre⟩
  let e : H ≃g G.induce ({c}ᶜ : Set V) :=
    { toFun := fun x ↦ ⟨x, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.2⟩
      invFun := fun x ↦ ⟨x, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.2⟩
      left_inv := fun x ↦ Subtype.ext rfl
      right_inv := fun x ↦ Subtype.ext rfl
      map_rel_iff' := by simp [H] }
  exact e.connected_iff.mp hH

/-- Absence of the exported separation witness is precisely enough for the
standard finite two-connected interface. -/
theorem twoConnected_of_not_separated (hCard : 3 ≤ Fintype.card V)
    (hsep : ¬ HasSeparationWitness G) : Erdos58.TwoConnected G := by
  refine ⟨hCard, connected_of_not_separated hCard hsep, ?_⟩
  exact delete_connected_of_not_separated hCard hsep

/-! ## Finite incidence lemmas -/

/-- Three lower degree bounds force an excess in one of three regions whose
capacities add to `n + 1`. -/
lemma degree_three_region {k n u d w : ℕ}
    (hsum : u + d + w = n + 1)
    {au ad aw bu bd bw qu qd qw : ℕ}
    (ha : k ≤ au + ad + aw) (hb : k ≤ bu + bd + bw)
    (hq : k ≤ qu + qd + qw) (hlarge : n + 1 < 3 * k) :
    u < au + bu + qu ∨ d < ad + bd + qd ∨ w < aw + bw + qw := by
  by_contra h
  push_neg at h
  omega

/-- The shifted pigeonhole argument on the first cycle arc. -/
lemma first_arc_collision {t : ℕ} {A B : Finset (Fin t)}
    (hcard : t < A.card + B.card) : ∃ i, i ∈ A ∧ i ∈ B := by
  by_contra h
  push_neg at h
  have hd : Disjoint A B := Finset.disjoint_left.mpr fun i hiA hiB ↦ h i hiA hiB
  have hle : A.card + B.card ≤ t := by
    rw [← Finset.card_union_of_disjoint hd]
    simpa using Finset.card_le_card (Finset.subset_univ (A ∪ B))
  omega

/-- The three shifted-neighbour collisions on the second cycle arc.  The
last point is excluded from `B` (in the application it represents the
vertex `b` itself), while shifting `Q` backwards can lose only its first
point. -/
lemma second_arc_collision {L : ℕ} {A B Q : Finset ℕ}
    (hA : A ⊆ Finset.range L) (hB : B ⊆ Finset.range L)
    (hQ : Q ⊆ Finset.range L)
    (hBlast : ∀ j ∈ B, j + 1 < L)
    (hcard : L + 1 < A.card + B.card + Q.card) :
    (∃ j, j ∈ B ∧ j + 1 ∈ A) ∨
      (∃ j, j ∈ A ∧ j + 1 ∈ Q) ∨
      (∃ j, j ∈ B ∧ j + 2 ∈ Q) := by
  let Bs : Finset ℕ := B.image Nat.succ
  let Qp : Finset ℕ := (Q.erase 0).image Nat.pred
  have hBsCard : Bs.card = B.card := by
    exact Finset.card_image_of_injective B Nat.succ_injective
  have hQpCard : Q.card ≤ Qp.card + 1 := by
    have himage : Qp.card = (Q.erase 0).card := by
      rw [Finset.card_image_iff]
      intro x hx y hy hxy
      have hx0 : x ≠ 0 := by
        exact fun h ↦ (Finset.mem_erase.mp hx).1 h
      have hy0 : y ≠ 0 := by
        exact fun h ↦ (Finset.mem_erase.mp hy).1 h
      have hxpos : 0 < x := Nat.pos_of_ne_zero hx0
      have hypos : 0 < y := Nat.pos_of_ne_zero hy0
      rw [← Nat.succ_pred_eq_of_pos hxpos, ← Nat.succ_pred_eq_of_pos hypos, hxy]
    rw [himage]
    by_cases h0 : 0 ∈ Q
    · rw [Finset.card_erase_add_one h0]
    · simp [Finset.erase_eq_of_notMem h0]
  have hBsSub : Bs ⊆ Finset.range L := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hBlast i hi)
  have hQpSub : Qp ⊆ Finset.range L := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hiQ : i ∈ Q := (Finset.mem_erase.mp hi).2
    have hiL : i < L := Finset.mem_range.mp (hQ hiQ)
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    exact Finset.mem_range.mpr (lt_trans (Nat.pred_lt hi0) hiL)
  by_contra h
  push_neg at h
  rcases h with ⟨hAB, hAQ, hBQ⟩
  have hA_Bs : Disjoint A Bs := by
    rw [Finset.disjoint_left]
    intro j hjA hjBs
    obtain ⟨i, hiB, hij⟩ := Finset.mem_image.mp hjBs
    subst j
    apply hAB i hiB
    simpa using hjA
  have hA_Qp : Disjoint A Qp := by
    rw [Finset.disjoint_left]
    intro j hjA hjQp
    obtain ⟨i, hiQ, hij⟩ := Finset.mem_image.mp hjQp
    subst j
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hiQ).1
    have hisucc : i.pred + 1 = i := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hi0)
    apply hAQ i.pred
    · exact hjA
    · simpa only [hisucc] using (Finset.mem_erase.mp hiQ).2
  have hBs_Qp : Disjoint Bs Qp := by
    rw [Finset.disjoint_left]
    intro j hjBs hjQp
    obtain ⟨b, hbB, hbj⟩ := Finset.mem_image.mp hjBs
    obtain ⟨q, hqQ, hqj⟩ := Finset.mem_image.mp hjQp
    have hq0 : q ≠ 0 := (Finset.mem_erase.mp hqQ).1
    have hqsucc : q.pred + 1 = q := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hq0)
    have hqb : b + 2 = q := by omega
    exact hBQ b hbB (hqb ▸ (Finset.mem_erase.mp hqQ).2)
  have hunionDisj : Disjoint (A ∪ Bs) Qp :=
    Finset.disjoint_union_left.mpr ⟨hA_Qp, hBs_Qp⟩
  have hUnionSub : A ∪ Bs ∪ Qp ⊆ Finset.range L := by
    exact Finset.union_subset (Finset.union_subset hA hBsSub) hQpSub
  have hle := Finset.card_le_card hUnionSub
  rw [Finset.card_union_of_disjoint hunionDisj,
    Finset.card_union_of_disjoint hA_Bs, hBsCard, Finset.card_range] at hle
  omega

/-! ## Exterior ears -/

/-- A simple path of length at least three joining two cycle vertices and
otherwise avoiding the cycle.  Storing the support condition with its two
endpoint exceptions is substantially more convenient than repeatedly
unfolding `tail.dropLast`. -/
structure ExteriorEar {z : V} (c : G.Walk z z) (x y : V) where
  path : G.Walk x y
  isPath : path.IsPath
  three_le : 3 ≤ path.length
  outside : ∀ w ∈ path.support, w = x ∨ w = y ∨ w ∉ c.support.toFinset

private lemma endpoint_not_mem_take_two
    {z x y : V} {q : G.Walk z z} (E : ExteriorEar q x y) :
    y ∉ (E.path.take 2).support := by
  intro hy
  obtain ⟨i, hi, hile⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
  have hitwo : i ≤ 2 := hile.trans (by simp)
  have hilePath : i ≤ E.path.length := hile.trans (by simp)
  have hi' : E.path.getVert i = y := by
    simpa [SimpleGraph.Walk.take_getVert, Nat.min_eq_right hitwo] using hi
  have hilength : i = E.path.length :=
    (E.isPath.getVert_eq_end_iff hilePath).mp hi'
  have hthree : 3 ≤ E.path.length := E.three_le
  omega

private lemma cycle_index_ne_base
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {i : ℕ} (hi0 : 0 < i) (hilength : i < q.length) :
    q.getVert i ≠ q.getVert 0 := by
  intro h
  have hz : q.getVert 0 = z := q.getVert_zero
  have hi : q.getVert i = z := h.trans hz
  rw [hq.getVert_endpoint_iff (by omega)] at hi
  omega

private lemma cycle_index_inj
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {i j : ℕ} (hi : i < q.length) (hj : j < q.length)
    (hij : i ≠ j) : q.getVert i ≠ q.getVert j := by
  intro h
  apply hij
  exact hq.getVert_injOn'
    (by simp only [Set.mem_setOf_eq]; omega)
    (by simp only [Set.mem_setOf_eq]; omega) h

private lemma shorter_exteriorEar_of_adj_getVert_two
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {i j : ℕ} (hi0 : 0 < i) (hij : i < j) (hjlen : j < q.length)
    (E : ExteriorEar q (q.getVert 0) (q.getVert j))
    (hadj : G.Adj (E.path.getVert 2) (q.getVert i)) :
    Nonempty (ExteriorEar q (q.getVert 0) (q.getVert i)) := by
  have hilen : i < q.length := hij.trans hjlen
  have hiBase : q.getVert i ≠ q.getVert 0 :=
    cycle_index_ne_base hq hi0 hilen
  have hiEnd : q.getVert i ≠ q.getVert j :=
    cycle_index_inj hq hilen hjlen (by omega)
  have hnotPrefix : q.getVert i ∉ (E.path.take 2).support := by
    intro hiPrefix
    have hiPath : q.getVert i ∈ E.path.support := by
      rw [SimpleGraph.Walk.support_take] at hiPrefix
      exact List.mem_of_mem_take hiPrefix
    rcases E.outside _ hiPath with hi | hi | hiOutside
    · exact hiBase hi
    · exact hiEnd hi
    · exact hiOutside (List.mem_toFinset.mpr (q.getVert_mem_support i))
  let r : G.Walk (q.getVert 0) (q.getVert i) :=
    (E.path.take 2).concat hadj
  have hrPath : r.IsPath := (E.isPath.take 2).concat hnotPrefix hadj
  have hthree : 3 ≤ E.path.length := E.three_le
  have hrlen : r.length = 3 := by
    rw [SimpleGraph.Walk.length_concat, SimpleGraph.Walk.take_length,
      Nat.min_eq_left (by omega)]
  have hrOutside : ∀ w ∈ r.support,
      w = q.getVert 0 ∨ w = q.getVert i ∨ w ∉ q.support.toFinset := by
    intro w hw
    simp only [r, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at hw
    rcases hw with hw | rfl
    · have hwPath : w ∈ E.path.support := by
        rw [SimpleGraph.Walk.support_take] at hw
        exact List.mem_of_mem_take hw
      rcases E.outside w hwPath with hbase | hend | hout
      · exact Or.inl hbase
      · subst w
        exact (endpoint_not_mem_take_two E hw).elim
      · exact Or.inr (Or.inr hout)
    · exact Or.inr (Or.inl rfl)
  exact ⟨{
    path := r
    isPath := hrPath
    three_le := by omega
    outside := hrOutside
  }⟩

/-- Select an exterior ear whose positive terminal cycle index is least.
Then the third ear vertex has no neighbour at an earlier positive cycle
index. -/
theorem exists_minimal_exteriorEar
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    (hex : ∃ j : ℕ, 0 < j ∧ j < q.length ∧
      Nonempty (ExteriorEar q (q.getVert 0) (q.getVert j))) :
    ∃ j : ℕ, ∃ E : ExteriorEar q (q.getVert 0) (q.getVert j),
      0 < j ∧ j < q.length ∧
      ∀ i : ℕ, 0 < i → i < j →
        ¬ G.Adj (E.path.getVert 2) (q.getVert i) := by
  let I : Finset ℕ := (Finset.range q.length).filter fun j ↦
    0 < j ∧ Nonempty (ExteriorEar q (q.getVert 0) (q.getVert j))
  have hI : I.Nonempty := by
    obtain ⟨j, hj0, hjlen, hjE⟩ := hex
    exact ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hjlen, hj0, hjE⟩⟩
  let j : ℕ := I.min' hI
  have hjI : j ∈ I := Finset.min'_mem I hI
  have hjdata := Finset.mem_filter.mp hjI
  have hjlen : j < q.length := Finset.mem_range.mp hjdata.1
  have hj0 : 0 < j := hjdata.2.1
  let E : ExteriorEar q (q.getVert 0) (q.getVert j) :=
    Classical.choice hjdata.2.2
  refine ⟨j, E, hj0, hjlen, ?_⟩
  intro i hi0 hij hadj
  have hiEar : Nonempty (ExteriorEar q (q.getVert 0) (q.getVert i)) :=
    shorter_exteriorEar_of_adj_getVert_two hq hi0 hij hjlen E hadj
  have hiI : i ∈ I := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (hij.trans hjlen), hi0, hiEar⟩
  have hji : j ≤ i := Finset.min'_le I i hiI
  omega

private lemma isPath_append_of_inter_eq_end
    {a b c : V} {p : G.Walk a b} {q : G.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x : V, x ∈ p.support → x ∈ q.support → x = b) :
    (p.append q).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  rw [List.disjoint_left]
  intro x hxp hxq
  have hxq' : x ∈ q.support := List.tail_subset _ hxq
  have hxb : x = b := hinter x hxp hxq'
  subst x
  have hn := hq.support_nodup
  rw [← q.cons_tail_support, List.nodup_cons] at hn
  exact hn.1 hxq

private lemma path_support_eq_endpoints_or_interior
    {a b w : V} {p : G.Walk a b} (hp : p.IsPath)
    (hw : w ∈ p.support) :
    w = a ∨ w = b ∨ w ∈ p.support.tail.dropLast := by
  by_cases hwa : w = a
  · exact Or.inl hwa
  by_cases hwb : w = b
  · exact Or.inr (Or.inl hwb)
  right; right
  have htail : w ∈ p.support.tail := by
    rw [← p.cons_tail_support] at hw
    exact (List.mem_cons.mp hw).resolve_left hwa
  exact List.mem_dropLast_of_mem_of_ne_getLast htail (by
    simpa [SimpleGraph.Walk.getLast_support] using hwb)

omit [Fintype V] [DecidableRel G.Adj] in
private lemma cycleCarrier_two_le {z : V} {c : G.Walk z z}
    (hc : c.IsCycle) : 2 ≤ c.support.toFinset.card := by
  have hcard : c.support.toFinset.card = c.length := by
    have hz : z ∈ c.support.tail := c.end_mem_tail_support hc.not_nil
    rw [← c.cons_tail_support, List.toFinset_cons,
      Finset.insert_eq_of_mem (List.mem_toFinset.mpr hz),
      List.toFinset_card_of_nodup hc.support_nodup]
    rw [List.length_tail, c.length_support]
    omega
  rw [hcard]
  exact hc.three_le_length.trans' (by omega)

/-- Two-connectivity supplies an exterior ear through any prescribed edge
outside a cycle.  Apply the checked two-set Menger theorem between the cycle
carrier and the two endpoints of the edge, and join the two disjoint linkage
paths by that edge. -/
theorem exists_exteriorEar_of_external_edge
    (hTwo : Erdos58.TwoConnected G) {z : V} {c : G.Walk z z}
    (hc : c.IsCycle) {v w : V} (hvw : G.Adj v w)
    (hv : v ∉ c.support.toFinset) (hw : w ∉ c.support.toFinset) :
    ∃ x y : V, x ∈ c.support.toFinset ∧ y ∈ c.support.toFinset ∧
      x ≠ y ∧ Nonempty (ExteriorEar c x y) := by
  let C : Set V := (c.support.toFinset : Set V)
  let B : Set V := {v, w}
  have hCB : Disjoint C B := by
    rw [Set.disjoint_left]
    intro a ha hab
    simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff] at hab
    rcases hab with rfl | rfl
    · exact hv ha
    · exact hw ha
  have hBcard : B.ncard = 2 := by
    exact Set.ncard_pair hvw.ne
  obtain ⟨(L : Erdos58.TwoLinkage G C B)⟩ :=
    hTwo.exists_twoLinkage (A := C) (B := B)
    (by
      change 2 ≤ ((c.support.toFinset : Finset V) : Set V).ncard
      rw [Set.ncard_coe_finset]
      exact cycleCarrier_two_le hc)
    (by omega : 2 ≤ B.ncard)
  have hb : G.Adj L.b₁ L.b₂ := by
    have hb₁ : L.b₁ = v ∨ L.b₁ = w := by simpa [B] using L.b₁_mem
    have hb₂ : L.b₂ = v ∨ L.b₂ = w := by simpa [B] using L.b₂_mem
    rcases hb₁ with hb₁ | hb₁ <;> rcases hb₂ with hb₂ | hb₂
    · exact (L.b_ne (hb₁.trans hb₂.symm)).elim
    · simpa [hb₁, hb₂] using hvw
    · simpa [hb₁, hb₂] using hvw.symm
    · exact (L.b_ne (hb₁.trans hb₂.symm)).elim
  let pe : G.Walk L.a₁ L.b₂ := L.p.concat hb
  have hpe : pe.IsPath := L.p_isPath.concat
    (fun hb₂p ↦ L.disjoint_support hb₂p L.q.end_mem_support) hb
  let r : G.Walk L.a₁ L.a₂ := pe.append L.q.reverse
  have hr : r.IsPath := by
    apply isPath_append_of_inter_eq_end hpe L.q_isPath.reverse
    intro a haPe haQ
    have haQ' : a ∈ L.q.support := by simpa using haQ
    simp only [pe, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at haPe
    rcases haPe with haP | rfl
    · exact (L.disjoint_support haP haQ').elim
    · rfl
  have hplen : 0 < L.p.length := L.p_nonempty hCB
  have hqlen : 0 < L.q.length := L.q_nonempty hCB
  have hrlen : 3 ≤ r.length := by
    simp only [r, pe, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_reverse]
    omega
  have hpOutside : ∀ a ∈ L.p.support,
      a = L.a₁ ∨ a = L.b₁ ∨ a ∉ C := by
    intro a ha
    rcases path_support_eq_endpoints_or_interior L.p_isPath ha with rfl | rfl | haInt
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr fun haC ↦ L.p_interior a haInt (Or.inl haC))
  have hqOutside : ∀ a ∈ L.q.support,
      a = L.a₂ ∨ a = L.b₂ ∨ a ∉ C := by
    intro a ha
    rcases path_support_eq_endpoints_or_interior L.q_isPath ha with rfl | rfl | haInt
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr fun haC ↦ L.q_interior a haInt (Or.inl haC))
  have hrOutside : ∀ a ∈ r.support,
      a = L.a₁ ∨ a = L.a₂ ∨ a ∉ c.support.toFinset := by
    intro a ha
    simp only [r, pe, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at ha
    rcases ha with (haP | rfl) | haQ
    · rcases hpOutside a haP with rfl | rfl | haC
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (fun hbC ↦ Set.disjoint_left.mp hCB hbC L.b₁_mem))
      · exact Or.inr (Or.inr haC)
    · exact Or.inr (Or.inr (fun hbC ↦ Set.disjoint_left.mp hCB hbC L.b₂_mem))
    · rcases hqOutside a haQ with rfl | rfl | haC
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (fun hbC ↦ Set.disjoint_left.mp hCB hbC L.b₂_mem))
      · exact Or.inr (Or.inr haC)
  refine ⟨L.a₁, L.a₂, L.a₁_mem, L.a₂_mem, L.a_ne, ⟨?_⟩⟩
  exact { path := r, isPath := hr, three_le := hrlen, outside := hrOutside }

/-- Rotate the cycle to the first end of an exterior ear and then minimize
the positive index of its other end.  This is the normalized configuration
used in the incidence argument. -/
theorem exists_normalized_exteriorEar_of_external_edge
    (hTwo : Erdos58.TwoConnected G) {z : V} {c : G.Walk z z}
    (hc : c.IsCycle) {v w : V} (hvw : G.Adj v w)
    (hv : v ∉ c.support.toFinset) (hw : w ∉ c.support.toFinset) :
    ∃ (x : V) (q : G.Walk x x) (j : ℕ)
      (E : ExteriorEar q (q.getVert 0) (q.getVert j)),
      q.IsCycle ∧ q.length = c.length ∧
      q.support.toFinset = c.support.toFinset ∧
      0 < j ∧ j < q.length ∧
      ∀ i : ℕ, 0 < i → i < j →
        ¬ G.Adj (E.path.getVert 2) (q.getVert i) := by
  obtain ⟨x, y, hxC, hyC, hxy, ⟨E₀⟩⟩ :=
    exists_exteriorEar_of_external_edge hTwo hc hvw hv hw
  have hxSupport : x ∈ c.support := List.mem_toFinset.mp hxC
  let q : G.Walk x x := c.rotate x hxSupport
  have hq : q.IsCycle := hc.rotate hxSupport
  have hyq : y ∈ q.support := by
    exact (c.mem_support_rotate_iff x hxSupport).mpr (List.mem_toFinset.mp hyC)
  obtain ⟨j₀, hj₀, hj₀le⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hyq
  have hj₀lt : j₀ < q.length := by
    by_contra h
    have hjlen : j₀ = q.length := by omega
    have : y = x := by
      rw [← hj₀, hjlen, q.getVert_length]
    exact hxy this.symm
  have hj₀pos : 0 < j₀ := by
    by_contra h
    have hjzero : j₀ = 0 := by omega
    have : y = x := by
      rw [← hj₀, hjzero, q.getVert_zero]
    exact hxy this.symm
  let p₀ : G.Walk (q.getVert 0) (q.getVert j₀) :=
    E₀.path.copy q.getVert_zero.symm hj₀.symm
  have hp₀ : p₀.IsPath := by
    simpa only [p₀, SimpleGraph.Walk.isPath_copy] using E₀.isPath
  have hp₀len : p₀.length = E₀.path.length := by
    exact SimpleGraph.Walk.length_copy E₀.path _ _
  have hp₀outside : ∀ a ∈ p₀.support,
      a = q.getVert 0 ∨ a = q.getVert j₀ ∨ a ∉ q.support.toFinset := by
    intro a ha
    have haE : a ∈ E₀.path.support := by
      simpa only [p₀, SimpleGraph.Walk.support_copy] using ha
    rcases E₀.outside a haE with hax | hay | haout
    · exact Or.inl (hax.trans q.getVert_zero.symm)
    · exact Or.inr (Or.inl (hay.trans hj₀.symm))
    · right; right
      intro haq
      apply haout
      apply List.mem_toFinset.mpr
      exact (c.mem_support_rotate_iff x hxSupport).mp
        (List.mem_toFinset.mp haq)
  let E₁ : ExteriorEar q (q.getVert 0) (q.getVert j₀) := {
    path := p₀
    isPath := hp₀
    three_le := by rw [hp₀len]; exact E₀.three_le
    outside := hp₀outside
  }
  obtain ⟨j, E, hjpos, hjlt, hminimal⟩ :=
    exists_minimal_exteriorEar hq ⟨j₀, hj₀pos, hj₀lt, ⟨E₁⟩⟩
  refine ⟨x, q, j, E, hq, by simp [q], ?_, hjpos, hjlt, hminimal⟩
  ext a
  simp only [List.mem_toFinset, q]
  exact c.mem_support_rotate_iff x hxSupport

/-! ## Indexed arcs of a normalized cycle -/

/-- The forward subpath of a cycle between two indices before its repeated
endpoint. -/
private def cycleArc {z : V} (q : G.Walk z z) (i j : ℕ)
    (hij : i ≤ j) (hj : j < q.length) :
    G.Walk (q.getVert i) (q.getVert j) :=
  ((q.take j).drop i).copy
    (by simp [SimpleGraph.Walk.drop_getVert, SimpleGraph.Walk.take_getVert,
      Nat.min_eq_right hij])
    (by
      simp [SimpleGraph.Walk.take_getVert, SimpleGraph.Walk.drop_getVert,
        SimpleGraph.Walk.take_length, Nat.min_eq_left hj.le, hij])

private lemma cycleArc_isPath {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {i j : ℕ} (hij : i ≤ j) (hj : j < q.length) :
    (cycleArc q i j hij hj).IsPath := by
  simp only [cycleArc, SimpleGraph.Walk.isPath_copy]
  exact (hq.isPath_take hj).drop i

private lemma cycleArc_length {z : V} {q : G.Walk z z}
    {i j : ℕ} (hij : i ≤ j) (hj : j < q.length) :
    (cycleArc q i j hij hj).length = j - i := by
  simp [cycleArc, SimpleGraph.Walk.drop_length,
    SimpleGraph.Walk.take_length, Nat.min_eq_left hj.le]

private lemma mem_cycleArc_index {z : V} {q : G.Walk z z}
    {i j : ℕ} (hij : i ≤ j) (hj : j < q.length)
    {a : V} (ha : a ∈ (cycleArc q i j hij hj).support) :
    ∃ k : ℕ, i ≤ k ∧ k ≤ j ∧ q.getVert k = a := by
  have ha' : a ∈ ((q.take j).drop i).support := by
    simpa only [cycleArc, SimpleGraph.Walk.support_copy] using ha
  obtain ⟨t, ht, htlen⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ha'
  have hitle : i + t ≤ j := by
    simp only [SimpleGraph.Walk.drop_length,
      SimpleGraph.Walk.take_length, Nat.min_eq_left hj.le] at htlen
    omega
  refine ⟨i + t, Nat.le_add_right i t, hitle, ?_⟩
  rw [SimpleGraph.Walk.drop_getVert, SimpleGraph.Walk.take_getVert,
    Nat.min_eq_right hitle] at ht
  exact ht

private lemma getVert_mem_cycleArc {z : V} {q : G.Walk z z}
    {i j k : ℕ} (hij : i ≤ j) (hj : j < q.length)
    (hik : i ≤ k) (hkj : k ≤ j) :
    q.getVert k ∈ (cycleArc q i j hij hj).support := by
  let t := k - i
  have htlen : t ≤ (cycleArc q i j hij hj).length := by
    rw [cycleArc_length hij hj]
    omega
  have hmem := (cycleArc q i j hij hj).getVert_mem_support t
  have hget : (cycleArc q i j hij hj).getVert t = q.getVert k := by
    simp only [cycleArc, SimpleGraph.Walk.getVert_copy,
      SimpleGraph.Walk.drop_getVert, SimpleGraph.Walk.take_getVert]
    rw [Nat.min_eq_right]
    · congr 1
      omega
    · omega
  exact hget ▸ hmem

private lemma cycle_index_eq_of_getVert_eq {z : V} {q : G.Walk z z}
    (hq : q.IsCycle) {i j : ℕ} (hi : i < q.length) (hj : j < q.length)
    (h : q.getVert i = q.getVert j) : i = j := by
  exact hq.getVert_injOn'
    (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega) h

private lemma exteriorEar_meets_cycle_only_ends
    {z : V} {q : G.Walk z z} {x y a : V}
    (E : ExteriorEar q x y) (haE : a ∈ E.path.support)
    (haq : a ∈ q.support) : a = x ∨ a = y := by
  rcases E.outside a haE with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (h (List.mem_toFinset.mpr haq)).elim

/-- The splice forced by a shifted collision on the first cycle arc. -/
private lemma longer_cycle_of_first_arc_collision
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j p : ℕ} (hj0 : 0 < j) (hj : j < q.length)
    (hp : p + 1 < j)
    (E : ExteriorEar q (q.getVert 0) (q.getVert j))
    (ha : G.Adj (q.getVert (j - 1)) (q.getVert p))
    (hb : G.Adj (q.getVert (q.length - 1)) (q.getVert (p + 1))) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ q.length < c.length := by
  have hm0 : 0 < q.length := by omega
  have hjm : j ≤ q.length - 1 := by omega
  have hpj : p + 1 ≤ j - 1 := by omega
  let d := cycleArc q j (q.length - 1) hjm (by omega)
  let mid := cycleArc q (p + 1) (j - 1) hpj (by omega)
  let pre := cycleArc q 0 p (by omega) (by omega)
  have hdPath : d.IsPath := cycleArc_isPath hq hjm (by omega)
  have hmidPath : mid.IsPath := cycleArc_isPath hq hpj (by omega)
  have hprePath : pre.IsPath := cycleArc_isPath hq (by omega) (by omega)
  have hEdMeet : ∀ a : V,
      a ∈ E.path.support → a ∈ d.support → a = q.getVert j := by
    intro a haE had
    obtain ⟨k, hjk, hkm, hka⟩ := mem_cycleArc_index hjm (by omega) had
    rcases exteriorEar_meets_cycle_only_ends E haE
        (hka ▸ q.getVert_mem_support k) with h0 | hj'
    · have hk0 := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
          (hka.trans h0)
      omega
    · exact hj'
  let r₁ := E.path.append d
  have hr₁Path : r₁.IsPath :=
    isPath_append_of_inter_eq_end E.isPath hdPath hEdMeet
  have hnextNotR₁ : q.getVert (p + 1) ∉ r₁.support := by
    intro hmem
    rcases (SimpleGraph.Walk.mem_support_append_iff E.path d).mp hmem with he | hd
    · rcases exteriorEar_meets_cycle_only_ends E he
          (q.getVert_mem_support (p + 1)) with h0 | hj'
      · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
            h0
        omega
      · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hj'
        omega
    · obtain ⟨k, hjk, hkm, hk⟩ := mem_cycleArc_index hjm (by omega) hd
      have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
        hk
      omega
  let r₂ := r₁.concat hb
  have hr₂Path : r₂.IsPath := hr₁Path.concat hnextNotR₁ hb
  have hr₂midMeet : ∀ a : V,
      a ∈ r₂.support → a ∈ mid.support → a = q.getVert (p + 1) := by
    intro a har ham
    obtain ⟨k, hpk, hkj, hka⟩ := mem_cycleArc_index hpj (by omega) ham
    simp only [r₂, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at har
    rcases har with har | rfl
    · rcases (SimpleGraph.Walk.mem_support_append_iff E.path d).mp har with he | hd
      · rcases exteriorEar_meets_cycle_only_ends E he
            (hka ▸ q.getVert_mem_support k) with h0 | hj'
        · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
              (hka.trans h0)
          omega
        · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
              (hka.trans hj')
          omega
      · obtain ⟨l, hjl, hlm, hla⟩ := mem_cycleArc_index hjm (by omega) hd
        have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
          (hla.trans hka.symm)
        omega
    · exact rfl
  let r₃ := r₂.append mid
  have hr₃Path : r₃.IsPath :=
    isPath_append_of_inter_eq_end hr₂Path hmidPath hr₂midMeet
  by_cases hpzero : p = 0
  · subst p
    let e := ha.toWalk
    have hePath : e.IsPath := ha.isPath_toWalk
    have hdisj : r₃.support.tail.Disjoint e.support.tail := by
      rw [List.disjoint_left]
      intro a har hae
      have hae' : a = q.getVert 0 := by
        simpa [e, SimpleGraph.Adj.support_toWalk] using hae
      subst a
      have hn := hr₃Path.support_nodup
      rw [← r₃.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 har
    let c := r₃.append e
    have hc : c.IsCycle := hr₃Path.isCycle_append hePath hdisj
      (Or.inl (by
        simp only [r₃, r₂, r₁, SimpleGraph.Walk.length_append,
          SimpleGraph.Walk.length_concat]
        have := E.three_le
        omega))
    refine ⟨q.getVert 0, c, hc, ?_⟩
    simp only [c, r₃, r₂, r₁, e, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_concat, SimpleGraph.Adj.length_toWalk]
    rw [cycleArc_length hjm (by omega), cycleArc_length hpj (by omega)]
    have := E.three_le
    omega
  have hp0 : 0 < p := Nat.pos_of_ne_zero hpzero
  have hpNotR₃ : q.getVert p ∉ r₃.support := by
    intro hmem
    rcases (SimpleGraph.Walk.mem_support_append_iff r₂ mid).mp hmem with hr | hm
    · simp only [r₂, SimpleGraph.Walk.support_concat, List.mem_append,
        List.mem_singleton] at hr
      rcases hr with hr | hEq
      · rcases (SimpleGraph.Walk.mem_support_append_iff E.path d).mp hr with he | hd
        · rcases exteriorEar_meets_cycle_only_ends E he
              (q.getVert_mem_support p) with h0 | hj'
          · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
                h0
            omega
          · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hj'
            omega
        · obtain ⟨k, hjk, hkm, hk⟩ := mem_cycleArc_index hjm (by omega) hd
          have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hk
          omega
      · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hEq.symm
        omega
    · obtain ⟨k, hpk, hkj, hk⟩ := mem_cycleArc_index hpj (by omega) hm
      have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hk
      omega
  let r₄ := r₃.concat ha
  have hr₄Path : r₄.IsPath := hr₃Path.concat hpNotR₃ ha
  have hinter : ∀ a : V, a ∈ r₄.support → a ∈ pre.reverse.support →
      a = q.getVert 0 ∨ a = q.getVert p := by
    intro a har hap
    have hap' : a ∈ pre.support := by simpa using hap
    obtain ⟨k, hk0, hkp, hka⟩ := mem_cycleArc_index (by omega) (by omega) hap'
    simp only [r₄, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at har
    rcases har with har | rfl
    · rcases (SimpleGraph.Walk.mem_support_append_iff r₂ mid).mp har with hr | hm
      · simp only [r₂, SimpleGraph.Walk.support_concat, List.mem_append,
          List.mem_singleton] at hr
        rcases hr with hr | hEq
        · rcases (SimpleGraph.Walk.mem_support_append_iff E.path d).mp hr with he | hd
          · rcases exteriorEar_meets_cycle_only_ends E he
                (hka ▸ q.getVert_mem_support k) with h0 | hj'
            · exact Or.inl h0
            · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
                  (hka.trans hj')
              omega
          · obtain ⟨l, hjl, hlm, hla⟩ := mem_cycleArc_index hjm (by omega) hd
            have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
              (hla.trans hka.symm)
            omega
        · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
              (hEq.symm.trans hka.symm)
          omega
      · obtain ⟨l, hpl, hlj, hla⟩ := mem_cycleArc_index hpj (by omega) hm
        have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
          (hla.trans hka.symm)
        omega
    · exact Or.inr rfl
  have htails : r₄.support.tail.Disjoint pre.reverse.support.tail := by
    rw [List.disjoint_left]
    intro a har hap
    have har' := List.tail_subset _ har
    have hap' := List.tail_subset _ hap
    rcases hinter a har' hap' with h0 | hp'
    · have hn := hr₄Path.support_nodup
      rw [← r₄.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 (h0.symm ▸ har)
    · have hn := hprePath.reverse.support_nodup
      rw [← pre.reverse.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 (hp' ▸ hap)
  let c := r₄.append pre.reverse
  have hc : c.IsCycle := hr₄Path.isCycle_append hprePath.reverse htails
    (Or.inl (by
      simp only [r₄, r₃, r₂, r₁, SimpleGraph.Walk.length_concat,
        SimpleGraph.Walk.length_append]
      have := E.three_le
      omega))
  refine ⟨q.getVert 0, c, hc, ?_⟩
  simp only [c, r₄, r₃, r₂, r₁, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_reverse]
  rw [cycleArc_length hjm (by omega), cycleArc_length hpj (by omega),
    cycleArc_length (by omega) (by omega)]
  have := E.three_le
  omega

private lemma longer_cycle_of_second_arc_collision_a
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j i : ℕ} (hj0 : 0 < j) (hji : j ≤ i)
    (hi : i + 1 < q.length)
    (E : ExteriorEar q (q.getVert 0) (q.getVert j))
    (hb : G.Adj (q.getVert (q.length - 1)) (q.getVert i))
    (ha : G.Adj (q.getVert (j - 1)) (q.getVert (i + 1))) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ q.length < c.length := by
  have hj : j < q.length := by omega
  have hm0 : 0 < q.length := by omega
  have him : i + 1 ≤ q.length - 1 := by omega
  have hjm : j - 1 < q.length := by omega
  let mid := cycleArc q j i hji (by omega)
  let post := cycleArc q (i + 1) (q.length - 1) him (by omega)
  let pre := cycleArc q 0 (j - 1) (by omega) hjm
  have hmidPath : mid.IsPath := cycleArc_isPath hq hji (by omega)
  have hpostPath : post.IsPath := cycleArc_isPath hq him (by omega)
  have hprePath : pre.IsPath := cycleArc_isPath hq (by omega) hjm
  have hEmidMeet : ∀ a : V,
      a ∈ E.path.support → a ∈ mid.support → a = q.getVert j := by
    intro a haE ham
    obtain ⟨k, hjk, hki, hka⟩ := mem_cycleArc_index hji (by omega) ham
    rcases exteriorEar_meets_cycle_only_ends E haE
        (hka ▸ q.getVert_mem_support k) with h0 | hj'
    · have hk0 := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
          (hka.trans h0)
      omega
    · exact hj'
  let r1 := E.path.append mid
  have hr1Path : r1.IsPath :=
    isPath_append_of_inter_eq_end E.isPath hmidPath hEmidMeet
  have hbNotR1 : q.getVert (q.length - 1) ∉ r1.support := by
    intro hmem
    rcases (SimpleGraph.Walk.mem_support_append_iff E.path mid).mp hmem with he | hm
    · rcases exteriorEar_meets_cycle_only_ends E he
          (q.getVert_mem_support (q.length - 1)) with h0 | hj'
      · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) h0
        omega
      · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hj'
        omega
    · obtain ⟨k, hjk, hki, hk⟩ := mem_cycleArc_index hji (by omega) hm
      have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hk
      omega
  let r2 := r1.concat hb.symm
  have hr2Path : r2.IsPath := hr1Path.concat hbNotR1 hb.symm
  have hr2postMeet : ∀ a : V,
      a ∈ r2.support → a ∈ post.reverse.support →
        a = q.getVert (q.length - 1) := by
    intro a har hap
    have hap' : a ∈ post.support := by simpa using hap
    obtain ⟨k, hik, hkm, hka⟩ := mem_cycleArc_index him (by omega) hap'
    simp only [r2, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at har
    rcases har with har | rfl
    · rcases (SimpleGraph.Walk.mem_support_append_iff E.path mid).mp har with he | hd
      · rcases exteriorEar_meets_cycle_only_ends E he
            (hka ▸ q.getVert_mem_support k) with h0 | hj'
        · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
              (hka.trans h0)
          omega
        · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
              (hka.trans hj')
          omega
      · obtain ⟨l, hjl, hli, hla⟩ := mem_cycleArc_index hji (by omega) hd
        have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
          (hla.trans hka.symm)
        omega
    · exact rfl
  let r3 := r2.append post.reverse
  have hr3Path : r3.IsPath :=
    isPath_append_of_inter_eq_end hr2Path hpostPath.reverse hr2postMeet
  by_cases hjone : j = 1
  · subst j
    let e := ha.symm.toWalk
    have hePath : e.IsPath := ha.symm.isPath_toWalk
    have hdisj : r3.support.tail.Disjoint e.support.tail := by
      rw [List.disjoint_left]
      intro a har hae
      have hae' : a = q.getVert 0 := by
        simpa [e, SimpleGraph.Adj.support_toWalk] using hae
      subst a
      have hn := hr3Path.support_nodup
      rw [← r3.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 har
    let c := r3.append e
    have hc : c.IsCycle := hr3Path.isCycle_append hePath hdisj
      (Or.inl (by
        simp only [r3, r2, r1, SimpleGraph.Walk.length_append,
          SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_reverse]
        have := E.three_le
        omega))
    refine ⟨q.getVert 0, c, hc, ?_⟩
    simp only [c, r3, r2, r1, e, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_reverse,
      SimpleGraph.Adj.length_toWalk]
    rw [cycleArc_length hji (by omega), cycleArc_length him (by omega)]
    have := E.three_le
    omega
  have hjtwo : 2 ≤ j := by omega
  have haNotR3 : q.getVert (j - 1) ∉ r3.support := by
    intro hmem
    rcases (SimpleGraph.Walk.mem_support_append_iff r2 post.reverse).mp hmem with hr | hp
    · simp only [r2, SimpleGraph.Walk.support_concat, List.mem_append,
        List.mem_singleton] at hr
      rcases hr with hr | hEq
      · rcases (SimpleGraph.Walk.mem_support_append_iff E.path mid).mp hr with he | hm
        · rcases exteriorEar_meets_cycle_only_ends E he
              (q.getVert_mem_support (j - 1)) with h0 | hj'
          · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) h0
            omega
          · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hj'
            omega
        · obtain ⟨k, hjk, hki, hk⟩ := mem_cycleArc_index hji (by omega) hm
          have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hk
          omega
      · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hEq.symm
        omega
    · have hp' : q.getVert (j - 1) ∈ post.support := by simpa using hp
      obtain ⟨k, hik, hkm, hk⟩ := mem_cycleArc_index him (by omega) hp'
      have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hk
      omega
  let r4 := r3.concat ha.symm
  have hr4Path : r4.IsPath := hr3Path.concat haNotR3 ha.symm
  have hinter : ∀ a : V, a ∈ r4.support → a ∈ pre.reverse.support →
      a = q.getVert 0 ∨ a = q.getVert (j - 1) := by
    intro a har hap
    have hap' : a ∈ pre.support := by simpa using hap
    obtain ⟨k, hk0, hkj, hka⟩ := mem_cycleArc_index (by omega) hjm hap'
    simp only [r4, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at har
    rcases har with har | rfl
    · rcases (SimpleGraph.Walk.mem_support_append_iff r2 post.reverse).mp har with hr | hp
      · simp only [r2, SimpleGraph.Walk.support_concat, List.mem_append,
          List.mem_singleton] at hr
        rcases hr with hr | hEq
        · rcases (SimpleGraph.Walk.mem_support_append_iff E.path mid).mp hr with he | hm
          · rcases exteriorEar_meets_cycle_only_ends E he
                (hka ▸ q.getVert_mem_support k) with h0 | hj'
            · exact Or.inl h0
            · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
                  (hka.trans hj')
              omega
          · obtain ⟨l, hjl, hli, hla⟩ := mem_cycleArc_index hji (by omega) hm
            have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
              (hla.trans hka.symm)
            omega
        · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
              (hEq.symm.trans hka.symm)
          omega
      · have hp' : a ∈ post.support := by simpa using hp
        obtain ⟨l, hil, hlm, hla⟩ := mem_cycleArc_index him (by omega) hp'
        have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
          (hla.trans hka.symm)
        omega
    · exact Or.inr rfl
  have htails : r4.support.tail.Disjoint pre.reverse.support.tail := by
    rw [List.disjoint_left]
    intro a har hap
    have har' := List.tail_subset _ har
    have hap' := List.tail_subset _ hap
    rcases hinter a har' hap' with h0 | hj'
    · have hn := hr4Path.support_nodup
      rw [← r4.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 (h0.symm ▸ har)
    · have hn := hprePath.reverse.support_nodup
      rw [← pre.reverse.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 (hj' ▸ hap)
  let c := r4.append pre.reverse
  have hc : c.IsCycle := hr4Path.isCycle_append hprePath.reverse htails
    (Or.inl (by
      simp only [r4, r3, r2, r1, SimpleGraph.Walk.length_concat,
        SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
      have := E.three_le
      omega))
  refine ⟨q.getVert 0, c, hc, ?_⟩
  simp only [c, r4, r3, r2, r1, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_reverse]
  rw [cycleArc_length hji (by omega), cycleArc_length him (by omega),
    cycleArc_length (by omega) hjm]
  have := E.three_le
  omega

private lemma start_not_mem_drop_two
    {z : V} {q : G.Walk z z} {j : ℕ}
    (E : ExteriorEar q (q.getVert 0) (q.getVert j)) :
    q.getVert 0 ∉ (E.path.drop 2).support := by
  intro h
  obtain ⟨t, ht, htle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp h
  have hidx : 2 + t ≤ E.path.length := by
    rw [SimpleGraph.Walk.drop_length] at htle
    have := E.three_le
    omega
  rw [SimpleGraph.Walk.drop_getVert] at ht
  have := (E.isPath.getVert_eq_start_iff hidx).mp ht
  omega

private lemma drop_two_meets_cycle_only_end
    {z : V} {q : G.Walk z z} {j : ℕ}
    (E : ExteriorEar q (q.getVert 0) (q.getVert j))
    {a : V} (ha : a ∈ (E.path.drop 2).support) (haq : a ∈ q.support) :
    a = q.getVert j := by
  have haE : a ∈ E.path.support := by
    rw [SimpleGraph.Walk.drop_support_eq_support_drop_min] at ha
    exact List.mem_of_mem_drop ha
  rcases exteriorEar_meets_cycle_only_ends E haE haq with h0 | hj
  · subst a
    exact (start_not_mem_drop_two E ha).elim
  · exact hj

private lemma longer_cycle_of_second_arc_collision_b
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j i : ℕ} (hj0 : 0 < j) (hj : j < q.length)
    (hji : j ≤ i) (hi : i + 1 < q.length)
    (E : ExteriorEar q (q.getVert 0) (q.getVert j))
    (ha : G.Adj (q.getVert (j - 1)) (q.getVert i))
    (hr : G.Adj (E.path.getVert 2) (q.getVert (i + 1))) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ q.length < c.length := by
  have hjm : j - 1 < q.length := by omega
  have hilt : i < q.length := by omega
  have him : i + 1 ≤ q.length - 1 := by omega
  let pre := cycleArc q 0 (j - 1) (by omega) hjm
  let mid := cycleArc q j i hji hilt
  let post := cycleArc q (i + 1) (q.length - 1) him (by omega)
  have hprePath : pre.IsPath := cycleArc_isPath hq (by omega) hjm
  have hmidPath : mid.IsPath := cycleArc_isPath hq hji hilt
  have hpostPath : post.IsPath := cycleArc_isPath hq him (by omega)
  have hiNotPre : q.getVert i ∉ pre.support := by
    intro hmem
    obtain ⟨k, hk0, hkj, hk⟩ := mem_cycleArc_index (by omega) hjm hmem
    have hki := cycle_index_eq_of_getVert_eq hq (by omega) hilt hk
    omega
  let s₁ := pre.concat ha
  have hs₁Path : s₁.IsPath := hprePath.concat hiNotPre ha
  have hs₁midMeet : ∀ a : V,
      a ∈ s₁.support → a ∈ mid.reverse.support → a = q.getVert i := by
    intro a has ham
    have ham' : a ∈ mid.support := by simpa using ham
    obtain ⟨k, hjk, hki, hka⟩ := mem_cycleArc_index hji hilt ham'
    simp only [s₁, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at has
    rcases has with has | rfl
    · obtain ⟨l, hl0, hlj, hla⟩ := mem_cycleArc_index (by omega) hjm has
      have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
        (hla.trans hka.symm)
      omega
    · exact rfl
  let s₂ := s₁.append mid.reverse
  have hs₂Path : s₂.IsPath :=
    isPath_append_of_inter_eq_end hs₁Path hmidPath.reverse hs₁midMeet
  have hs₂earMeet : ∀ a : V,
      a ∈ s₂.support → a ∈ (E.path.drop 2).reverse.support →
        a = q.getVert j := by
    intro a has hae
    have hae' : a ∈ (E.path.drop 2).support := by simpa using hae
    rcases (SimpleGraph.Walk.mem_support_append_iff s₁ mid.reverse).mp has with hs | hm
    · simp only [s₁, SimpleGraph.Walk.support_concat, List.mem_append,
        List.mem_singleton] at hs
      rcases hs with hp | rfl
      · obtain ⟨k, hk0, hkj, hka⟩ := mem_cycleArc_index (by omega) hjm hp
        have hend := drop_two_meets_cycle_only_end E hae'
          (hka ▸ q.getVert_mem_support k)
        have := cycle_index_eq_of_getVert_eq hq (by omega) hj
          (hka.trans hend)
        omega
      · have hend := drop_two_meets_cycle_only_end E hae'
          (q.getVert_mem_support i)
        have := cycle_index_eq_of_getVert_eq hq hilt hj hend
        omega
    · have hm' : a ∈ mid.support := by simpa using hm
      obtain ⟨k, hjk, hki, hka⟩ := mem_cycleArc_index hji hilt hm'
      have hend := drop_two_meets_cycle_only_end E hae'
        (hka ▸ q.getVert_mem_support k)
      have hk := cycle_index_eq_of_getVert_eq hq (by omega) hj
        (hka.trans hend)
      subst k
      exact hend
  let tail := (E.path.drop 2).reverse
  have htailPath : tail.IsPath := (E.isPath.drop 2).reverse
  let s₃ := s₂.append tail
  have hs₃Path : s₃.IsPath :=
    isPath_append_of_inter_eq_end hs₂Path htailPath hs₂earMeet
  have hnextNotS₃ : q.getVert (i + 1) ∉ s₃.support := by
    intro hmem
    rcases (SimpleGraph.Walk.mem_support_append_iff s₂ tail).mp hmem with hs | he
    · rcases (SimpleGraph.Walk.mem_support_append_iff s₁ mid.reverse).mp hs with hs | hm
      · simp only [s₁, SimpleGraph.Walk.support_concat, List.mem_append,
          List.mem_singleton] at hs
        rcases hs with hp | heq
        · obtain ⟨k, hk0, hkj, hk⟩ := mem_cycleArc_index (by omega) hjm hp
          have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hk
          omega
        · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) heq.symm
          omega
      · have hm' : q.getVert (i + 1) ∈ mid.support := by simpa using hm
        obtain ⟨k, hjk, hki, hk⟩ := mem_cycleArc_index hji hilt hm'
        have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hk
        omega
    · have he' : q.getVert (i + 1) ∈ (E.path.drop 2).support := by
        simpa [tail] using he
      have hend := drop_two_meets_cycle_only_end E he'
        (q.getVert_mem_support (i + 1))
      have := cycle_index_eq_of_getVert_eq hq (by omega) hj hend
      omega
  let s₄ := s₃.concat hr
  have hs₄Path : s₄.IsPath := hs₃Path.concat hnextNotS₃ hr
  have hs₄postMeet : ∀ a : V,
      a ∈ s₄.support → a ∈ post.support → a = q.getVert (i + 1) := by
    intro a has hap
    obtain ⟨k, hik, hkm, hka⟩ := mem_cycleArc_index him (by omega) hap
    simp only [s₄, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at has
    rcases has with has | rfl
    · rcases (SimpleGraph.Walk.mem_support_append_iff s₂ tail).mp has with hs | he
      · rcases (SimpleGraph.Walk.mem_support_append_iff s₁ mid.reverse).mp hs with hs | hm
        · simp only [s₁, SimpleGraph.Walk.support_concat, List.mem_append,
            List.mem_singleton] at hs
          rcases hs with hp | heq
          · obtain ⟨l, hl0, hlj, hla⟩ := mem_cycleArc_index (by omega) hjm hp
            have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
              (hla.trans hka.symm)
            omega
          · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
              (heq.symm.trans hka.symm)
            omega
        · have hm' : a ∈ mid.support := by simpa using hm
          obtain ⟨l, hjl, hli, hla⟩ := mem_cycleArc_index hji hilt hm'
          have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
            (hla.trans hka.symm)
          omega
      · have he' : a ∈ (E.path.drop 2).support := by simpa [tail] using he
        have hend := drop_two_meets_cycle_only_end E he'
          (hka ▸ q.getVert_mem_support k)
        have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
          (hend.symm.trans hka.symm)
        omega
    · exact rfl
  let s₅ := s₄.append post
  have hs₅Path : s₅.IsPath :=
    isPath_append_of_inter_eq_end hs₄Path hpostPath hs₄postMeet
  have hclose : G.Adj (q.getVert (q.length - 1)) (q.getVert 0) := by
    have hadj := q.adj_getVert_succ (by omega : q.length - 1 < q.length)
    have hm0 : 1 ≤ q.length := by omega
    simpa [Nat.sub_add_cancel hm0, q.getVert_length, q.getVert_zero] using hadj
  let close := hclose.toWalk
  have hclosePath : close.IsPath := hclose.isPath_toWalk
  have hdisj : s₅.support.tail.Disjoint close.support.tail := by
    rw [List.disjoint_left]
    intro a has hac
    have hac' : a = q.getVert 0 := by
      simpa [close, SimpleGraph.Adj.support_toWalk] using hac
    subst a
    have hn := hs₅Path.support_nodup
    rw [← s₅.cons_tail_support, List.nodup_cons] at hn
    exact hn.1 has
  let c := s₅.append close
  have hc : c.IsCycle := hs₅Path.isCycle_append hclosePath hdisj
    (Or.inl (by
      simp only [s₅, s₄, s₃, s₂, s₁,
        SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_concat]
      have := E.three_le
      omega))
  refine ⟨q.getVert 0, c, hc, ?_⟩
  simp only [c, s₅, s₄, s₃, s₂, s₁, tail, close,
    SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_concat,
    SimpleGraph.Walk.length_reverse, SimpleGraph.Adj.length_toWalk,
    SimpleGraph.Walk.drop_length]
  rw [cycleArc_length (by omega) hjm, cycleArc_length hji hilt,
    cycleArc_length him (by omega)]
  have := E.three_le
  omega

private lemma longer_cycle_of_second_arc_collision_c
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j i : ℕ} (hj0 : 0 < j) (hji : j ≤ i) (hi2 : i + 2 < q.length)
    (E : ExteriorEar q (q.getVert 0) (q.getVert j))
    (hb : G.Adj (q.getVert (q.length - 1)) (q.getVert i))
    (hr : G.Adj (E.path.getVert 2) (q.getVert (i + 2))) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ q.length < c.length := by
  have hm0 : 0 < q.length := by omega
  have hi : i < q.length := by omega
  have hj : j < q.length := hji.trans_lt hi
  have hi2last : i + 2 ≤ q.length - 1 := by omega
  let s := E.path.take 2
  have hsPath : s.IsPath := E.isPath.take 2
  have hslen : s.length = 2 := by
    simp only [s, SimpleGraph.Walk.take_length]
    rw [Nat.min_eq_left]
    exact E.three_le.trans' (by omega)
  have hnotS : q.getVert (i + 2) ∉ s.support := by
    intro hmem
    have hmemE : q.getVert (i + 2) ∈ E.path.support := by
      rw [SimpleGraph.Walk.support_take] at hmem
      exact List.mem_of_mem_take hmem
    rcases exteriorEar_meets_cycle_only_ends E hmemE
        (q.getVert_mem_support (i + 2)) with h0 | hj'
    · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) h0
      omega
    · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hj'
      omega
  let r₁ := s.concat hr
  have hr₁Path : r₁.IsPath := hsPath.concat hnotS hr
  let tail := cycleArc q (i + 2) (q.length - 1) hi2last (by omega)
  have htailPath : tail.IsPath := cycleArc_isPath hq hi2last (by omega)
  have hr₁tail : ∀ a : V, a ∈ r₁.support → a ∈ tail.support →
      a = q.getVert (i + 2) := by
    intro a har hat
    obtain ⟨k, hklo, hkhi, hka⟩ := mem_cycleArc_index hi2last (by omega) hat
    simp only [r₁, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at har
    rcases har with har | rfl
    · have harE : a ∈ E.path.support := by
        simp only [s, SimpleGraph.Walk.support_take] at har
        exact List.mem_of_mem_take har
      rcases exteriorEar_meets_cycle_only_ends E harE
          (hka ▸ q.getVert_mem_support k) with h0 | hj'
      · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
            (hka.trans h0)
        omega
      · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
            (hka.trans hj')
        omega
    · rfl
  let r₂ := r₁.append tail
  have hr₂Path : r₂.IsPath :=
    isPath_append_of_inter_eq_end hr₁Path htailPath hr₁tail
  have hiNotR₂ : q.getVert i ∉ r₂.support := by
    intro hmem
    rcases (SimpleGraph.Walk.mem_support_append_iff r₁ tail).mp hmem with hr₁ | ht
    · simp only [r₁, SimpleGraph.Walk.support_concat, List.mem_append,
        List.mem_singleton] at hr₁
      rcases hr₁ with hs | hEq
      · have hsE : q.getVert i ∈ E.path.support := by
          simp only [s, SimpleGraph.Walk.support_take] at hs
          exact List.mem_of_mem_take hs
        rcases exteriorEar_meets_cycle_only_ends E hsE
            (q.getVert_mem_support i) with h0 | hj'
        · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) h0
          omega
        · have hij : i = j :=
            cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hj'
          subst i
          exact endpoint_not_mem_take_two E hs
      · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hEq.symm
        omega
    · obtain ⟨k, hklo, hkhi, hk⟩ := mem_cycleArc_index hi2last (by omega) ht
      have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hk
      omega
  let r₃ := r₂.concat hb
  have hr₃Path : r₃.IsPath := hr₂Path.concat hiNotR₂ hb
  let pre := cycleArc q 0 i (by omega) hi
  have hprePath : pre.IsPath := cycleArc_isPath hq (by omega) hi
  have hinter : ∀ a : V, a ∈ r₃.support → a ∈ pre.reverse.support →
      a = q.getVert 0 ∨ a = q.getVert i := by
    intro a har hap
    have hap' : a ∈ pre.support := by simpa using hap
    obtain ⟨k, hk0, hki, hka⟩ := mem_cycleArc_index (by omega) hi hap'
    simp only [r₃, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at har
    rcases har with har | rfl
    · rcases (SimpleGraph.Walk.mem_support_append_iff r₁ tail).mp har with hr₁ | ht
      · simp only [r₁, SimpleGraph.Walk.support_concat, List.mem_append,
          List.mem_singleton] at hr₁
        rcases hr₁ with hs | hEq
        · have hsE : a ∈ E.path.support := by
            simp only [s, SimpleGraph.Walk.support_take] at hs
            exact List.mem_of_mem_take hs
          rcases exteriorEar_meets_cycle_only_ends E hsE
              (hka ▸ q.getVert_mem_support k) with h0 | hj'
          · exact Or.inl h0
          · have hkJ := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
                (hka.trans hj')
            subst k
            have haJ : a = q.getVert j := hka.symm
            subst a
            exact (endpoint_not_mem_take_two E hs).elim
        · have hkI2 := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
              (hEq.symm.trans hka.symm)
          omega
      · obtain ⟨l, hlo, hlhi, hla⟩ := mem_cycleArc_index hi2last (by omega) ht
        have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
          (hla.trans hka.symm)
        omega
    · exact Or.inr rfl
  have htails : r₃.support.tail.Disjoint pre.reverse.support.tail := by
    rw [List.disjoint_left]
    intro a har hap
    have har' := List.tail_subset _ har
    have hap' := List.tail_subset _ hap
    rcases hinter a har' hap' with h0 | hi'
    · have hn := hr₃Path.support_nodup
      rw [← r₃.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 (h0.symm ▸ har)
    · have hn := hprePath.reverse.support_nodup
      rw [← pre.reverse.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 (hi' ▸ hap)
  let c := r₃.append pre.reverse
  have hc : c.IsCycle := hr₃Path.isCycle_append hprePath.reverse htails
    (Or.inl (by
      simp only [r₃, r₂, r₁, SimpleGraph.Walk.length_concat,
        SimpleGraph.Walk.length_append]
      rw [hslen]
      omega))
  refine ⟨q.getVert 0, c, hc, ?_⟩
  simp only [c, r₃, r₂, r₁, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_reverse,
    SimpleGraph.Walk.take_length]
  rw [hslen, cycleArc_length hi2last (by omega),
    cycleArc_length (by omega) hi]
  omega

/-! ## Outside-region cycle splices -/

private lemma start_not_mem_drop {x y : V} {p : G.Walk x y}
    (hp : p.IsPath) {t : ℕ} (ht0 : 0 < t) (ht : t ≤ p.length) :
    x ∉ (p.drop t).support := by
  intro hx
  obtain ⟨n, hget, hn⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  have hsum : t + n ≤ p.length := by
    rw [SimpleGraph.Walk.drop_length] at hn
    omega
  have hzero : t + n = 0 :=
    (hp.getVert_eq_start_iff hsum).mp (by
      rw [SimpleGraph.Walk.drop_getVert] at hget
      exact hget)
  omega

private lemma end_not_mem_take {x y : V} {p : G.Walk x y}
    (hp : p.IsPath) {t : ℕ} (ht : t < p.length) :
    y ∉ (p.take t).support := by
  intro hy
  obtain ⟨n, hget, hn⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
  have hnle : n ≤ p.length := hn.trans (by simp)
  have hn_t : n ≤ t := by
    simpa only [SimpleGraph.Walk.take_length, Nat.min_eq_left ht.le] using hn
  have hget' : p.getVert n = y := by
    simpa [SimpleGraph.Walk.take_getVert, Nat.min_eq_right hn_t] using hget
  have : n = p.length := (hp.getVert_eq_end_iff hnle).mp hget'
  omega

private lemma ear_getVert_two_outside_cycle
    {z : V} {q : G.Walk z z} {j : ℕ}
    (E : ExteriorEar q (q.getVert 0) (q.getVert j)) :
    E.path.getVert 2 ∉ q.support.toFinset := by
  have h2le : 2 ≤ E.path.length := E.three_le.trans' (by omega)
  have h2mem : E.path.getVert 2 ∈ E.path.support :=
    E.path.getVert_mem_support 2
  rcases E.outside _ h2mem with h0 | hend | hout
  · have hzero := (E.isPath.getVert_eq_start_iff h2le).mp h0
    omega
  · have hlen := (E.isPath.getVert_eq_end_iff h2le).mp hend
    have := E.three_le
    omega
  · exact hout

private lemma isCycle_append_of_meet_ends
    {u v : V} {p : G.Walk u v} {q : G.Walk v u}
    (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ x : V, x ∈ p.support → x ∈ q.support →
      x = u ∨ x = v)
    (hlong : 1 < p.length ∨ 1 < q.length) :
    (p.append q).IsCycle := by
  have hdisj : p.support.tail.Disjoint q.support.tail := by
    rw [List.disjoint_left]
    intro x hxp hxq
    rcases hmeet x (List.tail_subset _ hxp) (List.tail_subset _ hxq) with hu | hv
    · have hn := hp.support_nodup
      rw [← p.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 (hu.symm ▸ hxp)
    · have hn := hq.support_nodup
      rw [← q.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 (hv.symm ▸ hxq)
  exact hp.isCycle_append hq hdisj hlong

/- The path around the cycle from position `j` to its predecessor `j-1`,
omitting only the edge between those two vertices. -/
private def wrapArc {z : V} (q : G.Walk z z) (j : ℕ)
    (hj0 : 0 < j) (hj : j < q.length) :
    G.Walk (q.getVert j) (q.getVert (j - 1)) := by
  let d := cycleArc q j (q.length - 1) (by omega) (by omega)
  have hlast : G.Adj (q.getVert (q.length - 1)) (q.getVert 0) := by
    have ha := q.adj_getVert_succ (i := q.length - 1) (by omega)
    rw [show q.length - 1 + 1 = q.length by omega,
      q.getVert_length] at ha
    simpa only [q.getVert_zero] using ha
  let r := d.concat hlast
  let pre := cycleArc q 0 (j - 1) (by omega) (by omega)
  exact r.append pre

private lemma wrapArc_length {z : V} {q : G.Walk z z}
    {j : ℕ} (hj0 : 0 < j) (hj : j < q.length) :
    (wrapArc q j hj0 hj).length = q.length - 1 := by
  simp only [wrapArc, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_concat]
  rw [cycleArc_length (by omega) (by omega),
    cycleArc_length (by omega) (by omega)]
  omega

private lemma wrapArc_isPath {z : V} {q : G.Walk z z}
    (hq : q.IsCycle) {j : ℕ} (hj0 : 0 < j) (hj : j < q.length) :
    (wrapArc q j hj0 hj).IsPath := by
  let d := cycleArc q j (q.length - 1) (by omega) (by omega)
  have hd : d.IsPath := cycleArc_isPath hq (by omega) (by omega)
  have hlast : G.Adj (q.getVert (q.length - 1)) (q.getVert 0) := by
    have ha := q.adj_getVert_succ (i := q.length - 1) (by omega)
    rw [show q.length - 1 + 1 = q.length by omega,
      q.getVert_length] at ha
    simpa only [q.getVert_zero] using ha
  have hzeroNotD : q.getVert 0 ∉ d.support := by
    intro hz
    obtain ⟨k, hjk, hkm, hk⟩ := mem_cycleArc_index (by omega) (by omega) hz
    have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) hk
    omega
  let r := d.concat hlast
  have hr : r.IsPath := hd.concat hzeroNotD hlast
  let pre := cycleArc q 0 (j - 1) (by omega) (by omega)
  have hpre : pre.IsPath := cycleArc_isPath hq (by omega) (by omega)
  have hinter : ∀ a : V, a ∈ r.support → a ∈ pre.support →
      a = q.getVert 0 := by
    intro a har hap
    obtain ⟨l, hl0, hlj, hla⟩ := mem_cycleArc_index (by omega) (by omega) hap
    simp only [r, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at har
    rcases har with had | rfl
    · obtain ⟨k, hjk, hkm, hka⟩ := mem_cycleArc_index (by omega) (by omega) had
      have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
        (hka.trans hla.symm)
      omega
    · exact rfl
  simpa only [wrapArc, d, r, pre] using
    isPath_append_of_inter_eq_end hr hpre hinter

private lemma wrapArc_support_subset_cycle {z : V} {q : G.Walk z z}
    {j : ℕ} (hj0 : 0 < j) (hj : j < q.length) {a : V}
    (ha : a ∈ (wrapArc q j hj0 hj).support) : a ∈ q.support := by
  simp only [wrapArc, SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at ha
  rcases ha with (had | rfl) | hap
  · obtain ⟨k, -, -, rfl⟩ := mem_cycleArc_index (by omega) (by omega) had
    exact q.getVert_mem_support k
  · exact q.getVert_mem_support 0
  · obtain ⟨k, -, -, rfl⟩ := mem_cycleArc_index (by omega) (by omega) hap
    exact q.getVert_mem_support k

/- If the predecessor `a` of the terminal ear endpoint sees a proper
internal ear vertex, replace the cycle edge `a--y` by the ear suffix and
the new chord. -/
lemma longer_cycle_of_a_adj_ear_internal
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j t : ℕ} (hj0 : 0 < j) (hj : j < q.length)
    (E : ExteriorEar q (q.getVert 0) (q.getVert j))
    (ht0 : 0 < t) (ht : t < E.path.length)
    (hadj : G.Adj (q.getVert (j - 1)) (E.path.getVert t)) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ q.length < c.length := by
  let s := E.path.drop t
  have hs : s.IsPath := E.isPath.drop t
  let w := wrapArc q j hj0 hj
  have hw : w.IsPath := wrapArc_isPath hq hj0 hj
  have hmeet : ∀ v : V, v ∈ s.support → v ∈ w.support →
      v = q.getVert j := by
    intro v hvs hvw
    have hvsE : v ∈ E.path.support := by
      rw [SimpleGraph.Walk.drop_support_eq_support_drop_min] at hvs
      exact List.mem_of_mem_drop hvs
    have hvq : v ∈ q.support := wrapArc_support_subset_cycle hj0 hj hvw
    rcases exteriorEar_meets_cycle_only_ends E hvsE hvq with h0 | hjv
    · subst v
      exact (start_not_mem_drop E.isPath ht0 ht.le hvs).elim
    · exact hjv
  let r := s.append w
  have hr : r.IsPath := isPath_append_of_inter_eq_end hs hw hmeet
  let e := hadj.toWalk
  have he : e.IsPath := hadj.isPath_toWalk
  have hdisj : r.support.tail.Disjoint e.support.tail := by
    rw [List.disjoint_left]
    intro v hvr hve
    have hvt : v = E.path.getVert t := by
      simpa [e, SimpleGraph.Adj.support_toWalk] using hve
    subst v
    have hn := hr.support_nodup
    rw [← r.cons_tail_support, List.nodup_cons] at hn
    exact hn.1 hvr
  let c := r.append e
  have hc : c.IsCycle := hr.isCycle_append he hdisj
    (Or.inl (by
      simp only [r, s, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.drop_length]
      rw [wrapArc_length hj0 hj]
      have := E.three_le
      omega))
  refine ⟨E.path.getVert t, c, hc, ?_⟩
  simp only [c, r, s, e, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.drop_length, SimpleGraph.Adj.length_toWalk]
  rw [wrapArc_length hj0 hj]
  omega

/- The symmetric splice at the last cycle vertex `b`: replace the closing
cycle edge `b--x` by an ear prefix and the new chord. -/
lemma longer_cycle_of_b_adj_ear_internal
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j t : ℕ} (hj0 : 0 < j) (hj : j < q.length)
    (E : ExteriorEar q (q.getVert 0) (q.getVert j))
    (ht0 : 0 < t) (ht : t < E.path.length)
    (hadj : G.Adj (q.getVert (q.length - 1)) (E.path.getVert t)) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ q.length < c.length := by
  let s := E.path.take t
  have hs : s.IsPath := E.isPath.take t
  have hbNotS : q.getVert (q.length - 1) ∉ s.support := by
    intro hb
    have hbE : q.getVert (q.length - 1) ∈ E.path.support := by
      rw [SimpleGraph.Walk.support_take] at hb
      exact List.mem_of_mem_take hb
    rcases exteriorEar_meets_cycle_only_ends E hbE
        (q.getVert_mem_support (q.length - 1)) with h0 | hjv
    · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) h0
      omega
    · have hb' : q.getVert (q.length - 1) ∈ (E.path.take t).support := by
        simpa only [s] using hb
      rw [hjv] at hb'
      exact end_not_mem_take E.isPath ht hb'
  let r := s.concat hadj.symm
  have hr : r.IsPath := hs.concat hbNotS hadj.symm
  let p := cycleArc q 0 (q.length - 1) (by omega) (by omega)
  have hp : p.IsPath := cycleArc_isPath hq (by omega) (by omega)
  have hmeet : ∀ v : V, v ∈ r.support → v ∈ p.reverse.support →
      v = q.getVert 0 ∨ v = q.getVert (q.length - 1) := by
    intro v hvr hvp
    have hvp' : v ∈ p.support := by simpa using hvp
    have hvq : v ∈ q.support := by
      obtain ⟨k, -, -, rfl⟩ := mem_cycleArc_index (by omega) (by omega) hvp'
      exact q.getVert_mem_support k
    simp only [r, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at hvr
    rcases hvr with hvs | rfl
    · have hvsE : v ∈ E.path.support := by
        rw [SimpleGraph.Walk.support_take] at hvs
        exact List.mem_of_mem_take hvs
      rcases exteriorEar_meets_cycle_only_ends E hvsE hvq with h0 | hjv
      · exact Or.inl h0
      · subst v
        exact (end_not_mem_take E.isPath ht hvs).elim
    · exact Or.inr rfl
  have hdisj : r.support.tail.Disjoint p.reverse.support.tail := by
    rw [List.disjoint_left]
    intro v hvr hvp
    rcases hmeet v (List.tail_subset _ hvr) (List.tail_subset _ hvp) with h0 | hb
    · have hn := hr.support_nodup
      rw [← r.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 (h0.symm ▸ hvr)
    · have hn := hp.reverse.support_nodup
      rw [← p.reverse.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 (hb ▸ hvp)
  let c := r.append p.reverse
  have hc : c.IsCycle := hr.isCycle_append hp.reverse hdisj
    (Or.inl (by
      simp only [r, s, SimpleGraph.Walk.length_concat,
        SimpleGraph.Walk.take_length]
      rw [Nat.min_eq_left ht.le]
      omega))
  refine ⟨q.getVert 0, c, hc, ?_⟩
  simp only [c, r, s, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_concat, SimpleGraph.Walk.take_length,
    SimpleGraph.Walk.length_reverse]
  rw [Nat.min_eq_left ht.le, cycleArc_length (by omega) (by omega)]
  omega

/- A vertex outside both the cycle and the ear which is adjacent to `a`
and the third ear vertex gives the two-edge replacement
`a--w--r` of the chord in the preceding splice. -/
lemma longer_cycle_of_external_common_neighbor_ar
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j : ℕ} (hj0 : 0 < j) (hj : j < q.length)
    (E : ExteriorEar q (q.getVert 0) (q.getVert j))
    {w : V} (hwq : w ∉ q.support.toFinset)
    (hwE : w ∉ E.path.support.toFinset)
    (haw : G.Adj (q.getVert (j - 1)) w)
    (hrw : G.Adj (E.path.getVert 2) w) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ q.length < c.length := by
  let s := E.path.drop 2
  have hs : s.IsPath := E.isPath.drop 2
  let wa := wrapArc q j hj0 hj
  have hwa : wa.IsPath := wrapArc_isPath hq hj0 hj
  have hmeetSW : ∀ v : V, v ∈ s.support → v ∈ wa.support →
      v = q.getVert j := by
    intro v hvs hvwa
    have hvsE : v ∈ E.path.support := by
      rw [SimpleGraph.Walk.drop_support_eq_support_drop_min] at hvs
      exact List.mem_of_mem_drop hvs
    have hvq : v ∈ q.support := wrapArc_support_subset_cycle hj0 hj hvwa
    rcases exteriorEar_meets_cycle_only_ends E hvsE hvq with h0 | hjv
    · subst v
      exact (start_not_mem_drop E.isPath (by omega)
        (by have := E.three_le; omega) hvs).elim
    · exact hjv
  let r := s.append wa
  have hr : r.IsPath := isPath_append_of_inter_eq_end hs hwa hmeetSW
  have hrOut : E.path.getVert 2 ∉ q.support.toFinset :=
    ear_getVert_two_outside_cycle E
  have hra : E.path.getVert 2 ≠ q.getVert (j - 1) := by
    intro h
    exact hrOut (List.mem_toFinset.mpr (h ▸ q.getVert_mem_support (j - 1)))
  have hrNotEdge : E.path.getVert 2 ∉ haw.toWalk.support := by
    simp [SimpleGraph.Adj.support_toWalk, hra, hrw.ne]
  let e := haw.toWalk.concat hrw.symm
  have he : e.IsPath := haw.isPath_toWalk.concat hrNotEdge hrw.symm
  have hwNotR : w ∉ r.support := by
    intro hwr
    rcases (SimpleGraph.Walk.mem_support_append_iff s wa).mp hwr with hws | hwwa
    · apply hwE
      apply List.mem_toFinset.mpr
      rw [SimpleGraph.Walk.drop_support_eq_support_drop_min] at hws
      exact List.mem_of_mem_drop hws
    · exact hwq (List.mem_toFinset.mpr
        (wrapArc_support_subset_cycle hj0 hj hwwa))
  have hmeet : ∀ v : V, v ∈ r.support → v ∈ e.support →
      v = E.path.getVert 2 ∨ v = q.getVert (j - 1) := by
    intro v hvr hve
    have hcases : v = q.getVert (j - 1) ∨ v = w ∨
        v = E.path.getVert 2 := by
      simpa [e, SimpleGraph.Walk.support_concat,
        SimpleGraph.Adj.support_toWalk, or_assoc] using hve
    rcases hcases with ha | hw | hr'
    · exact Or.inr ha
    · subst v
      exact (hwNotR hvr).elim
    · exact Or.inl hr'
  let c := r.append e
  have hc : c.IsCycle := isCycle_append_of_meet_ends hr he hmeet
    (Or.inl (by
      simp only [r, s, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.drop_length]
      rw [wrapArc_length hj0 hj]
      have := E.three_le
      omega))
  refine ⟨E.path.getVert 2, c, hc, ?_⟩
  simp only [c, r, s, e, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.drop_length, SimpleGraph.Walk.length_concat,
    SimpleGraph.Adj.length_toWalk]
  rw [wrapArc_length hj0 hj]
  have := E.three_le
  omega

lemma longer_cycle_of_external_common_neighbor_br
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j : ℕ} (hj0 : 0 < j) (hj : j < q.length)
    (E : ExteriorEar q (q.getVert 0) (q.getVert j))
    {w : V} (hwq : w ∉ q.support.toFinset)
    (hwE : w ∉ E.path.support.toFinset)
    (hbw : G.Adj (q.getVert (q.length - 1)) w)
    (hrw : G.Adj (E.path.getVert 2) w) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ q.length < c.length := by
  have htwo : 2 < E.path.length := by
    have := E.three_le
    omega
  let s := E.path.take 2
  have hs : s.IsPath := E.isPath.take 2
  have hwNotS : w ∉ s.support := by
    intro hws
    apply hwE
    apply List.mem_toFinset.mpr
    rw [SimpleGraph.Walk.support_take] at hws
    exact List.mem_of_mem_take hws
  let r₁ := s.concat hrw
  have hr₁ : r₁.IsPath := hs.concat hwNotS hrw
  have hbNotS : q.getVert (q.length - 1) ∉ s.support := by
    intro hb
    have hbE : q.getVert (q.length - 1) ∈ E.path.support := by
      rw [SimpleGraph.Walk.support_take] at hb
      exact List.mem_of_mem_take hb
    rcases exteriorEar_meets_cycle_only_ends E hbE
        (q.getVert_mem_support (q.length - 1)) with h0 | hjv
    · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) h0
      omega
    · have hb' : q.getVert (q.length - 1) ∈ (E.path.take 2).support := by
        simpa only [s] using hb
      rw [hjv] at hb'
      exact end_not_mem_take E.isPath htwo hb'
  have hbNotR₁ : q.getVert (q.length - 1) ∉ r₁.support := by
    intro hb
    simp only [r₁, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at hb
    rcases hb with hbs | hbw'
    · exact hbNotS hbs
    · exact hbw.ne hbw'
  let r := r₁.concat hbw.symm
  have hr : r.IsPath := hr₁.concat hbNotR₁ hbw.symm
  let p := cycleArc q 0 (q.length - 1) (by omega) (by omega)
  have hp : p.IsPath := cycleArc_isPath hq (by omega) (by omega)
  have hmeet : ∀ v : V, v ∈ r.support → v ∈ p.reverse.support →
      v = q.getVert 0 ∨ v = q.getVert (q.length - 1) := by
    intro v hvr hvp
    have hvp' : v ∈ p.support := by simpa using hvp
    have hvq : v ∈ q.support := by
      obtain ⟨k, -, -, rfl⟩ := mem_cycleArc_index (by omega) (by omega) hvp'
      exact q.getVert_mem_support k
    simp only [r, r₁, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at hvr
    rcases hvr with (hvs | rfl) | rfl
    · have hvsE : v ∈ E.path.support := by
        rw [SimpleGraph.Walk.support_take] at hvs
        exact List.mem_of_mem_take hvs
      rcases exteriorEar_meets_cycle_only_ends E hvsE hvq with h0 | hjv
      · exact Or.inl h0
      · have hvs' : v ∈ (E.path.take 2).support := by
          simpa only [s] using hvs
        rw [hjv] at hvs'
        exact (end_not_mem_take E.isPath htwo hvs').elim
    · exact (hwq (List.mem_toFinset.mpr hvq)).elim
    · exact Or.inr rfl
  let c := r.append p.reverse
  have hc : c.IsCycle := isCycle_append_of_meet_ends hr hp.reverse hmeet
    (Or.inl (by simp [r, r₁, s]))
  refine ⟨q.getVert 0, c, hc, ?_⟩
  simp only [c, r, r₁, s, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_concat, SimpleGraph.Walk.take_length,
    SimpleGraph.Walk.length_reverse]
  rw [Nat.min_eq_left htwo.le, cycleArc_length (by omega) (by omega)]
  omega

/- A common outside neighbour of the two predecessor vertices.  The new
cycle follows the whole ear, the terminal cycle arc, `b--w--a`, and the
initial cycle arc backwards. -/
lemma longer_cycle_of_external_common_neighbor_ab
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j : ℕ} (hj0 : 0 < j) (hj : j < q.length)
    (E : ExteriorEar q (q.getVert 0) (q.getVert j))
    {w : V} (hwq : w ∉ q.support.toFinset)
    (hwE : w ∉ E.path.support.toFinset)
    (haw : G.Adj (q.getVert (j - 1)) w)
    (hbw : G.Adj (q.getVert (q.length - 1)) w) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ q.length < c.length := by
  let d := cycleArc q j (q.length - 1) (by omega) (by omega)
  have hd : d.IsPath := cycleArc_isPath hq (by omega) (by omega)
  have hEdMeet : ∀ v : V, v ∈ E.path.support → v ∈ d.support →
      v = q.getVert j := by
    intro v hvE hvd
    obtain ⟨k, hjk, hkm, hkv⟩ := mem_cycleArc_index (by omega) (by omega) hvd
    rcases exteriorEar_meets_cycle_only_ends E hvE
        (hkv ▸ q.getVert_mem_support k) with h0 | hjv
    · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
          (hkv.trans h0)
      omega
    · exact hjv
  let r := E.path.append d
  have hr : r.IsPath := isPath_append_of_inter_eq_end E.isPath hd hEdMeet
  have hab : q.getVert (j - 1) ≠ q.getVert (q.length - 1) := by
    intro h
    have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega) h
    omega
  have haNotEdge : q.getVert (j - 1) ∉ hbw.toWalk.support := by
    simp [SimpleGraph.Adj.support_toWalk, hab, haw.ne]
  let e := hbw.toWalk.concat haw.symm
  have he : e.IsPath := hbw.isPath_toWalk.concat haNotEdge haw.symm
  let pre := cycleArc q 0 (j - 1) (by omega) (by omega)
  have hpre : pre.IsPath := cycleArc_isPath hq (by omega) (by omega)
  have hePreMeet : ∀ v : V, v ∈ e.support → v ∈ pre.reverse.support →
      v = q.getVert (j - 1) := by
    intro v hve hvpre
    have hvpre' : v ∈ pre.support := by simpa using hvpre
    obtain ⟨l, hl0, hlj, hlv⟩ := mem_cycleArc_index (by omega) (by omega) hvpre'
    have hcases : v = q.getVert (q.length - 1) ∨ v = w ∨
        v = q.getVert (j - 1) := by
      simpa [e, SimpleGraph.Walk.support_concat,
        SimpleGraph.Adj.support_toWalk, or_assoc] using hve
    rcases hcases with hb | hw | ha
    · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
          (hb.symm.trans hlv.symm)
      omega
    · have hvSupp : v ∈ q.support := hlv ▸ q.getVert_mem_support l
      exact (hwq (List.mem_toFinset.mpr (hw ▸ hvSupp))).elim
    · exact ha
  let t := e.append pre.reverse
  have ht : t.IsPath := isPath_append_of_inter_eq_end he hpre.reverse hePreMeet
  have hmeet : ∀ v : V, v ∈ r.support → v ∈ t.support →
      v = q.getVert 0 ∨ v = q.getVert (q.length - 1) := by
    intro v hvr hvt
    rcases (SimpleGraph.Walk.mem_support_append_iff e pre.reverse).mp hvt with
      hve | hvpre
    · have hcases : v = q.getVert (q.length - 1) ∨ v = w ∨
          v = q.getVert (j - 1) := by
        simpa [e, SimpleGraph.Walk.support_concat,
          SimpleGraph.Adj.support_toWalk, or_assoc] using hve
      rcases hcases with hb | hw | ha
      · exact Or.inr hb
      · subst v
        rcases (SimpleGraph.Walk.mem_support_append_iff E.path d).mp hvr with
          hwEar | hwD
        · exact (hwE (List.mem_toFinset.mpr hwEar)).elim
        · obtain ⟨k, -, -, hkw⟩ := mem_cycleArc_index (by omega) (by omega) hwD
          exact (hwq (List.mem_toFinset.mpr
            (hkw ▸ q.getVert_mem_support k))).elim
      · rcases (SimpleGraph.Walk.mem_support_append_iff E.path d).mp hvr with
          haEar | haD
        · rcases exteriorEar_meets_cycle_only_ends E haEar
              (ha ▸ q.getVert_mem_support (j - 1)) with h0 | hjv
          · exact Or.inl h0
          · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
                (ha.symm.trans hjv)
            omega
        · obtain ⟨k, hjk, hkm, hka⟩ := mem_cycleArc_index (by omega) (by omega) haD
          have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
            (hka.trans ha)
          omega
    · have hvpre' : v ∈ pre.support := by simpa using hvpre
      obtain ⟨l, hl0, hlj, hlv⟩ := mem_cycleArc_index (by omega) (by omega) hvpre'
      rcases (SimpleGraph.Walk.mem_support_append_iff E.path d).mp hvr with
        hvEar | hvD
      · rcases exteriorEar_meets_cycle_only_ends E hvEar
            (hlv ▸ q.getVert_mem_support l) with h0 | hjv
        · exact Or.inl h0
        · have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
              (hlv.trans hjv)
          omega
      · obtain ⟨k, hjk, hkm, hkv⟩ := mem_cycleArc_index (by omega) (by omega) hvD
        have := cycle_index_eq_of_getVert_eq hq (by omega) (by omega)
          (hkv.trans hlv.symm)
        omega
  let c := r.append t
  have hc : c.IsCycle := isCycle_append_of_meet_ends hr ht hmeet
    (Or.inl (by
      simp only [r, SimpleGraph.Walk.length_append]
      have := E.three_le
      omega))
  refine ⟨q.getVert 0, c, hc, ?_⟩
  simp only [c, r, t, e, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_reverse,
    SimpleGraph.Adj.length_toWalk]
  rw [cycleArc_length (by omega) (by omega),
    cycleArc_length (by omega) (by omega)]
  have := E.three_le
  omega

/- The single outside-region interface used by the degree pigeonhole
argument. -/
theorem longer_cycle_of_outside_collision
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j : ℕ} (hj0 : 0 < j) (hj : j < q.length)
    (E : ExteriorEar q (q.getVert 0) (q.getVert j))
    (hcollision :
      (∃ t : ℕ, 0 < t ∧ t < E.path.length ∧
        (G.Adj (q.getVert (j - 1)) (E.path.getVert t) ∨
          G.Adj (q.getVert (q.length - 1)) (E.path.getVert t))) ∨
      (∃ w : V, w ∉ q.support.toFinset ∧ w ∉ E.path.support.toFinset ∧
        ((G.Adj (q.getVert (j - 1)) w ∧
            G.Adj (q.getVert (q.length - 1)) w) ∨
          (G.Adj (q.getVert (j - 1)) w ∧
            G.Adj (E.path.getVert 2) w) ∨
          (G.Adj (q.getVert (q.length - 1)) w ∧
            G.Adj (E.path.getVert 2) w)))) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ q.length < c.length := by
  rcases hcollision with ⟨t, ht0, ht, ha | hb⟩ |
      ⟨w, hwq, hwE, hab | har | hbr⟩
  · exact longer_cycle_of_a_adj_ear_internal hq hj0 hj E ht0 ht ha
  · exact longer_cycle_of_b_adj_ear_internal hq hj0 hj E ht0 ht hb
  · exact longer_cycle_of_external_common_neighbor_ab hq hj0 hj E
      hwq hwE hab.1 hab.2
  · exact longer_cycle_of_external_common_neighbor_ar hq hj0 hj E
      hwq hwE har.1 har.2
  · exact longer_cycle_of_external_common_neighbor_br hq hj0 hj E
      hwq hwE hbr.1 hbr.2


/-! ## Finite cycle regions -/

private def cyclePrefix {z : V} (q : G.Walk z z) (j : ℕ) : Finset V :=
  (Finset.range j).image q.getVert

private lemma mem_cyclePrefix_iff {z : V} {q : G.Walk z z} {j : ℕ} {a : V} :
    a ∈ cyclePrefix q j ↔ ∃ i < j, q.getVert i = a := by
  simp [cyclePrefix]

private lemma card_cyclePrefix {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j : ℕ} (hj : j ≤ q.length) : (cyclePrefix q j).card = j := by
  change ((Finset.range j).image q.getVert).card = j
  have himage : ((Finset.range j).image q.getVert).card =
      (Finset.range j).card := Finset.card_image_iff.mpr (by
    intro i hi l hl hil
    have hi' : i < j := Finset.mem_range.mp hi
    have hl' : l < j := Finset.mem_range.mp hl
    exact hq.getVert_injOn'
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hil)
  simpa using himage

private lemma cyclePrefix_length_eq_carrier {z : V} {q : G.Walk z z}
    (hq : q.IsCycle) : cyclePrefix q q.length = q.support.toFinset := by
  ext a
  constructor
  · intro ha
    obtain ⟨i, -, rfl⟩ := mem_cyclePrefix_iff.mp ha
    exact List.mem_toFinset.mpr (q.getVert_mem_support i)
  · intro ha
    obtain ⟨i, hi, hile⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      (List.mem_toFinset.mp ha)
    by_cases him : i = q.length
    · subst i
      have hthree := hq.three_le_length
      refine mem_cyclePrefix_iff.mpr ⟨0, by omega, ?_⟩
      simpa using hi
    · exact mem_cyclePrefix_iff.mpr ⟨i, by omega, hi⟩

private lemma cyclePrefix_subset_carrier {z : V} {q : G.Walk z z}
    (hq : q.IsCycle) {j : ℕ} (hj : j ≤ q.length) :
    cyclePrefix q j ⊆ q.support.toFinset := by
  rw [← cyclePrefix_length_eq_carrier hq]
  intro a ha
  obtain ⟨i, hi, hia⟩ := mem_cyclePrefix_iff.mp ha
  exact mem_cyclePrefix_iff.mpr ⟨i, hi.trans_le hj, hia⟩

/-! ## Degree counts in the three ear regions -/

private def firstRegion {z : V} (q : G.Walk z z) (j : ℕ) : Finset V :=
  (Finset.range j).image q.getVert

private def cycleRegion {z : V} (q : G.Walk z z) : Finset V :=
  q.support.toFinset

private def secondRegion {z : V} (q : G.Walk z z) (j : ℕ) : Finset V :=
  cycleRegion q \ firstRegion q j

private def outsideRegion {z : V} (q : G.Walk z z) : Finset V :=
  Finset.univ \ cycleRegion q

private def adjacencyFinset (G : SimpleGraph V) [dG : DecidableRel G.Adj]
    (v : V) : Finset V :=
  @Finset.filter V (fun w ↦ G.Adj v w) (dG v) Finset.univ

private def regionDegree (G : SimpleGraph V) [dG : DecidableRel G.Adj]
    (v : V) (S : Finset V) : ℕ :=
  (adjacencyFinset (dG := dG) G v ∩ S).card

private lemma cycleRegion_card {z : V} {q : G.Walk z z} (hq : q.IsCycle) :
    (cycleRegion q).card = q.length := by
  have hz : z ∈ q.support.tail := q.end_mem_tail_support hq.not_nil
  simp only [cycleRegion]
  rw [← q.cons_tail_support, List.toFinset_cons,
    Finset.insert_eq_of_mem (List.mem_toFinset.mpr hz),
    List.toFinset_card_of_nodup hq.support_nodup]
  rw [List.length_tail, q.length_support]
  omega

private lemma firstRegion_subset_cycleRegion {z : V} {q : G.Walk z z}
    {j : ℕ} (hj : j ≤ q.length) :
    firstRegion q j ⊆ cycleRegion q := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  exact List.mem_toFinset.mpr (q.getVert_mem_support i)

private lemma firstRegion_card {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j : ℕ} (hj : j ≤ q.length) :
    (firstRegion q j).card = j := by
  simp only [firstRegion]
  rw [Finset.card_image_iff.mpr]
  · exact Finset.card_range j
  · intro i hi k hk hik
    apply hq.getVert_injOn'
    · simp only [Set.mem_ofPred_eq]
      have : i < q.length := (Finset.mem_range.mp hi).trans_le hj
      omega
    · simp only [Set.mem_ofPred_eq]
      have : k < q.length := (Finset.mem_range.mp hk).trans_le hj
      omega
    · exact hik

private lemma secondRegion_card {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j : ℕ} (hj : j ≤ q.length) :
    (secondRegion q j).card = q.length - j := by
  rw [secondRegion, Finset.card_sdiff_of_subset (firstRegion_subset_cycleRegion hj),
    cycleRegion_card hq, firstRegion_card hq hj]

private lemma outsideRegion_card {z : V} {q : G.Walk z z} (hq : q.IsCycle) :
    (outsideRegion q).card = Fintype.card V - q.length := by
  rw [outsideRegion, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, cycleRegion_card hq]

private lemma regionDegree_add {z : V} (q : G.Walk z z) (j : ℕ) (v : V)
    (hj : j ≤ q.length) :
    regionDegree G v (firstRegion q j) +
      regionDegree G v (secondRegion q j) +
      regionDegree G v (outsideRegion q) = G.degree v := by
  let N := adjacencyFinset G v
  let U := firstRegion q j
  let C := cycleRegion q
  let D := secondRegion q j
  let W := outsideRegion q
  have hUD : Disjoint (N ∩ U) (N ∩ D) := by
    rw [Finset.disjoint_left]
    intro x hxU hxD
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxD).2).2
      (Finset.mem_inter.mp hxU).2
  have hUDW : Disjoint ((N ∩ U) ∪ (N ∩ D)) (N ∩ W) := by
    rw [Finset.disjoint_left]
    intro x hxUD hxW
    have hxC : x ∈ C := by
      rcases Finset.mem_union.mp hxUD with hxU | hxD
      · exact firstRegion_subset_cycleRegion hj
          (Finset.mem_inter.mp hxU).2
      · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxD).2).1
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxW).2).2 hxC
  have hunion : ((N ∩ U) ∪ (N ∩ D)) ∪ (N ∩ W) = N := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_univ, true_and, N, U, C, D, W, secondRegion, outsideRegion]
    tauto
  have hdegree : N.card = G.degree v := by
    simp only [N, adjacencyFinset]
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_eq_filter]
  simp only [regionDegree]
  change (N ∩ U).card + (N ∩ D).card + (N ∩ W).card = G.degree v
  calc
    _ = (((N ∩ U) ∪ (N ∩ D)) ∪ (N ∩ W)).card := by
      rw [Finset.card_union_of_disjoint hUDW,
        Finset.card_union_of_disjoint hUD]
    _ = N.card := congrArg Finset.card hunion
    _ = G.degree v := hdegree

private lemma minimal_first_region_degree_le_one
    {z : V} {q : G.Walk z z} {j : ℕ}
    (hj : j ≤ q.length) (r : V)
    (hminimal : ∀ i : ℕ, 0 < i → i < j → ¬ G.Adj r (q.getVert i)) :
    regionDegree G r (firstRegion q j) ≤ 1 := by
  let N := adjacencyFinset G r
  have hsub : N ∩ firstRegion q j ⊆ {q.getVert 0} := by
    intro v hv
    obtain ⟨hvN, hvU⟩ := Finset.mem_inter.mp hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hvU
    have hij : i < j := Finset.mem_range.mp hi
    by_cases hi0 : i = 0
    · simp [hi0]
    · exact (hminimal i (Nat.pos_of_ne_zero hi0) hij
        (by simpa [N, adjacencyFinset] using hvN)).elim
  have hcard := Finset.card_le_card hsub
  simpa only [regionDegree, N, Finset.card_singleton] using hcard

private def neighborPositions {z : V} (q : G.Walk z z) (j : ℕ)
    (v : V) : Finset ℕ :=
  (Finset.range j).filter fun i ↦ G.Adj v (q.getVert i)

private lemma neighborPositions_card {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j : ℕ} (hj : j ≤ q.length) (v : V) :
    (neighborPositions q j v).card = regionDegree G v (firstRegion q j) := by
  have hinj : Set.InjOn q.getVert (neighborPositions q j v : Set ℕ) := by
    intro i hi k hk hik
    apply hq.getVert_injOn'
    · simp only [Set.mem_ofPred_eq]
      have hi' : i < j := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      omega
    · simp only [Set.mem_ofPred_eq]
      have hk' : k < j := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      omega
    · exact hik
  have himage : (neighborPositions q j v).image q.getVert =
      adjacencyFinset G v ∩ firstRegion q j := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hi' := Finset.mem_filter.mp hi
      exact Finset.mem_inter.mpr ⟨by simpa [adjacencyFinset] using hi'.2,
        Finset.mem_image.mpr ⟨i, hi'.1, rfl⟩⟩
    · intro hx
      obtain ⟨hxN, hxU⟩ := Finset.mem_inter.mp hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxU
      exact Finset.mem_image.mpr ⟨i,
        Finset.mem_filter.mpr ⟨hi, by simpa [adjacencyFinset] using hxN⟩, rfl⟩
  rw [regionDegree, ← himage, Finset.card_image_iff.mpr hinj]

private lemma first_region_collision
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j : ℕ} (hj0 : 0 < j) (hj : j < q.length) (r : V)
    (hminimal : ∀ i : ℕ, 0 < i → i < j → ¬ G.Adj r (q.getVert i))
    (hexcess : j + 1 <
      regionDegree G (q.getVert (j - 1)) (firstRegion q j) +
      regionDegree G (q.getVert (q.length - 1)) (firstRegion q j) +
      regionDegree G r (firstRegion q j)) :
    ∃ p : ℕ, p + 1 < j ∧
      G.Adj (q.getVert (j - 1)) (q.getVert p) ∧
      G.Adj (q.getVert (q.length - 1)) (q.getVert (p + 1)) := by
  let a := q.getVert (j - 1)
  let b := q.getVert (q.length - 1)
  let A : Finset ℕ :=
    (Finset.range (j - 1)).filter fun p ↦ G.Adj a (q.getVert p)
  let B : Finset ℕ :=
    (Finset.range (j - 1)).filter fun p ↦ G.Adj b (q.getVert (p + 1))
  have hPa : neighborPositions q j a = A := by
    ext i
    simp only [neighborPositions, A, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hij, hai⟩
      refine ⟨?_, hai⟩
      by_contra h
      have hi : i = j - 1 := by omega
      subst i
      exact G.irrefl hai
    · rintro ⟨hij, hai⟩
      exact ⟨by omega, hai⟩
  have hb0 : G.Adj b (q.getVert 0) := by
    have h := q.adj_getVert_succ (i := q.length - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at h
    simpa only [b, q.getVert_length, q.getVert_zero] using h
  have hPb : neighborPositions q j b = insert 0 (B.image Nat.succ) := by
    ext i
    simp only [neighborPositions, B, Finset.mem_filter, Finset.mem_range,
      Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨hij, hbi⟩
      by_cases hi0 : i = 0
      · exact Or.inl hi0
      · right
        refine ⟨i - 1, ?_, by omega⟩
        exact ⟨by omega, by
          simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi0)] using hbi⟩
    · rintro (rfl | ⟨p, ⟨hp, hbp⟩, rfl⟩)
      · exact ⟨hj0, hb0⟩
      · exact ⟨by omega, hbp⟩
  have hzeroNotB : 0 ∉ B.image Nat.succ := by simp
  have hBimageCard : (B.image Nat.succ).card = B.card :=
    Finset.card_image_of_injective B Nat.succ_injective
  have haCard : regionDegree G a (firstRegion q j) = A.card := by
    rw [← neighborPositions_card hq hj.le, hPa]
  have hbCard : regionDegree G b (firstRegion q j) = B.card + 1 := by
    rw [← neighborPositions_card hq hj.le, hPb,
      Finset.card_insert_of_notMem hzeroNotB, hBimageCard]
  have hrCard : regionDegree G r (firstRegion q j) ≤ 1 :=
    minimal_first_region_degree_le_one hj.le r hminimal
  have hABcard : j - 1 < A.card + B.card := by
    dsimp only [a] at haCard
    dsimp only [b] at hbCard
    rw [haCard, hbCard] at hexcess
    omega
  have hAsub : A ⊆ Finset.range (j - 1) :=
    fun i hi ↦ (Finset.mem_filter.mp hi).1
  have hBsub : B ⊆ Finset.range (j - 1) :=
    fun i hi ↦ (Finset.mem_filter.mp hi).1
  have hcollision : ∃ p, p ∈ A ∧ p ∈ B := by
    by_contra h
    push Not at h
    have hd : Disjoint A B :=
      Finset.disjoint_left.mpr fun p hpA hpB ↦ h p hpA hpB
    have hle : A.card + B.card ≤ j - 1 := by
      rw [← Finset.card_union_of_disjoint hd]
      have hc := Finset.card_le_card (Finset.union_subset hAsub hBsub)
      simpa using hc
    omega
  obtain ⟨p, hpA, hpB⟩ := hcollision
  have hpA' := Finset.mem_filter.mp hpA
  have hpB' := Finset.mem_filter.mp hpB
  have hp_lt : p < j - 1 := Finset.mem_range.mp hpA'.1
  exact ⟨p, by omega, hpA'.2, hpB'.2⟩

/-! ## Remaining region collisions -/

lemma secondRegion_eq_image
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j : ℕ} (hj0 : 0 < j) (hj : j < q.length) :
    secondRegion q j =
      (Finset.range (q.length - j)).image (fun s ↦ q.getVert (j + s)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxC, hxU⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨i, hi, hile⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      (List.mem_toFinset.mp hxC)
    have hilt : i < q.length := by
      by_contra h
      have hieq : i = q.length := by omega
      apply hxU
      refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hj0, ?_⟩
      rw [← hi, hieq, q.getVert_length, q.getVert_zero]
    have hji : j ≤ i := by
      by_contra h
      apply hxU
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), hi⟩
    refine Finset.mem_image.mpr
      ⟨i - j, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Nat.add_sub_of_le hji, hi]
  · intro hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    have hindex : j + s < q.length := by
      have := Finset.mem_range.mp hs
      omega
    apply Finset.mem_sdiff.mpr
    refine ⟨List.mem_toFinset.mpr (q.getVert_mem_support (j + s)), ?_⟩
    intro hU
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hU
    have hi' : i < j := Finset.mem_range.mp hi
    have := hq.getVert_injOn'
      (show j + s ≤ q.length - 1 by omega)
      (show i ≤ q.length - 1 by omega) heq.symm
    omega

def secondNeighborPositions {z : V} (q : G.Walk z z) (j : ℕ) (v : V) :
    Finset ℕ :=
  (Finset.range (q.length - j)).filter fun s ↦ G.Adj v (q.getVert (j + s))

lemma secondNeighborPositions_card
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j : ℕ} (hj0 : 0 < j) (hj : j < q.length) (v : V) :
    (secondNeighborPositions q j v).card =
      regionDegree G v (secondRegion q j) := by
  have hinj : Set.InjOn (fun s ↦ q.getVert (j + s))
      (secondNeighborPositions q j v : Set ℕ) := by
    intro s hs t ht heq
    have hs' : s < q.length - j :=
      Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    have ht' : t < q.length - j :=
      Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    have hst := hq.getVert_injOn'
      (show j + s ≤ q.length - 1 by omega)
      (show j + t ≤ q.length - 1 by omega) heq
    omega
  have himage : (secondNeighborPositions q j v).image
      (fun s ↦ q.getVert (j + s)) =
      adjacencyFinset G v ∩ secondRegion q j := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      have hs' := Finset.mem_filter.mp hs
      exact Finset.mem_inter.mpr
        ⟨by simpa [adjacencyFinset] using hs'.2,
          secondRegion_eq_image hq hj0 hj ▸
            Finset.mem_image.mpr ⟨s, hs'.1, rfl⟩⟩
    · intro hx
      obtain ⟨hxN, hxD⟩ := Finset.mem_inter.mp hx
      rw [secondRegion_eq_image hq hj0 hj] at hxD
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hxD
      exact Finset.mem_image.mpr ⟨s,
        Finset.mem_filter.mpr
          ⟨hs, by simpa [adjacencyFinset] using hxN⟩, rfl⟩
  rw [regionDegree, ← himage, Finset.card_image_iff.mpr hinj]

lemma second_region_collision
    {z : V} {q : G.Walk z z} (hq : q.IsCycle)
    {j : ℕ} (hj0 : 0 < j) (hj : j < q.length) (r : V)
    (hexcess : (q.length - j) + 1 <
      regionDegree G (q.getVert (j - 1)) (secondRegion q j) +
      regionDegree G (q.getVert (q.length - 1)) (secondRegion q j) +
      regionDegree G r (secondRegion q j)) :
    (∃ s : ℕ, s + 1 < q.length - j ∧
        G.Adj (q.getVert (q.length - 1)) (q.getVert (j + s)) ∧
        G.Adj (q.getVert (j - 1)) (q.getVert (j + (s + 1)))) ∨
      (∃ s : ℕ, s + 1 < q.length - j ∧
        G.Adj (q.getVert (j - 1)) (q.getVert (j + s)) ∧
        G.Adj r (q.getVert (j + (s + 1)))) ∨
      (∃ s : ℕ, s + 2 < q.length - j ∧
        G.Adj (q.getVert (q.length - 1)) (q.getVert (j + s)) ∧
        G.Adj r (q.getVert (j + (s + 2)))) := by
  let a := q.getVert (j - 1)
  let b := q.getVert (q.length - 1)
  let L := q.length - j
  let A := secondNeighborPositions q j a
  let B := secondNeighborPositions q j b
  let Q := secondNeighborPositions q j r
  have hAsub : A ⊆ Finset.range L :=
    fun s hs ↦ (Finset.mem_filter.mp hs).1
  have hBsub : B ⊆ Finset.range L :=
    fun s hs ↦ (Finset.mem_filter.mp hs).1
  have hQsub : Q ⊆ Finset.range L :=
    fun s hs ↦ (Finset.mem_filter.mp hs).1
  have hBlast : ∀ s ∈ B, s + 1 < L := by
    intro s hs
    have hs' := Finset.mem_filter.mp hs
    have hsL : s < L := Finset.mem_range.mp hs'.1
    by_contra h
    have hindex : j + s = q.length - 1 := by
      dsimp only [L] at hsL h
      omega
    have hadj : G.Adj b (q.getVert (j + s)) := hs'.2
    dsimp only [b] at hadj
    rw [hindex] at hadj
    exact G.irrefl hadj
  have hcard : L + 1 < A.card + B.card + Q.card := by
    dsimp only [A, B, Q, L, a, b]
    rw [secondNeighborPositions_card hq hj0 hj,
      secondNeighborPositions_card hq hj0 hj,
      secondNeighborPositions_card hq hj0 hj]
    exact hexcess
  rcases second_arc_collision hAsub hBsub hQsub hBlast hcard with
      ⟨s, hsB, hsA⟩ | ⟨s, hsA, hsQ⟩ | ⟨s, hsB, hsQ⟩
  · have hsB' := Finset.mem_filter.mp hsB
    have hsA' := Finset.mem_filter.mp hsA
    left
    exact ⟨s, hBlast s hsB, hsB'.2, hsA'.2⟩
  · have hsA' := Finset.mem_filter.mp hsA
    have hsQ' := Finset.mem_filter.mp hsQ
    right; left
    exact ⟨s, Finset.mem_range.mp hsQ'.1, hsA'.2, hsQ'.2⟩
  · have hsB' := Finset.mem_filter.mp hsB
    have hsQ' := Finset.mem_filter.mp hsQ
    right; right
    exact ⟨s, Finset.mem_range.mp hsQ'.1, hsB'.2, hsQ'.2⟩

lemma outside_region_collision
    (W : Finset V) (a b r : V) (hrW : r ∈ W)
    (hexcess : W.card - 1 <
      regionDegree G a W + regionDegree G b W + regionDegree G r W) :
    (G.Adj a r ∨ G.Adj b r) ∨
      ∃ x ∈ W,
        (G.Adj a x ∧ G.Adj b x) ∨
        (G.Adj a x ∧ G.Adj r x) ∨
        (G.Adj b x ∧ G.Adj r x) := by
  by_contra h
  push Not at h
  rcases h with ⟨⟨har, hbr⟩, hpairs⟩
  let Na := adjacencyFinset G a ∩ W
  let Nb := adjacencyFinset G b ∩ W
  let Nr := adjacencyFinset G r ∩ W
  have hab : Disjoint Na Nb := by
    rw [Finset.disjoint_left]
    intro x hxa hxb
    have hxa' := Finset.mem_inter.mp hxa
    have hxb' := Finset.mem_inter.mp hxb
    exact (hpairs x hxa'.2).1
      (by simpa [adjacencyFinset] using hxa'.1)
      (by simpa [adjacencyFinset] using hxb'.1)
  have harDisj : Disjoint Na Nr := by
    rw [Finset.disjoint_left]
    intro x hxa hxr
    have hxa' := Finset.mem_inter.mp hxa
    have hxr' := Finset.mem_inter.mp hxr
    exact (hpairs x hxa'.2).2.1
      (by simpa [adjacencyFinset] using hxa'.1)
      (by simpa [adjacencyFinset] using hxr'.1)
  have hbrDisj : Disjoint Nb Nr := by
    rw [Finset.disjoint_left]
    intro x hxb hxr
    have hxb' := Finset.mem_inter.mp hxb
    have hxr' := Finset.mem_inter.mp hxr
    exact (hpairs x hxb'.2).2.2
      (by simpa [adjacencyFinset] using hxb'.1)
      (by simpa [adjacencyFinset] using hxr'.1)
  have habr : Disjoint (Na ∪ Nb) Nr :=
    Finset.disjoint_union_left.mpr ⟨harDisj, hbrDisj⟩
  have hsub : (Na ∪ Nb) ∪ Nr ⊆ W.erase r := by
    intro x hx
    have hxW : x ∈ W := by
      rcases Finset.mem_union.mp hx with hxAB | hxR
      · rcases Finset.mem_union.mp hxAB with hxA | hxB
        · exact (Finset.mem_inter.mp hxA).2
        · exact (Finset.mem_inter.mp hxB).2
      · exact (Finset.mem_inter.mp hxR).2
    apply Finset.mem_erase.mpr
    refine ⟨?_, hxW⟩
    intro hxr
    subst x
    rcases Finset.mem_union.mp hx with hxAB | hxR
    · rcases Finset.mem_union.mp hxAB with hxA | hxB
      · exact har (by
          exact (by simpa [adjacencyFinset] using (Finset.mem_inter.mp hxA).1))
      · exact hbr (by
          exact (by simpa [adjacencyFinset] using (Finset.mem_inter.mp hxB).1))
    · have hxAdj : r ∈ adjacencyFinset G r := (Finset.mem_inter.mp hxR).1
      change r ∈ Finset.univ.filter (fun w ↦ G.Adj r w) at hxAdj
      have hadj : G.Adj r r := (Finset.mem_filter.mp hxAdj).2
      exact G.irrefl hadj
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint habr,
    Finset.card_union_of_disjoint hab,
    Finset.card_erase_of_mem hrW] at hle
  simp only [regionDegree] at hexcess
  change W.card - 1 < Na.card + Nb.card + Nr.card at hexcess
  omega


/-! ## Longest cycles -/

/-- A genuine cycle of maximum length. -/
def IsLongestCycle {z : V} (c : G.Walk z z) : Prop :=
  c.IsCycle ∧
    ∀ ⦃z' : V⦄ (c' : G.Walk z' z'), c'.IsCycle → c'.length ≤ c.length

lemma isCycle_length_le_card {z : V} {c : G.Walk z z} (hc : c.IsCycle) :
    c.length ≤ Fintype.card V := by
  have hnodup : c.support.tail.Nodup := hc.support_nodup
  have hsub : c.support.tail.toFinset ⊆ (Finset.univ : Finset V) :=
    Finset.subset_univ _
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnodup, Finset.card_univ] at hcard
  have hlen : c.support.tail.length = c.length := by
    rw [List.length_tail, c.length_support]
    omega
  simpa [hlen] using hcard

private def cycleLengths (G : SimpleGraph V) : Finset ℕ :=
  (Finset.range (Fintype.card V + 1)).filter fun m ↦
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ c.length = m

private lemma mem_cycleLengths_iff {m : ℕ} :
    m ∈ cycleLengths G ↔
      ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ c.length = m := by
  constructor
  · intro hm
    exact (Finset.mem_filter.mp hm).2
  · rintro ⟨z, c, hc, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (isCycle_length_le_card hc)),
      ⟨z, c, hc, rfl⟩⟩

theorem exists_isLongestCycle (hTwo : Erdos58.TwoConnected G) :
    ∃ (z : V) (c : G.Walk z z), IsLongestCycle c := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (by
    have := hTwo.card_three_le
    omega)
  let x : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨y, hyx⟩ := hTwo.exists_ne x
  obtain ⟨p, hp⟩ := hTwo.connected.exists_isPath x y
  have hpnon : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hyx.symm
  have hxp : G.Adj x p.snd := p.adj_snd hpnon
  obtain ⟨c₀, hc₀, -⟩ := hTwo.exists_cycle_through_edge hxp
  have hnonempty : (cycleLengths G).Nonempty := by
    exact ⟨c₀.length, mem_cycleLengths_iff.mpr ⟨x, c₀, hc₀, rfl⟩⟩
  obtain ⟨m, hm, hmax⟩ :=
    Finset.exists_max_image (cycleLengths G) id hnonempty
  obtain ⟨z, c, hc, hcm⟩ := mem_cycleLengths_iff.mp hm
  subst m
  refine ⟨z, c, hc, ?_⟩
  intro z' c' hc'
  have hc'mem := mem_cycleLengths_iff.mpr ⟨z', c', hc', rfl⟩
  simpa using hmax c'.length hc'mem

lemma cycleCarrier_card {z : V} {c : G.Walk z z} (hc : c.IsCycle) :
    c.support.toFinset.card = c.length := by
  have hz : z ∈ c.support.tail := c.end_mem_tail_support hc.not_nil
  rw [← c.cons_tail_support, List.toFinset_cons, Finset.insert_eq_of_mem
    (List.mem_toFinset.mpr hz), List.toFinset_card_of_nodup hc.support_nodup]
  rw [List.length_tail, c.length_support]
  omega

theorem compl_isIndepSet_of_isLongestCycle_of_extension
    {z : V} {c : G.Walk z z} (hc : IsLongestCycle c)
    (hextend : ∀ ⦃x y : V⦄,
      x ∉ c.support.toFinset → y ∉ c.support.toFinset → G.Adj x y →
        ∃ (z' : V) (c' : G.Walk z' z'), c'.IsCycle ∧ c.length < c'.length) :
    G.IsIndepSet ((c.support.toFinsetᶜ : Finset V) : Set V) := by
  intro x hx y hy hxy
  intro hadj
  obtain ⟨z', c', hc', hlong⟩ := hextend
    (by simpa using hx) (by simpa using hy) hadj
  exact (Nat.not_lt_of_ge (hc.2 c' hc')) hlong

theorem isHamiltonian_of_cycle_support_eq_univ
    {z : V} {c : G.Walk z z} (hc : c.IsCycle)
    (hspan : c.support.toFinset = (Finset.univ : Finset V)) :
    G.IsHamiltonian := by
  intro _
  refine ⟨z, c, ?_⟩
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨hc, ?_⟩
  have hcard := cycleCarrier_card hc
  rw [hspan, Finset.card_univ] at hcard
  exact hcard.symm

/-! ## The dominating-cycle theorem -/

/-- At the Nash--Williams degree threshold, an edge outside a cycle can be
absorbed into a strictly longer cycle.  This is Bondy's three-region ear
argument. -/
theorem exists_longer_cycle_of_external_edge
    (hTwo : Erdos58.TwoConnected G) {k : ℕ}
    (hThird : Fintype.card V + 2 < 3 * k)
    (hDegree : ∀ v : V, k ≤ G.degree v)
    {z : V} {c : G.Walk z z} (hc : c.IsCycle)
    {v w : V} (hvw : G.Adj v w)
    (hv : v ∉ c.support.toFinset) (hw : w ∉ c.support.toFinset) :
    ∃ (z' : V) (c' : G.Walk z' z'),
      c'.IsCycle ∧ c.length < c'.length := by
  obtain ⟨x, q, j, E, hq, hqlen, hqsupp, hj0, hj, hminimal⟩ :=
    exists_normalized_exteriorEar_of_external_edge hTwo hc hvw hv hw
  let a := q.getVert (j - 1)
  let b := q.getVert (q.length - 1)
  let r := E.path.getVert 2
  have hrOut : r ∉ q.support.toFinset := by
    exact ear_getVert_two_outside_cycle E
  have hrW : r ∈ outsideRegion q := by
    simp only [outsideRegion, cycleRegion, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    exact hrOut
  let p := E.path.getVert 1
  have hpOut : p ∉ q.support.toFinset := by
    have h1le : 1 ≤ E.path.length := by have := E.three_le; omega
    have h1mem : E.path.getVert 1 ∈ E.path.support :=
      E.path.getVert_mem_support 1
    rcases E.outside _ h1mem with hstart | hend | hout
    · have := (E.isPath.getVert_eq_start_iff h1le).mp hstart
      omega
    · have heq := (E.isPath.getVert_eq_end_iff h1le).mp hend
      have := E.three_le
      omega
    · exact hout
  have hpW : p ∈ outsideRegion q := by
    simp only [outsideRegion, cycleRegion, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    exact hpOut
  have hpr : p ≠ r := by
    intro h
    have heq := E.isPath.getVert_injOn
      (show 1 ≤ E.path.length by have := E.three_le; omega)
      (show 2 ≤ E.path.length by have := E.three_le; omega) h
    omega
  have hWtwo : 2 ≤ (outsideRegion q).card := by
    have hsub : ({p, r} : Finset V) ⊆ outsideRegion q := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hpW
      · exact hrW
    have hle := Finset.card_le_card hsub
    simpa [hpr] using hle
  have hsum :
      ((firstRegion q j).card + 1) +
        ((secondRegion q j).card + 1) +
        ((outsideRegion q).card - 1) = Fintype.card V + 1 := by
    have hgap : 2 ≤ Fintype.card V - q.length := by
      rw [← outsideRegion_card hq]
      exact hWtwo
    rw [firstRegion_card hq hj.le, secondRegion_card hq hj.le,
      outsideRegion_card hq]
    have hqcard := isCycle_length_le_card hq
    omega
  have hdegA : k ≤
      regionDegree G a (firstRegion q j) +
        regionDegree G a (secondRegion q j) +
        regionDegree G a (outsideRegion q) := by
    rw [regionDegree_add q j a hj.le]
    exact hDegree a
  have hdegB : k ≤
      regionDegree G b (firstRegion q j) +
        regionDegree G b (secondRegion q j) +
        regionDegree G b (outsideRegion q) := by
    rw [regionDegree_add q j b hj.le]
    exact hDegree b
  have hdegR : k ≤
      regionDegree G r (firstRegion q j) +
        regionDegree G r (secondRegion q j) +
        regionDegree G r (outsideRegion q) := by
    rw [regionDegree_add q j r hj.le]
    exact hDegree r
  have hlarge : Fintype.card V + 1 < 3 * k := by omega
  rcases degree_three_region
      (k := k) (n := Fintype.card V)
      (u := (firstRegion q j).card + 1)
      (d := (secondRegion q j).card + 1)
      (w := (outsideRegion q).card - 1)
      hsum hdegA hdegB hdegR hlarge with hU | hD | hW
  · have hU' : j + 1 <
        regionDegree G (q.getVert (j - 1)) (firstRegion q j) +
          regionDegree G (q.getVert (q.length - 1)) (firstRegion q j) +
          regionDegree G r (firstRegion q j) := by
      simpa only [firstRegion_card hq hj.le, a, b] using hU
    obtain ⟨s, hs, has, hbs⟩ :=
      first_region_collision hq hj0 hj r hminimal hU'
    obtain ⟨z', c', hc', hlong⟩ :=
      longer_cycle_of_first_arc_collision hq hj0 hj hs E has hbs
    exact ⟨z', c', hc', by omega⟩
  · have hD' : (q.length - j) + 1 <
        regionDegree G (q.getVert (j - 1)) (secondRegion q j) +
          regionDegree G (q.getVert (q.length - 1)) (secondRegion q j) +
          regionDegree G r (secondRegion q j) := by
      simpa only [secondRegion_card hq hj.le, a, b] using hD
    rcases second_region_collision hq hj0 hj r hD' with
        ⟨s, hs, hbs, has⟩ | ⟨s, hs, has, hrs⟩ | ⟨s, hs, hbs, hrs⟩
    · obtain ⟨z', c', hc', hlong⟩ :=
        longer_cycle_of_second_arc_collision_a hq hj0
          (i := j + s) (by omega) (by omega) E hbs
          (by simpa [Nat.add_assoc] using has)
      exact ⟨z', c', hc', by omega⟩
    · obtain ⟨z', c', hc', hlong⟩ :=
        longer_cycle_of_second_arc_collision_b hq hj0 hj
          (i := j + s) (by omega) (by omega) E has
          (by simpa [r, Nat.add_assoc] using hrs)
      exact ⟨z', c', hc', by omega⟩
    · obtain ⟨z', c', hc', hlong⟩ :=
        longer_cycle_of_second_arc_collision_c hq hj0
          (i := j + s) (by omega) (by omega) E hbs
          (by simpa [r, Nat.add_assoc] using hrs)
      exact ⟨z', c', hc', by omega⟩
  · have hW' : (outsideRegion q).card - 1 <
        regionDegree G (q.getVert (j - 1)) (outsideRegion q) +
          regionDegree G (q.getVert (q.length - 1)) (outsideRegion q) +
          regionDegree G r (outsideRegion q) := by
      simpa only [a, b] using hW
    have hcollision := outside_region_collision (outsideRegion q)
      (q.getVert (j - 1)) (q.getVert (q.length - 1)) r hrW hW'
    have houtsideCollision :
        (∃ t : ℕ, 0 < t ∧ t < E.path.length ∧
          (G.Adj (q.getVert (j - 1)) (E.path.getVert t) ∨
            G.Adj (q.getVert (q.length - 1)) (E.path.getVert t))) ∨
        (∃ y : V, y ∉ q.support.toFinset ∧ y ∉ E.path.support.toFinset ∧
          ((G.Adj (q.getVert (j - 1)) y ∧
              G.Adj (q.getVert (q.length - 1)) y) ∨
            (G.Adj (q.getVert (j - 1)) y ∧
              G.Adj (E.path.getVert 2) y) ∨
            (G.Adj (q.getVert (q.length - 1)) y ∧
              G.Adj (E.path.getVert 2) y))) := by
      rcases hcollision with (har | hbr) | ⟨y, hyW, hpairs⟩
      · left
        exact ⟨2, by omega, by have := E.three_le; omega,
          Or.inl (by simpa only [r] using har)⟩
      · left
        exact ⟨2, by omega, by have := E.three_le; omega,
          Or.inr (by simpa only [r] using hbr)⟩
      · have hyOut : y ∉ q.support.toFinset := by
          exact (Finset.mem_sdiff.mp hyW).2
        by_cases hyE : y ∈ E.path.support.toFinset
        · have hyES : y ∈ E.path.support := List.mem_toFinset.mp hyE
          obtain ⟨t, hty, htlen⟩ :=
            SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hyES
          have ht0 : 0 < t := by
            by_contra h
            have ht : t = 0 := by omega
            subst t
            apply hyOut
            have hy0 : y = q.getVert 0 := by simpa using hty.symm
            exact List.mem_toFinset.mpr (hy0 ▸ q.getVert_mem_support 0)
          have htlt : t < E.path.length := by
            by_contra h
            have ht : t = E.path.length := by omega
            subst t
            apply hyOut
            have hyj : q.getVert j = y := by
              simpa using hty
            exact List.mem_toFinset.mpr (hyj.symm ▸ q.getVert_mem_support j)
          left
          refine ⟨t, ht0, htlt, ?_⟩
          rcases hpairs with hab | har | hbr
          · exact Or.inl (by simpa [hty] using hab.1)
          · exact Or.inl (by simpa [hty] using har.1)
          · exact Or.inr (by simpa [hty] using hbr.1)
        · right
          refine ⟨y, hyOut, hyE, ?_⟩
          simpa only [r] using hpairs
    obtain ⟨z', c', hc', hlong⟩ :=
      longer_cycle_of_outside_collision hq hj0 hj E houtsideCollision
    exact ⟨z', c', hc', by omega⟩

/-- Every longest cycle is dominating at the strict Nash--Williams degree
threshold: its exterior is an independent set. -/
theorem longest_cycle_complement_isIndepSet
    (hTwo : Erdos58.TwoConnected G) {k : ℕ}
    (hThird : Fintype.card V + 2 < 3 * k)
    (hDegree : ∀ v : V, k ≤ G.degree v)
    {z : V} {c : G.Walk z z} (hc : c.IsCycle)
    (hmax : ∀ ⦃z' : V⦄ (c' : G.Walk z' z'),
      c'.IsCycle → c'.length ≤ c.length) :
    G.IsIndepSet ((c.support.toFinset : Set V)ᶜ) := by
  have hextend : ∀ ⦃x y : V⦄,
      x ∉ c.support.toFinset → y ∉ c.support.toFinset → G.Adj x y →
        ∃ (z' : V) (c' : G.Walk z' z'),
          c'.IsCycle ∧ c.length < c'.length := by
    intro x y hx hy hxy
    exact exists_longer_cycle_of_external_edge hTwo hThird hDegree hc hxy hx hy
  have hfin := compl_isIndepSet_of_isLongestCycle_of_extension
    (c := c) ⟨hc, hmax⟩ hextend
  simpa using hfin

/-! ## The successor-neighbour independent set -/

/-- Once the complement of a longest cycle is independent, the successors
of the neighbours of one exterior vertex, together with that vertex, form
the required independent set. -/
theorem independent_set_of_longest_cycle_complement_independent
    {k : ℕ} {z : V} (c : G.Walk z z) (hc : c.IsCycle)
    (hmax : ∀ (z' : V) (c' : G.Walk z' z'),
      c'.IsCycle → c'.length ≤ c.length)
    (hproper : c.support.toFinset ≠ (Finset.univ : Finset V))
    (hout : G.IsIndepSet ((c.support.toFinset : Set V)ᶜ))
    (hdegree : ∀ v : V, k ≤ G.degree v) :
    ∃ A : Finset V, A.card = k + 1 ∧ G.IsIndepSet (A : Set V) := by
  let C : Finset V := c.support.toFinset
  obtain ⟨x, hxC⟩ : ∃ x : V, x ∉ C := by
    by_contra h
    push Not at h
    exact hproper (Finset.eq_univ_of_forall h)
  have hneighborC : ∀ u : V, G.Adj x u → u ∈ C := by
    intro u hxu
    by_contra huC
    have hxOut : x ∈ (C : Set V)ᶜ := hxC
    have huOut : u ∈ (C : Set V)ᶜ := huC
    exact (hout hxOut huOut hxu.ne) hxu
  let xN : G.neighborFinset x ↪ C :=
    { toFun := fun u ↦
        ⟨u.1, hneighborC u.1 ((G.mem_neighborFinset x u.1).mp u.2)⟩
      inj' := fun u v huv ↦
        Subtype.ext (congrArg (fun y : C ↦ (y : V)) huv) }
  let zC : C := ⟨z, List.mem_toFinset.mpr c.start_mem_support⟩
  let hC : ∀ w ∈ c.support, w ∈ (C : Set V) := fun w hw ↦
    List.mem_toFinset.mpr hw
  let q : (G.induce (C : Set V)).Walk zC zC :=
    c.induce (C : Set V) hC
  have hq : q.IsHamiltonianCycle :=
    ChvatalErdos.induced_cycle_isHamiltonianCycle hc
  have hqLen : q.length = c.length := by
    calc
      q.length = Fintype.card C := hq.length_eq
      _ = C.card := Fintype.card_coe C
      _ = c.length := ChvatalErdos.cycleCarrier_card hc
  have hmaxq : ∀ (z' : V) (c' : G.Walk z' z'),
      c'.IsCycle → c'.length ≤ q.length := by
    intro z' c' hc'
    rw [hqLen]
    exact hmax z' c' hc'
  let N : Finset C := (Finset.univ : Finset (G.neighborFinset x)).map xN
  have hNcard : N.card = G.degree x := by
    calc
      N.card = (Finset.univ : Finset (G.neighborFinset x)).card :=
        Finset.card_map xN
      _ = Fintype.card (G.neighborFinset x) := Finset.card_univ
      _ = (G.neighborFinset x).card := Fintype.card_coe _
      _ = G.degree x := G.card_neighborFinset_eq_degree x
  let S₀ : Finset C := N.image hq.next
  let eC : C ↪ V := Function.Embedding.subtype _
  let S : Finset V := S₀.map eC
  have hScard : S.card = G.degree x := by
    calc
      S.card = S₀.card := Finset.card_map eC
      _ = N.card := Finset.card_image_of_injective N hq.next_inj
      _ = G.degree x := hNcard
  have hxS : x ∉ S := by
    intro hx
    obtain ⟨y, -, hy⟩ := Finset.mem_map.mp hx
    exact hxC (hy ▸ y.2)
  have hmemS : ∀ y : V, y ∈ S ↔
      ∃ u : C, u ∈ N ∧ y = (hq.next u : C) := by
    intro y
    constructor
    · intro hy
      obtain ⟨y₀, hy₀, hy⟩ := Finset.mem_map.mp hy
      obtain ⟨u, hu, huy⟩ := Finset.mem_image.mp hy₀
      exact ⟨u, hu, hy.symm.trans (congrArg Subtype.val huy.symm)⟩
    · rintro ⟨u, hu, rfl⟩
      apply Finset.mem_map.mpr
      exact ⟨hq.next u, Finset.mem_image.mpr ⟨u, hu, rfl⟩, rfl⟩
  have hNadj : ∀ u : C, u ∈ N → G.Adj x u.1 := by
    intro u hu
    obtain ⟨w, -, hw⟩ := Finset.mem_map.mp hu
    have hxw : G.Adj x w.1 := (G.mem_neighborFinset x w.1).mp w.2
    rw [← hw]
    exact hxw
  have hnotAdjNext : ∀ u : C, u ∈ N → ¬ G.Adj x (hq.next u).1 := by
    intro u hu h
    have hxu := hNadj u hu
    let r : G.Walk (u : V) (hq.next u : C) :=
      hxu.symm.toWalk.concat h
    have hr : r.IsPath := by
      apply hxu.symm.isPath_toWalk.concat
      · simp only [hxu.symm.support_toWalk, List.mem_cons,
          List.not_mem_nil, or_false]
        intro hmem
        rcases hmem with hEq | hEq
        · exact hq.next_ne (Subtype.ext hEq)
        · exact hxC (hEq ▸ (hq.next u).2)
    have hrsupport : ∀ w ∈ r.support,
        w = (u : V) ∨ w = (hq.next u : C) ∨ w ∉ C := by
      intro w hw
      simp only [r, SimpleGraph.Walk.support_concat,
        hxu.symm.support_toWalk, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      rcases hw with (rfl | rfl) | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hxC)
      · exact Or.inr (Or.inl rfl)
    exact ChvatalErdos.next_ne_of_exterior_path_of_longest q hq
      hq.next_ne.symm r hr (by simp [r]) hrsupport hmaxq rfl
  have hnotAdjNextPair : ∀ u v : C, u ∈ N → v ∈ N → u ≠ v →
      ¬ G.Adj (hq.next u).1 (hq.next v).1 := by
    intro u v hu hv huv
    have hxu := hNadj u hu
    have hxv := hNadj v hv
    let r : G.Walk (u : V) (v : V) := hxu.symm.toWalk.concat hxv
    have hr : r.IsPath := by
      apply hxu.symm.isPath_toWalk.concat
      · simp only [hxu.symm.support_toWalk, List.mem_cons,
          List.not_mem_nil, or_false]
        intro hmem
        rcases hmem with hEq | hEq
        · exact huv (Subtype.ext hEq.symm)
        · exact hxC (hEq ▸ v.2)
    have hrsupport : ∀ w ∈ r.support,
        w = (u : V) ∨ w = (v : V) ∨ w ∉ C := by
      intro w hw
      simp only [r, SimpleGraph.Walk.support_concat,
        hxu.symm.support_toWalk, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      rcases hw with (rfl | rfl) | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hxC)
      · exact Or.inr (Or.inl rfl)
    exact ChvatalErdos.not_adj_next_of_exterior_path_of_longest q hq
      huv r hr (by simp [r]) hrsupport hmaxq
  have hSindep : G.IsIndepSet (insert x S : Set V) := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff] at ha hb
    rcases ha with ha | haS
    · subst a
      rcases hb with hb | hbS
      · subst b
        exact (hab rfl).elim
      · obtain ⟨u, hu, rfl⟩ := (hmemS b).mp hbS
        exact hnotAdjNext u hu
    · rcases hb with hb | hbS
      · subst b
        obtain ⟨u, hu, rfl⟩ := (hmemS a).mp haS
        exact fun hadj ↦ hnotAdjNext u hu hadj.symm
      · obtain ⟨u, hu, hau⟩ := (hmemS a).mp haS
        obtain ⟨v, hv, hbv⟩ := (hmemS b).mp hbS
        have huv : u ≠ v := by
          intro huv
          apply hab
          rw [hau, hbv, huv]
        intro hadj
        apply hnotAdjNextPair u v hu hv huv
        simpa [hau, hbv] using hadj
  have hcardInsert : k + 1 ≤ (insert x S).card := by
    rw [Finset.card_insert_of_notMem hxS, hScard]
    have := hdegree x
    omega
  obtain ⟨A, hA, hAcard⟩ := Finset.exists_subset_card_eq hcardInsert
  refine ⟨A, hAcard, hSindep.mono ?_⟩
  intro y hy
  rw [Set.mem_insert_iff]
  exact Finset.mem_insert.mp (hA hy)

/-! ## Nash--Williams--Bondy alternative -/

/-- The finite Nash--Williams--Bondy theorem in the rounded form used by
the KSS stability argument. -/
theorem hamiltonian_or_separation_or_independent
    {k : ℕ} (hCard : 3 < Fintype.card V)
    (hThird : Fintype.card V + 2 < 3 * k)
    (hDegree : ∀ v : V, k ≤ G.degree v) :
    G.IsHamiltonian ∨ HasSeparationWitness G ∨
      HasIndependentSetAt G (k + 1) := by
  by_cases hSep : HasSeparationWitness G
  · exact Or.inr (Or.inl hSep)
  have hTwo : Erdos58.TwoConnected G :=
    twoConnected_of_not_separated (by omega) hSep
  obtain ⟨z, c, hc, hmax⟩ := exists_isLongestCycle hTwo
  by_cases hspan : c.support.toFinset = (Finset.univ : Finset V)
  · exact Or.inl (isHamiltonian_of_cycle_support_eq_univ hc hspan)
  · right; right
    exact independent_set_of_longest_cycle_complement_independent
      c hc (fun z' c' hc' ↦ hmax c' hc') hspan
      (longest_cycle_complement_isIndepSet hTwo hThird hDegree hc hmax)
      hDegree

end

end NashWilliamsBondy
end Erdos622
