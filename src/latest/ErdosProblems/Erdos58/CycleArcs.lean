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

The definitions `IsArm`, `ArmsDisj`, and the indexed-arc proof below are
adapted from `ListColoring.RubinCases` at commit
80a728c86f28222a58b11a777f9d22419fd2fb69 of
https://github.com/rkirov/list-color-function, released under Apache 2.0.
-/
import ErdosProblems.Erdos58.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# The two complementary arcs of a cycle

This file turns a `SimpleGraph.Walk.IsCycle` and two distinct vertices on it
into its two complementary arcs.  Two interfaces are supplied:

* `exists_arcs_of_cycle` gives explicitly indexed arms, which is convenient
  for length calculations and splicing constructions;
* `exists_path_arcs_of_cycle` gives actual Mathlib walks, proves that both are
  simple paths of positive length, and records support and edge exhaustion.

The construction rotates the cycle to begin at the first endpoint and splits
at the first occurrence of the second endpoint.
-/

open Set
open scoped SimpleGraph

namespace Erdos58

variable {V : Type*} {G : SimpleGraph V}

/-- `IsArm G s t P k` says that `P 0, ..., P k` is a simple path in `G`
from `s` to `t`, of positive length `k`. -/
def IsArm (G : SimpleGraph V) (s t : V) (P : ℕ → V) (k : ℕ) : Prop :=
  1 ≤ k ∧ P 0 = s ∧ P k = t ∧ (∀ j, j < k → G.Adj (P j) (P (j + 1))) ∧
    (∀ j, 0 < j → j < k → P j ≠ s ∧ P j ≠ t) ∧
    (∀ j j', 0 < j → j < k → 0 < j' → j' < k → P j = P j' → j = j')

/-- Two indexed arms are internally vertex-disjoint. -/
def ArmsDisj (P : ℕ → V) (k : ℕ) (Q : ℕ → V) (l : ℕ) : Prop :=
  ∀ j j', 0 < j → j < k → 0 < j' → j' < l → P j ≠ Q j'

/-- Internal disjointness of arms is symmetric. -/
theorem ArmsDisj.symm {P Q : ℕ → V} {k l : ℕ}
    (h : ArmsDisj P k Q l) : ArmsDisj Q l P k :=
  fun j j' hj hjk hj' hj'k e ↦ h j' j hj' hj'k hj hjk e.symm

/-- A path walk, indexed by `Walk.getVert`, is an arm. -/
theorem isArm_of_walk {s t : V} (p : G.Walk s t) (hp : p.IsPath) (hst : s ≠ t) :
    IsArm G s t p.getVert p.length := by
  have hinj := hp.getVert_injOn
  refine ⟨?_, p.getVert_zero, p.getVert_length, fun j hj ↦ p.adj_getVert_succ hj, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos p.length with h | h
    · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h) hst
    · exact h
  · intro j hj0 hjl
    constructor
    · intro he
      have : j = 0 := hinj (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) (by rw [he, p.getVert_zero])
      omega
    · intro he
      have : j = p.length := hinj (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) (by rw [he, p.getVert_length])
      omega
  · intro j j' _ hjl _ hj'l he
    exact hinj (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) he

/-- Two simple paths that meet only at their common endpoints give internally
disjoint indexed arms. -/
theorem armsDisj_of_walks {s t : V} (p q : G.Walk s t) (hp : p.IsPath) (hst : s ≠ t)
    (h : ∀ x ∈ p.support, x ∈ q.support → x = s ∨ x = t) :
    ArmsDisj p.getVert p.length q.getVert q.length := by
  intro j j' hj0 hjl hj0' hj'l he
  have hmem : p.getVert j ∈ q.support := he ▸ q.getVert_mem_support j'
  rcases h _ (p.getVert_mem_support j) hmem with hs | ht
  · exact (isArm_of_walk p hp hst).2.2.2.2.1 j hj0 hjl |>.1 hs
  · exact (isArm_of_walk p hp hst).2.2.2.2.1 j hj0 hjl |>.2 ht

/-- A step of a walk is one of its edges. -/
theorem getVert_mem_edges {x y : V} (p : G.Walk x y) : ∀ {i : ℕ}, i < p.length →
    s(p.getVert i, p.getVert (i + 1)) ∈ p.edges := by
  induction p with
  | nil => intro i hi; simp at hi
  | @cons u v w h q ih =>
      intro i hi
      cases i with
      | zero => simp
      | succ i =>
          simp only [SimpleGraph.Walk.length_cons] at hi
          simp only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.edges_cons,
            List.mem_cons]
          exact Or.inr (ih (by omega))

/-- The two indexed arcs of a cycle between two distinct vertices.

The arcs have positive lengths adding to the cycle length, are internally
disjoint simple arms, use only vertices and edges of the cycle, and together
exhaust the cycle support. -/
theorem exists_arcs_of_cycle {v : V} {c : G.Walk v v} (hc : c.IsCycle) {a b : V}
    (ha : a ∈ c.support) (hb : b ∈ c.support) (hab : a ≠ b) :
    ∃ (A B : ℕ → V) (α β : ℕ), 1 ≤ α ∧ 1 ≤ β ∧ α + β = c.length ∧
      IsArm G a b A α ∧ IsArm G a b B β ∧ ArmsDisj A α B β ∧
      (∀ t, t ≤ α → A t ∈ c.support) ∧ (∀ t, t ≤ β → B t ∈ c.support) ∧
      (∀ t, t < α → s(A t, A (t + 1)) ∈ c.edges) ∧
      (∀ t, t < β → s(B t, B (t + 1)) ∈ c.edges) ∧
      (∀ x, x ∈ c.support →
        (∃ t, t ≤ α ∧ A t = x) ∨ (∃ t, t ≤ β ∧ B t = x)) := by
  classical
  set c' : G.Walk a a := c.rotate a ha with hc'def
  have hc' : c'.IsCycle := (SimpleGraph.Walk.isCycle_rotate ha).mpr hc
  have hlen : c'.length = c.length := SimpleGraph.Walk.length_rotate c a ha
  have hmem : ∀ x : V, x ∈ c'.support ↔ x ∈ c.support := fun x ↦
    SimpleGraph.Walk.mem_support_rotate_iff c a ha
  have hedg : ∀ e : Sym2 V, e ∈ c'.edges ↔ e ∈ c.edges := fun _ ↦
    (SimpleGraph.Walk.rotate_edges c a ha).mem_iff
  set L : ℕ := c'.length with hLdef
  have h3 : 3 ≤ L := hc'.three_le_length
  have hinj : Set.InjOn c'.getVert {i | i ≤ L - 1} := hc'.getVert_injOn'
  have h0 : c'.getVert 0 = a := c'.getVert_zero
  have hLa : c'.getVert L = a := c'.getVert_length
  obtain ⟨j, hjget, hjle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ((hmem b).mpr hb)
  have hj0 : j ≠ 0 := by rintro rfl; exact hab (h0.symm.trans hjget)
  have hjL : j ≠ L := by rintro rfl; exact hab (hLa.symm.trans hjget)
  have hjlt : j < L := lt_of_le_of_ne hjle hjL
  have hj1 : 1 ≤ j := by omega
  refine ⟨c'.getVert, fun t ↦ c'.getVert (L - t), j, L - j, hj1, by omega,
    by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨hj1, h0, hjget, fun t ht ↦ c'.adj_getVert_succ (by omega), ?_, ?_⟩
    · intro t ht0 htj
      refine ⟨fun he ↦ ?_, fun he ↦ ?_⟩
      · have : t = 0 := hinj (by simp only [Set.mem_ofPred_eq]; omega)
          (by simp only [Set.mem_ofPred_eq]; omega) (by rw [he, h0])
        omega
      · have : t = j := hinj (by simp only [Set.mem_ofPred_eq]; omega)
          (by simp only [Set.mem_ofPred_eq]; omega) (by rw [he, ← hjget])
        omega
    · intro t t' _ htj _ ht'j he
      exact hinj (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) he
  · refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
    · show c'.getVert (L - 0) = a
      rw [Nat.sub_zero]
      exact hLa
    · show c'.getVert (L - (L - j)) = b
      rw [show L - (L - j) = j from by omega]
      exact hjget
    · intro t ht
      show G.Adj (c'.getVert (L - t)) (c'.getVert (L - (t + 1)))
      have hstep := c'.adj_getVert_succ (i := L - t - 1) (by omega)
      rw [show L - t - 1 + 1 = L - t from by omega] at hstep
      rw [show L - (t + 1) = L - t - 1 from by omega]
      exact hstep.symm
    · intro t ht0 htb
      show c'.getVert (L - t) ≠ a ∧ c'.getVert (L - t) ≠ b
      refine ⟨fun he ↦ ?_, fun he ↦ ?_⟩
      · have : L - t = 0 := hinj (by simp only [Set.mem_ofPred_eq]; omega)
          (by simp only [Set.mem_ofPred_eq]; omega) (by rw [he, h0])
        omega
      · have : L - t = j := hinj (by simp only [Set.mem_ofPred_eq]; omega)
          (by simp only [Set.mem_ofPred_eq]; omega) (by rw [he, ← hjget])
        omega
    · intro t t' _ htb _ ht'b he
      have he' : c'.getVert (L - t) = c'.getVert (L - t') := he
      have : L - t = L - t' := hinj (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) he'
      omega
  · intro t t' ht0 htj ht0' ht'b he
    have he' : c'.getVert t = c'.getVert (L - t') := he
    have : t = L - t' := hinj (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) he'
    omega
  · exact fun t _ ↦ (hmem _).mp (c'.getVert_mem_support t)
  · exact fun t _ ↦ (hmem _).mp (c'.getVert_mem_support (L - t))
  · exact fun t ht ↦ (hedg _).mp (getVert_mem_edges c' (by omega))
  · intro t ht
    show s(c'.getVert (L - t), c'.getVert (L - (t + 1))) ∈ c.edges
    have hstep := getVert_mem_edges c' (i := L - t - 1) (by omega)
    rw [show L - t - 1 + 1 = L - t from by omega] at hstep
    rw [show L - (t + 1) = L - t - 1 from by omega, Sym2.eq_swap]
    exact (hedg _).mp hstep
  · intro x hx
    obtain ⟨n, hn, hnL⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ((hmem x).mpr hx)
    rcases (by omega : n ≤ j ∨ j < n) with h | h
    · exact Or.inl ⟨n, h, hn⟩
    · refine Or.inr ⟨L - n, by omega, ?_⟩
      show c'.getVert (L - (L - n)) = x
      rw [show L - (L - n) = n from by omega]
      exact hn

/-- A walk-level version of the complementary-arc construction.

Both returned walks run from `a` to `b`.  They are nonempty simple paths,
their lengths sum to the cycle length, and their only possible common
vertices are their endpoints.  Their supports together exhaust the original
cycle support, and every arc edge belongs to the original cycle. -/
theorem exists_path_arcs_of_cycle {v : V} {c : G.Walk v v} (hc : c.IsCycle)
    {a b : V} (ha : a ∈ c.support) (hb : b ∈ c.support) (hab : a ≠ b) :
    ∃ (p q : G.Walk a b), p.IsPath ∧ q.IsPath ∧
      1 ≤ p.length ∧ 1 ≤ q.length ∧ p.length + q.length = c.length ∧
      (∀ x ∈ p.support, x ∈ q.support → x = a ∨ x = b) ∧
      (∀ x, x ∈ c.support ↔ x ∈ p.support ∨ x ∈ q.support) ∧
      (∀ e, e ∈ p.edges → e ∈ c.edges) ∧
      (∀ e, e ∈ q.edges → e ∈ c.edges) := by
  classical
  let c' : G.Walk a a := c.rotate a ha
  have hc' : c'.IsCycle := (SimpleGraph.Walk.isCycle_rotate ha).mpr hc
  have hb' : b ∈ c'.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c a ha).mpr hb
  let p : G.Walk a b := c'.takeUntil b hb'
  let r : G.Walk b a := c'.dropUntil b hb'
  let q : G.Walk a b := r.reverse
  have hdecomp : p.append r = c' := by
    exact c'.take_spec hb'
  have hpPath : p.IsPath := hc'.isPath_takeUntil hb'
  have happCycle : (p.append r).IsCycle := by
    rw [hdecomp]
    exact hc'
  have hrPath : r.IsPath := by
    exact happCycle.isPath_of_append_right (SimpleGraph.Walk.not_nil_of_ne hab)
  have hqPath : q.IsPath := hrPath.reverse
  have hpPos : 1 ≤ p.length := by
    have : 0 < p.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp
      (SimpleGraph.Walk.not_nil_of_ne hab)
    omega
  have hqPos : 1 ≤ q.length := by
    have : 0 < r.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp
      (SimpleGraph.Walk.not_nil_of_ne hab.symm)
    have : 1 ≤ r.length := by omega
    simpa [q] using this
  have hlen : p.length + q.length = c.length := by
    have := congrArg SimpleGraph.Walk.length hdecomp
    simpa [q, c', SimpleGraph.Walk.length_rotate] using this
  have htailNodup : (p.support.tail ++ r.support.tail).Nodup := by
    rw [← SimpleGraph.Walk.tail_support_append]
    rw [hdecomp]
    exact hc'.support_nodup
  have hmeet : ∀ x ∈ p.support, x ∈ q.support → x = a ∨ x = b := by
    intro x hxp hxq
    by_contra h
    push Not at h
    have hxpt : x ∈ p.support.tail :=
      (SimpleGraph.Walk.mem_support_iff p).mp hxp |>.resolve_left h.1
    have hxr : x ∈ r.support := by
      simpa [q, SimpleGraph.Walk.support_reverse] using hxq
    have hxrt : x ∈ r.support.tail :=
      (SimpleGraph.Walk.mem_support_iff r).mp hxr |>.resolve_left h.2
    exact (List.disjoint_of_nodup_append htailNodup hxpt hxrt)
  have hsupp : ∀ x, x ∈ c.support ↔ x ∈ p.support ∨ x ∈ q.support := by
    intro x
    rw [← SimpleGraph.Walk.mem_support_rotate_iff c a ha]
    change x ∈ c'.support ↔ x ∈ p.support ∨ x ∈ q.support
    rw [← hdecomp, SimpleGraph.Walk.mem_support_append_iff]
    simp only [q, SimpleGraph.Walk.support_reverse, List.mem_reverse]
  have hedg : ∀ e : Sym2 V, e ∈ c'.edges ↔ e ∈ c.edges := fun _ ↦
    (SimpleGraph.Walk.rotate_edges c a ha).mem_iff
  have hpEdges : ∀ e, e ∈ p.edges → e ∈ c.edges := by
    intro e he
    apply (hedg e).mp
    exact SimpleGraph.Walk.edges_takeUntil_subset_edges c' hb' he
  have hqEdges : ∀ e, e ∈ q.edges → e ∈ c.edges := by
    intro e he
    apply (hedg e).mp
    apply SimpleGraph.Walk.edges_dropUntil_subset_edges c' hb'
    simpa [q, SimpleGraph.Walk.edges_reverse] using he
  exact ⟨p, q, hpPath, hqPath, hpPos, hqPos, hlen, hmeet, hsupp, hpEdges, hqEdges⟩

end Erdos58
