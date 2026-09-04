/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 57.
https://www.erdosproblems.com/forum/thread/57

Informal authors:
- Paul Erdős
- András Hajnal
- Hong Liu
- Richard Montgomery

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos57.md
-/
/-
This is a Lean formalization of the solution to Erdős Problem 57.
https://www.erdosproblems.com/57

Informal authors:
- Erdős and Hajnal (conjecture)
- Hong Liu and Richard Montgomery (proof)

Formal author:
- OpenAI Codex
-/

import Mathlib
import ErdosProblems.Erdos58.Bipartite
import ErdosProblems.Erdos760
import ErdosProblems.Erdos63.Bridges
import ErdosProblems.Erdos63.ExactPaths
import ErdosProblems.Erdos63.ExpanderExtraction
import ErdosProblems.Erdos63.Subdivision

namespace Erdos57

open scoped BigOperators

open Set Filter Topology

attribute [local instance] Classical.decEq

/-- `G` has a (simple) cycle with exactly `n` edges. -/
def HasCycleLength {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = n

/-- A closed walk of length at least three whose only repeated support
vertex is its base point is a simple cycle.  This support-oriented constructor
is convenient when a cycle is assembled by concatenating several paths. -/
lemma isCycle_of_three_le_length_of_tail_support_nodup {V : Type*}
    {G : SimpleGraph V} {v : V} (w : G.Walk v v)
    (hlen : 3 ≤ w.length) (hsupp : w.support.tail.Nodup) : w.IsCycle := by
  cases w with
  | nil => simp at hlen
  | @cons _ u _ huv p =>
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      have hpPath : p.IsPath := SimpleGraph.Walk.IsPath.mk' (by simpa using hsupp)
      refine ⟨hpPath, ?_⟩
      intro hedge
      rw [Sym2.eq_swap] at hedge
      have hpLen : p.length = 1 := hpPath.length_eq_one_of_mem_edges hedge
      simp [hpLen] at hlen

lemma SimpleGraph.Walk.IsPath.start_not_mem_tail_support {V : Type*}
    {G : SimpleGraph V} {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    u ∉ p.support.tail := by
  have hn := hp.support_nodup
  rw [← p.cons_tail_support] at hn
  exact (List.nodup_cons.mp hn).1

lemma SimpleGraph.Walk.mem_dropLast_support_or_eq_end {V : Type*}
    {G : SimpleGraph V} {u v x : V} (p : G.Walk u v)
    (hx : x ∈ p.support) : x ∈ p.support.dropLast ∨ x = v := by
  have hdecomp := List.dropLast_append_getLast p.support_ne_nil
  have hx' : x ∈ p.support.dropLast ∨
      x = p.support.getLast p.support_ne_nil := by
    rw [← hdecomp] at hx
    rw [List.mem_append, List.mem_singleton] at hx
    exact hx
  simpa using hx'

/-- Build a cycle directly from its cyclic vertex list.  The list contains
the base vertex at both ends; all other occurrences are required to be
distinct. -/
lemma hasCycleLength_of_cyclic_support {V : Type*} {G : SimpleGraph V}
    (l : List V) (hne : l ≠ []) (hchain : l.IsChain G.Adj)
    (hclosed : l.getLast hne = l.head hne)
    (hlen : 4 ≤ l.length) (hnodup : l.tail.Nodup) :
    HasCycleLength G (l.length - 1) := by
  let p := SimpleGraph.Walk.ofSupport l hne hchain
  let c : G.Walk (l.head hne) (l.head hne) := p.copy rfl hclosed
  refine ⟨l.head hne, c, ?_, ?_⟩
  · apply isCycle_of_three_le_length_of_tail_support_nodup c
    · simp [c, p]
      omega
    · simpa [c, p] using hnodup
  · simp [c, p]

/-! ### Extremal contacts of a path with a finite carrier -/

/-- Positions along a walk at which a vertex predicate holds. -/
noncomputable def walkPositionsIn {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S : V → Prop) : Finset ℕ := by
  classical
  exact (Finset.range (p.length + 1)).filter fun i => S (p.getVert i)

@[simp] lemma mem_walkPositionsIn_iff {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S : V → Prop) (i : ℕ) :
    i ∈ walkPositionsIn p S ↔ i ≤ p.length ∧ S (p.getVert i) := by
  classical
  simp [walkPositionsIn]

lemma walkPositionsIn_nonempty_of_start {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S : V → Prop) (hu : S u) :
    (walkPositionsIn p S).Nonempty := by
  refine ⟨0, ?_⟩
  simp [hu]

/-- Last position of a walk lying in `S`, when its initial vertex lies in
`S`. -/
noncomputable def walkLastPositionIn {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S : V → Prop) (hu : S u) : ℕ :=
  (walkPositionsIn p S).max' (walkPositionsIn_nonempty_of_start p S hu)

lemma walkLastPositionIn_mem {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S : V → Prop) (hu : S u) :
    walkLastPositionIn p S hu ∈ walkPositionsIn p S := by
  exact Finset.max'_mem _ _

lemma walkLastPositionIn_le_length {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S : V → Prop) (hu : S u) :
    walkLastPositionIn p S hu ≤ p.length :=
  (mem_walkPositionsIn_iff p S _).mp (walkLastPositionIn_mem p S hu) |>.1

lemma walkLastPositionIn_vertex_mem {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S : V → Prop) (hu : S u) :
    S (p.getVert (walkLastPositionIn p S hu)) :=
  (mem_walkPositionsIn_iff p S _).mp (walkLastPositionIn_mem p S hu) |>.2

lemma le_walkLastPositionIn {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S : V → Prop) (hu : S u)
    {i : ℕ} (hi : i ≤ p.length) (hiS : S (p.getVert i)) :
    i ≤ walkLastPositionIn p S hu := by
  apply Finset.le_max' (walkPositionsIn p S)
  exact (mem_walkPositionsIn_iff p S i).2 ⟨hi, hiS⟩

/-- Positions satisfying `S` are also nonempty when the terminal vertex
does, and hence have a first position. -/
lemma walkPositionsIn_nonempty_of_end {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S : V → Prop) (hv : S v) :
    (walkPositionsIn p S).Nonempty := by
  refine ⟨p.length, ?_⟩
  rw [mem_walkPositionsIn_iff]
  simpa using hv

noncomputable def walkFirstPositionIn {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S : V → Prop) (hv : S v) : ℕ :=
  (walkPositionsIn p S).min' (walkPositionsIn_nonempty_of_end p S hv)

lemma walkFirstPositionIn_mem {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S : V → Prop) (hv : S v) :
    walkFirstPositionIn p S hv ∈ walkPositionsIn p S := by
  exact Finset.min'_mem _ _

lemma walkFirstPositionIn_le_length {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S : V → Prop) (hv : S v) :
    walkFirstPositionIn p S hv ≤ p.length :=
  (mem_walkPositionsIn_iff p S _).mp (walkFirstPositionIn_mem p S hv) |>.1

lemma walkFirstPositionIn_vertex_mem {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S : V → Prop) (hv : S v) :
    S (p.getVert (walkFirstPositionIn p S hv)) :=
  (mem_walkPositionsIn_iff p S _).mp (walkFirstPositionIn_mem p S hv) |>.2

lemma walkFirstPositionIn_le {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S : V → Prop) (hv : S v)
    {i : ℕ} (hi : i ≤ p.length) (hiS : S (p.getVert i)) :
    walkFirstPositionIn p S hv ≤ i := by
  apply Finset.min'_le
  exact (mem_walkPositionsIn_iff p S i).2 ⟨hi, hiS⟩

lemma walkLastPositionIn_lt_length_of_end_not_mem
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (S : V → Prop) (hu : S u) (hv : ¬S v) :
    walkLastPositionIn p S hu < p.length := by
  have hle := walkLastPositionIn_le_length p S hu
  have hmem := walkLastPositionIn_vertex_mem p S hu
  by_contra h
  have heq : walkLastPositionIn p S hu = p.length := by omega
  rw [heq, SimpleGraph.Walk.getVert_length] at hmem
  exact hv hmem

lemma walkFirstPositionIn_pos_of_start_not_mem
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (S : V → Prop) (hv : S v) (hu : ¬S u) :
    0 < walkFirstPositionIn p S hv := by
  have hmem := walkFirstPositionIn_vertex_mem p S hv
  by_contra h
  have heq : walkFirstPositionIn p S hv = 0 := by omega
  rw [heq, SimpleGraph.Walk.getVert_zero] at hmem
  exact hu hmem

/-- Suffix beginning at the final contact with `S`. -/
noncomputable def walkAfterLastIn {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S : V → Prop) (hu : S u) :
    G.Walk (p.getVert (walkLastPositionIn p S hu)) v :=
  p.drop (walkLastPositionIn p S hu)

/-- From a walk beginning in `S` and ending in `T`, retain the segment from
its last `S`-contact to its first subsequent `T`-contact. -/
noncomputable def trimWalkBetween {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S T : V → Prop) (hu : S u) (hv : T v) :
    G.Walk (p.getVert (walkLastPositionIn p S hu))
      ((walkAfterLastIn p S hu).getVert
        (walkFirstPositionIn (walkAfterLastIn p S hu) T hv)) :=
  (walkAfterLastIn p S hu).take
    (walkFirstPositionIn (walkAfterLastIn p S hu) T hv)

lemma walkAfterLastIn_isPath {V : Type*} {G : SimpleGraph V}
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (S : V → Prop) (hu : S u) : (walkAfterLastIn p S hu).IsPath := by
  exact hp.drop _

lemma trimWalkBetween_isPath {V : Type*} {G : SimpleGraph V}
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (S T : V → Prop) (hu : S u) (hv : T v) :
    (trimWalkBetween p S T hu hv).IsPath := by
  exact (walkAfterLastIn_isPath hp S hu).take _

lemma trimWalkBetween_start_mem {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S T : V → Prop) (hu : S u) (hv : T v) :
    S (p.getVert (walkLastPositionIn p S hu)) :=
  walkLastPositionIn_vertex_mem p S hu

lemma trimWalkBetween_end_mem {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S T : V → Prop) (hu : S u) (hv : T v) :
    T ((walkAfterLastIn p S hu).getVert
      (walkFirstPositionIn (walkAfterLastIn p S hu) T hv)) :=
  walkFirstPositionIn_vertex_mem (walkAfterLastIn p S hu) T hv

lemma trimWalkBetween_getVert_length {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S T : V → Prop) (hu : S u) (hv : T v) :
    (trimWalkBetween p S T hu hv).getVert
        (trimWalkBetween p S T hu hv).length =
      (walkAfterLastIn p S hu).getVert
        (walkFirstPositionIn (walkAfterLastIn p S hu) T hv) := by
  simp [trimWalkBetween,
    walkFirstPositionIn_le_length (walkAfterLastIn p S hu) T hv]

lemma trimWalkBetween_length_le {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S T : V → Prop) (hu : S u) (hv : T v) :
    (trimWalkBetween p S T hu hv).length ≤ p.length := by
  calc
    (trimWalkBetween p S T hu hv).length ≤ (walkAfterLastIn p S hu).length := by
      simp [trimWalkBetween]
    _ ≤ p.length := by
      simp [walkAfterLastIn]

lemma trimWalkBetween_support_subset {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S T : V → Prop) (hu : S u) (hv : T v) :
    ∀ x ∈ (trimWalkBetween p S T hu hv).support, x ∈ p.support := by
  intro x hx
  rw [trimWalkBetween, SimpleGraph.Walk.support_take] at hx
  have hxAfter : x ∈ (walkAfterLastIn p S hu).support :=
    List.mem_of_mem_take hx
  rw [walkAfterLastIn,
    SimpleGraph.Walk.drop_support_eq_support_drop_min] at hxAfter
  exact List.mem_of_mem_drop hxAfter

lemma trimWalkBetween_endpoints_ne_of_disjoint {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S T : Finset V) (hu : u ∈ S) (hv : v ∈ T)
    (hST : Disjoint S T) :
    p.getVert (walkLastPositionIn p (fun x => x ∈ S) hu) ≠
      (walkAfterLastIn p (fun x => x ∈ S) hu).getVert
        (walkFirstPositionIn (walkAfterLastIn p (fun x => x ∈ S) hu)
          (fun x => x ∈ T) hv) := by
  intro heq
  have hs : p.getVert (walkLastPositionIn p (fun x => x ∈ S) hu) ∈ S :=
    trimWalkBetween_start_mem p (fun x => x ∈ S) (fun x => x ∈ T) hu hv
  have ht : p.getVert (walkLastPositionIn p (fun x => x ∈ S) hu) ∈ T := by
    rw [heq]
    exact trimWalkBetween_end_mem p (fun x => x ∈ S) (fun x => x ∈ T) hu hv
  exact (Finset.disjoint_left.mp hST) hs ht

lemma trimWalkBetween_length_eq_firstPosition {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S T : V → Prop) (hu : S u) (hv : T v) :
    (trimWalkBetween p S T hu hv).length =
      walkFirstPositionIn (walkAfterLastIn p S hu) T hv := by
  rw [trimWalkBetween, SimpleGraph.Walk.take_length,
    inf_eq_left.mpr (walkFirstPositionIn_le_length (walkAfterLastIn p S hu) T hv)]

lemma trimWalkBetween_pos_of_disjoint {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S T : Finset V) (hu : u ∈ S) (hv : v ∈ T)
    (hST : Disjoint S T) :
    0 < (trimWalkBetween p (fun x => x ∈ S) (fun x => x ∈ T) hu hv).length := by
  rw [trimWalkBetween_length_eq_firstPosition]
  apply walkFirstPositionIn_pos_of_start_not_mem
  intro hT
  have hS := walkLastPositionIn_vertex_mem p (fun x => x ∈ S) hu
  exact (Finset.disjoint_left.mp hST) hS hT

/-- After the initial vertex of the trimmed walk, no vertex lies in the
starting carrier. -/
lemma trimWalkBetween_getVert_not_mem_start {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S T : V → Prop) (hu : S u) (hv : T v)
    (i : ℕ) (hi0 : 0 < i)
    (hi : i ≤ (trimWalkBetween p S T hu hv).length) :
    ¬S ((trimWalkBetween p S T hu hv).getVert i) := by
  intro hiS
  have hib : i ≤ walkFirstPositionIn (walkAfterLastIn p S hu) T hv := by
    rwa [trimWalkBetween_length_eq_firstPosition] at hi
  have hiAfter :
      (trimWalkBetween p S T hu hv).getVert i =
        (walkAfterLastIn p S hu).getVert i := by
    simp [trimWalkBetween, inf_eq_right.mpr hib]
  have hiafterLen : i ≤ (walkAfterLastIn p S hu).length :=
    hib.trans (walkFirstPositionIn_le_length (walkAfterLastIn p S hu) T hv)
  have ha := walkLastPositionIn_le_length p S hu
  have hisub : i ≤ p.length - walkLastPositionIn p S hu := by
    simpa [walkAfterLastIn] using hiafterLen
  have hai : walkLastPositionIn p S hu + i ≤ p.length := by
    omega
  have hiOriginal :
      S (p.getVert (walkLastPositionIn p S hu + i)) := by
    rw [← SimpleGraph.Walk.drop_getVert, ← walkAfterLastIn, ← hiAfter]
    exact hiS
  have hmax := le_walkLastPositionIn p S hu hai hiOriginal
  omega

/-- Before the terminal vertex of the trimmed walk, no vertex lies in the
ending carrier. -/
lemma trimWalkBetween_getVert_not_mem_end {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (S T : V → Prop) (hu : S u) (hv : T v)
    (i : ℕ) (hi : i < (trimWalkBetween p S T hu hv).length) :
    ¬T ((trimWalkBetween p S T hu hv).getVert i) := by
  intro hiT
  have hib : i < walkFirstPositionIn (walkAfterLastIn p S hu) T hv := by
    rwa [trimWalkBetween_length_eq_firstPosition] at hi
  have hiAfter :
      (trimWalkBetween p S T hu hv).getVert i =
        (walkAfterLastIn p S hu).getVert i := by
    simp [trimWalkBetween, inf_eq_right.mpr (Nat.le_of_lt hib)]
  have hfirst := walkFirstPositionIn_le (walkAfterLastIn p S hu) T hv
    (Nat.le_of_lt (hib.trans_le
      (walkFirstPositionIn_le_length (walkAfterLastIn p S hu) T hv)))
    (hiAfter ▸ hiT)
  omega

/-- The interior after the initial vertex of a trimmed path avoids the
starting carrier. -/
lemma trimWalkBetween_tail_support_not_mem_start {V : Type*} {G : SimpleGraph V}
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (S T : V → Prop) (hu : S u) (hv : T v) :
    ∀ x ∈ (trimWalkBetween p S T hu hv).support.tail, ¬S x := by
  let q := trimWalkBetween p S T hu hv
  have hqPath : q.IsPath := trimWalkBetween_isPath hp S T hu hv
  have hstart : q.getVert 0 ∉ q.support.tail := by
    rw [SimpleGraph.Walk.getVert_zero]
    have hn := hqPath.support_nodup
    rw [← q.cons_tail_support, List.nodup_cons] at hn
    exact hn.1
  intro x hx hiS
  have hxfull : x ∈ q.support := List.mem_of_mem_tail hx
  obtain ⟨i, hix, hi⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxfull
  have hi0 : 0 < i := by
    by_contra h
    have : i = 0 := by omega
    subst i
    exact hstart (hix ▸ hx)
  exact trimWalkBetween_getVert_not_mem_start p S T hu hv i hi0 hi
    (hix ▸ hiS)

/-- The interior before the terminal vertex of a trimmed path avoids the
ending carrier. -/
lemma trimWalkBetween_dropLast_support_not_mem_end {V : Type*}
    {G : SimpleGraph V} {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (S T : V → Prop) (hu : S u) (hv : T v) :
    ∀ x ∈ (trimWalkBetween p S T hu hv).support.dropLast, ¬T x := by
  let q := trimWalkBetween p S T hu hv
  have hqPath : q.IsPath := trimWalkBetween_isPath hp S T hu hv
  have hend : q.getVert q.length ∉ q.support.dropLast := by
    have hdecomp : q.support.dropLast ++ [q.getVert q.length] = q.support := by
      simpa only [SimpleGraph.Walk.getVert_length,
        SimpleGraph.Walk.getLast_support] using
        (List.dropLast_append_getLast q.support_ne_nil)
    have hn : (q.support.dropLast ++ [q.getVert q.length]).Nodup := by
      rw [hdecomp]
      exact hqPath.support_nodup
    rw [List.nodup_append] at hn
    intro hx
    exact hn.2.2 _ hx _ (by simp) rfl
  intro x hx hiT
  have hxfull : x ∈ q.support := List.mem_of_mem_dropLast hx
  obtain ⟨i, hix, hi⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxfull
  have hilength : i < q.length := by
    by_contra h
    have : i = q.length := by omega
    subst i
    exact hend (hix ▸ hx)
  exact trimWalkBetween_getVert_not_mem_end p S T hu hv i hilength
    (hix ▸ hiT)

/-! ### Concatenating a finite chain of walks -/

/-- Witness carried by the recursive concatenation.  Recording its endpoint,
length, and support facts together avoids exposing transports between equal
successive endpoints. -/
structure AppendWalkListResult {I V : Type*} (G : SimpleGraph V)
    (left right : I → V) (path : ∀ i, G.Walk (left i) (right i))
    (l : List I) (hne : l ≠ []) where
  firstVertex : V
  lastVertex : V
  walk : G.Walk firstVertex lastVertex
  firstVertex_eq : firstVertex = left (l.head hne)
  lastVertex_eq : lastVertex = right (l.getLast hne)
  length_eq : walk.length = (l.map fun i => (path i).length).sum
  tail_support_eq : walk.support.tail =
    (l.map fun i => (path i).support.tail).flatten
  support_subset : ∀ x ∈ walk.support, ∃ i ∈ l, x ∈ (path i).support
  edges_subset : ∀ e ∈ walk.edges, ∃ i ∈ l, e ∈ (path i).edges

/-- Recursive construction behind `appendWalkList`. -/
noncomputable def appendWalkListResult {I V : Type*} {G : SimpleGraph V}
    (left right : I → V) (path : ∀ i, G.Walk (left i) (right i)) :
    ∀ (l : List I) (hne : l ≠ []),
      l.IsChain (fun a b => right a = left b) →
      AppendWalkListResult G left right path l hne
  | [], hne, _ => (hne rfl).elim
  | [a], _, _ => {
      firstVertex := left a
      lastVertex := right a
      walk := path a
      firstVertex_eq := by simp
      lastVertex_eq := by simp
      length_eq := by simp
      tail_support_eq := by simp
      support_subset := by
        intro x hx
        exact ⟨a, by simp, hx⟩
      edges_subset := by
        intro e he
        exact ⟨a, by simp, he⟩
    }
  | a :: b :: rest, _, hchain => by
      have hab : right a = left b := (List.isChain_cons_cons.mp hchain).1
      have htail : (b :: rest).IsChain (fun x y => right x = left y) :=
        (List.isChain_cons_cons.mp hchain).2
      let q := appendWalkListResult left right path (b :: rest) (by simp) htail
      let q' : G.Walk (right a) q.lastVertex :=
        q.walk.copy (q.firstVertex_eq.trans hab.symm) rfl
      let w : G.Walk (left a) q.lastVertex := (path a).append q'
      exact {
        firstVertex := left a
        lastVertex := q.lastVertex
        walk := w
        firstVertex_eq := by simp
        lastVertex_eq := by simpa [q] using q.lastVertex_eq
        length_eq := by simp [w, q', q.length_eq]
        tail_support_eq := by
          simp [w, q', SimpleGraph.Walk.support_append,
            q.tail_support_eq, List.append_assoc]
        support_subset := by
          intro x hx
          simp only [w, SimpleGraph.Walk.support_append, List.mem_append] at hx
          rcases hx with hx | hx
          · exact ⟨a, by simp, hx⟩
          · obtain ⟨i, hi, hxi⟩ := q.support_subset x
              (by simpa [q'] using List.mem_of_mem_tail hx)
            exact ⟨i, by simp [hi], hxi⟩
        edges_subset := by
          intro e he
          simp only [w, SimpleGraph.Walk.edges_append, List.mem_append] at he
          rcases he with he | he
          · exact ⟨a, by simp, he⟩
          · obtain ⟨i, hi, hei⟩ := q.edges_subset e (by simpa [q'] using he)
            exact ⟨i, by simp [hi], hei⟩
      }

/-- Concatenate a nonempty list of walks whose successive endpoints agree.
The explicit list construction is useful below because complementary runs of
pieces are defined combinatorially before their connector paths are trimmed. -/
noncomputable def appendWalkList {I V : Type*} {G : SimpleGraph V}
    (left right : I → V) (path : ∀ i, G.Walk (left i) (right i))
    (l : List I) (hne : l ≠ [])
    (hchain : l.IsChain (fun a b => right a = left b)) :
    G.Walk (left (l.head hne)) (right (l.getLast hne)) :=
  let q := appendWalkListResult left right path l hne hchain
  q.walk.copy q.firstVertex_eq q.lastVertex_eq

@[simp] lemma appendWalkList_length {I V : Type*} {G : SimpleGraph V}
    (left right : I → V) (path : ∀ i, G.Walk (left i) (right i))
    (l : List I) (hne : l ≠ [])
    (hchain : l.IsChain (fun a b => right a = left b)) :
    (appendWalkList left right path l hne hchain).length =
      (l.map fun i => (path i).length).sum := by
  simpa [appendWalkList] using
    (appendWalkListResult left right path l hne hchain).length_eq

lemma appendWalkList_support_subset {I V : Type*} {G : SimpleGraph V}
    (left right : I → V) (path : ∀ i, G.Walk (left i) (right i))
    (l : List I) (hne : l ≠ [])
    (hchain : l.IsChain (fun a b => right a = left b)) :
    ∀ x ∈ (appendWalkList left right path l hne hchain).support,
      ∃ i ∈ l, x ∈ (path i).support := by
  simpa [appendWalkList] using
    (appendWalkListResult left right path l hne hchain).support_subset

@[simp] lemma appendWalkList_tail_support {I V : Type*} {G : SimpleGraph V}
    (left right : I → V) (path : ∀ i, G.Walk (left i) (right i))
    (l : List I) (hne : l ≠ [])
    (hchain : l.IsChain (fun a b => right a = left b)) :
    (appendWalkList left right path l hne hchain).support.tail =
      (l.map fun i => (path i).support.tail).flatten := by
  simpa [appendWalkList] using
    (appendWalkListResult left right path l hne hchain).tail_support_eq

lemma appendWalkList_tail_support_nodup {I V : Type*} {G : SimpleGraph V}
    (left right : I → V) (path : ∀ i, G.Walk (left i) (right i))
    (l : List I) (hne : l ≠ [])
    (hchain : l.IsChain (fun a b => right a = left b))
    (hlnodup : l.Nodup)
    (hpath : ∀ i, (path i).IsPath)
    (hdisjoint : ∀ i j, i ≠ j →
      List.Disjoint (path i).support.tail (path j).support.tail) :
    (appendWalkList left right path l hne hchain).support.tail.Nodup := by
  rw [appendWalkList_tail_support]
  apply List.nodup_flatten.mpr
  constructor
  · intro s hs
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
    exact (hpath i).support_nodup.tail
  · rw [List.pairwise_map]
    exact hlnodup.imp (fun hij => hdisjoint _ _ hij)

lemma appendWalkList_edges_subset {I V : Type*} {G : SimpleGraph V}
    (left right : I → V) (path : ∀ i, G.Walk (left i) (right i))
    (l : List I) (hne : l ≠ [])
    (hchain : l.IsChain (fun a b => right a = left b)) :
    ∀ e ∈ (appendWalkList left right path l hne hchain).edges,
      ∃ i ∈ l, e ∈ (path i).edges := by
  simpa [appendWalkList] using
    (appendWalkListResult left right path l hne hchain).edges_subset

/-- An injective relabelling commutes with cyclic list successor. -/
lemma list_map_next_of_injective {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (hf : Function.Injective f) (l : List X) (hn : l.Nodup)
    (x : X) (hx : x ∈ l) :
    (l.map f).next (f x) (List.mem_map.mpr ⟨x, hx, rfl⟩) =
      f (l.next x hx) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hiMap : i < (l.map f).length := by simpa
  have hlen : 0 < l.length := by omega
  have hmod : (i + 1) % l.length < l.length := Nat.mod_lt _ hlen
  have hmodMap : (i + 1) % (l.map f).length < (l.map f).length := by
    simpa using hmod
  calc
    (l.map f).next (f l[i]) _ =
        (l.map f).next ((l.map f)[i]'hiMap) (List.get_mem ..) := by
      congr 2 <;> simp
    _ = (l.map f)[(i + 1) % (l.map f).length]'hmodMap :=
      List.next_getElem (l.map f) (hn.map hf) i (by simpa)
    _ = f (l[(i + 1) % l.length]'hmod) := by simp
    _ = f (l.next l[i] (List.get_mem ..)) := by
      rw [List.next_getElem l hn i hi]

lemma list_next_eq_of_eq {X : Type*} [DecidableEq X]
    {l l' : List X} (h : l = l') (x : X) (hx : x ∈ l) (hx' : x ∈ l') :
    l.next x hx = l'.next x hx' := by
  subst l'
  rfl

lemma list_prev_eq_of_eq {X : Type*} [DecidableEq X]
    (l : List X) {x y : X} (hxy : x = y) (hx : x ∈ l) (hy : y ∈ l) :
    l.prev x hx = l.prev y hy := by
  subst y
  rfl

lemma list_head_eq_of_eq {X : Type*} {l l' : List X}
    (h : l = l') (hl : l ≠ []) (hl' : l' ≠ []) :
    l.head hl = l'.head hl' := by
  subst l'
  rfl

/-- If every element is related to its cyclic successor, every rotation is
linearly chained by that relation. -/
lemma list_rotate_isChain_of_rel_next {X : Type*} [DecidableEq X]
    (R : X → X → Prop) (l : List X) (hn : l.Nodup)
    (hnext : ∀ x (hx : x ∈ l), R x (l.next x hx)) (n : ℕ) :
    (l.rotate n).IsChain R := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hrot : l ~r l.rotate n := ⟨n, rfl⟩
  have hlen : (l.rotate n).length = l.length := List.length_rotate _ _
  have hilt : i < (l.rotate n).length := by omega
  let x := (l.rotate n)[i]
  have hxrot : x ∈ l.rotate n := List.get_mem _ _
  have hx : x ∈ l := hrot.mem_iff.mpr hxrot
  have hsame := List.isRotated_next_eq hrot hn hx
  have hnextRot := List.next_getElem (l.rotate n)
    (hrot.nodup_iff.mp hn) i hilt
  have hmod : (i + 1) % (l.rotate n).length = i + 1 :=
    Nat.mod_eq_of_lt hi
  have hnextRot' :
      (l.rotate n).next x hxrot = (l.rotate n)[i + 1] := by
    simpa [x, hmod] using hnextRot
  have hrel := hnext x hx
  rw [hsame, hnextRot'] at hrel
  simpa [x] using hrel

/-- A property implied by every right-hand element of a chain holds on the
whole tail. -/
lemma list_isChain_forall_mem_tail_of_right {X : Type*}
    {R : X → X → Prop} {P : X → Prop} {l : List X}
    (hchain : l.IsChain R) (hR : ∀ a b, R a b → P b) :
    ∀ b ∈ l.tail, P b := by
  intro b hb
  obtain ⟨i, hi, hib⟩ := List.getElem_of_mem hb
  have hisucc : i + 1 < l.length := by
    simp at hi
    omega
  have hrel := (List.isChain_iff_getElem.mp hchain) i hisucc
  have hb' : l[i + 1] = b := by simpa using hib
  rw [← hb']
  exact hR l[i] l[i + 1] hrel

/-- Inside a `splitBy` block which continues precisely when the next element
fails `p`, every element after the head fails `p`. -/
lemma splitBy_group_tail_not {X : Type*} (p : X → Prop) [DecidablePred p]
    (l g : List X)
    (hg : g ∈ l.splitBy (fun _ y => decide (¬p y))) :
    ∀ x ∈ g.tail, ¬p x := by
  apply list_isChain_forall_mem_tail_of_right
    (P := fun x => ¬p x) (List.isChain_of_mem_splitBy hg)
  intro a b hab
  simpa using hab

/-- If the original head satisfies `p`, then every block produced by
splitting immediately before the next `p`-element has a `p`-head. -/
lemma splitBy_group_head {X : Type*} (p : X → Prop) [DecidablePred p]
    (l : List X) (hne : l ≠ []) (hhead : p (l.head hne))
    (g : List X) (hg : g ∈ l.splitBy (fun _ y => decide (¬p y))) :
    p (g.head (List.ne_nil_of_mem_splitBy hg)) := by
  classical
  let r : X → X → Bool := fun _ y => decide (¬p y)
  let gs := l.splitBy r
  have hgsne : gs ≠ [] := (List.splitBy_ne_nil).2 hne
  have hchain := List.isChain_getLast_head_splitBy r l
  have htail : ∀ b ∈ gs.tail, ∀ hb : b ≠ [], p (b.head hb) := by
    apply list_isChain_forall_mem_tail_of_right
      (P := fun b => ∀ hb : b ≠ [], p (b.head hb)) hchain
    intro a b hab hb
    obtain ⟨ha, hb', hfalse⟩ := hab
    simpa [r] using hfalse
  by_cases hfirst : g = gs.head hgsne
  · subst g
    have hheads := List.head_head_splitBy r hne
    have hheads' :
        ((gs.head hgsne).head
          (List.ne_nil_of_mem_splitBy (List.head_mem hgsne))) = l.head hne := by
      simpa [gs] using hheads
    exact hheads'.symm ▸ hhead
  · have hgtail : g ∈ gs.tail := by
      have hg' : g ∈ gs := by exact hg
      cases hgs : gs with
      | nil => exact (hgsne hgs).elim
      | cons a rest =>
          simp only [hgs, List.head_cons] at hfirst
          rw [hgs] at hg'
          simp only [List.mem_cons] at hg'
          exact hg'.resolve_left hfirst
    exact htail g hgtail _

/-- Every `p`-element of the original list is the head of one of the blocks
which split immediately before `p`-elements. -/
lemma exists_splitBy_group_head_eq {X : Type*} (p : X → Prop)
    [DecidablePred p] (l : List X) (x : X) (hx : x ∈ l) (hpx : p x) :
    ∃ g, ∃ hg : g ∈ l.splitBy (fun _ y => decide (¬p y)),
      g.head (List.ne_nil_of_mem_splitBy hg) = x := by
  have hxflat : x ∈ (l.splitBy (fun _ y => decide (¬p y))).flatten := by
    simpa using hx
  obtain ⟨g, hg, hxg⟩ := List.mem_flatten.mp hxflat
  have hgne : g ≠ [] := List.ne_nil_of_mem_splitBy hg
  refine ⟨g, hg, ?_⟩
  cases g with
  | nil => exact (hgne rfl).elim
  | cons a rest =>
      simp only [List.head_cons]
      simp only [List.mem_cons] at hxg
      rcases hxg with hxa | hxrest
      · exact hxa.symm
      · have hnot := splitBy_group_tail_not p l (a :: rest) hg x hxrest
        exact (hnot hpx).elim

noncomputable def listRotateTo {X : Type*} [DecidableEq X]
    (l : List X) (x : X) : List X := l.rotate (l.idxOf x)

lemma listRotateTo_ne_nil {X : Type*} [DecidableEq X]
    (l : List X) (x : X) (hx : x ∈ l) : listRotateTo l x ≠ [] := by
  simpa [listRotateTo] using List.ne_nil_of_mem hx

lemma listRotateTo_head {X : Type*} [DecidableEq X]
    (l : List X) (x : X) (hx : x ∈ l) :
    (listRotateTo l x).head (listRotateTo_ne_nil l x hx) = x := by
  have hidx : l.idxOf x < l.length := List.idxOf_lt_length_of_mem hx
  apply Option.some.inj
  rw [← List.head?_eq_some_head (listRotateTo_ne_nil l x hx)]
  rw [listRotateTo, List.head?_rotate hidx, List.getElem?_idxOf hx]

lemma list_next_of_append_cons_cons {X : Type*} [DecidableEq X]
    (pre post : List X) (x y : X)
    (hn : (pre ++ x :: y :: post).Nodup) :
    (pre ++ x :: y :: post).next x (by simp) = y := by
  have hxpre : x ∉ pre := by
    intro hx
    exact (List.nodup_append.mp hn).2.2 x hx x (by simp) rfl
  rw [List.next_eq_getElem]
  have hlt : pre.length + 1 < (pre ++ x :: y :: post).length := by simp
  have hmod : (pre.length + 1) % (pre ++ x :: y :: post).length =
      pre.length + 1 := Nat.mod_eq_of_lt hlt
  simp only [List.idxOf_append_of_notMem hxpre, List.idxOf_cons_self,
    Nat.add_zero, hmod]
  simp

lemma list_next_of_append_singleton {X : Type*} [DecidableEq X]
    (pre : List X) (x : X) (hn : (pre ++ [x]).Nodup) :
    (pre ++ [x]).next x (by simp) =
      (pre ++ [x]).head (by simp) := by
  have hlast : (pre ++ [x]).getLast (by simp) = x := by simp
  simpa [hlast] using
    (List.next_getLast_eq_head (pre ++ [x]) (by simp) hn)

lemma list_getLast_tail_eq_getLast {X : Type*} {l : List X}
    (htail : l.tail ≠ []) :
    l.tail.getLast htail = l.getLast (by
      intro hl
      subst l
      exact htail rfl) := by
  cases l with
  | nil => exact (htail rfl).elim
  | cons a rest =>
      cases rest with
      | nil => exact (htail rfl).elim
      | cons b rest => rfl

/-- A set of cardinality at most two which contains two distinct points has
no third point. -/
lemma finset_mem_eq_of_card_le_two {X : Type*} [DecidableEq X]
    (s : Finset X) {a b x : X} (hcard : s.card ≤ 2)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hx : x ∈ s) :
    x = a ∨ x = b := by
  by_contra h
  push Not at h
  have hsub : ({a, b, x} : Finset X) ⊆ s := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hx
  have hthree : ({a, b, x} : Finset X).card = 3 := by
    simp [hab, h.1, h.2, Ne.symm h.1, Ne.symm h.2]
  have := Finset.card_le_card hsub
  rw [hthree] at this
  omega

/-- Two distinct successive points which close up under cyclic `next`
exhaust a noduplicated cyclic list. -/
lemma list_mem_of_two_cycle {X : Type*} [DecidableEq X]
    (l : List X) (hn : l.Nodup) {a b : X}
    (ha : a ∈ l) (hab : a ≠ b)
    (hAB : l.next a ha = b)
    (hBA : l.next b (hAB ▸ List.next_mem l a ha) = a) :
    ∀ x ∈ l, x = a ∨ x = b := by
  classical
  let r := listRotateTo l a
  have hrot : l ~r r := ⟨l.idxOf a, rfl⟩
  have hrn : r.Nodup := hrot.nodup_iff.mp hn
  have hra : a ∈ r := hrot.mem_iff.mp ha
  have hrb : b ∈ r := by
    rw [← hAB]
    exact hrot.mem_iff.mp (List.next_mem l a ha)
  have hrAB : r.next a hra = b :=
    (List.isRotated_next_eq hrot hn ha).symm.trans hAB
  have hrBA : r.next b hrb = a :=
    (List.isRotated_next_eq hrot hn
      (hAB ▸ List.next_mem l a ha)).symm.trans hBA
  have hhead : r.head (listRotateTo_ne_nil l a ha) = a :=
    listRotateTo_head l a ha
  have hre : r = [a, b] := by
    cases hr : r with
    | nil => exact (listRotateTo_ne_nil l a ha hr).elim
    | cons x xs =>
        have hxa : x = a := by simpa [hr] using hhead
        subst x
        cases hxs : xs with
        | nil =>
            have : a = b := by simpa [r, hr, hxs] using hrAB
            exact (hab this).elim
        | cons y ys =>
            have hyb : y = b := by simpa [r, hr, hxs] using hrAB
            subst y
            cases hys : ys with
            | nil => rfl
            | cons d ds =>
                have hshape : r = [a] ++ b :: d :: ds := by
                  simp [hr, hxs, hys]
                have hnext : r.next b hrb = d :=
                  (list_next_eq_of_eq hshape b hrb (by simp)).trans
                    (list_next_of_append_cons_cons [a] ds b d (by
                      simpa only [← hshape] using hrn))
                have hda : d = a := hnext.symm.trans hrBA
                have hnd := hrn
                rw [hr, hxs, hys] at hnd
                exact ((List.nodup_cons.mp hnd).1 (by simp [hda])).elim
  intro x hx
  have hxr : x ∈ r := hrot.mem_iff.mp hx
  simpa [hre] using hxr

/-- Three distinct successive points which close up under cyclic `next`
exhaust a noduplicated cyclic list. -/
lemma list_mem_of_three_cycle {X : Type*} [DecidableEq X]
    (l : List X) (hn : l.Nodup) {a b c : X}
    (ha : a ∈ l) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hAB : l.next a ha = b)
    (hBC : l.next b (hAB ▸ List.next_mem l a ha) = c)
    (hCA : l.next c (hBC ▸ List.next_mem l b (hAB ▸ List.next_mem l a ha)) = a) :
    ∀ x ∈ l, x = a ∨ x = b ∨ x = c := by
  classical
  let r := listRotateTo l a
  have hrot : l ~r r := ⟨l.idxOf a, rfl⟩
  have hrn : r.Nodup := hrot.nodup_iff.mp hn
  have hra : a ∈ r := hrot.mem_iff.mp ha
  have hrb : b ∈ r := by
    rw [← hAB]
    exact hrot.mem_iff.mp (List.next_mem l a ha)
  have hrc : c ∈ r := by
    rw [← hBC]
    exact hrot.mem_iff.mp
      (List.next_mem l b (hAB ▸ List.next_mem l a ha))
  have hrAB : r.next a hra = b :=
    (List.isRotated_next_eq hrot hn ha).symm.trans hAB
  have hrBC : r.next b hrb = c :=
    (List.isRotated_next_eq hrot hn
      (hAB ▸ List.next_mem l a ha)).symm.trans hBC
  have hrCA : r.next c hrc = a :=
    (List.isRotated_next_eq hrot hn
      (hBC ▸ List.next_mem l b (hAB ▸ List.next_mem l a ha))).symm.trans hCA
  have hhead : r.head (listRotateTo_ne_nil l a ha) = a :=
    listRotateTo_head l a ha
  have hre : r = [a, b, c] := by
    cases hr : r with
    | nil => exact (listRotateTo_ne_nil l a ha hr).elim
    | cons x xs =>
        have hxa : x = a := by simpa [hr] using hhead
        subst x
        cases hxs : xs with
        | nil =>
            have : a = b := by simpa [r, hr, hxs] using hrAB
            exact (hab this).elim
        | cons y ys =>
            have hyb : y = b := by simpa [r, hr, hxs] using hrAB
            subst y
            cases hys : ys with
            | nil =>
                have hshape : r = [a] ++ [b] := by simp [hr, hxs, hys]
                have hnext : r.next b hrb = a :=
                  (list_next_eq_of_eq hshape b hrb (by simp)).trans
                    (list_next_of_append_singleton [a] b (by
                      simpa only [← hshape] using hrn))
                have : a = c := hnext.symm.trans hrBC
                exact (hca this.symm).elim
            | cons z zs =>
                have hshape : r = [a] ++ b :: z :: zs := by
                  simp [hr, hxs, hys]
                have hnext : r.next b hrb = z :=
                  (list_next_eq_of_eq hshape b hrb (by simp)).trans
                    (list_next_of_append_cons_cons [a] zs b z (by
                      simpa only [← hshape] using hrn))
                have hzc : z = c := hnext.symm.trans hrBC
                cases hzs : zs with
                | nil =>
                    exact congrArg (fun t => [a, b, t]) hzc
                | cons d ds =>
                    have hnext : r.next c hrc = d := by
                      have hshape : r = [a, b] ++ c :: d :: ds := by
                        rw [hr, hxs, hys, hzc, hzs]
                        rfl
                      exact (list_next_eq_of_eq hshape c hrc (by simp)).trans
                        (list_next_of_append_cons_cons [a, b] ds c d (by
                          simpa only [← hshape] using hrn))
                    have hda : d = a := hnext.symm.trans hrCA
                    have hshape : r = a :: b :: c :: d :: ds := by
                      rw [hr, hxs, hys, hzc, hzs]
                    have hnd := hrn
                    rw [hshape] at hnd
                    have haNot : a ∉ b :: c :: d :: ds := (List.nodup_cons.mp hnd).1
                    exact (haNot (by simp [hda])).elim
  intro x hx
  have hxr : x ∈ r := hrot.mem_iff.mp hx
  rw [hre] at hxr
  simpa [eq_comm, or_assoc] using hxr

/-- `n` is the length of an odd cycle in `G`. -/
def IsOddCycleLength {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  Odd n ∧ HasCycleLength G n

/-- The reciprocal of `n` when `n` is an odd-cycle length of `G`, and zero otherwise. -/
noncomputable def oddCycleReciprocal {V : Type*} (G : SimpleGraph V) (n : ℕ) : ℝ :=
  by
    classical
    exact if IsOddCycleLength G n then (n : ℝ)⁻¹ else 0

lemma HasCycleLength.map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) {n : ℕ} (h : HasCycleLength G n) : HasCycleLength H n := by
  rcases h with ⟨v, c, hc, rfl⟩
  exact ⟨f v, c.map f.toHom, hc.map f.injective, by simp⟩

lemma HasCycleLength.of_induce {V : Type*} (G : SimpleGraph V) (s : Set V) {n : ℕ}
    (h : HasCycleLength (G.induce s) n) : HasCycleLength G n :=
  h.map (SimpleGraph.Embedding.induce s)

/-- Every odd closed walk contains an odd simple cycle using only vertices
from the original walk.  Passing to the induced graph on the support makes
the support containment automatic. -/
theorem exists_odd_cycle_support_subset {V : Type*} {G : SimpleGraph V}
    {v : V} (w : G.Walk v v) (hodd : Odd w.length) :
    ∃ z, ∃ c : G.Walk z z, c.IsCycle ∧ Odd c.length ∧
      ∀ x ∈ c.support, x ∈ w.support := by
  let s : Set V := {x | x ∈ w.support}
  have hw : ∀ x ∈ w.support, x ∈ s := by simp [s]
  let wi := w.induce s hw
  have hwiLength : wi.length = w.length := by
    dsimp [wi]
    calc
      (w.induce s hw).length =
          ((w.induce s hw).map (SimpleGraph.Embedding.induce s).toHom).length :=
        (SimpleGraph.Walk.length_map _ _).symm
      _ = w.length := by
        rw [w.map_induce hw]
        rfl
  have hwiOdd : Odd wi.length := hwiLength.symm ▸ hodd
  have hnotColor : ¬(G.induce s).Colorable 2 := by
    intro hcolor
    have heven : Even wi.length :=
      (SimpleGraph.two_colorable_iff_forall_loop_even.mp hcolor) _ wi
    exact (Nat.not_even_iff_odd.mpr hwiOdd) heven
  have hcycle : ∃ z, ∃ c : (G.induce s).Walk z z,
      c.IsCycle ∧ Odd c.length := by
    by_contra h
    apply hnotColor
    apply Erdos58.colorable_two_of_no_odd_isCycle
    intro z c hc hcodd
    exact h ⟨z, c, hc, hcodd⟩
  obtain ⟨z, c, hc, hcodd⟩ := hcycle
  let f : (G.induce s) ↪g G := SimpleGraph.Embedding.induce s
  let c' := c.map f.toHom
  refine ⟨f z, c', hc.map f.injective, ?_, ?_⟩
  · have hlen : c'.length = c.length := by
      dsimp [c']
      exact SimpleGraph.Walk.length_map _ _
    exact hlen.symm ▸ hcodd
  · intro x hx
    have hx' : x ∈ List.map f c.support := by
      dsimp [c'] at hx
      rw [SimpleGraph.Walk.support_map] at hx
      exact hx
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx'
    rw [← hyx]
    exact y.2

/-- A graph is `q`-colorable if all of its finite induced subgraphs are `q`-colorable. -/
theorem colorable_of_finite_induce_colorable {V : Type*} (G : SimpleGraph V) (q : ℕ)
    (h : ∀ s : Finset V, (G.induce (s : Set V)).Colorable q) : G.Colorable q := by
  classical
  let localColor : (s : Finset V) → s → Fin q := fun s x =>
    (Classical.choice (h s) : (G.induce (s : Set V)).Coloring (Fin q)) x
  obtain ⟨color, hcolor⟩ := Finset.rado_selection_subtype
    (β := fun _ : V => Fin q) localColor
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro v w hvw heq
  obtain ⟨t, hsub, ht⟩ := hcolor {v, w}
  have hvt : v ∈ t := hsub (by simp)
  have hwt : w ∈ t := hsub (by simp)
  have hadj : (G.induce (t : Set V)).Adj ⟨v, hvt⟩ ⟨w, hwt⟩ := hvw
  have hne : localColor t ⟨v, hvt⟩ ≠ localColor t ⟨w, hwt⟩ := by
    simpa [localColor] using
      (Classical.choice (h t) : (G.induce (t : Set V)).Coloring (Fin q)).valid hadj
  apply hne
  rw [← ht ⟨v, by simp⟩, ← ht ⟨w, by simp⟩]
  exact heq

/-- Infinite chromatic number supplies a finite induced subgraph that is not `q`-colorable. -/
theorem exists_finite_induce_not_colorable {V : Type*} (G : SimpleGraph V)
    (hχ : G.chromaticNumber = ⊤) (q : ℕ) :
    ∃ s : Finset V, ¬(G.induce (s : Set V)).Colorable q := by
  by_contra h
  push Not at h
  have hcol : G.Colorable q := colorable_of_finite_induce_colorable G q h
  have hle : G.chromaticNumber ≤ q := SimpleGraph.chromaticNumber_le_iff_colorable.mpr hcol
  rw [hχ] at hle
  simp at hle

/-- A finite collection contains an inclusion-maximal subcollection whose members are good and
have pairwise disjoint finite supports.  This is the finite maximal-packing step used in the
Liu--Montgomery construction. -/
theorem exists_maximal_good_pairwiseDisjoint {α β : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq β] (Good : α → Prop) (support : α → Finset β) :
    ∃ A : Finset α,
      (∀ a ∈ A, Good a) ∧
      (↑A : Set α).Pairwise (fun a b => Disjoint (support a) (support b)) ∧
      ∀ a, Good a →
        (∀ b ∈ A, a ≠ b → Disjoint (support a) (support b)) → a ∈ A := by
  classical
  let candidates : Finset α := Finset.univ.filter Good
  let families : Finset (Finset α) := candidates.powerset.filter fun A =>
    (↑A : Set α).Pairwise (fun a b => Disjoint (support a) (support b))
  have hempty : (∅ : Finset α) ∈ families := by
    simp [families]
  obtain ⟨A, hAmax⟩ := families.exists_maximal ⟨∅, hempty⟩
  have hAfamily := Finset.mem_filter.mp hAmax.1
  refine ⟨A, ?_, hAfamily.2, ?_⟩
  · intro a ha
    have haCandidates : a ∈ candidates :=
      (Finset.mem_powerset.mp hAfamily.1) ha
    exact (Finset.mem_filter.mp haCandidates).2
  · intro a haGood hdisjoint
    have hinsert : insert a A ∈ families := by
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_powerset]
        intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, haGood⟩
        · exact (Finset.mem_powerset.mp hAfamily.1) hb
      · intro x hx y hy hxy
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · exact (hxy rfl).elim
        · exact hdisjoint y hy hxy
        · exact (hdisjoint x hx hxy.symm).symm
        · exact hAfamily.2 hx hy hxy
    have hback : insert a A ⊆ A := hAmax.2 hinsert (Finset.subset_insert a A)
    exact hback (Finset.mem_insert_self a A)

/-! ### Finite Liu--Montgomery packing interface -/

/-- A simple path of length `n` in `H` all of whose vertices lie in `S`. -/
def HasPathIn {V : Type*} (H : SimpleGraph V) (S : Finset V)
    (u v : V) (n : ℕ) : Prop :=
  ∃ p : H.Walk u v, p.IsPath ∧ p.length = n ∧ ∀ x ∈ p.support, x ∈ S

/-- A finite subgraph together with its intended (non-isolated) carrier. -/
abbrev PackedSubgraph (V : Type*) := Finset V × SimpleGraph V

/-- A bipartite piece having all parity-compatible path lengths in a long interval.

This is the form in which Liu--Montgomery Corollary 5.1 enters the odd-cycle proof. -/
def IsFlexiblePiece {V : Type*} [Fintype V] (G : SimpleGraph V) (R : ℕ)
    (P : PackedSubgraph V) : Prop :=
  P.1.Nonempty ∧ P.2.edgeSet.Nonempty ∧ P.2 ≤ G ∧
    (∀ ⦃u v⦄, P.2.Adj u v → u ∈ P.1 ∧ v ∈ P.1) ∧
    ∃ c : P.2.Coloring (Fin 2), ∃ ell : ℕ, 0 < ell ∧
      ∀ u ∈ P.1, ∀ v ∈ P.1, u ≠ v → ∀ n : ℕ,
        ell ≤ n → n ≤ ell * R → (Even n ↔ c u = c v) →
          HasPathIn P.2 P.1 u v n

/-! ### Transporting flexible pieces through graph embeddings -/

/-- Push both the carrier and the graph of a packed piece through a graph
embedding.  Vertices outside the image are isolated in the mapped graph. -/
noncomputable def PackedSubgraph.mapEmbedding {V W : Type*}
    [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) (P : PackedSubgraph V) : PackedSubgraph W :=
  (P.1.map f.toEmbedding, P.2.map f.toEmbedding)

/-- A two-coloring extends uniquely across the image of an embedding; the
irrelevant isolated vertices are assigned color zero. -/
noncomputable def mapColoring {V W : Type*} [Fintype V] [Fintype W]
    {J : SimpleGraph V} (f : V ↪ W) (c : J.Coloring (Fin 2)) :
    (J.map f).Coloring (Fin 2) := by
  classical
  refine SimpleGraph.Coloring.mk (Function.extend f c 0) ?_
  intro u v huv
  rw [SimpleGraph.map_adj] at huv
  obtain ⟨u', v', huv', rfl, rfl⟩ := huv
  rw [f.injective.extend_apply, f.injective.extend_apply]
  exact c.valid huv'

@[simp] lemma mapColoring_apply {V W : Type*} [Fintype V] [Fintype W]
    {J : SimpleGraph V} (f : V ↪ W) (c : J.Coloring (Fin 2)) (v : V) :
    mapColoring f c (f v) = c v := by
  classical
  exact f.injective.extend_apply c (fun _ => 0) v

/-- Flexibility is invariant under embedding the ambient graph.  The proof
also transports the witnesses as actual mapped simple paths, so their support
remains inside the mapped finite carrier. -/
theorem IsFlexiblePiece.mapEmbedding {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {R : ℕ}
    {P : PackedSubgraph V} (hP : IsFlexiblePiece G R P) (f : G ↪g H) :
    IsFlexiblePiece H R (P.mapEmbedding f) := by
  classical
  let e : V ↪ W := f.toEmbedding
  change IsFlexiblePiece H R (P.1.map e, P.2.map e)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hP.1
    exact ⟨e v, Finset.mem_map.mpr ⟨v, hv, rfl⟩⟩
  · obtain ⟨a, ha⟩ := hP.2.1
    induction a using Sym2.inductionOn with
    | _ u v =>
        refine ⟨s(e u, e v), ?_⟩
        rw [SimpleGraph.mem_edgeSet]
        exact (SimpleGraph.map_adj_apply (G := P.2) (f := e)).2 (by simpa using ha)
  · intro u v huv
    rw [SimpleGraph.map_adj] at huv
    obtain ⟨u', v', huv', rfl, rfl⟩ := huv
    exact f.toHom.map_adj (hP.2.2.1 huv')
  · intro u v huv
    rw [SimpleGraph.map_adj] at huv
    obtain ⟨u', v', huv', rfl, rfl⟩ := huv
    obtain ⟨hu', hv'⟩ := hP.2.2.2.1 huv'
    exact ⟨Finset.mem_map.mpr ⟨u', hu', rfl⟩,
      Finset.mem_map.mpr ⟨v', hv', rfl⟩⟩
  · obtain ⟨c, ell, hell, hpaths⟩ := hP.2.2.2.2
    refine ⟨mapColoring e c, ell, hell, ?_⟩
    intro u hu v hv huv n hnlow hnhigh hnparity
    rw [Finset.mem_map] at hu hv
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    have huv' : u' ≠ v' := fun h => huv (congrArg e h)
    have hnparity' : Even n ↔ c u' = c v' := by
      simpa using hnparity
    obtain ⟨p, hp, hplen, hpsupport⟩ :=
      hpaths u' hu' v' hv' huv' n hnlow hnhigh hnparity'
    let ph : P.2 →g P.2.map e :=
      { toFun := fun x => e x
        map_rel' := by
          intro a b h
          exact (SimpleGraph.map_adj_apply (G := P.2) (f := e)).2 h }
    let pmap : (P.2.map e).Walk (e u') (e v') := p.map ph
    refine ⟨pmap, ?_, ?_, ?_⟩
    · exact hp.map e.injective
    · simpa only [pmap, SimpleGraph.Walk.length_map] using hplen
    · intro x hx
      have hsupp : pmap.support = p.support.map e := by
        simpa [pmap, ph] using (SimpleGraph.Walk.support_map (f := ph) p)
      rw [hsupp] at hx
      obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
      exact Finset.mem_map.mpr ⟨x', hpsupport x' hx', rfl⟩

/-- Push a packed piece through an injective graph homomorphism. -/
noncomputable def PackedSubgraph.mapCopy {V W : Type*}
    [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : SimpleGraph.Copy G H) (P : PackedSubgraph V) : PackedSubgraph W :=
  (P.1.map f.toEmbedding, P.2.map f.toEmbedding)

/-- Flexible pieces transport through ordinary (not necessarily induced)
copies.  This is the form needed for the subdivision alternative. -/
theorem IsFlexiblePiece.mapCopy {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {R : ℕ}
    {P : PackedSubgraph V} (hP : IsFlexiblePiece G R P)
    (f : SimpleGraph.Copy G H) :
    IsFlexiblePiece H R (P.mapCopy f) := by
  classical
  let e : V ↪ W := f.toEmbedding
  change IsFlexiblePiece H R (P.1.map e, P.2.map e)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hP.1
    exact ⟨e v, Finset.mem_map.mpr ⟨v, hv, rfl⟩⟩
  · obtain ⟨a, ha⟩ := hP.2.1
    induction a using Sym2.inductionOn with
    | _ u v =>
        refine ⟨s(e u, e v), ?_⟩
        rw [SimpleGraph.mem_edgeSet]
        exact (SimpleGraph.map_adj_apply (G := P.2) (f := e)).2 (by simpa using ha)
  · intro u v huv
    rw [SimpleGraph.map_adj] at huv
    obtain ⟨u', v', huv', rfl, rfl⟩ := huv
    exact f.toHom.map_adj (hP.2.2.1 huv')
  · intro u v huv
    rw [SimpleGraph.map_adj] at huv
    obtain ⟨u', v', huv', rfl, rfl⟩ := huv
    obtain ⟨hu', hv'⟩ := hP.2.2.2.1 huv'
    exact ⟨Finset.mem_map.mpr ⟨u', hu', rfl⟩,
      Finset.mem_map.mpr ⟨v', hv', rfl⟩⟩
  · obtain ⟨c, ell, hell, hpaths⟩ := hP.2.2.2.2
    refine ⟨mapColoring e c, ell, hell, ?_⟩
    intro u hu v hv huv n hnlow hnhigh hnparity
    rw [Finset.mem_map] at hu hv
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    have huv' : u' ≠ v' := fun h => huv (congrArg e h)
    have hnparity' : Even n ↔ c u' = c v' := by
      simpa using hnparity
    obtain ⟨p, hp, hplen, hpsupport⟩ :=
      hpaths u' hu' v' hv' huv' n hnlow hnhigh hnparity'
    let ph : P.2 →g P.2.map e :=
      { toFun := fun x => e x
        map_rel' := by
          intro a b h
          exact (SimpleGraph.map_adj_apply (G := P.2) (f := e)).2 h }
    let pmap : (P.2.map e).Walk (e u') (e v') := p.map ph
    refine ⟨pmap, ?_, ?_, ?_⟩
    · exact hp.map e.injective
    · simpa only [pmap, SimpleGraph.Walk.length_map] using hplen
    · intro x hx
      have hsupp : pmap.support = p.support.map e := by
        simpa [pmap, ph] using (SimpleGraph.Walk.support_map (f := ph) p)
      rw [hsupp] at hx
      obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
      exact Finset.mem_map.mpr ⟨x', hpsupport x' hx', rfl⟩

/-! ### Explicit flexible gadgets from Liu--Montgomery's dichotomy -/

namespace FlexibleGadgets

open Erdos63

noncomputable def subdivisionEdgeOfNe {t : ℕ} (i j : Fin t) (hij : i ≠ j) :
    SubdivisionEdge t :=
  if h : i < j then ⟨(i, j), h⟩
  else ⟨(j, i), lt_of_le_of_ne (le_of_not_gt h) hij.symm⟩

lemma left_mem_subdivisionEdgeOfNe {t : ℕ} (i j : Fin t) (hij : i ≠ j) :
    i = (subdivisionEdgeOfNe i j hij).1.1 ∨
      i = (subdivisionEdgeOfNe i j hij).1.2 := by
  simp only [subdivisionEdgeOfNe]
  split <;> simp

lemma right_mem_subdivisionEdgeOfNe {t : ℕ} (i j : Fin t) (hij : i ≠ j) :
    j = (subdivisionEdgeOfNe i j hij).1.1 ∨
      j = (subdivisionEdgeOfNe i j hij).1.2 := by
  simp only [subdivisionEdgeOfNe]
  split <;> simp

lemma subdivisionEdgeOfNe_fst_eq {t : ℕ} (i j : Fin t) (hij : i ≠ j) :
    (subdivisionEdgeOfNe i j hij).1.1 = i ∨
      (subdivisionEdgeOfNe i j hij).1.1 = j := by
  simp only [subdivisionEdgeOfNe]
  split <;> simp

lemma subdivisionEdgeOfNe_snd_eq {t : ℕ} (i j : Fin t) (hij : i ≠ j) :
    (subdivisionEdgeOfNe i j hij).1.2 = i ∨
      (subdivisionEdgeOfNe i j hij).1.2 = j := by
  simp only [subdivisionEdgeOfNe]
  split <;> simp

noncomputable def subdivideCompleteWalk {t : ℕ} {i j : Fin t} :
    (SimpleGraph.completeGraph (Fin t)).Walk i j →
      (oneSubdivisionClique t).Walk (.inl i) (.inl j)
  | .nil => .nil
  | @SimpleGraph.Walk.cons _ _ _ k _ hik p => by
      let hne : i ≠ k := by simpa using hik
      let e := subdivisionEdgeOfNe i k hne
      have hleft : (oneSubdivisionClique t).Adj (.inl i) (.inr e) := by
        simpa [e] using left_mem_subdivisionEdgeOfNe i k hne
      have hright : (oneSubdivisionClique t).Adj (.inr e) (.inl k) := by
        simpa [e] using right_mem_subdivisionEdgeOfNe i k hne
      exact .cons hleft (.cons hright (subdivideCompleteWalk p))

@[simp] lemma subdivideCompleteWalk_length {t : ℕ} {i j : Fin t}
    (p : (SimpleGraph.completeGraph (Fin t)).Walk i j) :
    (subdivideCompleteWalk p).length = 2 * p.length := by
  induction p with
  | nil => simp [subdivideCompleteWalk]
  | cons h p ih => simp [subdivideCompleteWalk, ih]; omega

lemma mem_subdivideCompleteWalk_support_core_iff {t : ℕ} {i j x : Fin t}
    (p : (SimpleGraph.completeGraph (Fin t)).Walk i j) :
    Sum.inl x ∈ (subdivideCompleteWalk p).support ↔ x ∈ p.support := by
  induction p with
  | nil => simp [subdivideCompleteWalk]
  | @cons u v w h p ih => simp [subdivideCompleteWalk, ih]

lemma mem_subdivideCompleteWalk_support_edge_endpoints {t : ℕ} {i j : Fin t}
    (p : (SimpleGraph.completeGraph (Fin t)).Walk i j) {e : SubdivisionEdge t}
    (he : Sum.inr e ∈ (subdivideCompleteWalk p).support) :
    e.1.1 ∈ p.support ∧ e.1.2 ∈ p.support := by
  induction p with
  | nil => simp [subdivideCompleteWalk] at he
  | @cons u v w huv p ih =>
      simp only [subdivideCompleteWalk, SimpleGraph.Walk.support_cons,
        List.mem_cons, Sum.inr.injEq, Sum.inr.injEq] at he
      rcases he with he | he | he
      · cases he
      · subst e
        constructor
        · rcases subdivisionEdgeOfNe_fst_eq u v (by simpa using huv) with h | h
          · simp [h]
          · simp [h]
        · rcases subdivisionEdgeOfNe_snd_eq u v (by simpa using huv) with h | h
          · simp [h]
          · simp [h]
      · have h := ih he
        exact ⟨by simp [h.1], by simp [h.2]⟩

theorem subdivideCompleteWalk_isPath {t : ℕ} {i j : Fin t}
    {p : (SimpleGraph.completeGraph (Fin t)).Walk i j} (hp : p.IsPath) :
    (subdivideCompleteWalk p).IsPath := by
  induction p with
  | nil => exact SimpleGraph.Walk.IsPath.nil
  | @cons u v w huv p ih =>
      have hp' : p.IsPath := (SimpleGraph.Walk.cons_isPath_iff huv p).1 hp |>.1
      have hu : u ∉ p.support := (SimpleGraph.Walk.cons_isPath_iff huv p).1 hp |>.2
      have hi := ih hp'
      apply SimpleGraph.Walk.IsPath.mk'
      simp only [subdivideCompleteWalk, SimpleGraph.Walk.support_cons,
        List.nodup_cons]
      constructor
      · simp only [List.mem_cons, Sum.inl_ne_inr, false_or]
        exact fun h => hu ((mem_subdivideCompleteWalk_support_core_iff p).1 h)
      constructor
      · intro he
        have hend := mem_subdivideCompleteWalk_support_edge_endpoints p he
        have hue : u = (subdivisionEdgeOfNe u v (by simpa using huv)).1.1 ∨
            u = (subdivisionEdgeOfNe u v (by simpa using huv)).1.2 :=
          left_mem_subdivisionEdgeOfNe u v (by simpa using huv)
        exact hue.elim (fun h => hu (h ▸ hend.1)) (fun h => hu (h ▸ hend.2))
      · exact hi.support_nodup

lemma mem_subdivideCompleteWalk_support_edge_edges {t : ℕ} {i j : Fin t}
    (p : (SimpleGraph.completeGraph (Fin t)).Walk i j) {e : SubdivisionEdge t}
    (he : Sum.inr e ∈ (subdivideCompleteWalk p).support) :
    s(e.1.1, e.1.2) ∈ p.edges := by
  induction p with
  | nil => simp [subdivideCompleteWalk] at he
  | @cons u v w huv p ih =>
      simp only [subdivideCompleteWalk, SimpleGraph.Walk.support_cons,
        List.mem_cons, Sum.inr_ne_inl, false_or, Sum.inr.injEq] at he
      rcases he with he | he
      · cases he
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        left
        rw [Sym2.eq_iff]
        simp only [subdivisionEdgeOfNe]
        split <;> simp
      · exact List.mem_cons_of_mem _ (ih he)

lemma exists_fresh_core_list {t r : ℕ} (F : Finset (Fin t))
    (hcard : r + F.card ≤ t) :
    ∃ l : List (Fin t), l.Nodup ∧ l.length = r ∧
      ∀ x ∈ l, x ∉ F := by
  classical
  have havail : r ≤ ((Finset.univ : Finset (Fin t)) \ F).card := by
    rw [Finset.card_sdiff]
    simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨M, hMsub, hMcard⟩ := Finset.exists_subset_card_eq havail
  refine ⟨M.toList, Finset.nodup_toList M, by simpa using hMcard, ?_⟩
  intro x hx hFx
  have hxM : x ∈ M := by simpa using hx
  have := hMsub hxM
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at this
  exact this hFx

lemma exists_completePath_avoiding {t m : ℕ} {a b : Fin t}
    (hab : a ≠ b) (hm : 1 ≤ m) (F : Finset (Fin t))
    (haF : a ∈ F) (hbF : b ∈ F) (hcard : (m - 1) + F.card ≤ t) :
    ∃ p : (SimpleGraph.completeGraph (Fin t)).Walk a b,
      p.IsPath ∧ p.length = m ∧
      ∀ x ∈ p.support, x = a ∨ x = b ∨ x ∉ F := by
  classical
  obtain ⟨l, hlnodup, hllen, hlfresh⟩ :=
    exists_fresh_core_list F hcard
  let support : List (Fin t) := a :: (l ++ [b])
  have haL : a ∉ l := fun h => hlfresh a h haF
  have hbL : b ∉ l := fun h => hlfresh b h hbF
  have hsNodup : support.Nodup := by
    have hlb : (l ++ [b]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hlnodup, by simp, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst y
      intro hxy
      exact hbL (hxy ▸ hx)
    change (a :: (l ++ [b])).Nodup
    rw [List.nodup_cons]
    exact ⟨by simp [haL, hab], hlb⟩
  have hsChain : support.IsChain (SimpleGraph.completeGraph (Fin t)).Adj := by
    apply hsNodup.isChain.imp
    intro x y hxy
    simpa using hxy
  have hsNonempty : support ≠ [] := by simp [support]
  let q := SimpleGraph.Walk.ofSupport support hsNonempty hsChain
  let p : (SimpleGraph.completeGraph (Fin t)).Walk a b :=
    q.copy (by simp [q, support]) (by simp [q, support])
  have hpSupport : p.support = support := by
    calc
      p.support = q.support := by
        exact SimpleGraph.Walk.support_copy q _ _
      _ = support := by
        exact SimpleGraph.Walk.support_ofSupport hsNonempty hsChain
  have hpLength : p.length = support.length - 1 := by
    calc
      p.length = q.length := by
        exact SimpleGraph.Walk.length_copy q _ _
      _ = support.length - 1 := by
        exact SimpleGraph.Walk.length_ofSupport hsNonempty hsChain
  refine ⟨p, ?_, ?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.mk'
    rw [hpSupport]
    exact hsNodup
  · rw [hpLength]
    simp [support, hllen, Nat.sub_add_cancel hm]
  · intro x hx
    have hx' : x ∈ support := by simpa [hpSupport] using hx
    simp only [support, List.mem_cons, List.mem_append,
      List.mem_singleton] at hx'
    simp only [List.mem_nil_iff, or_false] at hx'
    rcases hx' with rfl | hx'
    · exact Or.inl rfl
    rcases hx' with hx' | rfl
    · exact Or.inr (Or.inr (hlfresh x hx'))
    · exact Or.inr (Or.inl rfl)

lemma endpoint_edge_not_mem_subdivided_core_path {t m : ℕ}
    {a b : Fin t} {p : (SimpleGraph.completeGraph (Fin t)).Walk a b}
    (hp : p.IsPath) (hplen : p.length = m) (hm : 2 ≤ m)
    (e : SubdivisionEdge t)
    (hab : a ≠ b)
    (ha : a = e.1.1 ∨ a = e.1.2) (hb : b = e.1.1 ∨ b = e.1.2) :
    Sum.inr e ∉ (subdivideCompleteWalk p).support := by
  intro he
  have hedge := mem_subdivideCompleteWalk_support_edge_edges p he
  have habedge : s(a, b) = s(e.1.1, e.1.2) := by
    rw [Sym2.eq_iff]
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact (hab (ha.trans hb.symm)).elim
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
    · exact (hab (ha.trans hb.symm)).elim
  rw [← habedge] at hedge
  have := hp.length_eq_one_of_mem_edges hedge
  omega

noncomputable def endpointAway {t : ℕ} (a : Fin t) (e : SubdivisionEdge t) : Fin t :=
  if a = e.1.1 then e.1.2 else e.1.1

lemma endpointAway_mem {t : ℕ} (a : Fin t) (e : SubdivisionEdge t) :
    endpointAway a e = e.1.1 ∨ endpointAway a e = e.1.2 := by
  simp only [endpointAway]
  split <;> simp

lemma endpointAway_ne {t : ℕ} (a : Fin t) (e : SubdivisionEdge t) :
    endpointAway a e ≠ a := by
  simp only [endpointAway]
  split
  · rename_i h
    intro h'
    exact (ne_of_lt e.2) (h.symm.trans h'.symm)
  · rename_i h
    exact fun h' => h h'.symm

lemma forbidden_edge_not_mem_subdivided_core_path {t m : ℕ}
    {a b : Fin t} {p : (SimpleGraph.completeGraph (Fin t)).Walk a b}
    (hp : p.IsPath) (hplen : p.length = m) (hm : 2 ≤ m)
    (F : Finset (Fin t))
    (havoid : ∀ x ∈ p.support, x = a ∨ x = b ∨ x ∉ F)
    (e : SubdivisionEdge t) (hefst : e.1.1 ∈ F) (hesnd : e.1.2 ∈ F) :
    Sum.inr e ∉ (subdivideCompleteWalk p).support := by
  intro he
  have hend := mem_subdivideCompleteWalk_support_edge_endpoints p he
  have hfst := havoid e.1.1 hend.1
  have hsnd := havoid e.1.2 hend.2
  rcases hfst with hfst | hfst | hfst
  · rcases hsnd with hsnd | hsnd | hsnd
    · exact (ne_of_lt e.2) (hfst.trans hsnd.symm)
    · exact endpoint_edge_not_mem_subdivided_core_path hp hplen hm e
        (by intro h; exact (ne_of_lt e.2) (hfst.trans (h.trans hsnd.symm)))
        (Or.inl hfst.symm) (Or.inr hsnd.symm) he
    · exact hsnd hesnd
  · rcases hsnd with hsnd | hsnd | hsnd
    · exact endpoint_edge_not_mem_subdivided_core_path hp hplen hm e
        (by intro h; exact (ne_of_lt e.2) (hfst.trans (h.symm.trans hsnd.symm)))
        (Or.inr hsnd.symm) (Or.inl hfst.symm) he
    · exact (ne_of_lt e.2) (hfst.trans hsnd.symm)
    · exact hsnd hesnd
  · exact hfst hefst

lemma exists_subdivisionPath_core_core {t n : ℕ} {a b : Fin t}
    (hab : a ≠ b) (heven : Even n) (hlow : 12 ≤ n)
    (hupper : n ≤ 2 * t - 12) :
    ∃ q : (oneSubdivisionClique t).Walk (Sum.inl a) (Sum.inl b),
      q.IsPath ∧ q.length = n := by
  classical
  let m := n / 2
  let F : Finset (Fin t) := {a, b}
  have htwom : 2 * m = n := by
    exact Nat.two_mul_div_two_of_even heven
  have hm : 2 ≤ m := by omega
  have haF : a ∈ F := by simp [F]
  have hbF : b ∈ F := by simp [F]
  have hFcard : F.card ≤ 2 := by simpa [F] using (Finset.card_le_two (a := a) (b := b))
  have hcard : (m - 1) + F.card ≤ t := by omega
  obtain ⟨p, hp, hplen, _havoid⟩ :=
    exists_completePath_avoiding hab (by omega) F haF hbF hcard
  refine ⟨subdivideCompleteWalk p, subdivideCompleteWalk_isPath hp, ?_⟩
  rw [subdivideCompleteWalk_length, hplen]
  exact htwom

lemma exists_subdivisionPath_core_edge {t n : ℕ} (a : Fin t)
    (e : SubdivisionEdge t) (hodd : Odd n) (hlow : 12 ≤ n)
    (hupper : n ≤ 2 * t - 12) :
    ∃ q : (oneSubdivisionClique t).Walk (Sum.inl a) (Sum.inr e),
      q.IsPath ∧ q.length = n := by
  classical
  let b := endpointAway a e
  let m := n / 2
  let F : Finset (Fin t) := {a, b, e.1.1, e.1.2}
  have htwom : 2 * m + 1 = n := by
    exact Nat.two_mul_div_two_add_one_of_odd hodd
  have hab : a ≠ b := (endpointAway_ne a e).symm
  have hm : 2 ≤ m := by omega
  have haF : a ∈ F := by simp [F]
  have hbF : b ∈ F := by simp [F]
  have hefst : e.1.1 ∈ F := by simp [F]
  have hesnd : e.1.2 ∈ F := by simp [F]
  have hFcard : F.card ≤ 4 := by
    simpa [F] using
      (Finset.card_le_four (a := a) (b := b) (c := e.1.1) (d := e.1.2))
  have hcard : (m - 1) + F.card ≤ t := by omega
  obtain ⟨p, hp, hplen, havoid⟩ :=
    exists_completePath_avoiding hab (by omega) F haF hbF hcard
  let q := subdivideCompleteWalk p
  have hq : q.IsPath := subdivideCompleteWalk_isPath hp
  have heNot : Sum.inr e ∉ q.support :=
    forbidden_edge_not_mem_subdivided_core_path hp hplen hm F havoid e hefst hesnd
  have hbe : (oneSubdivisionClique t).Adj (Sum.inl b) (Sum.inr e) := by
    simpa [b] using endpointAway_mem a e
  refine ⟨q.concat hbe, hq.concat heNot hbe, ?_⟩
  simp only [SimpleGraph.Walk.length_concat, q, subdivideCompleteWalk_length, hplen]
  exact htwom

lemma exists_subdivisionPath_edge_core {t n : ℕ} (e : SubdivisionEdge t)
    (b : Fin t) (hodd : Odd n) (hlow : 12 ≤ n)
    (hupper : n ≤ 2 * t - 12) :
    ∃ q : (oneSubdivisionClique t).Walk (Sum.inr e) (Sum.inl b),
      q.IsPath ∧ q.length = n := by
  obtain ⟨q, hq, hlen⟩ :=
    exists_subdivisionPath_core_edge b e hodd hlow hupper
  exact ⟨q.reverse, hq.reverse, by simpa using hlen⟩

lemma exists_subdivisionPath_edge_edge {t n : ℕ} {e f : SubdivisionEdge t}
    (hef : e ≠ f) (heven : Even n) (hlow : 12 ≤ n)
    (hupper : n ≤ 2 * t - 12) :
    ∃ q : (oneSubdivisionClique t).Walk (Sum.inr e) (Sum.inr f),
      q.IsPath ∧ q.length = n := by
  classical
  let a : Fin t := e.1.1
  let b : Fin t := endpointAway a f
  let k := n / 2 - 1
  let F : Finset (Fin t) := {a, b, e.1.1, e.1.2, f.1.1, f.1.2}
  have htwodiv : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even heven
  have hlenk : 2 * k + 2 = n := by omega
  have hab : a ≠ b := (endpointAway_ne a f).symm
  have hk : 2 ≤ k := by omega
  have haF : a ∈ F := by simp [F]
  have hbF : b ∈ F := by simp [F]
  have he1F : e.1.1 ∈ F := by simp [F]
  have he2F : e.1.2 ∈ F := by simp [F]
  have hf1F : f.1.1 ∈ F := by simp [F]
  have hf2F : f.1.2 ∈ F := by simp [F]
  have hFcard : F.card ≤ 6 := by
    simpa [F] using (Finset.card_le_six (a := a) (b := b)
      (c := e.1.1) (d := e.1.2) (e := f.1.1) (f := f.1.2))
  have hcard : (k - 1) + F.card ≤ t := by omega
  obtain ⟨p, hp, hplen, havoid⟩ :=
    exists_completePath_avoiding hab (by omega) F haF hbF hcard
  let q := subdivideCompleteWalk p
  have hq : q.IsPath := subdivideCompleteWalk_isPath hp
  have heNot : Sum.inr e ∉ q.support :=
    forbidden_edge_not_mem_subdivided_core_path hp hplen hk F havoid e he1F he2F
  have hfNot : Sum.inr f ∉ q.support :=
    forbidden_edge_not_mem_subdivided_core_path hp hplen hk F havoid f hf1F hf2F
  have hea : (oneSubdivisionClique t).Adj (Sum.inr e) (Sum.inl a) := by
    exact Or.inl rfl
  have hbf : (oneSubdivisionClique t).Adj (Sum.inl b) (Sum.inr f) := by
    simpa [b] using endpointAway_mem a f
  let q' := SimpleGraph.Walk.cons hea q
  have hq' : q'.IsPath := hq.cons heNot
  have hfNot' : Sum.inr f ∉ q'.support := by
    simp only [q', SimpleGraph.Walk.support_cons, List.mem_cons]
    intro h
    rcases h with h | h
    · exact hef (Sum.inr.inj h).symm
    · exact hfNot h
  refine ⟨q'.concat hbf, hq'.concat hfNot' hbf, ?_⟩
  simp only [SimpleGraph.Walk.length_concat, q', SimpleGraph.Walk.length_cons,
    q, subdivideCompleteWalk_length, hplen]
  exact hlenk

noncomputable def subdivisionColoring (t : ℕ) :
    (oneSubdivisionClique t).Coloring (Fin 2) := by
  refine SimpleGraph.Coloring.mk (fun x => match x with
    | Sum.inl _ => 0
    | Sum.inr _ => 1) ?_
  intro x y hxy
  cases x <;> cases y <;> simp_all [oneSubdivisionClique, subdivisionAdj]

@[simp] lemma subdivisionColoring_apply_core {t : ℕ} (a : Fin t) :
    subdivisionColoring t (Sum.inl a) = 0 := rfl

@[simp] lemma subdivisionColoring_apply_edge {t : ℕ} (e : SubdivisionEdge t) :
    subdivisionColoring t (Sum.inr e) = 1 := rfl

theorem subdivisionClique_isFlexible (R t : ℕ) (ht : 6 * R + 6 ≤ t) :
    IsFlexiblePiece (oneSubdivisionClique t) R
      ((Finset.univ : Finset (SubdivisionVertex t)), oneSubdivisionClique t) := by
  classical
  have htTwo : 2 ≤ t := by omega
  let a : Fin t := ⟨0, by omega⟩
  let b : Fin t := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b]
  let e := subdivisionEdgeOfNe a b hab
  have hae : (oneSubdivisionClique t).Adj (Sum.inl a) (Sum.inr e) := by
    simpa [e] using left_mem_subdivisionEdgeOfNe a b hab
  refine ⟨⟨Sum.inl a, Finset.mem_univ _⟩, ?_, le_rfl, ?_, ?_⟩
  · refine ⟨s(Sum.inl a, Sum.inr e), ?_⟩
    simpa using hae
  · intro u v _huv
    exact ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  · refine ⟨subdivisionColoring t, 12, by omega, ?_⟩
    intro u _hu v _hv huv n hnlow hnupper hparity
    have hupper : n ≤ 2 * t - 12 := by
      have : 12 * R ≤ 2 * t - 12 := by omega
      exact hnupper.trans this
    rcases u with a | e <;> rcases v with b | f
    · have heven : Even n := hparity.mpr (by rfl)
      obtain ⟨q, hq, hlen⟩ :=
        exists_subdivisionPath_core_core (by simpa using huv) heven hnlow hupper
      exact ⟨q, hq, hlen, by simp⟩
    · have hodd : Odd n := Nat.not_even_iff_odd.mp (by
        intro heven
        have := hparity.mp heven
        simpa using this)
      obtain ⟨q, hq, hlen⟩ :=
        exists_subdivisionPath_core_edge a f hodd hnlow hupper
      exact ⟨q, hq, hlen, by simp⟩
    · have hodd : Odd n := Nat.not_even_iff_odd.mp (by
        intro heven
        have := hparity.mp heven
        simpa using this)
      obtain ⟨q, hq, hlen⟩ :=
        exists_subdivisionPath_edge_core e b hodd hnlow hupper
      exact ⟨q, hq, hlen, by simp⟩
    · have hef : e ≠ f := by
        intro h
        exact huv (congrArg Sum.inr h)
      have heven : Even n := hparity.mpr (by rfl)
      obtain ⟨q, hq, hlen⟩ :=
        exists_subdivisionPath_edge_edge hef heven hnlow hupper
      exact ⟨q, hq, hlen, by simp⟩

theorem eventually_ceil_log_seven_mul_le_pathScale (R : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (((⌈Real.log (N : ℝ) ^ 7⌉₊ * R : ℕ) : ℝ)) ≤
        Parameters.lmPathScale (N : ℝ) := by
  have hsmall := Parameters.eventually_const_mul_log_pow_le_self
    (4 * (R : ℝ) ^ 2) 14
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmall
  have hpath := tendsto_natCast_atTop_atTop.eventually
    Parameters.eventually_log_pow_twelve_le_sqrt
  filter_upwards [eventually_ge_atTop 3, hsmallNat, hpath] with N hN hsmallN hpathN
  have hlogOne : 1 ≤ Real.log (N : ℝ) := by
    have : Real.exp 1 ≤ (N : ℝ) := by
      have hexpThree : Real.exp 1 ≤ (3 : ℝ) :=
        (Real.exp_one_lt_d9.trans (by norm_num)).le
      exact hexpThree.trans (by exact_mod_cast hN)
    exact (Real.le_log_iff_exp_le (by positivity)).2 this
  have hceil : ((⌈Real.log (N : ℝ) ^ 7⌉₊ : ℕ) : ℝ) ≤
      2 * Real.log (N : ℝ) ^ 7 := by
    have hNrealOne : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (show 1 ≤ N by omega)
    have hlt := Nat.ceil_lt_add_one
      (pow_nonneg (Real.log_nonneg hNrealOne) 7)
    have hpOne : 1 ≤ Real.log (N : ℝ) ^ 7 := one_le_pow₀ hlogOne
    linarith
  have hprod : (((⌈Real.log (N : ℝ) ^ 7⌉₊ * R : ℕ) : ℝ)) ≤
      2 * Real.log (N : ℝ) ^ 7 * R := by
    push_cast
    exact mul_le_mul_of_nonneg_right hceil (Nat.cast_nonneg R)
  have hsquare :
      (((⌈Real.log (N : ℝ) ^ 7⌉₊ * R : ℕ) : ℝ)) ^ 2 ≤ (N : ℝ) := by
    calc
      (((⌈Real.log (N : ℝ) ^ 7⌉₊ * R : ℕ) : ℝ)) ^ 2 ≤
          (2 * Real.log (N : ℝ) ^ 7 * R) ^ 2 := by
            exact pow_le_pow_left₀ (by positivity) hprod 2
      _ = 4 * (R : ℝ) ^ 2 * Real.log (N : ℝ) ^ 14 := by ring
      _ ≤ (N : ℝ) := hsmallN
  have hsqrt : (((⌈Real.log (N : ℝ) ^ 7⌉₊ * R : ℕ) : ℝ)) ≤ √(N : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact hsquare
  have hNone : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  exact hsqrt.trans (Parameters.sqrt_le_lmPathScale hNone hpathN)

noncomputable def bipartitionFinColoring {V : Type*} [Fintype V]
    {J : SimpleGraph V} (B : Bipartition J) : J.Coloring (Fin 2) :=
  SimpleGraph.recolorOfEquiv J finTwoEquiv.symm B.coloring

@[simp] lemma bipartitionFinColoring_apply {V : Type*} [Fintype V]
    {J : SimpleGraph V} (B : Bipartition J) (x : V) :
    finTwoEquiv (bipartitionFinColoring B x) = B.coloring x := by
  simp [bipartitionFinColoring, SimpleGraph.recolorOfEquiv]

lemma parityCompatible_iff_bipartitionFinColoring {V : Type*} [Fintype V]
    {J : SimpleGraph V} (B : Bipartition J) (x y : V) (n : ℕ) :
    ParityCompatible B x y n ↔
      (Even n ↔ bipartitionFinColoring B x = bipartitionFinColoring B y) := by
  rw [parityCompatible_iff, B.sameSide_iff_left_membership]
  have hc :
      (bipartitionFinColoring B x = bipartitionFinColoring B y) ↔
        (x ∈ B.left ↔ y ∈ B.left) := by
    rw [← finTwoEquiv.injective.eq_iff]
    simp [Bipartition.coloring_apply]
  tauto

theorem exactPathGraph_isFlexible {V : Type*} [Fintype V]
    (J : SimpleGraph V) (B : Bipartition J) (R : ℕ)
    (hV : 3 ≤ Fintype.card V) (hedge : J.edgeSet.Nonempty)
    (hscale : (((⌈Real.log (Fintype.card V : ℝ) ^ 7⌉₊ * R : ℕ) : ℝ)) ≤
      Parameters.lmPathScale (Fintype.card V : ℝ))
    (hexact : ∀ {x y : V} {q : ℕ}, x ≠ y →
      ParityCompatible B x y q →
      Real.log (Fintype.card V : ℝ) ^ 7 ≤ q →
      (q : ℝ) ≤ Parameters.lmPathScale (Fintype.card V : ℝ) →
      HasPathBetweenLength J x y q) :
    IsFlexiblePiece J R ((Finset.univ : Finset V), J) := by
  classical
  let ell := ⌈Real.log (Fintype.card V : ℝ) ^ 7⌉₊
  have hlogpos : 0 < Real.log (Fintype.card V : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Fintype.card V by omega)
  have hellpos : 0 < ell := Nat.ceil_pos.mpr (pow_pos hlogpos 7)
  refine ⟨⟨Classical.choice (Fintype.card_pos_iff.mp (by omega)), Finset.mem_univ _⟩,
    hedge, le_rfl, by simp, bipartitionFinColoring B, ell, hellpos, ?_⟩
  intro u _hu v _hv huv n hnlow hnupper hnparity
  have hparity : ParityCompatible B u v n :=
    (parityCompatible_iff_bipartitionFinColoring B u v n).2 hnparity
  have hlower : Real.log (Fintype.card V : ℝ) ^ 7 ≤ (n : ℝ) := by
    calc
      Real.log (Fintype.card V : ℝ) ^ 7 ≤ (ell : ℝ) := Nat.le_ceil _
      _ ≤ (n : ℝ) := by exact_mod_cast hnlow
  have hupper : (n : ℝ) ≤ Parameters.lmPathScale (Fintype.card V : ℝ) := by
    calc
      (n : ℝ) ≤ ((ell * R : ℕ) : ℝ) := by exact_mod_cast hnupper
      _ ≤ Parameters.lmPathScale (Fintype.card V : ℝ) := by
        simpa [ell] using hscale
  obtain ⟨p, hp, hplen⟩ := hexact huv hparity hlower hupper
  exact ⟨p, hp, hplen, by simp⟩


end FlexibleGadgets

/-- The path-interval data carried by a flexible piece. -/
structure FlexiblePathData {V : Type*} [Fintype V] (R : ℕ)
    (P : PackedSubgraph V) where
  color : P.2.Coloring (Fin 2)
  base : ℕ
  base_pos : 0 < base
  hasPath : ∀ u ∈ P.1, ∀ v ∈ P.1, u ≠ v → ∀ n : ℕ,
    base ≤ n → n ≤ base * R → (Even n ↔ color u = color v) →
      HasPathIn P.2 P.1 u v n

/-- Extract the path data from a proof that a piece is flexible. -/
noncomputable def IsFlexiblePiece.pathData {V : Type*} [Fintype V]
    {G : SimpleGraph V} {R : ℕ} {P : PackedSubgraph V}
    (hP : IsFlexiblePiece G R P) : FlexiblePathData R P := by
  let c := Classical.choose hP.2.2.2.2
  have hc := Classical.choose_spec hP.2.2.2.2
  let ell := Classical.choose hc
  have hell := Classical.choose_spec hc
  exact ⟨c, ell, hell.1, hell.2⟩

/-- Required residue of a path between two vertices in a bipartite piece. -/
def FlexiblePathData.residue {V : Type*} [Fintype V] {R : ℕ}
    {P : PackedSubgraph V} (D : FlexiblePathData R P) (u v : V) : ℕ :=
  if D.color u = D.color v then 0 else 1

lemma FlexiblePathData.residue_lt_two {V : Type*} [Fintype V] {R : ℕ}
    {P : PackedSubgraph V} (D : FlexiblePathData R P) (u v : V) :
    D.residue u v < 2 := by
  by_cases h : D.color u = D.color v <;>
    simp [FlexiblePathData.residue, h]

lemma FlexiblePathData.residue_comm {V : Type*} [Fintype V] {R : ℕ}
    {P : PackedSubgraph V} (D : FlexiblePathData R P) (u v : V) :
    D.residue u v = D.residue v u := by
  simp only [FlexiblePathData.residue, eq_comm]

lemma FlexiblePathData.parityCompatible_iff_modEq {V : Type*} [Fintype V]
    {R : ℕ} {P : PackedSubgraph V} (D : FlexiblePathData R P)
    (u v : V) (n : ℕ) :
    (Even n ↔ D.color u = D.color v) ↔ n % 2 = D.residue u v := by
  by_cases hcolor : D.color u = D.color v
  · simp [FlexiblePathData.residue, hcolor, Nat.even_iff]
  · simp only [hcolor, iff_false, FlexiblePathData.residue, if_false]
    rw [Nat.even_iff]
    have hn := Nat.mod_two_eq_zero_or_one n
    omega

lemma FlexiblePathData.hasPath_of_modEq {V : Type*} [Fintype V] {R : ℕ}
    {P : PackedSubgraph V} (D : FlexiblePathData R P)
    {u v : V} (hu : u ∈ P.1) (hv : v ∈ P.1) (huv : u ≠ v)
    {n : ℕ} (hlow : D.base ≤ n) (hhigh : n ≤ D.base * R)
    (hmod : n % 2 = D.residue u v) : HasPathIn P.2 P.1 u v n := by
  exact D.hasPath u hu v hv huv n hlow hhigh
    ((D.parityCompatible_iff_modEq u v n).2 hmod)

/-- The graph formed by the edges in a finite packed family. -/
def packedUnion {V : Type*} (A : Finset (PackedSubgraph V)) : SimpleGraph V :=
  A.sup fun P => P.2

lemma le_packedUnion {V : Type*} {A : Finset (PackedSubgraph V)} {P : PackedSubgraph V}
    (hP : P ∈ A) : P.2 ≤ packedUnion A := by
  classical
  exact Finset.le_sup hP

/-- The edge set of a packed piece, represented without requiring a global
`Fintype P.2.edgeSet` instance. -/
noncomputable def packedEdges {V : Type*} [Fintype V]
    (P : PackedSubgraph V) : Finset (Sym2 V) :=
  (Set.toFinite P.2.edgeSet).toFinset

@[simp] lemma mem_packedEdges {V : Type*} [Fintype V]
    {P : PackedSubgraph V} {e : Sym2 V} :
    e ∈ packedEdges P ↔ e ∈ P.2.edgeSet := by
  simp [packedEdges]

lemma packedUnion_le {V : Type*} [Fintype V] {G : SimpleGraph V} {R : ℕ}
    {A : Finset (PackedSubgraph V)} (hA : ∀ P ∈ A, IsFlexiblePiece G R P) :
    packedUnion A ≤ G := by
  classical
  apply Finset.sup_le
  intro P hP
  exact (hA P hP).2.2.1

lemma disjoint_packedEdges_iff {V : Type*} [Fintype V]
    {P Q : PackedSubgraph V} :
    Disjoint (packedEdges P) (packedEdges Q) ↔ Disjoint P.2 Q.2 := by
  rw [Finset.disjoint_left, SimpleGraph.disjoint_left]
  constructor
  · intro h u v huv huvQ
    exact h (a := s(u, v)) (by simpa using huv) (by simpa using huvQ)
  · intro h e heP heQ
    induction e using Sym2.inductionOn with
    | _ u v => exact h u v (by simpa using heP) (by simpa using heQ)

/-- A maximal edge-disjoint collection of flexible pieces exists in every finite graph. -/
theorem exists_maximal_flexibleFamily {V : Type*} [Fintype V]
    (G : SimpleGraph V) (R : ℕ) :
    ∃ A : Finset (PackedSubgraph V),
      (∀ P ∈ A, IsFlexiblePiece G R P) ∧
      (↑A : Set (PackedSubgraph V)).Pairwise
        (fun P Q => Disjoint P.2 Q.2) ∧
      ∀ P, IsFlexiblePiece G R P →
        (∀ Q ∈ A, P ≠ Q → Disjoint P.2 Q.2) → P ∈ A := by
  classical
  obtain ⟨A, hgood, hpair, hmax⟩ := exists_maximal_good_pairwiseDisjoint
    (α := PackedSubgraph V) (β := Sym2 V)
    (IsFlexiblePiece G R) packedEdges
  refine ⟨A, hgood, ?_, ?_⟩
  · intro P hP Q hQ hPQ
    exact disjoint_packedEdges_iff.mp (hpair hP hQ hPQ)
  · intro P hP hdisj
    apply hmax P hP
    intro Q hQ hPQ
    exact disjoint_packedEdges_iff.mpr (hdisj Q hQ hPQ)

/-- The finite robust-path extraction statement used in the packing argument.
For a fixed multiplicative range `R`, the threshold `d` is uniform over all
finite vertex types in the indicated universe. -/
def FlexiblePieceExtraction.{u} (R d : ℕ) : Prop :=
  ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
    ¬H.Colorable d → ∃ P : PackedSubgraph W, IsFlexiblePiece H R P

/-- A maximal packing leaves a `d`-colorable remainder. -/
theorem packedRemainder_colorable.{u} {V : Type u} [Fintype V]
    {G : SimpleGraph V} {R d : ℕ} (hextract : FlexiblePieceExtraction.{u} R d)
    {A : Finset (PackedSubgraph V)}
    (hgood : ∀ P ∈ A, IsFlexiblePiece G R P)
    (hmax : ∀ P, IsFlexiblePiece G R P →
      (∀ Q ∈ A, P ≠ Q → Disjoint P.2 Q.2) → P ∈ A) :
    (G \ packedUnion A).Colorable d := by
  classical
  by_contra hcolor
  obtain ⟨P, hP⟩ := hextract (W := V) (G \ packedUnion A) hcolor
  have hPdisj : ∀ Q ∈ A, P ≠ Q → Disjoint P.2 Q.2 := by
    intro Q hQ _hPQ
    rw [SimpleGraph.disjoint_left]
    intro x y hPxy hQxy
    have hrem : (G \ packedUnion A).Adj x y := hP.2.2.1 hPxy
    have hunion : (packedUnion A).Adj x y := le_packedUnion hQ hQxy
    exact hrem.2 hunion
  have hPin : P ∈ A := by
    apply hmax P
    · refine ⟨hP.1, hP.2.1, ?_, hP.2.2.2⟩
      exact hP.2.2.1.trans sdiff_le
    · exact hPdisj
  obtain ⟨e, he⟩ := hP.2.1
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hPxy : P.2.Adj x y := by simpa using he
      have hrem : (G \ packedUnion A).Adj x y := hP.2.2.1 hPxy
      have hunion : (packedUnion A).Adj x y := le_packedUnion hPin hPxy
      exact hrem.2 hunion

/-- Product coloring for the union of two spanning simple graphs. -/
theorem colorable_sup {V : Type*} {G₁ G₂ : SimpleGraph V} {p q : ℕ}
    (h₁ : G₁.Colorable p) (h₂ : G₂.Colorable q) :
    (G₁ ⊔ G₂).Colorable (p * q) := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  exact ⟨fun v ↦ finProdFinEquiv (c₁ v, c₂ v), by aesop⟩

/-- If the ambient graph needs more than `2*d` colors, the union of a maximal
flexible-piece packing is non-bipartite. -/
theorem packedUnion_not_colorable_two.{u} {V : Type u} [Fintype V]
    {G : SimpleGraph V} {R d : ℕ} (hextract : FlexiblePieceExtraction.{u} R d)
    {A : Finset (PackedSubgraph V)}
    (hgood : ∀ P ∈ A, IsFlexiblePiece G R P)
    (hmax : ∀ P, IsFlexiblePiece G R P →
      (∀ Q ∈ A, P ≠ Q → Disjoint P.2 Q.2) → P ∈ A)
    (hG : ¬G.Colorable (d * 2)) :
    ¬(packedUnion A).Colorable 2 := by
  intro htwo
  have hrem : (G \ packedUnion A).Colorable d :=
    packedRemainder_colorable hextract hgood hmax
  have hsup : ((G \ packedUnion A) ⊔ packedUnion A).Colorable (d * 2) :=
    colorable_sup hrem htwo
  have hle : packedUnion A ≤ G := packedUnion_le hgood
  exact hG (by simpa [sdiff_sup_cancel hle] using hsup)

/-! ### Finite step-two interval sums -/

/-- Distribute a prescribed total among finitely many natural capacities. -/
theorem exists_bounded_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (cap : ι → ℕ) {D : ℕ}
    (hD : D ≤ ∑ i ∈ s, cap i) :
    ∃ x : ι → ℕ, (∀ i ∈ s, x i ≤ cap i) ∧ ∑ i ∈ s, x i = D := by
  induction s using Finset.induction generalizing D with
  | empty =>
      have hDz : D = 0 := by simpa using hD
      exact ⟨fun _ => 0, by simp [hDz]⟩
  | @insert a s ha ih =>
      let xa := min (cap a) D
      have hrest : D - xa ≤ ∑ i ∈ s, cap i := by
        dsimp [xa]
        by_cases hsmall : D ≤ cap a
        · simp [min_eq_right hsmall]
        · rw [min_eq_left (Nat.le_of_not_ge hsmall)]
          have htotal : D ≤ cap a + ∑ i ∈ s, cap i := by
            simpa [ha] using hD
          omega
      obtain ⟨x, hx, hxsum⟩ := ih hrest
      refine ⟨fun i => if i = a then xa else x i, ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · simp [xa]
        · have hia : i ≠ a := by
            intro hia
            subst i
            exact ha hi
          simp [hia, hx i hi]
      · rw [Finset.sum_insert ha]
        simp only [if_pos]
        have hxa : xa ≤ D := min_le_right _ _
        have hsum :
            ∑ i ∈ s, (if i = a then xa else x i) = ∑ i ∈ s, x i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hia : i ≠ a := by
            intro hia
            subst i
            exact ha hi
          simp [hia]
        rw [hsum, hxsum]
        exact Nat.add_sub_of_le hxa

/-- Sums of finite step-two intervals contain every step-two value between
their endpoint sums.  The witness `j i` records how many increments are used
in coordinate `i`. -/
theorem exists_stepTwo_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (lo cap : ι → ℕ) {D : ℕ}
    (hD : D ≤ ∑ i ∈ s, cap i) :
    ∃ x j : ι → ℕ,
      (∀ i ∈ s, j i ≤ cap i ∧ x i = lo i + 2 * j i) ∧
      ∑ i ∈ s, x i = (∑ i ∈ s, lo i) + 2 * D := by
  obtain ⟨j, hj, hjsum⟩ := exists_bounded_sum s cap hD
  let x : ι → ℕ := fun i => lo i + 2 * j i
  refine ⟨x, j, ?_, ?_⟩
  · intro i hi
    exact ⟨hj i hi, rfl⟩
  · simp only [x, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hjsum]

/-- Least integer at least `a` with residue `r` modulo two. -/
def parityStart (a r : ℕ) : ℕ :=
  if a % 2 = r then a else a + 1

/-- Greatest integer at most `b` with residue `r` modulo two. -/
def parityEnd (b r : ℕ) : ℕ :=
  if b % 2 = r then b else b - 1

lemma parityStart_bounds (a r : ℕ) :
    a ≤ parityStart a r ∧ parityStart a r ≤ a + 1 := by
  by_cases h : a % 2 = r <;> simp [parityStart, h]

lemma parityStart_mod_two {a r : ℕ} (hr : r < 2) :
    parityStart a r % 2 = r := by
  rw [parityStart]
  split_ifs with h
  · exact h
  · have ha : a % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega

lemma parityStart_cast_eq_residue {a r : ℕ} (hr : r < 2) :
    (parityStart a r : ZMod 2) = (r : ZMod 2) := by
  calc
    (parityStart a r : ZMod 2) = ((parityStart a r % 2 : ℕ) : ZMod 2) :=
      (ZMod.natCast_mod _ 2).symm
    _ = (r : ZMod 2) := by rw [parityStart_mod_two hr]

lemma parityEnd_le (b r : ℕ) : parityEnd b r ≤ b := by
  by_cases h : b % 2 = r <;> simp [parityEnd, h]

lemma sub_one_le_parityEnd (b r : ℕ) : b - 1 ≤ parityEnd b r := by
  by_cases h : b % 2 = r <;> simp [parityEnd, h]

lemma parityEnd_mod_two {b r : ℕ} (hb : 0 < b) (hr : r < 2) :
    parityEnd b r % 2 = r := by
  rw [parityEnd]
  split_ifs with h
  · exact h
  · have hbmod : b % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega

lemma parityStart_le_parityEnd_mul {a T r : ℕ}
    (ha : 0 < a) (hT : 3 ≤ T) :
    parityStart a r ≤ parityEnd (a * T) r := by
  have hstart := (parityStart_bounds a r).2
  have hend := sub_one_le_parityEnd (a * T) r
  have hmul : 3 * a ≤ T * a := Nat.mul_le_mul_right a hT
  rw [mul_comm 3 a, mul_comm T a] at hmul
  omega

/-- Number of step-two increments available between the parity-adjusted
endpoints of `[a,a*T]`. -/
def parityCapacity (a T r : ℕ) : ℕ :=
  (parityEnd (a * T) r - parityStart a r) / 2

lemma parityEnd_eq_start_add_twice_capacity {a T r : ℕ}
    (ha : 0 < a) (hT : 3 ≤ T) (hr : r < 2) :
    parityEnd (a * T) r =
      parityStart a r + 2 * parityCapacity a T r := by
  have hle := parityStart_le_parityEnd_mul (r := r) ha hT
  have hstart := parityStart_mod_two (a := a) hr
  have hend := parityEnd_mod_two (b := a * T) (Nat.mul_pos ha (by omega)) hr
  simp only [parityCapacity]
  omega

lemma stepTwo_mem_parity_interval {a T r j : ℕ}
    (ha : 0 < a) (hT : 3 ≤ T) (hr : r < 2)
    (hj : j ≤ parityCapacity a T r) :
    a ≤ parityStart a r + 2 * j ∧
      parityStart a r + 2 * j ≤ a * T ∧
      (parityStart a r + 2 * j) % 2 = r := by
  have hlow := (parityStart_bounds a r).1
  have hend := parityEnd_eq_start_add_twice_capacity ha hT hr
  have hupparity := parityEnd_le (a * T) r
  have hmod := parityStart_mod_two (a := a) hr
  constructor
  · omega
  constructor
  · have htwice := Nat.mul_le_mul_left 2 hj
    omega
  · omega

/-- Coordinatewise parity intervals add without gaps (at step two). -/
theorem exists_parity_interval_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a r : ι → ℕ) {T N : ℕ}
    (ha : ∀ i ∈ s, 0 < a i) (hT : 3 ≤ T)
    (hr : ∀ i ∈ s, r i < 2)
    (hNlow : (∑ i ∈ s, parityStart (a i) (r i)) ≤ N)
    (hNhigh : N ≤ ∑ i ∈ s, parityEnd (a i * T) (r i))
    (hNmod : N % 2 = (∑ i ∈ s, parityStart (a i) (r i)) % 2) :
    ∃ x : ι → ℕ,
      (∀ i ∈ s, a i ≤ x i ∧ x i ≤ a i * T ∧ x i % 2 = r i) ∧
      ∑ i ∈ s, x i = N := by
  let lo : ι → ℕ := fun i => parityStart (a i) (r i)
  let cap : ι → ℕ := fun i => parityCapacity (a i) T (r i)
  let D := (N - ∑ i ∈ s, lo i) / 2
  have hend :
      (∑ i ∈ s, parityEnd (a i * T) (r i)) =
        (∑ i ∈ s, lo i) + 2 * ∑ i ∈ s, cap i := by
    calc
      (∑ i ∈ s, parityEnd (a i * T) (r i)) =
          ∑ i ∈ s, (lo i + 2 * cap i) := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [lo, cap]
        exact parityEnd_eq_start_add_twice_capacity (ha i hi) hT (hr i hi)
      _ = (∑ i ∈ s, lo i) + 2 * ∑ i ∈ s, cap i := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hrepr : N = (∑ i ∈ s, lo i) + 2 * D := by
    dsimp [D]
    have hmod : N % 2 = (∑ i ∈ s, lo i) % 2 := by
      simpa [lo] using hNmod
    have hlow : (∑ i ∈ s, lo i) ≤ N := by simpa [lo] using hNlow
    omega
  have hD : D ≤ ∑ i ∈ s, cap i := by
    have hhigh : N ≤ (∑ i ∈ s, lo i) + 2 * ∑ i ∈ s, cap i := by
      rw [← hend]
      exact hNhigh
    omega
  obtain ⟨x, j, hx, hxsum⟩ := exists_stepTwo_sum s lo cap hD
  refine ⟨x, ?_, ?_⟩
  · intro i hi
    obtain ⟨hj, hxi⟩ := hx i hi
    rw [hxi]
    simpa [lo, cap] using
      (stepTwo_mem_parity_interval (ha i hi) hT (hr i hi) hj)
  · rw [hxsum, ← hrepr]

/-- Add a fixed path length to a family of flexible parity intervals.  Once
the sum of upper endpoints covers `Q` times the lower endpoint, every total
of the prescribed parity in that multiplicative interval is represented. -/
theorem exists_parity_lengths_for_total {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a r : ι → ℕ) (L₀ Q : ℕ) {T : ℕ}
    (ha : ∀ i ∈ s, 0 < a i) (hT : 3 ≤ T)
    (hr : ∀ i ∈ s, r i < 2)
    (hcover :
      Q * (L₀ + ∑ i ∈ s, parityStart (a i) (r i)) ≤
        L₀ + ∑ i ∈ s, parityEnd (a i * T) (r i))
    {N : ℕ}
    (hNlow : L₀ + (∑ i ∈ s, parityStart (a i) (r i)) ≤ N)
    (hNhigh : N ≤ Q * (L₀ + ∑ i ∈ s, parityStart (a i) (r i)))
    (hNmod : N % 2 =
      (L₀ + ∑ i ∈ s, parityStart (a i) (r i)) % 2) :
    ∃ x : ι → ℕ,
      (∀ i ∈ s, a i ≤ x i ∧ x i ≤ a i * T ∧ x i % 2 = r i) ∧
      L₀ + ∑ i ∈ s, x i = N := by
  let M := N - L₀
  have hMlow : (∑ i ∈ s, parityStart (a i) (r i)) ≤ M := by
    dsimp [M]
    omega
  have hMhigh : M ≤ ∑ i ∈ s, parityEnd (a i * T) (r i) := by
    dsimp [M]
    omega
  have hMmod : M % 2 = (∑ i ∈ s, parityStart (a i) (r i)) % 2 := by
    dsimp [M]
    omega
  obtain ⟨x, hx, hxsum⟩ :=
    exists_parity_interval_sum s a r ha hT hr hMlow hMhigh hMmod
  refine ⟨x, hx, ?_⟩
  dsimp [M] at hxsum
  omega

/-- A one-third share of the total base weight suffices for a multiplicative
interval.  The deliberately generous factor `6*Q+3` absorbs both parity
rounding and the fixed complementary paths. -/
theorem parity_interval_cover_of_weight {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a r : ι → ℕ) (L₀ Q : ℕ)
    (ha : ∀ i ∈ s, 0 < a i)
    (hweight :
      L₀ + (∑ i ∈ s, (a i + 1)) ≤ 3 * ∑ i ∈ s, (a i + 1)) :
    Q * (L₀ + ∑ i ∈ s, parityStart (a i) (r i)) ≤
      L₀ + ∑ i ∈ s, parityEnd (a i * (6 * Q + 3)) (r i) := by
  let A := ∑ i ∈ s, a i
  let W := ∑ i ∈ s, (a i + 1)
  have hcard : s.card ≤ A := by
    calc
      s.card = ∑ _i ∈ s, 1 := by simp
      _ ≤ ∑ i ∈ s, a i := Finset.sum_le_sum fun i hi => ha i hi
      _ = A := rfl
  have hW : W = A + s.card := by
    dsimp [W, A]
    simp only [Finset.sum_add_distrib]
    simp
  have hWtwo : W ≤ 2 * A := by omega
  have hstart :
      (∑ i ∈ s, parityStart (a i) (r i)) ≤ W := by
    dsimp [W]
    exact Finset.sum_le_sum fun i _ => (parityStart_bounds (a i) (r i)).2
  have hL :
      L₀ + (∑ i ∈ s, parityStart (a i) (r i)) ≤ 3 * W := by
    exact (Nat.add_le_add_left hstart L₀).trans hweight
  have hQL :
      Q * (L₀ + ∑ i ∈ s, parityStart (a i) (r i)) ≤ 6 * Q * A := by
    calc
      Q * (L₀ + ∑ i ∈ s, parityStart (a i) (r i)) ≤ Q * (3 * W) :=
        Nat.mul_le_mul_left Q hL
      _ = 3 * Q * W := by ring
      _ ≤ 3 * Q * (2 * A) := Nat.mul_le_mul_left (3 * Q) hWtwo
      _ = 6 * Q * A := by ring
  have hpoint : ∀ i ∈ s,
      6 * Q * a i ≤ parityEnd (a i * (6 * Q + 3)) (r i) := by
    intro i hi
    have hend := sub_one_le_parityEnd (a i * (6 * Q + 3)) (r i)
    have hai := ha i hi
    have hmul : 6 * Q * a i ≤ a i * (6 * Q + 3) - 1 := by
      apply Nat.le_sub_one_of_lt
      calc
        6 * Q * a i < 6 * Q * a i + 3 * a i :=
          Nat.lt_add_of_pos_right (Nat.mul_pos (by norm_num) hai)
        _ = a i * (6 * Q + 3) := by ring
    exact hmul.trans hend
  have hsum : 6 * Q * A ≤
      ∑ i ∈ s, parityEnd (a i * (6 * Q + 3)) (r i) := by
    calc
      6 * Q * A = ∑ i ∈ s, 6 * Q * a i := by
        dsimp [A]
        simp only [Finset.mul_sum]
      _ ≤ ∑ i ∈ s, parityEnd (a i * (6 * Q + 3)) (r i) :=
        Finset.sum_le_sum hpoint
  exact hQL.trans (hsum.trans (Nat.le_add_left _ _))

/-- Every flexible piece supplies a parity-compatible path no longer than
one more than its base length. -/
lemma FlexiblePathData.exists_short_path {V : Type*} [Fintype V] {R : ℕ}
    {P : PackedSubgraph V} (D : FlexiblePathData R P) (hR : 3 ≤ R)
    {u v : V} (hu : u ∈ P.1) (hv : v ∈ P.1) (huv : u ≠ v) :
    ∃ p : P.2.Walk u v, p.IsPath ∧ p.length ≤ D.base + 1 ∧
      ∀ x ∈ p.support, x ∈ P.1 := by
  have hn := stepTwo_mem_parity_interval D.base_pos hR
    (D.residue_lt_two u v)
    (show 0 ≤ parityCapacity D.base R (D.residue u v) by omega)
  obtain ⟨p, hp, hplen, hsupp⟩ :=
    D.hasPath_of_modEq hu hv huv hn.1 hn.2.1 hn.2.2
  refine ⟨p, hp, ?_, hsupp⟩
  simpa [hplen] using (parityStart_bounds D.base (D.residue u v)).2

/-- The canonical lower endpoint itself is realized by a path. -/
lemma FlexiblePathData.exists_parityStart_path {V : Type*} [Fintype V]
    {R : ℕ} {P : PackedSubgraph V} (D : FlexiblePathData R P) (hR : 3 ≤ R)
    {u v : V} (hu : u ∈ P.1) (hv : v ∈ P.1) (huv : u ≠ v) :
    ∃ p : P.2.Walk u v, p.IsPath ∧
      p.length = parityStart D.base (D.residue u v) ∧
      ∀ x ∈ p.support, x ∈ P.1 := by
  have hn := stepTwo_mem_parity_interval D.base_pos hR
    (D.residue_lt_two u v)
    (show 0 ≤ parityCapacity D.base R (D.residue u v) by omega)
  exact D.hasPath_of_modEq hu hv huv hn.1 hn.2.1 hn.2.2

/-! ### Output of the minimal odd gadget-cycle construction -/

/-- The precise data extracted from the minimal odd cyclic sequence in
Liu--Montgomery Section 5.  The `realizes` field states the simple-cycle
assembly property after the fixed paths and the pairwise separated variable
pieces have been selected. -/
structure VariableCycleAssembly.{u} {V : Type u} [Fintype V]
    (G : SimpleGraph V) (T : ℕ) where
  Index : Type u
  [indexFintype : Fintype Index]
  [indexNonempty : Nonempty Index]
  piece : Index → PackedSubgraph V
  data : (i : Index) → FlexiblePathData T (piece i)
  left : Index → V
  right : Index → V
  left_mem : ∀ i, left i ∈ (piece i).1
  right_mem : ∀ i, right i ∈ (piece i).1
  endpoints_ne : ∀ P, left P ≠ right P
  fixedLength : ℕ
  weight :
    fixedLength + (∑ P, ((data P).base + 1)) ≤
      3 * ∑ P, ((data P).base + 1)
  lower_odd : Odd
    (fixedLength + ∑ P,
      parityStart (data P).base ((data P).residue (left P) (right P)))
  realizes : ∀ x : Index → ℕ,
    (∀ P, (data P).base ≤ x P ∧ x P ≤ (data P).base * T ∧
      x P % 2 = (data P).residue (left P) (right P)) →
    HasCycleLength G (fixedLength + ∑ P, x P)

lemma mod_two_eq_one_of_odd {n : ℕ} (hn : Odd n) : n % 2 = 1 := by
  have hne : n % 2 ≠ 0 := by
    intro hzero
    exact (Nat.not_even_iff_odd.mpr hn) (Nat.even_iff.mpr hzero)
  rcases Nat.mod_two_eq_zero_or_one n with hzero | hone
  · exact (hne hzero).elim
  · exact hone

/-- The assembly data produces the full odd interval needed by the harmonic
argument. -/
theorem oddCycleInterval_of_variableCycleAssembly {V : Type*} [Fintype V]
    {G : SimpleGraph V} (Q : ℕ)
    (A : VariableCycleAssembly G (6 * Q + 3)) :
    ∃ L : ℕ, 0 < L ∧
      ∀ n : ℕ, L ≤ n → n ≤ Q * L → Odd n → HasCycleLength G n := by
  classical
  let : Fintype A.Index := A.indexFintype
  let : Nonempty A.Index := A.indexNonempty
  let a : A.Index → ℕ := fun P => (A.data P).base
  let r : A.Index → ℕ := fun P =>
    (A.data P).residue (A.left P) (A.right P)
  let L : ℕ := A.fixedLength + ∑ P, parityStart (a P) (r P)
  have ha : ∀ P ∈ (Finset.univ : Finset A.Index), 0 < a P := by
    intro P _
    exact (A.data P).base_pos
  have hr : ∀ P ∈ (Finset.univ : Finset A.Index), r P < 2 := by
    intro P _
    exact (A.data P).residue_lt_two (A.left P) (A.right P)
  have hweight :
      A.fixedLength + (∑ P : A.Index, (a P + 1)) ≤
        3 * ∑ P : A.Index, (a P + 1) := by
    simpa [a] using A.weight
  have hcover :
      Q * (A.fixedLength + ∑ P : A.Index, parityStart (a P) (r P)) ≤
        A.fixedLength + ∑ P : A.Index,
          parityEnd (a P * (6 * Q + 3)) (r P) := by
    simpa using parity_interval_cover_of_weight
      (Finset.univ : Finset A.Index) a r A.fixedLength Q ha hweight
  have hLpos : 0 < L := by
    let P' : A.Index := Classical.choice A.indexNonempty
    have hterm : 0 < parityStart (a P') (r P') :=
      (ha P' (Finset.mem_univ _)).trans_le (parityStart_bounds (a P') (r P')).1
    have hsum : parityStart (a P') (r P') ≤
        ∑ X : A.Index, parityStart (a X) (r X) := by
      simpa using (Finset.single_le_sum
        (s := (Finset.univ : Finset A.Index))
        (f := fun X => parityStart (a X) (r X))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ P'))
    change 0 < A.fixedLength + ∑ X : A.Index, parityStart (a X) (r X)
    exact hterm.trans_le (hsum.trans (Nat.le_add_left _ _))
  refine ⟨L, hLpos, ?_⟩
  intro n hnlow hnhigh hnodd
  have hLodd : Odd L := by simpa [L, a, r] using A.lower_odd
  have hnmod : n % 2 = L % 2 := by
    rw [mod_two_eq_one_of_odd hnodd, mod_two_eq_one_of_odd hLodd]
  obtain ⟨x, hx, hxsum⟩ := exists_parity_lengths_for_total
    (Finset.univ : Finset A.Index) a r A.fixedLength Q ha
    (by omega) hr hcover (by simpa [L] using hnlow)
    (by simpa [L] using hnhigh) (by simpa [L] using hnmod)
  rw [← hxsum]
  apply A.realizes x
  intro P
  simpa [a, r] using hx P (Finset.mem_univ P)

/-- The structural Section 5 assertion: every non-bipartite edge-disjoint
union of flexible pieces has a separated variable-cycle assembly. -/
def FlexiblePackingAssembly.{u} : Prop :=
  ∀ (T : ℕ), 3 ≤ T → ∀ {V : Type u} [Fintype V]
    {G : SimpleGraph V} {A : Finset (PackedSubgraph V)},
    (∀ P ∈ A, IsFlexiblePiece G T P) →
    (↑A : Set (PackedSubgraph V)).Pairwise (fun P Q => Disjoint P.2 Q.2) →
    ¬(packedUnion A).Colorable 2 →
      Nonempty (VariableCycleAssembly G T)

/-- Uniform robust-path extraction at every requested multiplicative scale. -/
def FlexiblePieceTheorem.{u} : Prop :=
  ∀ T : ℕ, ∃ d : ℕ, FlexiblePieceExtraction.{u} T d

/-! ### Signed incidence graph of a flexible-piece family -/

/-- Vertices used to turn the parity constraints of overlapping bipartite
pieces into an ordinary graph.  The last summand contains one potential
subdivision vertex for every piece/ambient-vertex pair. -/
abbrev FamilyAuxVertex (V : Type*) (A : Finset (PackedSubgraph V)) :=
  V ⊕ (↥A ⊕ (↥A × V))

/-- Adjacency in the signed incidence graph.  An incidence of piece-color
`1` is represented by one edge, while an incidence of piece-color `0` is
represented by a two-edge path through its dedicated subdivision vertex. -/
def familyAuxAdj {V : Type*} [Fintype V] {A : Finset (PackedSubgraph V)}
    {T : ℕ} (D : (P : ↥A) → FlexiblePathData T P.1) :
    FamilyAuxVertex V A → FamilyAuxVertex V A → Prop
  | .inl v, .inr (.inl P) => v ∈ P.1.1 ∧ (D P).color v = 1
  | .inr (.inl P), .inl v => v ∈ P.1.1 ∧ (D P).color v = 1
  | .inl v, .inr (.inr (P, w)) =>
      v = w ∧ w ∈ P.1.1 ∧ (D P).color w = 0
  | .inr (.inr (P, w)), .inl v =>
      v = w ∧ w ∈ P.1.1 ∧ (D P).color w = 0
  | .inr (.inl P), .inr (.inr (Q, w)) =>
      P = Q ∧ w ∈ Q.1.1 ∧ (D Q).color w = 0
  | .inr (.inr (Q, w)), .inr (.inl P) =>
      P = Q ∧ w ∈ Q.1.1 ∧ (D Q).color w = 0
  | _, _ => False

/-- The ordinary simple graph encoding the signed incidence constraints. -/
def familyAuxGraph {V : Type*} [Fintype V] {A : Finset (PackedSubgraph V)}
    {T : ℕ} (D : (P : ↥A) → FlexiblePathData T P.1) :
    SimpleGraph (FamilyAuxVertex V A) where
  Adj := familyAuxAdj D
  symm := by
    constructor
    intro x y hxy
    cases x with
    | inl v =>
        cases y with
        | inl w => exact hxy.elim
        | inr z =>
            cases z with
            | inl P => exact hxy
            | inr Pw =>
                rcases Pw with ⟨P, w⟩
                exact hxy
    | inr z =>
        cases z with
        | inl P =>
            cases y with
            | inl v => exact hxy
            | inr z' =>
                cases z' with
                | inl Q => exact hxy.elim
                | inr Qw =>
                    rcases Qw with ⟨Q, w⟩
                    exact hxy
        | inr Pw =>
            rcases Pw with ⟨P, w⟩
            cases y with
            | inl v => exact hxy
            | inr z' =>
                cases z' with
                | inl Q => exact hxy
                | inr Qz => exact hxy.elim
  loopless := by
    constructor
    intro x
    cases x with
    | inl v => exact id
    | inr z =>
        cases z with
        | inl P => exact id
        | inr Pw => exact id

@[simp] lemma familyAuxGraph_adj_vertex_piece {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1) (v : V) (P : ↥A) :
    (familyAuxGraph D).Adj (.inl v) (.inr (.inl P)) ↔
      v ∈ P.1.1 ∧ (D P).color v = 1 :=
  Iff.rfl

@[simp] lemma familyAuxGraph_adj_vertex_dummy {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1) (v w : V) (P : ↥A) :
    (familyAuxGraph D).Adj (.inl v) (.inr (.inr (P, w))) ↔
      v = w ∧ w ∈ P.1.1 ∧ (D P).color w = 0 :=
  Iff.rfl

@[simp] lemma familyAuxGraph_adj_piece_dummy {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1) (P Q : ↥A) (w : V) :
    (familyAuxGraph D).Adj (.inr (.inl P)) (.inr (.inr (Q, w))) ↔
      P = Q ∧ w ∈ Q.1.1 ∧ (D Q).color w = 0 :=
  Iff.rfl

lemma fin_two_eq_zero_or_one (x : Fin 2) : x = 0 ∨ x = 1 := by
  have hx : x.val = 0 ∨ x.val = 1 := by omega
  rcases hx with hx | hx
  · left
    exact Fin.ext hx
  · right
    exact Fin.ext hx

lemma FlexiblePathData.residue_eq_colorVal_add_mod {V : Type*} [Fintype V]
    {R : ℕ} {P : PackedSubgraph V} (D : FlexiblePathData R P) (u v : V) :
    D.residue u v = ((D.color u).val + (D.color v).val) % 2 := by
  rcases fin_two_eq_zero_or_one (D.color u) with hu | hu <;>
    rcases fin_two_eq_zero_or_one (D.color v) with hv | hv <;>
    simp [FlexiblePathData.residue, hu, hv]

lemma FlexiblePathData.residue_cast_eq_color_val_add {V : Type*} [Fintype V]
    {R : ℕ} {P : PackedSubgraph V} (D : FlexiblePathData R P) (u v : V) :
    (D.residue u v : ZMod 2) =
      ((D.color u).val : ZMod 2) + ((D.color v).val : ZMod 2) := by
  rcases fin_two_eq_zero_or_one (D.color u) with hu | hu <;>
    rcases fin_two_eq_zero_or_one (D.color v) with hv | hv <;>
    simp [FlexiblePathData.residue, hu, hv] <;> decide

/-- In a bipartite graph, the parity of a walk is the sum of the endpoint
color bits.  The `ZMod 2` formulation is convenient for cyclic splicing. -/
lemma coloring_walk_length_cast_eq_color_val_add {V : Type*} {G : SimpleGraph V}
    (color : G.Coloring (Fin 2)) {u v : V} (p : G.Walk u v) :
    (p.length : ZMod 2) =
      ((color u).val : ZMod 2) + ((color v).val : ZMod 2) := by
  let boolColor : G.Coloring Bool :=
    SimpleGraph.recolorOfEquiv G finTwoEquiv color
  have heven := boolColor.even_length_iff_congr p
  rcases fin_two_eq_zero_or_one (color u) with hu | hu <;>
    rcases fin_two_eq_zero_or_one (color v) with hv | hv
  · have hpEven : Even p.length := by
      apply heven.mpr
      simp [boolColor, SimpleGraph.recolorOfEquiv, finTwoEquiv, hu, hv]
    have hmod := Nat.even_iff.mp hpEven
    calc
      (p.length : ZMod 2) = ((p.length % 2 : ℕ) : ZMod 2) :=
        (ZMod.natCast_mod _ 2).symm
      _ = ((color u).val : ZMod 2) + ((color v).val : ZMod 2) := by
        simp [hmod, hu, hv] <;> decide
  · have hpNotEven : ¬Even p.length := by
      intro hp
      have := heven.mp hp
      simpa [boolColor, SimpleGraph.recolorOfEquiv, finTwoEquiv, hu, hv] using this
    have hmod : p.length % 2 = 1 :=
      (Nat.mod_two_eq_zero_or_one p.length).resolve_left
        (fun hzero => hpNotEven (Nat.even_iff.mpr hzero))
    calc
      (p.length : ZMod 2) = ((p.length % 2 : ℕ) : ZMod 2) :=
        (ZMod.natCast_mod _ 2).symm
      _ = ((color u).val : ZMod 2) + ((color v).val : ZMod 2) := by
        simp [hmod, hu, hv] <;> decide
  · have hpNotEven : ¬Even p.length := by
      intro hp
      have := heven.mp hp
      simpa [boolColor, SimpleGraph.recolorOfEquiv, finTwoEquiv, hu, hv] using this
    have hmod : p.length % 2 = 1 :=
      (Nat.mod_two_eq_zero_or_one p.length).resolve_left
        (fun hzero => hpNotEven (Nat.even_iff.mpr hzero))
    calc
      (p.length : ZMod 2) = ((p.length % 2 : ℕ) : ZMod 2) :=
        (ZMod.natCast_mod _ 2).symm
      _ = ((color u).val : ZMod 2) + ((color v).val : ZMod 2) := by
        rw [hmod, hu, hv]
        decide
  · have hpEven : Even p.length := by
      apply heven.mpr
      simp [boolColor, SimpleGraph.recolorOfEquiv, finTwoEquiv, hu, hv]
    have hmod := Nat.even_iff.mp hpEven
    calc
      (p.length : ZMod 2) = ((p.length % 2 : ℕ) : ZMod 2) :=
        (ZMod.natCast_mod _ 2).symm
      _ = ((color u).val : ZMod 2) + ((color v).val : ZMod 2) := by
        rw [hmod, hu, hv]
        decide

lemma fin_two_eq_of_ne_of_ne {x y z : Fin 2} (hxy : x ≠ y) (hyz : y ≠ z) :
    x = z := by
  rcases fin_two_eq_zero_or_one x with rfl | rfl <;>
    rcases fin_two_eq_zero_or_one y with rfl | rfl <;>
    rcases fin_two_eq_zero_or_one z with rfl | rfl <;> simp_all

lemma finTwo_val_add_eq_of_eq_iff_eq (a b c d : Fin 2)
    (h : (a = b ↔ c = d)) :
    (a.val : ZMod 2) + b.val = (c.val : ZMod 2) + d.val := by
  rcases fin_two_eq_zero_or_one a with rfl | rfl <;>
    rcases fin_two_eq_zero_or_one b with rfl | rfl <;>
    rcases fin_two_eq_zero_or_one c with rfl | rfl <;>
    rcases fin_two_eq_zero_or_one d with rfl | rfl <;>
    simp_all only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.cast_one, Nat.zero_mod,
    Nat.cast_zero, add_zero] <;> decide

lemma finTwo_cross_val_add_eq_of_eq_iff_eq (a b c d : Fin 2)
    (h : (a = b ↔ c = d)) :
    (a.val : ZMod 2) + c.val = (b.val : ZMod 2) + d.val := by
  rcases fin_two_eq_zero_or_one a with rfl | rfl <;>
    rcases fin_two_eq_zero_or_one b with rfl | rfl <;>
    rcases fin_two_eq_zero_or_one c with rfl | rfl <;>
    rcases fin_two_eq_zero_or_one d with rfl | rfl <;>
    simp_all only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.cast_one, Nat.zero_mod,
    Nat.cast_zero, add_zero] <;> decide

/-- If the two pairs of binary colors contribute odd total parity, equality
inside the first pair cannot be equivalent to equality inside the second. -/
lemma finTwo_pair_relations_ne_of_val_sum_eq_one (a b c d : Fin 2)
    (h : (a.val : ZMod 2) + b.val + c.val + d.val = 1) :
    ¬((a = b) ↔ (c = d)) := by
  intro hab
  have heq := finTwo_val_add_eq_of_eq_iff_eq a b c d hab
  have hzero : (a.val : ZMod 2) + b.val + c.val + d.val = 0 := by
    rw [heq]
    ring_nf
    simp [show (2 : ZMod 2) = 0 by decide]
  have hone : (0 : ZMod 2) = 1 := hzero.symm.trans h
  norm_num at hone

/-- Two distinct combined binary-color signatures divide all vertices into
complementary equality classes. -/
lemma finTwo_combined_relations_complementary
    (p q p₀ q₀ p₁ q₁ : Fin 2)
    (h : ¬((p₀ = p₁) ↔ (q₀ = q₁))) :
    ((p = p₀ ↔ q = q₀) ↔ ¬(p = p₁ ↔ q = q₁)) := by
  rcases fin_two_eq_zero_or_one p with rfl | rfl <;>
    rcases fin_two_eq_zero_or_one q with rfl | rfl <;>
    rcases fin_two_eq_zero_or_one p₀ with rfl | rfl <;>
    rcases fin_two_eq_zero_or_one q₀ with rfl | rfl <;>
    rcases fin_two_eq_zero_or_one p₁ with rfl | rfl <;>
    rcases fin_two_eq_zero_or_one q₁ with rfl | rfl <;>
    simp_all

lemma familyAuxColor_eq_piece_of_color_zero {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (z : (familyAuxGraph D).Coloring (Fin 2)) (P : ↥A) (v : V)
    (hv : v ∈ P.1.1) (hcolor : (D P).color v = 0) :
    z (.inl v) = z (.inr (.inl P)) := by
  let dummy : FamilyAuxVertex V A := .inr (.inr (P, v))
  have hvd : (familyAuxGraph D).Adj (.inl v) dummy := by
    simp [dummy, hv, hcolor]
  have hdp : (familyAuxGraph D).Adj dummy (.inr (.inl P)) := by
    simpa [dummy, hv, hcolor] using
      (show (familyAuxGraph D).Adj (.inr (.inl P)) dummy by
        simp [dummy, hv, hcolor]) |>.symm
  exact fin_two_eq_of_ne_of_ne (z.valid hvd) (z.valid hdp)

lemma familyAuxColor_ne_piece_of_color_one {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (z : (familyAuxGraph D).Coloring (Fin 2)) (P : ↥A) (v : V)
    (hv : v ∈ P.1.1) (hcolor : (D P).color v = 1) :
    z (.inl v) ≠ z (.inr (.inl P)) :=
  z.valid (by simp [hv, hcolor])

lemma exists_piece_adj_of_packedUnion_adj {V : Type*}
    {A : Finset (PackedSubgraph V)} {u v : V}
    (h : (packedUnion A).Adj u v) :
    ∃ P ∈ A, P.2.Adj u v := by
  classical
  induction A using Finset.induction with
  | empty => simpa [packedUnion] using h
  | @insert P A hPA ih =>
      rw [packedUnion, Finset.sup_insert, SimpleGraph.sup_adj] at h
      rcases h with hP | hA
      · exact ⟨P, Finset.mem_insert_self _ _, hP⟩
      · obtain ⟨Q, hQA, hQ⟩ := ih (by simpa [packedUnion] using hA)
        exact ⟨Q, Finset.mem_insert_of_mem hQA, hQ⟩

/-- A two-coloring of the auxiliary signed-incidence graph induces a
two-coloring of the packed union. -/
theorem packedUnion_colorable_of_familyAuxColorable {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (hcarrier : ∀ P : ↥A, ∀ ⦃u v⦄, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (haux : (familyAuxGraph D).Colorable 2) :
    (packedUnion A).Colorable 2 := by
  obtain ⟨z⟩ := haux
  refine ⟨SimpleGraph.Coloring.mk (fun v => z (.inl v)) ?_⟩
  intro u v huv
  obtain ⟨P, hP, hPuv⟩ := exists_piece_adj_of_packedUnion_adj huv
  let P' : ↥A := ⟨P, hP⟩
  have hmem := hcarrier P' hPuv
  have hcne : (D P').color u ≠ (D P').color v :=
    (D P').color.valid hPuv
  rcases fin_two_eq_zero_or_one ((D P').color u) with hu0 | hu1 <;>
    rcases fin_two_eq_zero_or_one ((D P').color v) with hv0 | hv1
  · exact (hcne (hu0.trans hv0.symm)).elim
  · have hzu := familyAuxColor_eq_piece_of_color_zero D z P' u hmem.1 hu0
    have hzv := familyAuxColor_ne_piece_of_color_one D z P' v hmem.2 hv1
    intro huvz
    exact hzv (huvz.symm.trans hzu)
  · have hzu := familyAuxColor_ne_piece_of_color_one D z P' u hmem.1 hu1
    have hzv := familyAuxColor_eq_piece_of_color_zero D z P' v hmem.2 hv0
    intro huvz
    exact hzu (huvz.trans hzv)
  · exact (hcne (hu1.trans hv1.symm)).elim

/-- Canonical path data for every member of a proved flexible family. -/
noncomputable def flexibleFamilyData {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {G : SimpleGraph V} {T : ℕ}
    (hgood : ∀ P ∈ A, IsFlexiblePiece G T P)
    (P : ↥A) : FlexiblePathData T P.1 :=
  (hgood P.1 P.2).pathData

theorem familyAuxGraph_not_colorable_two {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {G : SimpleGraph V} {T : ℕ}
    (hgood : ∀ P ∈ A, IsFlexiblePiece G T P)
    (hunion : ¬(packedUnion A).Colorable 2) :
    ¬(familyAuxGraph (flexibleFamilyData hgood)).Colorable 2 := by
  intro haux
  apply hunion
  apply packedUnion_colorable_of_familyAuxColorable
    (flexibleFamilyData hgood) (haux := haux)
  intro P u v huv
  exact (hgood P.1 P.2).2.2.2.1 huv

/-- A non-bipartite packed union yields an odd simple cycle in its signed
incidence graph. -/
theorem exists_odd_familyAux_cycle {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {G : SimpleGraph V} {T : ℕ}
    (hgood : ∀ P ∈ A, IsFlexiblePiece G T P)
    (hunion : ¬(packedUnion A).Colorable 2) :
    ∃ z, ∃ c : (familyAuxGraph (flexibleFamilyData hgood)).Walk z z,
      c.IsCycle ∧ Odd c.length := by
  have haux := familyAuxGraph_not_colorable_two hgood hunion
  by_contra hcycle
  apply haux
  apply Erdos58.colorable_two_of_no_odd_isCycle
  intro z c hc hodd
  exact hcycle ⟨z, c, hc, hodd⟩

/-- Piece nodes occurring in the support of an auxiliary walk. -/
noncomputable def auxPiecesInWalk {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {x y : FamilyAuxVertex V A} (w : (familyAuxGraph D).Walk x y) :
    Finset ↥A := by
  classical
  exact Finset.univ.filter fun P => (.inr (.inl P) : FamilyAuxVertex V A) ∈ w.support

@[simp] lemma mem_auxPiecesInWalk_iff {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {x y : FamilyAuxVertex V A} {w : (familyAuxGraph D).Walk x y} {P : ↥A} :
    P ∈ auxPiecesInWalk w ↔
      (.inr (.inl P) : FamilyAuxVertex V A) ∈ w.support := by
  classical
  simp [auxPiecesInWalk]

lemma auxPiecesInWalk_mono_support {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {x y x' y' : FamilyAuxVertex V A}
    {p : (familyAuxGraph D).Walk x y} {q : (familyAuxGraph D).Walk x' y'}
    (h : ∀ z ∈ p.support, z ∈ q.support) :
    auxPiecesInWalk p ⊆ auxPiecesInWalk q := by
  intro P hP
  rw [mem_auxPiecesInWalk_iff] at hP ⊢
  exact h _ hP

/-- Choose an odd auxiliary cycle with the minimum possible number of piece
nodes.  This is the formal minimization used to eliminate nonconsecutive
piece intersections. -/
theorem exists_minimal_odd_familyAux_cycle {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {G : SimpleGraph V} {T : ℕ}
    (hgood : ∀ P ∈ A, IsFlexiblePiece G T P)
    (hunion : ¬(packedUnion A).Colorable 2) :
    ∃ z, ∃ c : (familyAuxGraph (flexibleFamilyData hgood)).Walk z z,
      c.IsCycle ∧ Odd c.length ∧
      ∀ z' (c' : (familyAuxGraph (flexibleFamilyData hgood)).Walk z' z'),
        c'.IsCycle → Odd c'.length →
          (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card := by
  classical
  let GoodCount : ℕ → Prop := fun m =>
    ∃ z, ∃ c : (familyAuxGraph (flexibleFamilyData hgood)).Walk z z,
      c.IsCycle ∧ Odd c.length ∧ (auxPiecesInWalk c).card = m
  have hGoodCount : ∃ m, GoodCount m := by
    obtain ⟨z, c, hc, hodd⟩ := exists_odd_familyAux_cycle hgood hunion
    exact ⟨(auxPiecesInWalk c).card, z, c, hc, hodd, rfl⟩
  obtain ⟨z, c, hc, hodd, hcount⟩ := Nat.find_spec hGoodCount
  refine ⟨z, c, hc, hodd, ?_⟩
  intro z' c' hc' hodd'
  rw [hcount]
  exact Nat.find_min' hGoodCount
    ⟨z', c', hc', hodd', rfl⟩

/-! ### Canonical incidence paths and chords -/

/-- The path in the auxiliary graph representing one piece/vertex
incidence.  Color `1` uses one edge and color `0` uses the dedicated
two-edge subdivision. -/
noncomputable def incidenceWalk {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (P : ↥A) (v : V) (hv : v ∈ P.1.1) :
    (familyAuxGraph D).Walk (.inl v) (.inr (.inl P)) := by
  classical
  by_cases hzero : (D P).color v = 0
  · let d : FamilyAuxVertex V A := .inr (.inr (P, v))
    have hvd : (familyAuxGraph D).Adj (.inl v) d := by
      simp [d, hv, hzero]
    have hdp : (familyAuxGraph D).Adj d (.inr (.inl P)) := by
      apply (show (familyAuxGraph D).Adj (.inr (.inl P)) d by
        simp [d, hv, hzero]).symm
    exact hvd.toWalk.append hdp.toWalk
  · have hone : (D P).color v = 1 := by
      rcases fin_two_eq_zero_or_one ((D P).color v) with h | h
      · exact (hzero h).elim
      · exact h
    exact (show (familyAuxGraph D).Adj (.inl v) (.inr (.inl P)) by
      simp [hv, hone]).toWalk

lemma incidenceWalk_length {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (P : ↥A) (v : V) (hv : v ∈ P.1.1) :
    (incidenceWalk D P v hv).length =
      if (D P).color v = 0 then 2 else 1 := by
  classical
  unfold incidenceWalk
  split <;> simp

lemma incidenceWalk_length_cast {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (P : ↥A) (v : V) (hv : v ∈ P.1.1) :
    ((incidenceWalk D P v hv).length : ZMod 2) =
      ((D P).color v).val := by
  rw [incidenceWalk_length]
  rcases fin_two_eq_zero_or_one ((D P).color v) with h | h <;>
    simp only [Fin.isValue, Nat.cast_ite, Nat.cast_ofNat, Nat.cast_one] <;> decide

lemma incidenceWalk_isPath {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (P : ↥A) (v : V) (hv : v ∈ P.1.1) :
    (incidenceWalk D P v hv).IsPath := by
  classical
  unfold incidenceWalk
  split <;> simp

lemma mem_incidenceWalk_support_iff {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (P : ↥A) (v : V) (hv : v ∈ P.1.1) (x : FamilyAuxVertex V A) :
    x ∈ (incidenceWalk D P v hv).support ↔
      x = .inl v ∨ x = .inr (.inl P) ∨
        ((D P).color v = 0 ∧ x = .inr (.inr (P, v))) := by
  classical
  unfold incidenceWalk
  split <;> rename_i hzero
  · simp [SimpleGraph.Walk.support_append]
    tauto
  · have hzero' : ¬(0 : Fin 2) = (D P).color v := fun h => hzero h.symm
    simp [hzero, hzero']

/-- The canonical auxiliary path between two pieces meeting at `v`. -/
noncomputable def pieceChord {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (P Q : ↥A) (v : V) (hvP : v ∈ P.1.1) (hvQ : v ∈ Q.1.1) :
    (familyAuxGraph D).Walk (.inr (.inl P)) (.inr (.inl Q)) :=
  (incidenceWalk D P v hvP).reverse.append (incidenceWalk D Q v hvQ)

lemma pieceChord_length_cast {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (P Q : ↥A) (v : V) (hvP : v ∈ P.1.1) (hvQ : v ∈ Q.1.1) :
    ((pieceChord D P Q v hvP hvQ).length : ZMod 2) =
      (((D P).color v).val : ZMod 2) + ((D Q).color v).val := by
  simp only [pieceChord, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_reverse, Nat.cast_add]
  rw [incidenceWalk_length_cast, incidenceWalk_length_cast]

lemma auxPiecesInWalk_pieceChord_subset {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (P Q : ↥A) (v : V) (hvP : v ∈ P.1.1) (hvQ : v ∈ Q.1.1) :
    (↑(auxPiecesInWalk (pieceChord D P Q v hvP hvQ)) : Set ↥A) ⊆
      {P, Q} := by
  classical
  intro R hR
  change R ∈ auxPiecesInWalk (pieceChord D P Q v hvP hvQ) at hR
  rw [mem_auxPiecesInWalk_iff] at hR
  simp only [pieceChord, SimpleGraph.Walk.support_append, List.mem_append,
    SimpleGraph.Walk.support_reverse, List.mem_reverse] at hR
  rcases hR with hR | hR
  · rw [mem_incidenceWalk_support_iff] at hR
    simp_all
  · have hR' := List.mem_of_mem_tail hR
    rw [mem_incidenceWalk_support_iff] at hR'
    simp_all

lemma auxPiecesInWalk_append_subset_union {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {x y z : FamilyAuxVertex V A}
    (p : (familyAuxGraph D).Walk x y) (q : (familyAuxGraph D).Walk y z) :
    auxPiecesInWalk (p.append q) ⊆ auxPiecesInWalk p ∪ auxPiecesInWalk q := by
  classical
  intro P hP
  rw [mem_auxPiecesInWalk_iff] at hP
  rw [SimpleGraph.Walk.mem_support_append_iff] at hP
  rw [Finset.mem_union]
  rcases hP with hP | hP
  · exact Or.inl (mem_auxPiecesInWalk_iff.mpr hP)
  · exact Or.inr (mem_auxPiecesInWalk_iff.mpr hP)

lemma auxPiecesInWalk_append_subset_left {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {x y z : FamilyAuxVertex V A}
    (p : (familyAuxGraph D).Walk x y) (q : (familyAuxGraph D).Walk y z)
    (hq : auxPiecesInWalk q ⊆ auxPiecesInWalk p) :
    auxPiecesInWalk (p.append q) ⊆ auxPiecesInWalk p := by
  intro P hP
  have hP' := auxPiecesInWalk_append_subset_union p q hP
  rw [Finset.mem_union] at hP'
  exact hP'.elim id (fun h => hq h)

lemma auxPiecesInWalk_append_subset_right {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {x y z : FamilyAuxVertex V A}
    (p : (familyAuxGraph D).Walk x y) (q : (familyAuxGraph D).Walk y z)
    (hp : auxPiecesInWalk p ⊆ auxPiecesInWalk q) :
    auxPiecesInWalk (p.append q) ⊆ auxPiecesInWalk q := by
  intro P hP
  have hP' := auxPiecesInWalk_append_subset_union p q hP
  rw [Finset.mem_union] at hP'
  exact hP'.elim (fun h => hp h) id

lemma auxPiecesInWalk_reverse {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {x y : FamilyAuxVertex V A}
    (p : (familyAuxGraph D).Walk x y) :
    auxPiecesInWalk p.reverse = auxPiecesInWalk p := by
  classical
  ext P
  simp [mem_auxPiecesInWalk_iff]

lemma auxPiecesInWalk_rotate {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {x y : FamilyAuxVertex V A}
    (c : (familyAuxGraph D).Walk x x) (hy : y ∈ c.support) :
    auxPiecesInWalk (c.rotate y hy) = auxPiecesInWalk c := by
  classical
  ext P
  simp [mem_auxPiecesInWalk_iff]

lemma auxPiecesInWalk_takeUntil_subset {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {x y z : FamilyAuxVertex V A}
    (p : (familyAuxGraph D).Walk x y) (hz : z ∈ p.support) :
    auxPiecesInWalk (p.takeUntil z hz) ⊆ auxPiecesInWalk p := by
  intro P hP
  rw [mem_auxPiecesInWalk_iff] at hP ⊢
  exact p.support_takeUntil_subset_support hz hP

lemma auxPiecesInWalk_dropUntil_subset {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {x y z : FamilyAuxVertex V A}
    (p : (familyAuxGraph D).Walk x y) (hz : z ∈ p.support) :
    auxPiecesInWalk (p.dropUntil z hz) ⊆ auxPiecesInWalk p := by
  intro P hP
  rw [mem_auxPiecesInWalk_iff] at hP ⊢
  exact p.support_dropUntil_subset_support hz hP

/-- A vertex whose first occurrence is no later than that of the endpoint
belongs to the corresponding initial segment of a walk. -/
lemma mem_takeUntil_support_of_idxOf_le {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x y z w : V} (p : G.Walk x y)
    (hz : z ∈ p.support) (hw : w ∈ p.support)
    (hindex : p.support.idxOf w ≤ p.support.idxOf z) :
    w ∈ (p.takeUntil z hz).support := by
  rw [p.takeUntil_eq_take hz]
  simp only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_take]
  rw [List.mem_take_iff_idxOf_lt hw]
  omega

/-- Dually, a vertex whose first occurrence is no earlier than the split
vertex belongs to the corresponding final segment. -/
lemma mem_dropUntil_support_of_idxOf_le {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x y z w : V} (p : G.Walk x y)
    (hz : z ∈ p.support) (hw : w ∈ p.support)
    (hindex : p.support.idxOf z ≤ p.support.idxOf w) :
    w ∈ (p.dropUntil z hz).support := by
  rw [p.dropUntil_eq_drop hz]
  simp only [SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.drop_support_eq_support_drop_min]
  have hzlt : p.support.idxOf z < p.support.length :=
    List.idxOf_lt_length_of_mem hz
  have hzle : p.support.idxOf z ≤ p.length := by
    rw [SimpleGraph.Walk.length_support] at hzlt
    omega
  rw [Nat.min_eq_left hzle]
  let j := p.support.idxOf w - p.support.idxOf z
  have hwlt : p.support.idxOf w < p.support.length :=
    List.idxOf_lt_length_of_mem hw
  have hj : j < (p.support.drop (p.support.idxOf z)).length := by
    simp only [j, List.length_drop]
    omega
  apply List.mem_iff_getElem.mpr
  refine ⟨j, hj, ?_⟩
  rw [List.getElem_drop]
  have hsum : p.support.idxOf z + j = p.support.idxOf w := by
    dsimp [j]
    omega
  simpa only [hsum] using (List.getElem_idxOf hwlt)

/-- On a walk started at the piece node `P`, there is at most one distinct
piece `Q` for which the initial arc from `P` to `Q` has no third piece. -/
lemma unique_piece_with_piece_free_takeUntil {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {pnode : FamilyAuxVertex V A}
    (cr : (familyAuxGraph D).Walk pnode pnode) (P Q R : ↥A)
    (hpnode : pnode = .inr (.inl P))
    (hQP : Q ≠ P) (hRP : R ≠ P)
    (hQ : Q ∈ auxPiecesInWalk cr) (hR : R ∈ auxPiecesInWalk cr)
    (hQonly : ∀ X ∈ auxPiecesInWalk
      (cr.takeUntil (.inr (.inl Q)) (mem_auxPiecesInWalk_iff.mp hQ)),
        X = P ∨ X = Q)
    (hRonly : ∀ X ∈ auxPiecesInWalk
      (cr.takeUntil (.inr (.inl R)) (mem_auxPiecesInWalk_iff.mp hR)),
        X = P ∨ X = R) :
    Q = R := by
  classical
  let qnode : FamilyAuxVertex V A := .inr (.inl Q)
  let rnode : FamilyAuxVertex V A := .inr (.inl R)
  have hqnode : qnode ∈ cr.support := mem_auxPiecesInWalk_iff.mp hQ
  have hrnode : rnode ∈ cr.support := mem_auxPiecesInWalk_iff.mp hR
  rcases le_total
      (@List.idxOf (FamilyAuxVertex V A) instBEqOfDecidableEq qnode cr.support)
      (@List.idxOf (FamilyAuxVertex V A) instBEqOfDecidableEq rnode cr.support) with
    hqr | hrq
  · have hQarc : Q ∈ auxPiecesInWalk (cr.takeUntil rnode hrnode) := by
      rw [mem_auxPiecesInWalk_iff]
      exact mem_takeUntil_support_of_idxOf_le cr hrnode hqnode hqr
    rcases hRonly Q hQarc with h | h
    · exact (hQP h).elim
    · exact h
  · have hRarc : R ∈ auxPiecesInWalk (cr.takeUntil qnode hqnode) := by
      rw [mem_auxPiecesInWalk_iff]
      exact mem_takeUntil_support_of_idxOf_le cr hqnode hrnode hrq
    rcases hQonly R hRarc with h | h
    · exact (hRP h).elim
    · exact h.symm

/-- The analogous uniqueness statement for the final arc back to `P`. -/
lemma unique_piece_with_piece_free_dropUntil {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {pnode : FamilyAuxVertex V A}
    (cr : (familyAuxGraph D).Walk pnode pnode) (P Q R : ↥A)
    (hpnode : pnode = .inr (.inl P))
    (hQP : Q ≠ P) (hRP : R ≠ P)
    (hQ : Q ∈ auxPiecesInWalk cr) (hR : R ∈ auxPiecesInWalk cr)
    (hQonly : ∀ X ∈ auxPiecesInWalk
      (cr.dropUntil (.inr (.inl Q)) (mem_auxPiecesInWalk_iff.mp hQ)),
        X = P ∨ X = Q)
    (hRonly : ∀ X ∈ auxPiecesInWalk
      (cr.dropUntil (.inr (.inl R)) (mem_auxPiecesInWalk_iff.mp hR)),
        X = P ∨ X = R) :
    Q = R := by
  classical
  let qnode : FamilyAuxVertex V A := .inr (.inl Q)
  let rnode : FamilyAuxVertex V A := .inr (.inl R)
  have hqnode : qnode ∈ cr.support := mem_auxPiecesInWalk_iff.mp hQ
  have hrnode : rnode ∈ cr.support := mem_auxPiecesInWalk_iff.mp hR
  rcases le_total
      (@List.idxOf (FamilyAuxVertex V A) instBEqOfDecidableEq qnode cr.support)
      (@List.idxOf (FamilyAuxVertex V A) instBEqOfDecidableEq rnode cr.support) with
    hqr | hrq
  · have hRarc : R ∈ auxPiecesInWalk (cr.dropUntil qnode hqnode) := by
      rw [mem_auxPiecesInWalk_iff]
      exact mem_dropUntil_support_of_idxOf_le cr hqnode hrnode hqr
    rcases hQonly R hRarc with h | h
    · exact (hRP h).elim
    · exact h.symm
  · have hQarc : Q ∈ auxPiecesInWalk (cr.dropUntil rnode hrnode) := by
      rw [mem_auxPiecesInWalk_iff]
      exact mem_dropUntil_support_of_idxOf_le cr hrnode hqnode hrq
    rcases hRonly Q hQarc with h | h
    · exact (hQP h).elim
    · exact h

lemma odd_of_odd_add_split {a b k : ℕ} (hodd : Odd (a + b)) :
    Odd (a + k) ∨ Odd (b + k) := by
  by_contra h
  push_neg at h
  have hea : Even (a + k) := Nat.not_odd_iff_even.mp h.1
  have heb : Even (b + k) := Nat.not_odd_iff_even.mp h.2
  obtain ⟨u, hu⟩ := hea
  obtain ⟨v, hv⟩ := heb
  obtain ⟨w, hw⟩ := hodd
  omega

/-- In a minimum-piece odd auxiliary cycle, two pieces that share a carrier
vertex must be consecutive: one of the two cycle arcs between their piece
nodes contains no third piece node. -/
theorem shared_vertex_consecutive_on_minimal_odd_cycle {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A}
    (c : (familyAuxGraph D).Walk z z) (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (P Q : ↥A) (hPQ : P ≠ Q)
    (hP : P ∈ auxPiecesInWalk c) (hQ : Q ∈ auxPiecesInWalk c)
    (v : V) (hvP : v ∈ P.1.1) (hvQ : v ∈ Q.1.1) :
    let pnode : FamilyAuxVertex V A := .inr (.inl P)
    let qnode : FamilyAuxVertex V A := .inr (.inl Q)
    let cr := c.rotate pnode (mem_auxPiecesInWalk_iff.mp hP)
    let hQr : qnode ∈ cr.support :=
      (SimpleGraph.Walk.mem_support_rotate_iff c pnode
        (mem_auxPiecesInWalk_iff.mp hP)).2 (mem_auxPiecesInWalk_iff.mp hQ)
    (∀ R ∈ auxPiecesInWalk (cr.takeUntil qnode hQr), R = P ∨ R = Q) ∨
      (∀ R ∈ auxPiecesInWalk (cr.dropUntil qnode hQr), R = P ∨ R = Q) := by
  classical
  dsimp only
  let pnode : FamilyAuxVertex V A := .inr (.inl P)
  let qnode : FamilyAuxVertex V A := .inr (.inl Q)
  have hpnode : pnode ∈ c.support := mem_auxPiecesInWalk_iff.mp hP
  let cr := c.rotate pnode hpnode
  have hqnode : qnode ∈ cr.support := by
    apply (SimpleGraph.Walk.mem_support_rotate_iff c pnode hpnode).2
    exact mem_auxPiecesInWalk_iff.mp hQ
  let front := cr.takeUntil qnode hqnode
  let back := cr.dropUntil qnode hqnode
  by_contra hconsecutive
  have hnot := not_or.mp hconsecutive
  have hfrontExtra : ∃ R, R ∈ auxPiecesInWalk front ∧ R ≠ P ∧ R ≠ Q := by
    push Not at hnot
    exact hnot.1
  have hbackExtra : ∃ R, R ∈ auxPiecesInWalk back ∧ R ≠ P ∧ R ≠ Q := by
    push Not at hnot
    exact hnot.2
  obtain ⟨Rf, hRfFront, hRfP, hRfQ⟩ := hfrontExtra
  obtain ⟨Rb, hRbBack, hRbP, hRbQ⟩ := hbackExtra
  let chord := pieceChord D P Q v hvP hvQ
  have hPFront : P ∈ auxPiecesInWalk front := by
    rw [mem_auxPiecesInWalk_iff]
    exact front.start_mem_support
  have hQFront : Q ∈ auxPiecesInWalk front := by
    rw [mem_auxPiecesInWalk_iff]
    exact front.end_mem_support
  have hQBack : Q ∈ auxPiecesInWalk back := by
    rw [mem_auxPiecesInWalk_iff]
    exact back.start_mem_support
  have hPBack : P ∈ auxPiecesInWalk back := by
    rw [mem_auxPiecesInWalk_iff]
    exact back.end_mem_support
  have hchordFront : auxPiecesInWalk chord.reverse ⊆ auxPiecesInWalk front := by
    rw [auxPiecesInWalk_reverse]
    intro R hR
    have hRset := auxPiecesInWalk_pieceChord_subset D P Q v hvP hvQ hR
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hRset
    rcases hRset with rfl | rfl
    · exact hPFront
    · exact hQFront
  have hchordBack : auxPiecesInWalk chord ⊆ auxPiecesInWalk back := by
    intro R hR
    have hRset := auxPiecesInWalk_pieceChord_subset D P Q v hvP hvQ hR
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hRset
    rcases hRset with rfl | rfl
    · exact hPBack
    · exact hQBack
  have hnewFront : auxPiecesInWalk (front.append chord.reverse) ⊆
      auxPiecesInWalk front :=
    auxPiecesInWalk_append_subset_left front chord.reverse hchordFront
  have hnewBack : auxPiecesInWalk (chord.append back) ⊆
      auxPiecesInWalk back :=
    auxPiecesInWalk_append_subset_right chord back hchordBack
  have hfrontCr : auxPiecesInWalk front ⊆ auxPiecesInWalk cr := by
    exact auxPiecesInWalk_takeUntil_subset cr hqnode
  have hbackCr : auxPiecesInWalk back ⊆ auxPiecesInWalk cr := by
    exact auxPiecesInWalk_dropUntil_subset cr hqnode
  have hcrEq : auxPiecesInWalk cr = auxPiecesInWalk c :=
    auxPiecesInWalk_rotate c hpnode
  have hfrontC : auxPiecesInWalk front ⊆ auxPiecesInWalk c := by
    intro R hR
    rw [← hcrEq]
    exact hfrontCr hR
  have hbackC : auxPiecesInWalk back ⊆ auxPiecesInWalk c := by
    intro R hR
    rw [← hcrEq]
    exact hbackCr hR
  have hRbC : Rb ∈ auxPiecesInWalk c := hbackC hRbBack
  have hRfC : Rf ∈ auxPiecesInWalk c := hfrontC hRfFront
  have hRbNotFront : Rb ∉ auxPiecesInWalk front := by
    intro hRbFront
    have hnodeFront := mem_auxPiecesInWalk_iff.mp hRbFront
    have hnodeBack := mem_auxPiecesInWalk_iff.mp hRbBack
    have hnodeFrontTail : (.inr (.inl Rb) : FamilyAuxVertex V A) ∈
        front.support.tail := by
      exact (front.mem_support_iff.mp hnodeFront).resolve_left (by
        simpa [pnode] using hRbP)
    have hnodeBackTail : (.inr (.inl Rb) : FamilyAuxVertex V A) ∈
        back.support.tail := by
      exact (back.mem_support_iff.mp hnodeBack).resolve_left (by
        simpa [qnode] using hRbQ)
    have hsplit : cr.support.tail.Nodup := (hc.rotate hpnode).support_nodup
    -- The two arcs of a simple cycle meet only at their endpoints.
    rw [← cr.take_spec hqnode] at hsplit
    simp only [SimpleGraph.Walk.tail_support_append, List.nodup_append] at hsplit
    exact (hsplit.2.2 _ hnodeFrontTail _ hnodeBackTail rfl).elim
  have hRfNotBack : Rf ∉ auxPiecesInWalk back := by
    intro hRfBack
    have hnodeFront := mem_auxPiecesInWalk_iff.mp hRfFront
    have hnodeBack := mem_auxPiecesInWalk_iff.mp hRfBack
    have hnodeFrontTail : (.inr (.inl Rf) : FamilyAuxVertex V A) ∈
        front.support.tail := by
      exact (front.mem_support_iff.mp hnodeFront).resolve_left (by
        simpa [pnode] using hRfP)
    have hnodeBackTail : (.inr (.inl Rf) : FamilyAuxVertex V A) ∈
        back.support.tail := by
      exact (back.mem_support_iff.mp hnodeBack).resolve_left (by
        simpa [qnode] using hRfQ)
    have hsplit : cr.support.tail.Nodup := (hc.rotate hpnode).support_nodup
    rw [← cr.take_spec hqnode] at hsplit
    simp only [SimpleGraph.Walk.tail_support_append, List.nodup_append] at hsplit
    exact (hsplit.2.2 _ hnodeFrontTail _ hnodeBackTail rfl).elim
  have hfrontProper : auxPiecesInWalk front ⊂ auxPiecesInWalk c := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hfrontC, ?_⟩
    intro heq
    exact hRbNotFront (heq ▸ hRbC)
  have hbackProper : auxPiecesInWalk back ⊂ auxPiecesInWalk c := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hbackC, ?_⟩
    intro heq
    exact hRfNotBack (heq ▸ hRfC)
  have hsplitLength : cr.length = front.length + back.length := by
    have hwalk : front.append back = cr := by
      dsimp [front, back]
      exact cr.take_spec hqnode
    have hlen := congrArg SimpleGraph.Walk.length hwalk
    simpa using hlen.symm
  have hsplitOdd : Odd (front.length + back.length) := by
    rw [← hsplitLength]
    simpa [cr] using hcodd
  have hoddNew := odd_of_odd_add_split (k := chord.length) hsplitOdd
  rcases hoddNew with hoddNew | hoddNew
  · have hoddWalk : Odd (front.append chord.reverse).length := by
      simpa using hoddNew
    obtain ⟨z', c', hc', hc'odd, hsupp⟩ :=
      exists_odd_cycle_support_subset (front.append chord.reverse) hoddWalk
    have hc'new := auxPiecesInWalk_mono_support hsupp
    have hcard : (auxPiecesInWalk c').card < (auxPiecesInWalk c).card :=
      (Finset.card_le_card (hc'new.trans hnewFront)).trans_lt
        (Finset.card_lt_card hfrontProper)
    exact (Nat.not_lt_of_ge (hminimal z' c' hc' hc'odd)) hcard

  · have hoddWalk : Odd (chord.append back).length := by
      simpa [add_comm] using hoddNew
    obtain ⟨z', c', hc', hc'odd, hsupp⟩ :=
      exists_odd_cycle_support_subset (chord.append back) hoddWalk
    have hc'new := auxPiecesInWalk_mono_support hsupp
    have hcard : (auxPiecesInWalk c').card < (auxPiecesInWalk c).card :=
      (Finset.card_le_card (hc'new.trans hnewBack)).trans_lt
        (Finset.card_lt_card hbackProper)
    exact (Nat.not_lt_of_ge (hminimal z' c' hc' hc'odd)) hcard

/-- If the minimum-piece odd auxiliary cycle uses at least three pieces,
then two of its pieces cannot disagree about the relative bipartition labels
of two common carrier vertices.  Otherwise the two canonical incidence
chords form an odd closed walk supported on only those two pieces. -/
lemma two_piece_color_relation_on_minimal_cycle {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcard : 3 ≤ (auxPiecesInWalk c).card)
    (P Q : ↥(auxPiecesInWalk c)) (hPQ : P ≠ Q)
    (a v : V) (haP : a ∈ P.1.1.1) (haQ : a ∈ Q.1.1.1)
    (hvP : v ∈ P.1.1.1) (hvQ : v ∈ Q.1.1.1) :
    ((D P.1).color v = (D P.1).color a ↔
      (D Q.1).color v = (D Q.1).color a) := by
  classical
  by_contra hrelation
  let pa := pieceChord D P.1 Q.1 a haP haQ
  let pv := pieceChord D P.1 Q.1 v hvP hvQ
  let w : (familyAuxGraph D).Walk (.inr (.inl P.1)) (.inr (.inl P.1)) :=
    pa.append pv.reverse
  have hwcast : (w.length : ZMod 2) = 1 := by
    calc
      (w.length : ZMod 2) = (pa.length : ZMod 2) + (pv.length : ZMod 2) := by
        simp [w]
      _ = (((D P.1).color a).val : ZMod 2) +
          ((D Q.1).color a).val +
          ((((D P.1).color v).val : ZMod 2) +
            ((D Q.1).color v).val) := by
        rw [pieceChord_length_cast, pieceChord_length_cast]
      _ = 1 := by
        rcases fin_two_eq_zero_or_one ((D P.1).color a) with hPa | hPa <;>
          rcases fin_two_eq_zero_or_one ((D Q.1).color a) with hQa | hQa <;>
          rcases fin_two_eq_zero_or_one ((D P.1).color v) with hPv | hPv <;>
          rcases fin_two_eq_zero_or_one ((D Q.1).color v) with hQv | hQv <;>
          simp_all <;> decide
  have hwodd : Odd w.length := ZMod.natCast_eq_one_iff_odd.mp hwcast
  obtain ⟨z', c', hc', hc'odd, hsupp⟩ :=
    exists_odd_cycle_support_subset w hwodd
  have hc'w : auxPiecesInWalk c' ⊆ auxPiecesInWalk w :=
    auxPiecesInWalk_mono_support hsupp
  have hwPieces : auxPiecesInWalk w ⊆ ({P.1, Q.1} : Finset ↥A) := by
    intro R hR
    have hAppend := auxPiecesInWalk_append_subset_union pa pv.reverse hR
    rw [Finset.mem_union] at hAppend
    rcases hAppend with hpa | hpv
    · have hset := auxPiecesInWalk_pieceChord_subset
        D P.1 Q.1 a haP haQ hpa
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Finset.mem_insert, Finset.mem_singleton] using hset
    · rw [auxPiecesInWalk_reverse] at hpv
      have hset := auxPiecesInWalk_pieceChord_subset
        D P.1 Q.1 v hvP hvQ hpv
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Finset.mem_insert, Finset.mem_singleton] using hset
  have hsmall : (auxPiecesInWalk c').card ≤ 2 := by
    have hsub : auxPiecesInWalk c' ⊆ ({P.1, Q.1} : Finset ↥A) :=
      hc'w.trans hwPieces
    have hPQval : P.1 ≠ Q.1 := by
      intro h
      exact hPQ (Subtype.ext h)
    exact (Finset.card_le_card hsub).trans (by simp [hPQval])
  have hmin := hminimal z' c' hc' hc'odd
  omega

/-! ### Piece occurrence and coarse parity on auxiliary walks -/

/-- Coarse side of an auxiliary vertex: original vertices lie on one side,
while both kinds of gadget vertices lie on the other.  Along an auxiliary
walk containing no piece node, every used edge changes this side. -/
def familyAuxCoarseSide {V : Type*} {A : Finset (PackedSubgraph V)} :
    FamilyAuxVertex V A → Bool
  | .inl _ => false
  | .inr _ => true

/-- Ambient vertex represented by a non-piece auxiliary vertex. -/
def familyAuxRoot {V : Type*} {A : Finset (PackedSubgraph V)} :
    FamilyAuxVertex V A → Option V
  | .inl v => some v
  | .inr (.inl _) => none
  | .inr (.inr (_, v)) => some v

/-- The coarse auxiliary side, regarded as a bit. -/
def familyAuxSideBit {V : Type*} {A : Finset (PackedSubgraph V)} :
    FamilyAuxVertex V A → ZMod 2
  | .inl _ => 0
  | .inr _ => 1

/-- A directed incidence contributes one precisely when its source is a
piece node and the target is rooted at a colour-zero vertex of that piece. -/
def familyAuxZeroIncidence {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1) :
    FamilyAuxVertex V A → FamilyAuxVertex V A → ZMod 2
  | .inr (.inl P), y =>
      match familyAuxRoot y with
      | some v => if (D P).color v = 0 then 1 else 0
      | none => 0
  | _, _ => 0

/-- On every auxiliary edge, its unit length is the sum of the coarse-side
change and the two directed colour-zero incidence bits. -/
lemma familyAux_edge_bit_identity {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    {x y : FamilyAuxVertex V A} (hxy : (familyAuxGraph D).Adj x y) :
    (1 : ZMod 2) = familyAuxSideBit x + familyAuxSideBit y +
      familyAuxZeroIncidence D x y + familyAuxZeroIncidence D y x := by
  cases x with
  | inl v =>
      cases y with
      | inl w => simp [familyAuxGraph, familyAuxAdj] at hxy
      | inr q =>
          cases q with
          | inl P =>
              have h := hxy
              simp [familyAuxGraph, familyAuxAdj] at h
              simp [familyAuxSideBit, familyAuxZeroIncidence, familyAuxRoot, h.2]
          | inr Pw =>
              rcases Pw with ⟨P, w⟩
              have h := hxy
              simp [familyAuxGraph, familyAuxAdj] at h
              rcases h with ⟨rfl, hv, h0⟩
              simp [familyAuxSideBit, familyAuxZeroIncidence, familyAuxRoot, h0]
  | inr p =>
      cases p with
      | inl P =>
          cases y with
          | inl v =>
              have h := hxy
              simp [familyAuxGraph, familyAuxAdj] at h
              simp [familyAuxSideBit, familyAuxZeroIncidence, familyAuxRoot, h.2]
          | inr q =>
              cases q with
              | inl Q => simp [familyAuxGraph, familyAuxAdj] at hxy
              | inr Qw =>
                  rcases Qw with ⟨Q, w⟩
                  have h := hxy
                  simp [familyAuxGraph, familyAuxAdj] at h
                  rcases h with ⟨rfl, hw, h0⟩
                  simp [familyAuxSideBit, familyAuxZeroIncidence, familyAuxRoot, h0]
                  decide
      | inr Pv =>
          rcases Pv with ⟨P, v⟩
          cases y with
          | inl w =>
              have h := hxy
              simp [familyAuxGraph, familyAuxAdj] at h
              rcases h with ⟨rfl, hv, h0⟩
              simp [familyAuxSideBit, familyAuxZeroIncidence, familyAuxRoot, h0]
          | inr q =>
              cases q with
              | inl Q =>
                  have h := hxy
                  simp [familyAuxGraph, familyAuxAdj] at h
                  rcases h with ⟨rfl, hv, h0⟩
                  simp [familyAuxSideBit, familyAuxZeroIncidence, familyAuxRoot, h0]
                  decide
              | inr Qw => simp [familyAuxGraph, familyAuxAdj] at hxy

/-- Total directed colour-zero incidence contribution along a walk. -/
def familyAuxZeroSum {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    {x y : FamilyAuxVertex V A} (p : (familyAuxGraph D).Walk x y) : ZMod 2 :=
  (p.darts.map fun d =>
    familyAuxZeroIncidence D d.fst d.snd +
      familyAuxZeroIncidence D d.snd d.fst).sum

lemma familyAuxSideBit_add_self {V : Type*}
    {A : Finset (PackedSubgraph V)} (x : FamilyAuxVertex V A) :
    familyAuxSideBit x + familyAuxSideBit x = 0 := by
  cases x <;> simp [familyAuxSideBit] <;> decide

/-- Summing the edge-bit identity along a walk telescopes all internal
coarse-side bits. -/
lemma familyAux_walk_length_bit {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    {x y : FamilyAuxVertex V A} (p : (familyAuxGraph D).Walk x y) :
    (p.length : ZMod 2) = familyAuxSideBit x + familyAuxSideBit y +
      familyAuxZeroSum D p := by
  induction p with
  | nil =>
      simp only [SimpleGraph.Walk.length_nil, Nat.cast_zero, familyAuxZeroSum,
        SimpleGraph.Walk.darts_nil, List.map_nil, List.sum_nil, add_zero]
      exact (familyAuxSideBit_add_self _).symm
  | @cons x y z hxy p ih =>
      have hzeroCons : familyAuxZeroSum D (SimpleGraph.Walk.cons hxy p) =
          familyAuxZeroIncidence D x y + familyAuxZeroIncidence D y x +
            familyAuxZeroSum D p := by
        simp [familyAuxZeroSum]
      rw [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      rw [hzeroCons]
      have hedge := familyAux_edge_bit_identity D hxy
      have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
      linear_combination ih + hedge + htwo * familyAuxSideBit y

lemma familyAux_cycle_length_bit {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    {x : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk x x) :
    (c.length : ZMod 2) = familyAuxZeroSum D c := by
  have h := familyAux_walk_length_bit D c
  have hside := familyAuxSideBit_add_self x
  linear_combination h + hside

lemma familyAux_cycle_zeroSum_eq_one_of_odd {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    {x : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk x x)
    (hcodd : Odd c.length) : familyAuxZeroSum D c = 1 := by
  rw [← familyAux_cycle_length_bit D c]
  calc
    (c.length : ZMod 2) = ((c.length % 2 : ℕ) : ZMod 2) :=
      (ZMod.natCast_mod c.length 2).symm
    _ = 1 := by simp [mod_two_eq_one_of_odd hcodd]

lemma odd_of_zmod_two_natCast_eq_one {n : ℕ} (h : (n : ZMod 2) = 1) : Odd n := by
  rw [Nat.odd_iff]
  rcases Nat.mod_two_eq_zero_or_one n with hzero | hone
  · have hcast : (n : ZMod 2) = 0 := by
      calc
        (n : ZMod 2) = ((n % 2 : ℕ) : ZMod 2) :=
          (ZMod.natCast_mod n 2).symm
        _ = 0 := by simp [hzero]
    rw [h] at hcast
    exact ((by decide : (1 : ZMod 2) ≠ 0) hcast).elim
  · exact hone

lemma list_eq_of_mem_of_mem_of_map_eq_of_map_nodup
    {X Y : Type*} {l : List X} (f : X → Y) {a b : X}
    (hn : (l.map f).Nodup) (ha : a ∈ l) (hb : b ∈ l)
    (hab : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
      rw [List.map_cons, List.nodup_cons] at hn
      rw [List.mem_cons] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · rfl
      · apply (hn.1 ?_).elim
        rw [hab]
        exact List.mem_map.mpr ⟨b, hb, rfl⟩
      · apply (hn.1 ?_).elim
        rw [hab.symm]
        exact List.mem_map.mpr ⟨a, ha, rfl⟩
      · exact ih hn.2 ha hb

lemma cycle_dart_eq_of_fst_eq {V : Type*} {G : SimpleGraph V}
    {x : V} {c : G.Walk x x} (hc : c.IsCycle) {d e : G.Dart}
    (hd : d ∈ c.darts) (he : e ∈ c.darts) (hfst : d.fst = e.fst) : d = e := by
  apply list_eq_of_mem_of_mem_of_map_eq_of_map_nodup (fun q : G.Dart => q.fst)
    (a := d) (b := e) ?_ hd he hfst
  rw [c.map_fst_darts]
  exact hc.nodup_dropLast_support

lemma cycle_dart_eq_of_snd_eq {V : Type*} {G : SimpleGraph V}
    {x : V} {c : G.Walk x x} (hc : c.IsCycle) {d e : G.Dart}
    (hd : d ∈ c.darts) (he : e ∈ c.darts) (hsnd : d.snd = e.snd) : d = e := by
  apply list_eq_of_mem_of_mem_of_map_eq_of_map_nodup (fun q : G.Dart => q.snd)
    (a := d) (b := e) ?_ hd he hsnd
  rw [c.map_snd_darts]
  exact hc.support_nodup

/-- An auxiliary edge from a piece node reaches a non-piece node rooted at
a vertex of that piece. -/
lemma exists_root_of_piece_adj {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (P : ↥A) {x : FamilyAuxVertex V A}
    (h : (familyAuxGraph D).Adj (.inr (.inl P)) x) :
    ∃ v : V, familyAuxRoot x = some v ∧ v ∈ P.1.1 := by
  cases x with
  | inl v =>
      refine ⟨v, rfl, ?_⟩
      have h' := h
      simp [familyAuxGraph, familyAuxAdj] at h'
      exact h'.1
  | inr q =>
      cases q with
      | inl Q => simp [familyAuxGraph, familyAuxAdj] at h
      | inr Qv =>
          rcases Qv with ⟨Q, v⟩
          refine ⟨v, rfl, ?_⟩
          have h' := h
          simp [familyAuxGraph, familyAuxAdj] at h'
          rcases h' with ⟨rfl, hv, _⟩
          exact hv

/-- Along an auxiliary edge between two non-piece nodes, the represented
ambient root is unchanged. -/
lemma familyAuxRoot_eq_of_adj {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    {x y : FamilyAuxVertex V A} {u v : V}
    (hxy : (familyAuxGraph D).Adj x y)
    (hx : familyAuxRoot x = some u) (hy : familyAuxRoot y = some v) :
    u = v := by
  cases x with
  | inl a =>
      cases y with
      | inl b => simp [familyAuxGraph, familyAuxAdj] at hxy
      | inr q =>
          cases q with
          | inl P => simp [familyAuxRoot] at hy
          | inr Pv =>
              rcases Pv with ⟨P, b⟩
              simp [familyAuxRoot] at hx hy
              subst u
              subst v
              have h' := hxy
              simp [familyAuxGraph, familyAuxAdj] at h'
              exact h'.1
  | inr p =>
      cases p with
      | inl P => simp [familyAuxRoot] at hx
      | inr Pa =>
          rcases Pa with ⟨P, a⟩
          cases y with
          | inl b =>
              simp [familyAuxRoot] at hx hy
              subst u
              subst v
              have h' := hxy
              simp [familyAuxGraph, familyAuxAdj] at h'
              exact h'.1.symm
          | inr q =>
              cases q with
              | inl Q => simp [familyAuxRoot] at hy
              | inr Qb => simp [familyAuxGraph, familyAuxAdj] at hxy

/-- A path whose final vertex is a piece node and whose earlier vertices are
all non-piece nodes keeps one ambient root throughout; that root belongs to
the final piece. -/
lemma root_mem_final_piece_of_auxPath {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (Q : ↥A) {x : FamilyAuxVertex V A} {v : V}
    (p : (familyAuxGraph D).Walk x (.inr (.inl Q)))
    (hp : p.IsPath) (hroot : familyAuxRoot x = some v)
    (hno : ∀ R : ↥A,
      (.inr (.inl R) : FamilyAuxVertex V A) ∉ p.support.dropLast) :
    v ∈ Q.1.1 := by
  generalize htarget : (.inr (.inl Q) : FamilyAuxVertex V A) = target at p
  induction p with
  | nil =>
      rw [← htarget] at hroot
      simp [familyAuxRoot] at hroot
  | @cons x y z hxy p ih =>
      by_cases hpNil : p.Nil
      · have hyQ : y = (.inr (.inl Q) : FamilyAuxVertex V A) := by
          exact hpNil.eq.trans htarget.symm
        subst y
        obtain ⟨w, hwroot, hwQ⟩ := exists_root_of_piece_adj D Q hxy.symm
        have : v = w := by simpa [hroot] using hwroot
        simpa [this] using hwQ
      · have hyNonpiece : ∀ R : ↥A,
            y ≠ (.inr (.inl R) : FamilyAuxVertex V A) := by
          intro R hyR
          apply hno R
          rw [SimpleGraph.Walk.support_cons,
            List.dropLast_cons_of_ne_nil
              (List.ne_nil_of_mem p.start_mem_support)]
          apply List.mem_cons_of_mem
          rw [← hyR]
          cases p with
          | nil => simp at hpNil
          | @cons _ y' _ hy' q =>
              rw [SimpleGraph.Walk.support_cons,
                List.dropLast_cons_of_ne_nil
                  (List.ne_nil_of_mem q.start_mem_support)]
              exact List.mem_cons_self
        have hyRoot : ∃ w : V, familyAuxRoot y = some w := by
          cases y with
          | inl a => exact ⟨a, rfl⟩
          | inr q =>
              cases q with
              | inl R => exact (hyNonpiece R rfl).elim
              | inr Rw => exact ⟨Rw.2, rfl⟩
        obtain ⟨w, hw⟩ := hyRoot
        have hvw : v = w := familyAuxRoot_eq_of_adj D hxy hroot hw
        have hnoTail : ∀ R : ↥A,
            (.inr (.inl R) : FamilyAuxVertex V A) ∉ p.support.dropLast := by
          intro R hR
          apply hno R
          rw [SimpleGraph.Walk.support_cons,
            List.dropLast_cons_of_ne_nil
              (List.ne_nil_of_mem p.start_mem_support)]
          exact List.mem_cons_of_mem x hR
        have hwv : familyAuxRoot y = some v := by simpa [hvw] using hw
        exact ih hwv htarget (SimpleGraph.Walk.IsPath.of_cons hp) hnoTail

/-- Along the same kind of path, the penultimate auxiliary vertex has the
same ambient root as the initial vertex. -/
lemma root_penultimate_eq_of_auxPath {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (Q : ↥A) {x : FamilyAuxVertex V A} {v : V}
    (p : (familyAuxGraph D).Walk x (.inr (.inl Q)))
    (hp : p.IsPath) (hroot : familyAuxRoot x = some v)
    (hno : ∀ R : ↥A,
      (.inr (.inl R) : FamilyAuxVertex V A) ∉ p.support.dropLast) :
    familyAuxRoot p.penultimate = some v := by
  generalize htarget : (.inr (.inl Q) : FamilyAuxVertex V A) = target at p
  induction p with
  | nil =>
      rw [← htarget] at hroot
      simp [familyAuxRoot] at hroot
  | @cons x y z hxy p ih =>
      by_cases hpNil : p.Nil
      · cases p with
        | nil => simpa using hroot
        | cons h q => simp at hpNil
      · have hyNonpiece : ∀ R : ↥A,
            y ≠ (.inr (.inl R) : FamilyAuxVertex V A) := by
          intro R hyR
          apply hno R
          rw [SimpleGraph.Walk.support_cons,
            List.dropLast_cons_of_ne_nil
              (List.ne_nil_of_mem p.start_mem_support)]
          apply List.mem_cons_of_mem
          rw [← hyR]
          cases p with
          | nil => simp at hpNil
          | @cons _ y' _ hy' q =>
              rw [SimpleGraph.Walk.support_cons,
                List.dropLast_cons_of_ne_nil
                  (List.ne_nil_of_mem q.start_mem_support)]
              exact List.mem_cons_self
        have hyRoot : ∃ w : V, familyAuxRoot y = some w := by
          cases y with
          | inl a => exact ⟨a, rfl⟩
          | inr q =>
              cases q with
              | inl R => exact (hyNonpiece R rfl).elim
              | inr Rw => exact ⟨Rw.2, rfl⟩
        obtain ⟨w, hw⟩ := hyRoot
        have hvw : v = w := familyAuxRoot_eq_of_adj D hxy hroot hw
        have hnoTail : ∀ R : ↥A,
            (.inr (.inl R) : FamilyAuxVertex V A) ∉ p.support.dropLast := by
          intro R hR
          apply hno R
          rw [SimpleGraph.Walk.support_cons,
            List.dropLast_cons_of_ne_nil
              (List.ne_nil_of_mem p.start_mem_support)]
          exact List.mem_cons_of_mem x hR
        have hwv : familyAuxRoot y = some v := by simpa [hvw] using hw
        have hrec := ih hwv htarget (SimpleGraph.Walk.IsPath.of_cons hp) hnoTail
        simpa [SimpleGraph.Walk.penultimate_cons_of_not_nil hxy p hpNil] using hrec

/-- A piece-free auxiliary path between two distinct piece nodes identifies
a genuine ambient vertex shared by the two carriers. -/
lemma exists_shared_vertex_of_piece_free_auxPath {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (P Q : ↥A) (hPQ : P ≠ Q)
    (p : (familyAuxGraph D).Walk (.inr (.inl P)) (.inr (.inl Q)))
    (hp : p.IsPath)
    (honly : ∀ R ∈ auxPiecesInWalk p, R = P ∨ R = Q) :
    ∃ v : V, v ∈ P.1.1 ∧ v ∈ Q.1.1 := by
  classical
  cases p with
  | nil => exact (hPQ rfl).elim
  | @cons _ x _ hPx tail =>
      obtain ⟨v, hxroot, hvP⟩ := exists_root_of_piece_adj D P hPx
      have htailPath : tail.IsPath := SimpleGraph.Walk.IsPath.of_cons hp
      have hPnotTail :
          (.inr (.inl P) : FamilyAuxVertex V A) ∉ tail.support := by
        have hn := hp.support_nodup
        rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hn
        exact hn.1
      have hQnotDrop :
          (.inr (.inl Q) : FamilyAuxVertex V A) ∉ tail.support.dropLast := by
        have hdecomp : tail.support.dropLast ++
            [(.inr (.inl Q) : FamilyAuxVertex V A)] = tail.support := by
          simpa only [SimpleGraph.Walk.getLast_support] using
            (List.dropLast_append_getLast tail.support_ne_nil)
        have hn : (tail.support.dropLast ++
            [(.inr (.inl Q) : FamilyAuxVertex V A)]).Nodup := by
          rw [hdecomp]
          exact htailPath.support_nodup
        rw [List.nodup_append] at hn
        intro hQ
        exact hn.2.2 _ hQ _ (by simp) rfl
      have hno : ∀ R : ↥A,
          (.inr (.inl R) : FamilyAuxVertex V A) ∉
            tail.support.dropLast := by
        intro R hR
        have hRfull : R ∈ auxPiecesInWalk
            (SimpleGraph.Walk.cons hPx tail) := by
          rw [mem_auxPiecesInWalk_iff, SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ (List.mem_of_mem_dropLast hR)
        rcases honly R hRfull with rfl | rfl
        · exact hPnotTail (List.mem_of_mem_dropLast hR)
        · exact hQnotDrop hR
      have hvQ := root_mem_final_piece_of_auxPath D Q tail htailPath hxroot hno
      exact ⟨v, hvP, hvQ⟩

/-- Rooted form of the preceding lemma: the shared ambient vertex is the
root of the first non-piece vertex of the path. -/
lemma exists_rooted_shared_vertex_of_piece_free_auxPath
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    (P Q : ↥A) (hPQ : P ≠ Q)
    (p : (familyAuxGraph D).Walk (.inr (.inl P)) (.inr (.inl Q)))
    (hp : p.IsPath)
    (honly : ∀ R ∈ auxPiecesInWalk p, R = P ∨ R = Q) :
    ∃ v : V, familyAuxRoot p.snd = some v ∧
      familyAuxRoot p.penultimate = some v ∧ v ∈ P.1.1 ∧ v ∈ Q.1.1 := by
  classical
  cases p with
  | nil => exact (hPQ rfl).elim
  | @cons _ x _ hPx tail =>
      obtain ⟨v, hxroot, hvP⟩ := exists_root_of_piece_adj D P hPx
      have htailPath : tail.IsPath := SimpleGraph.Walk.IsPath.of_cons hp
      have hPnotTail :
          (.inr (.inl P) : FamilyAuxVertex V A) ∉ tail.support := by
        have hn := hp.support_nodup
        rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hn
        exact hn.1
      have hQnotDrop :
          (.inr (.inl Q) : FamilyAuxVertex V A) ∉ tail.support.dropLast := by
        have hdecomp : tail.support.dropLast ++
            [(.inr (.inl Q) : FamilyAuxVertex V A)] = tail.support := by
          simpa only [SimpleGraph.Walk.getLast_support] using
            (List.dropLast_append_getLast tail.support_ne_nil)
        have hn : (tail.support.dropLast ++
            [(.inr (.inl Q) : FamilyAuxVertex V A)]).Nodup := by
          rw [hdecomp]
          exact htailPath.support_nodup
        rw [List.nodup_append] at hn
        intro hQ
        exact hn.2.2 _ hQ _ (by simp) rfl
      have hno : ∀ R : ↥A,
          (.inr (.inl R) : FamilyAuxVertex V A) ∉
            tail.support.dropLast := by
        intro R hR
        have hRfull : R ∈ auxPiecesInWalk
            (SimpleGraph.Walk.cons hPx tail) := by
          rw [mem_auxPiecesInWalk_iff, SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ (List.mem_of_mem_dropLast hR)
        rcases honly R hRfull with rfl | rfl
        · exact hPnotTail (List.mem_of_mem_dropLast hR)
        · exact hQnotDrop hR
      have hvQ := root_mem_final_piece_of_auxPath D Q tail htailPath hxroot hno
      have htailNonNil : ¬tail.Nil := by
        intro hnil
        have hxQ : x = (.inr (.inl Q) : FamilyAuxVertex V A) := hnil.eq
        rw [hxQ] at hxroot
        simp [familyAuxRoot] at hxroot
      have hpenTail :=
        root_penultimate_eq_of_auxPath D Q tail htailPath hxroot hno
      have hpen : familyAuxRoot
          (SimpleGraph.Walk.cons hPx tail).penultimate = some v := by
        simpa [SimpleGraph.Walk.penultimate_cons_of_not_nil hPx tail htailNonNil]
          using hpenTail
      refine ⟨v, ?_, hpen, hvP, hvQ⟩
      simpa only [SimpleGraph.Walk.snd_cons] using hxroot

/-! ### The cyclic order of the piece nodes -/

/-- Read a piece label from a signed-incidence vertex, when that vertex is a
piece node. -/
def familyAuxPiece? {V : Type*} {A : Finset (PackedSubgraph V)} :
    FamilyAuxVertex V A → Option ↥A
  | .inr (.inl P) => some P
  | _ => none

@[simp] lemma familyAuxPiece?_eq_some_iff {V : Type*}
    {A : Finset (PackedSubgraph V)} {x : FamilyAuxVertex V A} {P : ↥A} :
    familyAuxPiece? x = some P ↔ x = .inr (.inl P) := by
  cases x with
  | inl v => simp [familyAuxPiece?]
  | inr q =>
      cases q with
      | inl Q => simp [familyAuxPiece?]
      | inr Qv => simp [familyAuxPiece?]

/-- Filtering the tail of a closed auxiliary cycle records its piece nodes
in their cyclic order.  The initial vertex occurs again at the end, so using
the tail retains every piece exactly once. -/
noncomputable def auxPieceOrder {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {x y : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk x y) :
    List ↥A :=
  c.support.tail.filterMap familyAuxPiece?

lemma mem_auxPieceOrder_iff_tail {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {x y : FamilyAuxVertex V A} {c : (familyAuxGraph D).Walk x y}
    {P : ↥A} :
    P ∈ auxPieceOrder c ↔
      (.inr (.inl P) : FamilyAuxVertex V A) ∈ c.support.tail := by
  classical
  simp [auxPieceOrder]

lemma mem_auxPieceOrder_iff {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} {c : (familyAuxGraph D).Walk z z}
    (hc : c.IsCycle) {P : ↥A} :
    P ∈ auxPieceOrder c ↔ P ∈ auxPiecesInWalk c := by
  rw [mem_auxPieceOrder_iff_tail, mem_auxPiecesInWalk_iff]
  constructor
  · exact List.mem_of_mem_tail
  · intro hP
    rw [c.mem_support_iff] at hP
    rcases hP with hP | hP
    · subst z
      exact c.end_mem_tail_support hc.not_nil
    · exact hP

lemma auxPieceOrder_nodup {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} {c : (familyAuxGraph D).Walk z z}
    (hc : c.IsCycle) : (auxPieceOrder c).Nodup := by
  classical
  apply hc.support_nodup.filterMap
  intro x y P hx hy
  simp only [Option.mem_def] at hx hy
  rw [familyAuxPiece?_eq_some_iff] at hx hy
  exact hx.trans hy.symm

lemma auxPieceOrder_toFinset {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} {c : (familyAuxGraph D).Walk z z}
    (hc : c.IsCycle) : (auxPieceOrder c).toFinset = auxPiecesInWalk c := by
  classical
  ext P
  simpa [mem_auxPieceOrder_iff hc]

/-- The ordered piece list, with membership in the cycle recorded in the
type.  This avoids repeatedly transporting membership proofs when recursing
around the cyclic order. -/
noncomputable def auxPieceOrderSubtype {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) : List ↥(auxPiecesInWalk c) :=
  (auxPieceOrder c).attach.map fun P =>
    ⟨P.1, (mem_auxPieceOrder_iff hc).mp P.2⟩

@[simp] lemma auxPieceOrderSubtype_map_val {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) :
    (auxPieceOrderSubtype c hc).map Subtype.val = auxPieceOrder c := by
  rw [auxPieceOrderSubtype, List.map_map]
  change (auxPieceOrder c).attach.map Subtype.val = auxPieceOrder c
  exact List.attach_map_subtype_val _

lemma mem_auxPieceOrderSubtype_iff {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (P : ↥(auxPiecesInWalk c)) :
    P ∈ auxPieceOrderSubtype c hc := by
  have hval : P.1 ∈ (auxPieceOrderSubtype c hc).map Subtype.val := by
    rw [auxPieceOrderSubtype_map_val c hc]
    exact (mem_auxPieceOrder_iff hc).2 P.2
  obtain ⟨Q, hQ, hQP⟩ := List.mem_map.mp hval
  have : Q = P := Subtype.ext hQP
  simpa [this] using hQ

lemma auxPieceOrderSubtype_nodup {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) : (auxPieceOrderSubtype c hc).Nodup := by
  apply List.Nodup.of_map Subtype.val
  rw [auxPieceOrderSubtype_map_val c hc]
  exact auxPieceOrder_nodup hc

@[simp] lemma auxPieceOrderSubtype_toFinset {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) :
    (auxPieceOrderSubtype c hc).toFinset = Finset.univ := by
  ext P
  simp [mem_auxPieceOrderSubtype_iff c hc P]

/-- Selected pieces in the cyclic order inherited from the auxiliary
cycle. -/
noncomputable def auxSelectedOrder {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c)) :
    List ↥(auxPiecesInWalk c) :=
  (auxPieceOrderSubtype c hc).filter fun P => P ∈ S

@[simp] lemma mem_auxSelectedOrder_iff {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (P : ↥(auxPiecesInWalk c)) :
    P ∈ auxSelectedOrder c hc S ↔ P ∈ S := by
  simp [auxSelectedOrder, mem_auxPieceOrderSubtype_iff c hc P]

lemma auxSelectedOrder_nodup {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c)) :
    (auxSelectedOrder c hc S).Nodup :=
  (auxPieceOrderSubtype_nodup c hc).filter _

@[simp] lemma auxSelectedOrder_toFinset {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c)) :
    (auxSelectedOrder c hc S).toFinset = S := by
  ext P
  simp [mem_auxSelectedOrder_iff c hc S P]

lemma auxSelectedOrder_ne_nil {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) {S : Finset ↥(auxPiecesInWalk c)}
    (hS : S.Nonempty) : auxSelectedOrder c hc S ≠ [] := by
  obtain ⟨P, hP⟩ := hS
  exact List.ne_nil_of_mem ((mem_auxSelectedOrder_iff c hc S P).2 hP)

/-- Cyclic successor inside the selected class. -/
noncomputable def auxSelectedSuccessor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (P : ↥S) : ↥S := by
  classical
  let l := auxSelectedOrder c hc S
  have hP : P.1 ∈ l := (mem_auxSelectedOrder_iff c hc S P.1).2 P.2
  let Q := l.next P.1 hP
  refine ⟨Q, ?_⟩
  apply (mem_auxSelectedOrder_iff c hc S Q).1
  exact List.next_mem l P.1 hP

/-- A two-valued parity label for the part of the auxiliary graph obtained
when `P` is the only allowed piece node.  Ambient vertices receive their
`P`-colour, and every dummy vertex receives the opposite colour of its
ambient root. -/
def familyAuxSinglePieceSide {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (Q : ↥A) → FlexiblePathData T Q.1) (P : ↥A) :
    FamilyAuxVertex V A → Fin 2
  | .inl v => (D P).color v
  | .inr (.inl _) => 0
  | .inr (.inr (_, v)) => if (D P).color v = 0 then 1 else 0

/-- Every auxiliary edge not incident with a piece node other than `P`
changes the preceding parity label. -/
lemma familyAuxSinglePieceSide_ne_of_adj {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (Q : ↥A) → FlexiblePathData T Q.1) (P : ↥A)
    {x y : FamilyAuxVertex V A} (hxy : (familyAuxGraph D).Adj x y)
    (hx : ∀ Q : ↥A, x = .inr (.inl Q) → Q = P)
    (hy : ∀ Q : ↥A, y = .inr (.inl Q) → Q = P) :
    familyAuxSinglePieceSide D P x ≠ familyAuxSinglePieceSide D P y := by
  cases x with
  | inl v =>
      cases y with
      | inl w => simp [familyAuxGraph, familyAuxAdj] at hxy
      | inr q =>
          cases q with
          | inl Q =>
              have hQP : Q = P := hy Q rfl
              subst Q
              have h := hxy
              simp [familyAuxGraph, familyAuxAdj] at h
              simp [familyAuxSinglePieceSide, h.2]
          | inr Qw =>
              rcases Qw with ⟨Q, w⟩
              have h := hxy
              simp only [ne_eq] at h
              rcases h with ⟨rfl, hw, hQ⟩
              rcases fin_two_eq_zero_or_one ((D P).color v) with h0 | h1
              · simp [familyAuxSinglePieceSide, h0]
              · simp [familyAuxSinglePieceSide, h1]
  | inr p =>
      cases p with
      | inl Q =>
          have hQP : Q = P := hx Q rfl
          subst Q
          cases y with
          | inl v =>
              have h := hxy
              simp [familyAuxGraph, familyAuxAdj] at h
              simp [familyAuxSinglePieceSide, h.2]
          | inr q =>
              cases q with
              | inl R => simp [familyAuxGraph, familyAuxAdj] at hxy
              | inr Rv =>
                  rcases Rv with ⟨R, v⟩
                  have h := hxy
                  simp only [ne_eq] at h
                  rcases h with ⟨rfl, hv, h0⟩
                  simp [familyAuxSinglePieceSide, h0]
      | inr Qv =>
          rcases Qv with ⟨Q, v⟩
          cases y with
          | inl w =>
              have h := hxy
              simp only [ne_eq] at h
              rcases h with ⟨rfl, hv, hQ⟩
              rcases fin_two_eq_zero_or_one ((D P).color w) with h0 | h1
              · simp [familyAuxSinglePieceSide, h0]
              · simp [familyAuxSinglePieceSide, h1]
          | inr q =>
              cases q with
              | inl R =>
                  have hRP : R = P := hy R rfl
                  subst R
                  have h := hxy
                  simp only [ne_eq] at h
                  rcases h with ⟨rfl, hv, h0⟩
                  simp [familyAuxSinglePieceSide, h0]
              | inr Rw => simp [familyAuxGraph, familyAuxAdj] at hxy

/-- A closed auxiliary walk whose only possible piece node is `P` has even
length. -/
lemma even_length_of_at_most_one_auxPiece {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (Q : ↥A) → FlexiblePathData T Q.1}
    (P : ↥A) {x y : FamilyAuxVertex V A}
    (w : (familyAuxGraph D).Walk x y)
    (honly : ∀ Q : ↥A,
      (.inr (.inl Q) : FamilyAuxVertex V A) ∈ w.support → Q = P) :
    Even w.length ↔
      familyAuxSinglePieceSide D P x = familyAuxSinglePieceSide D P y := by
  induction w with
  | nil => simp
  | @cons x y z hxy p ih =>
      have honlyP : ∀ Q : ↥A,
          (.inr (.inl Q) : FamilyAuxVertex V A) ∈ p.support → Q = P := by
        intro Q hQ
        exact honly Q (List.mem_cons_of_mem x hQ)
      have hx : ∀ Q : ↥A, x = .inr (.inl Q) → Q = P := by
        intro Q hxQ
        apply honly Q
        rw [SimpleGraph.Walk.support_cons]
        simpa [hxQ]
      have hy : ∀ Q : ↥A, y = .inr (.inl Q) → Q = P := by
        intro Q hyQ
        apply honlyP Q
        simpa [hyQ] using p.start_mem_support
      have hside := familyAuxSinglePieceSide_ne_of_adj D P hxy hx hy
      have hih := ih honlyP
      rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, hih]
      constructor
      · exact fun hyz ↦ fin_two_eq_of_ne_of_ne hside hyz
      · intro hxz hyz
        exact hside (hxz.trans hyz.symm)

/-- A piece-free auxiliary arc has the parity of the disagreement between
the two piece colours at its common ambient root. -/
lemma piece_free_auxPath_length_mod_two {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (R : ↥A) → FlexiblePathData T R.1) (P Q : ↥A) (hPQ : P ≠ Q)
    (p : (familyAuxGraph D).Walk (.inr (.inl P)) (.inr (.inl Q)))
    (hp : p.IsPath)
    (honly : ∀ R : ↥A,
      (.inr (.inl R) : FamilyAuxVertex V A) ∈ p.support → R = P ∨ R = Q)
    {v : V} (hroot : familyAuxRoot p.snd = some v) :
    p.length % 2 = (((D P).color v).val + ((D Q).color v).val) % 2 := by
  cases p with
  | nil => exact (hPQ rfl).elim
  | @cons _ x _ hPx tail =>
      have hPnotTail :
          (.inr (.inl P) : FamilyAuxVertex V A) ∉ tail.support := by
        have hn := hp.support_nodup
        rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hn
        exact hn.1
      have honlyTail : ∀ R : ↥A,
          (.inr (.inl R) : FamilyAuxVertex V A) ∈ tail.support → R = Q := by
        intro R hR
        rcases honly R (List.mem_cons_of_mem _ hR) with hRP | hRQ
        · subst R
          exact (hPnotTail hR).elim
        · exact hRQ
      have heven : Even tail.length ↔
          familyAuxSinglePieceSide D Q x = 0 := by
        simpa [familyAuxSinglePieceSide] using
          (even_length_of_at_most_one_auxPiece Q tail honlyTail)
      simp only [SimpleGraph.Walk.snd_cons] at hroot
      simp only [SimpleGraph.Walk.length_cons]
      cases x with
      | inl a =>
          have hPx' := hPx
          simp [familyAuxGraph, familyAuxAdj] at hPx'
          simp [familyAuxRoot] at hroot
          subst a
          rcases fin_two_eq_zero_or_one ((D Q).color v) with hQ0 | hQ1
          · rw [Nat.even_iff] at heven
            have htail0 : tail.length % 2 = 0 :=
              heven.mpr (by simp [familyAuxSinglePieceSide, hQ0])
            simp [hPx'.2, hQ0]
            omega
          · rw [Nat.even_iff] at heven
            have htailNe : tail.length % 2 ≠ 0 := by
              intro hzero
              have hfalse := heven.mp hzero
              simp [familyAuxSinglePieceSide, hQ1] at hfalse
            rcases Nat.mod_two_eq_zero_or_one tail.length with htail0 | htail1
            · exact (htailNe htail0).elim
            · simp [hPx'.2, hQ1]
              omega
      | inr q =>
          cases q with
          | inl R => simp [familyAuxGraph, familyAuxAdj] at hPx
          | inr Ra =>
              rcases Ra with ⟨R, a⟩
              have hPx' := hPx
              simp [familyAuxGraph, familyAuxAdj] at hPx'
              rcases hPx' with ⟨hPR, ha, hP0⟩
              subst R
              simp [familyAuxRoot] at hroot
              subst a
              rcases fin_two_eq_zero_or_one ((D Q).color v) with hQ0 | hQ1
              · rw [Nat.even_iff] at heven
                have htailNe : tail.length % 2 ≠ 0 := by
                  intro hzero
                  have hfalse := heven.mp hzero
                  simpa [familyAuxSinglePieceSide, hQ0] using hfalse
                rcases Nat.mod_two_eq_zero_or_one tail.length with htail0 | htail1
                · exact (htailNe htail0).elim
                · simp [hP0, hQ0]
                  omega
              · rw [Nat.even_iff] at heven
                have htail0 : tail.length % 2 = 0 :=
                  heven.mpr (by simp [familyAuxSinglePieceSide, hQ1])
                simp [hP0, hQ1]
                omega

lemma familyAuxCoarseSide_ne_of_adj_of_no_piece {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1)
    {x y : FamilyAuxVertex V A} (hxy : (familyAuxGraph D).Adj x y)
    (hx : ∀ P : ↥A, x ≠ .inr (.inl P))
    (hy : ∀ P : ↥A, y ≠ .inr (.inl P)) :
    familyAuxCoarseSide x ≠ familyAuxCoarseSide y := by
  cases x with
  | inl v =>
      cases y with
      | inl w => simp [familyAuxGraph, familyAuxAdj] at hxy
      | inr q =>
          cases q with
          | inl P => exact (hy P rfl).elim
          | inr Pv => simp [familyAuxCoarseSide]
  | inr p =>
      cases p with
      | inl P => exact (hx P rfl).elim
      | inr Pv =>
          cases y with
          | inl w => simp [familyAuxCoarseSide]
          | inr q =>
              cases q with
              | inl P => exact (hy P rfl).elim
              | inr Qw => simp [familyAuxGraph, familyAuxAdj] at hxy

/-- A closed auxiliary walk with no piece node has even length. -/
lemma even_length_of_no_auxPiece {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {x y : FamilyAuxVertex V A} (w : (familyAuxGraph D).Walk x y)
    (hno : ∀ P : ↥A,
      (.inr (.inl P) : FamilyAuxVertex V A) ∉ w.support) :
    Even w.length ↔ familyAuxCoarseSide x = familyAuxCoarseSide y := by
  induction w with
  | nil => simp
  | @cons x y z hxy p ih =>
      have hnoP : ∀ P : ↥A,
          (.inr (.inl P) : FamilyAuxVertex V A) ∉ p.support := by
        intro P hP
        exact hno P (List.mem_cons_of_mem x hP)
      have hx : ∀ P : ↥A, x ≠ .inr (.inl P) := by
        intro P h
        apply hno P
        simpa [h] using (show x ∈ (hxy.toWalk.append p).support from
          (hxy.toWalk.append p).start_mem_support)
      have hy : ∀ P : ↥A, y ≠ .inr (.inl P) := by
        intro P h
        apply hnoP P
        simpa [h] using p.start_mem_support
      have hside := familyAuxCoarseSide_ne_of_adj_of_no_piece D hxy hx hy
      have hih := ih hnoP
      simp only [SimpleGraph.Walk.length_cons, Nat.even_add_one, hih]
      cases hxs : familyAuxCoarseSide x <;>
        cases hys : familyAuxCoarseSide y <;>
          cases hzs : familyAuxCoarseSide z <;> simp_all

/-- Every odd closed auxiliary walk actually visits at least one piece node. -/
lemma auxPiecesInWalk_nonempty_of_odd {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hcodd : Odd c.length) :
    (auxPiecesInWalk c).Nonempty := by
  classical
  by_contra hempty
  have hno : ∀ P : ↥A,
      (.inr (.inl P) : FamilyAuxVertex V A) ∉ c.support := by
    intro P hP
    apply hempty
    exact ⟨P, mem_auxPiecesInWalk_iff.mpr hP⟩
  have heven : Even c.length :=
    (even_length_of_no_auxPiece c hno).2 rfl
  exact (Nat.not_even_iff_odd.mpr hcodd) heven

/-- An odd auxiliary closed walk contains at least two distinct piece
nodes. -/
lemma two_le_card_auxPiecesInWalk_of_odd {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (Q : ↥A) → FlexiblePathData T Q.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hcodd : Odd c.length) : 2 ≤ (auxPiecesInWalk c).card := by
  classical
  obtain ⟨P, hP⟩ := auxPiecesInWalk_nonempty_of_odd c hcodd
  by_contra hcard
  have hle : (auxPiecesInWalk c).card ≤ 1 := by omega
  have honly : ∀ Q : ↥A,
      (.inr (.inl Q) : FamilyAuxVertex V A) ∈ c.support → Q = P := by
    intro Q hQ
    have hQ' : Q ∈ auxPiecesInWalk c := mem_auxPiecesInWalk_iff.mpr hQ
    exact Finset.card_le_one.mp hle Q hQ' P hP
  have heven : Even c.length :=
    (even_length_of_at_most_one_auxPiece P c honly).2 rfl
  exact (Nat.not_even_iff_odd.mpr hcodd) heven

lemma list_isRotated_filterMap {X Y : Type*} [DecidableEq X]
    {l l' : List X} (h : l ~r l') (f : X → Option Y) :
    l.filterMap f ~r l'.filterMap f := by
  obtain ⟨n, rfl⟩ := h
  let k := n % l.length
  rw [List.rotate_eq_drop_append_take_mod]
  simp only [List.filterMap_append]
  change l.filterMap f ~r
    (l.drop k).filterMap f ++ (l.take k).filterMap f
  calc
    l.filterMap f = ((l.take k) ++ (l.drop k)).filterMap f := by
      rw [List.take_append_drop]
    _ = (l.take k).filterMap f ++ (l.drop k).filterMap f := by
      rw [List.filterMap_append]
    _ ~r (l.drop k).filterMap f ++ (l.take k).filterMap f :=
      List.isRotated_append

/-- A rotation of a duplicate-free nonempty list is determined by its last
element. -/
lemma list_eq_of_isRotated_of_nodup_of_getLast_eq
    {X : Type*} [DecidableEq X] {l l' : List X}
    (hrot : l ~r l') (hn : l.Nodup)
    (hl : l ≠ []) (hl' : l' ≠ [])
    (hlast : l.getLast hl = l'.getLast hl') : l = l' := by
  obtain ⟨n, rfl⟩ := hrot
  have hlen : 0 < l.length := List.length_pos_of_ne_nil hl
  have hrotNe : l.rotate n ≠ [] := by
    simpa using hl
  have hlast' : l.getLast hl = (l.rotate n).getLast hrotNe := by
    exact hlast
  rw [List.getLast_eq_getElem hl, List.getLast_eq_getElem hrotNe,
    List.getElem_rotate] at hlast'
  have hlast'' : l[l.length - 1]'(by omega) =
      l[(l.length - 1 + n) % l.length]'(Nat.mod_lt _ hlen) := by
    simpa using hlast'
  have hidx : l.length - 1 =
      (l.length - 1 + n) % l.length :=
    hn.getElem_inj_iff.mp hlast''
  have hnmod : n % l.length = 0 := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : l.length - 1 < l.length)] at hidx
    by_contra hm
    have hmpos : 0 < n % l.length := Nat.pos_of_ne_zero hm
    have hmlt : n % l.length < l.length := Nat.mod_lt _ hlen
    have hcalc : (l.length - 1 + n % l.length) % l.length =
        n % l.length - 1 := by
      rw [show l.length - 1 + n % l.length =
        l.length + (n % l.length - 1) by omega]
      simp [Nat.mod_eq_of_lt (by omega : n % l.length - 1 < l.length)]
    rw [hcalc] at hidx
    omega
  rw [← List.rotate_mod, hnmod, List.rotate_zero]

lemma support_tail_getLast_of_not_nil {X : Type*} [Fintype X]
    {H : SimpleGraph X} {x : X} (w : H.Walk x x) (hw : ¬w.Nil) :
    w.support.tail.getLast (List.ne_nil_of_mem (w.end_mem_tail_support hw)) = x := by
  cases w with
  | nil => exact (hw (by simp)).elim
  | @cons _ y _ h p => simpa using p.getLast_support

/-- Rotating a simple cycle first at `u` and then at `v` gives the same
oriented cycle as rotating it directly at `v`. -/
lemma rotate_rotate_eq_of_isCycle {X : Type*} [Fintype X]
    {H : SimpleGraph X} {x u v : X} (c : H.Walk x x) (hc : c.IsCycle)
    (hu : u ∈ c.support) (hv : v ∈ c.support) :
    let cu := c.rotate u hu
    let hvu : v ∈ cu.support :=
      (SimpleGraph.Walk.mem_support_rotate_iff c u hu).2 hv
    cu.rotate v hvu = c.rotate v hv := by
  dsimp only
  let cu := c.rotate u hu
  have hvu : v ∈ cu.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c u hu).2 hv
  let left := cu.rotate v hvu
  let right := c.rotate v hv
  apply SimpleGraph.Walk.support_injective
  have hleftCycle : left.IsCycle := (hc.rotate hu).rotate hvu
  have hrightCycle : right.IsCycle := hc.rotate hv
  have hrot : left.support.tail ~r right.support.tail := by
    exact (cu.support_rotate v hvu).trans
      ((c.support_rotate u hu).trans (c.support_rotate v hv).symm)
  have htail : left.support.tail = right.support.tail := by
    let hl : left.support.tail ≠ [] :=
      List.ne_nil_of_mem (left.end_mem_tail_support hleftCycle.not_nil)
    let hr : right.support.tail ≠ [] :=
      List.ne_nil_of_mem (right.end_mem_tail_support hrightCycle.not_nil)
    exact list_eq_of_isRotated_of_nodup_of_getLast_eq hrot
      hleftCycle.support_nodup hl hr
      ((support_tail_getLast_of_not_nil left hleftCycle.not_nil).trans
        (support_tail_getLast_of_not_nil right hrightCycle.not_nil).symm)
  rw [← left.cons_tail_support, ← right.cons_tail_support, htail]

lemma snd_append_of_left_not_nil {X : Type*}
    {H : SimpleGraph X} {x y z : X}
    (p : H.Walk x y) (q : H.Walk y z) (hp : ¬p.Nil) :
    (p.append q).snd = p.snd := by
  have hlen : 1 ≤ p.length := by
    have : 0 < p.length := by
      simpa [SimpleGraph.Walk.not_nil_iff_lt_length] using hp
    omega
  unfold SimpleGraph.Walk.snd
  rw [SimpleGraph.Walk.getVert_append']
  simp [hlen]

lemma penultimate_append_of_right_not_nil {X : Type*}
    {H : SimpleGraph X} {x y z : X}
    (p : H.Walk x y) (q : H.Walk y z) (hq : ¬q.Nil) :
    (p.append q).penultimate = q.penultimate := by
  calc
    (p.append q).penultimate = (p.append q).reverse.snd :=
      (p.append q).snd_reverse.symm
    _ = (q.reverse.append p.reverse).snd := by rw [SimpleGraph.Walk.reverse_append]
    _ = q.reverse.snd := snd_append_of_left_not_nil q.reverse p.reverse (by simpa)
    _ = q.penultimate := q.snd_reverse

lemma list_next_ne_self_of_nodup {X : Type*} [DecidableEq X]
    {l : List X} (hn : l.Nodup) (hl : 2 ≤ l.length)
    (x : X) (hx : x ∈ l) : l.next x hx ≠ x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.next_getElem l hn i hi]
  intro heq
  have hindex : (i + 1) % l.length = i :=
    hn.getElem_inj_iff.mp heq
  by_cases hs : i + 1 < l.length
  · rw [Nat.mod_eq_of_lt hs] at hindex
    omega
  · have hisucc : i + 1 = l.length := by omega
    rw [hisucc, Nat.mod_self] at hindex
    omega

/-- The next piece in the cyclic order induced by the auxiliary cycle. -/
noncomputable def auxPieceSuccessor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (P : ↥(auxPiecesInWalk c)) :
    ↥(auxPiecesInWalk c) := by
  classical
  let hP : P.1 ∈ auxPieceOrder c := (mem_auxPieceOrder_iff hc).2 P.2
  let Q : ↥A := (auxPieceOrder c).next P.1 hP
  refine ⟨Q, ?_⟩
  apply (mem_auxPieceOrder_iff hc).1
  exact List.next_mem (auxPieceOrder c) P.1 hP

/-- The subtype-valued cyclic list and the original definition of piece
successor have the same `next` operation. -/
lemma auxPieceOrderSubtype_next_eq_successor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (P : ↥(auxPiecesInWalk c)) :
    let l := auxPieceOrderSubtype c hc
    l.next P (mem_auxPieceOrderSubtype_iff c hc P) =
      auxPieceSuccessor c hc P := by
  classical
  dsimp only
  apply Subtype.ext
  have hmap := list_map_next_of_injective Subtype.val
    Subtype.val_injective (auxPieceOrderSubtype c hc)
    (auxPieceOrderSubtype_nodup c hc) P
    (mem_auxPieceOrderSubtype_iff c hc P)
  have hPorder : P.1 ∈ auxPieceOrder c :=
    (mem_auxPieceOrder_iff hc).2 P.2
  change ((auxPieceOrderSubtype c hc).next P _).1 =
    (auxPieceOrder c).next P.1 hPorder
  exact hmap.symm.trans (list_next_eq_of_eq
    (auxPieceOrderSubtype_map_val c hc) P.1 _ hPorder)

lemma auxPieceSuccessor_ne {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) : auxPieceSuccessor c hc P ≠ P := by
  classical
  intro h
  have hlen : 2 ≤ (auxPieceOrder c).length := by
    have hcard := two_le_card_auxPiecesInWalk_of_odd c hcodd
    rw [← auxPieceOrder_toFinset hc] at hcard
    simpa [List.toFinset_card_of_nodup (auxPieceOrder_nodup hc)] using hcard
  have hne := list_next_ne_self_of_nodup (auxPieceOrder_nodup hc) hlen P.1
    ((mem_auxPieceOrder_iff hc).2 P.2)
  apply hne
  exact congrArg Subtype.val h

lemma auxPieceSuccessor_injective {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) : Function.Injective (auxPieceSuccessor c hc) := by
  classical
  intro P Q hPQ
  apply Subtype.ext
  let l := auxPieceOrder c
  let hP : P.1 ∈ l := (mem_auxPieceOrder_iff hc).2 P.2
  let hQ : Q.1 ∈ l := (mem_auxPieceOrder_iff hc).2 Q.2
  have hnext : l.next P.1 hP = l.next Q.1 hQ := by
    exact congrArg Subtype.val hPQ
  have hprevP := List.prev_next l (auxPieceOrder_nodup hc) P.1 hP
  have hprevQ := List.prev_next l (auxPieceOrder_nodup hc) Q.1 hQ
  calc
    P.1 = l.prev (l.next P.1 hP) (List.next_mem l P.1 hP) := hprevP.symm
    _ = l.prev (l.next Q.1 hQ) (List.next_mem l Q.1 hQ) := by
      congr 1
    _ = Q.1 := hprevQ

/-- The preceding piece in the cyclic order induced by the auxiliary cycle. -/
noncomputable def auxPiecePredecessor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (P : ↥(auxPiecesInWalk c)) :
    ↥(auxPiecesInWalk c) := by
  classical
  let hP : P.1 ∈ auxPieceOrder c := (mem_auxPieceOrder_iff hc).2 P.2
  let Q : ↥A := (auxPieceOrder c).prev P.1 hP
  refine ⟨Q, ?_⟩
  apply (mem_auxPieceOrder_iff hc).1
  exact List.prev_mem (auxPieceOrder c) P.1 hP

@[simp] lemma auxPieceSuccessor_predecessor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (P : ↥(auxPiecesInWalk c)) :
    auxPieceSuccessor c hc (auxPiecePredecessor c hc P) = P := by
  classical
  apply Subtype.ext
  let l := auxPieceOrder c
  let hP : P.1 ∈ l := (mem_auxPieceOrder_iff hc).2 P.2
  change l.next (l.prev P.1 hP) (List.prev_mem l P.1 hP) = P.1
  exact List.next_prev l (auxPieceOrder_nodup hc) P.1 hP

@[simp] lemma auxPiecePredecessor_successor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (P : ↥(auxPiecesInWalk c)) :
    auxPiecePredecessor c hc (auxPieceSuccessor c hc P) = P := by
  classical
  apply Subtype.ext
  let l := auxPieceOrder c
  let hP : P.1 ∈ l := (mem_auxPieceOrder_iff hc).2 P.2
  change l.prev (l.next P.1 hP) (List.next_mem l P.1 hP) = P.1
  exact List.prev_next l (auxPieceOrder_nodup hc) P.1 hP

lemma auxPiecePredecessor_ne_successor_of_three_le_card
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hcard : 3 ≤ (auxPiecesInWalk c).card)
    (P : ↥(auxPiecesInWalk c)) :
    auxPiecePredecessor c hc P ≠ auxPieceSuccessor c hc P := by
  classical
  intro hpredsucc
  let l := auxPieceOrderSubtype c hc
  let Q := auxPieceSuccessor c hc P
  have hPQ : P ≠ Q := (auxPieceSuccessor_ne c hc hcodd P).symm
  have hPmem : P ∈ l := mem_auxPieceOrderSubtype_iff c hc P
  have hPQnext : l.next P hPmem = Q :=
    auxPieceOrderSubtype_next_eq_successor c hc P
  have hQPnext : l.next Q (hPQnext ▸ List.next_mem l P hPmem) = P := by
    rw [auxPieceOrderSubtype_next_eq_successor]
    change auxPieceSuccessor c hc Q = P
    change auxPieceSuccessor c hc (auxPieceSuccessor c hc P) = P
    rw [← hpredsucc]
    exact auxPieceSuccessor_predecessor c hc P
  have hexhaust := list_mem_of_two_cycle l (auxPieceOrderSubtype_nodup c hc)
    hPmem hPQ hPQnext hQPnext
  have hsub : (Finset.univ : Finset ↥(auxPiecesInWalk c)) ⊆ {P, Q} := by
    intro R _
    have hR := hexhaust R (mem_auxPieceOrderSubtype_iff c hc R)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hR
  have hle := Finset.card_le_card hsub
  have hPQ' : P ≠ Q := hPQ
  simp [hPQ'] at hle
  omega

lemma auxPieceOrder_rotate_isRotated {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z y : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hy : y ∈ c.support) :
    auxPieceOrder (c.rotate y hy) ~r auxPieceOrder c := by
  classical
  exact list_isRotated_filterMap (c.support_rotate y hy) familyAuxPiece?

/-- When an auxiliary cycle is based at a piece node, its ordered piece list
ends at that piece node. -/
lemma auxPieceOrder_eq_append_start {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    (P : ↥A)
    (c : (familyAuxGraph D).Walk (.inr (.inl P)) (.inr (.inl P)))
    (hc : c.IsCycle) :
    ∃ l : List ↥A, auxPieceOrder c = l ++ [P] := by
  classical
  have hend : (.inr (.inl P) : FamilyAuxVertex V A) ∈ c.support.tail :=
    c.end_mem_tail_support hc.not_nil
  have htail : c.support.tail ≠ [] := List.ne_nil_of_mem hend
  have hlast : c.support.tail.getLast htail =
      (.inr (.inl P) : FamilyAuxVertex V A) := by
    cases c with
    | nil => exact (hc.not_nil (by simp)).elim
    | @cons _ v _ hv p => simpa using p.getLast_support
  let l := c.support.tail.dropLast.filterMap familyAuxPiece?
  refine ⟨l, ?_⟩
  unfold auxPieceOrder
  have hdecomp := List.dropLast_append_getLast htail
  rw [hlast] at hdecomp
  calc
    c.support.tail.filterMap familyAuxPiece? =
        (c.support.tail.dropLast ++
          [(.inr (.inl P) : FamilyAuxVertex V A)]).filterMap
            familyAuxPiece? := congrArg (fun s ↦ s.filterMap familyAuxPiece?) hdecomp.symm
    _ = l ++ [P] := by simp [l, familyAuxPiece?]

/-- For a walk from one piece node to a distinct piece node, the ordered
piece list ends at its terminal piece. -/
lemma auxPieceOrder_eq_append_end {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    (P Q : ↥A) (hPQ : P ≠ Q)
    (p : (familyAuxGraph D).Walk (.inr (.inl P)) (.inr (.inl Q))) :
    ∃ l : List ↥A, auxPieceOrder p = l ++ [Q] := by
  classical
  have hnodes : (.inr (.inl P) : FamilyAuxVertex V A) ≠ .inr (.inl Q) := by
    intro h
    have h' : (Sum.inl P : ↥A ⊕ (↥A × V)) = Sum.inl Q := Sum.inr.inj h
    exact hPQ (Sum.inl.inj h')
  have hend : (.inr (.inl Q) : FamilyAuxVertex V A) ∈ p.support.tail :=
    p.end_mem_tail_support_of_ne hnodes
  have htail : p.support.tail ≠ [] := List.ne_nil_of_mem hend
  have hlast : p.support.tail.getLast htail =
      (.inr (.inl Q) : FamilyAuxVertex V A) := by
    cases p with
    | nil => exact (hnodes rfl).elim
    | @cons _ v _ hv q => simpa using q.getLast_support
  let l := p.support.tail.dropLast.filterMap familyAuxPiece?
  refine ⟨l, ?_⟩
  unfold auxPieceOrder
  have hdecomp := List.dropLast_append_getLast htail
  rw [hlast] at hdecomp
  calc
    p.support.tail.filterMap familyAuxPiece? =
        (p.support.tail.dropLast ++
          [(.inr (.inl Q) : FamilyAuxVertex V A)]).filterMap
            familyAuxPiece? := congrArg (fun s ↦ s.filterMap familyAuxPiece?) hdecomp.symm
    _ = l ++ [Q] := by simp [l, familyAuxPiece?]

/-- Rotating at `P` makes its cyclic successor the first piece node and
keeps `P` as the final piece node. -/
lemma auxPieceOrder_rotate_at_piece {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) :
    let pnode : FamilyAuxVertex V A := .inr (.inl P.1)
    let hpnode : pnode ∈ c.support := mem_auxPiecesInWalk_iff.mp P.2
    let cr := c.rotate pnode hpnode
    ∃ l : List ↥A,
      auxPieceOrder cr = (auxPieceSuccessor c hc P).1 :: l ++ [P.1] := by
  classical
  dsimp only
  let pnode : FamilyAuxVertex V A := .inr (.inl P.1)
  have hpnode : pnode ∈ c.support := mem_auxPiecesInWalk_iff.mp P.2
  let cr := c.rotate pnode hpnode
  obtain ⟨pre, hpre⟩ :=
    auxPieceOrder_eq_append_start P.1 cr (hc.rotate hpnode)
  have hlen : 2 ≤ (auxPieceOrder cr).length := by
    have hcard := two_le_card_auxPiecesInWalk_of_odd cr (by simpa [cr] using hcodd)
    rw [← auxPieceOrder_toFinset (hc.rotate hpnode)] at hcard
    simpa [List.toFinset_card_of_nodup
      (auxPieceOrder_nodup (hc.rotate hpnode))] using hcard
  have hpreNe : pre ≠ [] := by
    intro h
    rw [h, List.nil_append] at hpre
    simp [hpre] at hlen
  obtain ⟨Q, rest, rfl⟩ := List.exists_cons_of_ne_nil hpreNe
  have hrot : auxPieceOrder cr ~r auxPieceOrder c :=
    auxPieceOrder_rotate_isRotated c hpnode
  have hPcr : P.1 ∈ auxPieceOrder cr := by
    apply (mem_auxPieceOrder_iff (hc.rotate hpnode)).2
    rw [auxPiecesInWalk_rotate c hpnode]
    exact P.2
  have hnextRot :
      (auxPieceOrder cr).next P.1 hPcr =
        (auxPieceOrder c).next P.1
          ((mem_auxPieceOrder_iff hc).2 P.2) := by
    exact List.isRotated_next_eq hrot (auxPieceOrder_nodup (hc.rotate hpnode)) hPcr
  have horderNe : auxPieceOrder cr ≠ [] := by
    rw [hpre]
    simp
  have hgetLast : (auxPieceOrder cr).getLast horderNe = P.1 := by
    have hlastSome : (auxPieceOrder cr).getLast? = some P.1 := by
      rw [hpre]
      rw [List.getLast?_append_of_ne_nil (Q :: rest) (by simp)]
      rfl
    rw [List.getLast?_eq_getLast_of_ne_nil horderNe] at hlastSome
    exact Option.some.inj hlastSome
  have hwrap := List.next_getLast_eq_head (auxPieceOrder cr) horderNe
    (auxPieceOrder_nodup (hc.rotate hpnode))
  have hnextHead : (auxPieceOrder cr).next P.1 hPcr = Q := by
    have hhead : (auxPieceOrder cr).head horderNe = Q := by
      have hheadSome : (auxPieceOrder cr).head? = some Q := by
        rw [hpre]
        rfl
      rw [List.head?_eq_some_head horderNe] at hheadSome
      exact Option.some.inj hheadSome
    simpa [hgetLast, hhead] using hwrap
  have hsucc : (auxPieceSuccessor c hc P).1 = Q := by
    change (auxPieceOrder c).next P.1
        ((mem_auxPieceOrder_iff hc).2 P.2) = Q
    exact hnextRot.symm.trans hnextHead
  refine ⟨rest, ?_⟩
  rw [hpre, hsucc]

lemma auxPieceOrder_nodup_of_isPath {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {x y : FamilyAuxVertex V A} {p : (familyAuxGraph D).Walk x y}
    (hp : p.IsPath) : (auxPieceOrder p).Nodup := by
  classical
  apply hp.support_nodup.tail.filterMap
  intro a b P ha hb
  simp only [Option.mem_def] at ha hb
  rw [familyAuxPiece?_eq_some_iff] at ha hb
  exact ha.trans hb.symm

/-- The initial arc from a piece node to its cyclic successor contains no
third piece node. -/
theorem exists_piece_free_successor_arc {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) :
    let Q := auxPieceSuccessor c hc P
    ∃ p : (familyAuxGraph D).Walk (.inr (.inl P.1)) (.inr (.inl Q.1)),
      p.IsPath ∧
      (∀ R ∈ auxPiecesInWalk p, R = P.1 ∨ R = Q.1) ∧
      p.snd = (c.rotate (.inr (.inl P.1))
        (mem_auxPiecesInWalk_iff.mp P.2)).snd ∧
      p.penultimate = (c.rotate (.inr (.inl Q.1))
        (mem_auxPiecesInWalk_iff.mp Q.2)).penultimate := by
  classical
  dsimp only
  let Q := auxPieceSuccessor c hc P
  let pnode : FamilyAuxVertex V A := .inr (.inl P.1)
  let qnode : FamilyAuxVertex V A := .inr (.inl Q.1)
  have hpnode : pnode ∈ c.support := mem_auxPiecesInWalk_iff.mp P.2
  let cr := c.rotate pnode hpnode
  have hqnode : qnode ∈ cr.support := by
    apply (SimpleGraph.Walk.mem_support_rotate_iff c pnode hpnode).2
    exact mem_auxPiecesInWalk_iff.mp Q.2
  let p := cr.takeUntil qnode hqnode
  have hPQsub : Q ≠ P := auxPieceSuccessor_ne c hc hcodd P
  have hPQ : P.1 ≠ Q.1 := by
    intro h
    exact hPQsub (Subtype.ext h.symm)
  have hnodes : pnode ≠ qnode := by
    intro h
    have h' : (Sum.inl P.1 : ↥A ⊕ (↥A × V)) = Sum.inl Q.1 := Sum.inr.inj h
    exact hPQ (Sum.inl.inj h')
  have hpPath : p.IsPath :=
    (hc.rotate hpnode).isPath_takeUntil hqnode
  have hprefixSupport : p.support <+: cr.support := by
    exact cr.support_takeUntil_prefix_support hqnode
  have hprefixTail : p.support.tail <+: cr.support.tail := by
    apply (List.prefix_cons_inj pnode).mp
    simpa [pnode, p, cr] using hprefixSupport
  have hprefixOrder : auxPieceOrder p <+: auxPieceOrder cr :=
    hprefixTail.filterMap familyAuxPiece?
  obtain ⟨rest, hcrOrder⟩ := auxPieceOrder_rotate_at_piece c hc hcodd P
  have hQtail : qnode ∈ p.support.tail := by
    exact p.end_mem_tail_support_of_ne hnodes
  have hQorder : Q.1 ∈ auxPieceOrder p :=
    mem_auxPieceOrder_iff_tail.mpr hQtail
  have hpOrderNe : auxPieceOrder p ≠ [] := List.ne_nil_of_mem hQorder
  obtain ⟨R, rs, hpOrder⟩ := List.exists_cons_of_ne_nil hpOrderNe
  have hfirst : R = Q.1 := by
    have hpre := hprefixOrder
    rw [hpOrder, hcrOrder] at hpre
    exact (List.cons_prefix_cons.mp hpre).1
  subst R
  obtain ⟨endpre, hendOrder⟩ :=
    auxPieceOrder_eq_append_end P.1 Q.1 hPQ p
  have hlast : (auxPieceOrder p).getLast hpOrderNe = Q.1 := by
    have hlastSome : (auxPieceOrder p).getLast? = some Q.1 := by
      rw [hendOrder]
      rw [List.getLast?_append_of_ne_nil endpre (by simp)]
      rfl
    rw [List.getLast?_eq_getLast_of_ne_nil hpOrderNe] at hlastSome
    exact Option.some.inj hlastSome
  have hhead : (auxPieceOrder p).head hpOrderNe = Q.1 := by
    have hheadSome : (auxPieceOrder p).head? = some Q.1 := by
      rw [hpOrder]
      rfl
    rw [List.head?_eq_some_head hpOrderNe] at hheadSome
    exact Option.some.inj hheadSome
  obtain ⟨X, hsingleton⟩ :=
    (List.Nodup.head_eq_getLast_iff hpOrderNe
      (auxPieceOrder_nodup_of_isPath hpPath)).1 (hhead.trans hlast.symm)
  have hX : X = Q.1 := by
    have : Q.1 ∈ [X] := by simpa [hsingleton] using hQorder
    exact (show Q.1 = X by simpa using this).symm
  have hpOrderSingle : auxPieceOrder p = [Q.1] := by
    simpa [hX] using hsingleton
  refine ⟨p, hpPath, ?_, ?_, ?_⟩
  · intro R hR
    have hRnode := mem_auxPiecesInWalk_iff.mp hR
    rw [p.mem_support_iff] at hRnode
    rcases hRnode with hstart | htail
    · left
      have h' : (Sum.inl R : ↥A ⊕ (↥A × V)) = Sum.inl P.1 :=
        Sum.inr.inj hstart
      exact Sum.inl.inj h'
    · right
      have hRorder : R ∈ auxPieceOrder p :=
        mem_auxPieceOrder_iff_tail.mpr htail
      rw [hpOrderSingle] at hRorder
      simpa using hRorder
  · exact cr.snd_takeUntil hnodes.symm hqnode
  · have hqC : qnode ∈ c.support := mem_auxPiecesInWalk_iff.mp Q.2
    have hrotate : cr.rotate qnode hqnode = c.rotate qnode hqC := by
      exact rotate_rotate_eq_of_isCycle c hc hpnode hqC
    have hpNonNil : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne hnodes
    have hpen : (cr.rotate qnode hqnode).penultimate = p.penultimate := by
      unfold SimpleGraph.Walk.rotate
      exact penultimate_append_of_right_not_nil _ p hpNonNil
    exact hpen.symm.trans (congrArg SimpleGraph.Walk.penultimate hrotate)

/-- Consecutive piece nodes in the auxiliary cycle determine a genuine
ambient vertex shared by their carriers. -/
theorem exists_successor_joint {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) :
    ∃ v : V,
      familyAuxRoot (c.rotate (.inr (.inl P.1))
        (mem_auxPiecesInWalk_iff.mp P.2)).snd = some v ∧
      familyAuxRoot (c.rotate
        (.inr (.inl (auxPieceSuccessor c hc P).1))
        (mem_auxPiecesInWalk_iff.mp (auxPieceSuccessor c hc P).2)).penultimate =
          some v ∧
      v ∈ P.1.1.1 ∧ v ∈ (auxPieceSuccessor c hc P).1.1.1 := by
  classical
  let Q := auxPieceSuccessor c hc P
  obtain ⟨p, hp, honly, hsnd, hpenEq⟩ :=
    exists_piece_free_successor_arc c hc hcodd P
  have hPQ : P.1 ≠ Q.1 := by
    intro h
    exact auxPieceSuccessor_ne c hc hcodd P (Subtype.ext h.symm)
  obtain ⟨v, hroot, hpen, hvP, hvQ⟩ :=
    exists_rooted_shared_vertex_of_piece_free_auxPath D P.1 Q.1 hPQ p hp honly
  refine ⟨v, ?_, ?_, hvP, hvQ⟩
  · simpa [hsnd] using hroot
  · simpa [hpenEq] using hpen

/-- Canonical ambient joint between a piece and its cyclic successor. -/
noncomputable def auxPieceJoint {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) : V :=
  Classical.choose (exists_successor_joint c hc hcodd P)

lemma auxPieceJoint_root_snd {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) :
    familyAuxRoot (c.rotate (.inr (.inl P.1))
      (mem_auxPiecesInWalk_iff.mp P.2)).snd = some (auxPieceJoint c hc hcodd P) :=
  (Classical.choose_spec (exists_successor_joint c hc hcodd P)).1

lemma auxPieceJoint_root_penultimate {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) :
    familyAuxRoot (c.rotate
      (.inr (.inl (auxPieceSuccessor c hc P).1))
      (mem_auxPiecesInWalk_iff.mp (auxPieceSuccessor c hc P).2)).penultimate =
        some (auxPieceJoint c hc hcodd P) :=
  (Classical.choose_spec (exists_successor_joint c hc hcodd P)).2.1

lemma auxPieceJoint_mem_left {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) :
    auxPieceJoint c hc hcodd P ∈ P.1.1.1 :=
  (Classical.choose_spec (exists_successor_joint c hc hcodd P)).2.2.1

lemma auxPieceJoint_mem_right {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) :
    auxPieceJoint c hc hcodd P ∈ (auxPieceSuccessor c hc P).1.1.1 :=
  (Classical.choose_spec (exists_successor_joint c hc hcodd P)).2.2.2

/-- For a fixed piece, an adjacent auxiliary vertex is uniquely determined
by its ambient root. -/
lemma familyAuxNeighbor_eq_of_root {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    (D : (P : ↥A) → FlexiblePathData T P.1) (P : ↥A)
    {x y : FamilyAuxVertex V A} {v : V}
    (hx : (familyAuxGraph D).Adj (.inr (.inl P)) x)
    (hy : (familyAuxGraph D).Adj (.inr (.inl P)) y)
    (hrootx : familyAuxRoot x = some v)
    (hrooty : familyAuxRoot y = some v) : x = y := by
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          simp [familyAuxRoot] at hrootx hrooty
          subst a
          subst b
          rfl
      | inr q =>
          cases q with
          | inl Q => simp [familyAuxRoot] at hrooty
          | inr Qb =>
              rcases Qb with ⟨Q, b⟩
              have hx' := hx
              have hy' := hy
              simp only [reduceCtorEq] at hx' hy'
              simp only [reduceCtorEq] at hrootx hrooty
              subst a
              subst b
              have hQP : Q = P := hy'.1.symm
              subst Q
              exact (by simp_all : False).elim
  | inr p =>
      cases p with
      | inl Q => simp [familyAuxRoot] at hrootx
      | inr Qa =>
          rcases Qa with ⟨Q, a⟩
          cases y with
          | inl b =>
              have hx' := hx
              have hy' := hy
              simp only [reduceCtorEq] at hx' hy'
              simp only [reduceCtorEq] at hrootx hrooty
              subst a
              subst b
              have hQP : Q = P := hx'.1.symm
              subst Q
              exact (by simp_all : False).elim
          | inr q =>
              cases q with
              | inl R => simp [familyAuxRoot] at hrooty
              | inr Rb =>
                  rcases Rb with ⟨R, b⟩
                  have hx' := hx
                  have hy' := hy
                  simp only [Sum.inr.injEq, Prod.mk.injEq] at hx' hy'
                  simp [familyAuxRoot] at hrootx hrooty
                  subst a
                  subst b
                  have hQP : Q = P := hx'.1.symm
                  have hRP : R = P := hy'.1.symm
                  subst Q
                  subst R
                  rfl

/-- The two joints incident with `P`, in the orientation of the auxiliary
cycle. -/
noncomputable def auxPieceLeft {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) : V :=
  auxPieceJoint c hc hcodd (auxPiecePredecessor c hc P)

noncomputable def auxPieceRight {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) : V :=
  auxPieceJoint c hc hcodd P

lemma auxPieceLeft_mem {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) : auxPieceLeft c hc hcodd P ∈ P.1.1.1 := by
  unfold auxPieceLeft
  have h := auxPieceJoint_mem_right c hc hcodd (auxPiecePredecessor c hc P)
  simpa using h

lemma auxPieceRight_mem {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) : auxPieceRight c hc hcodd P ∈ P.1.1.1 :=
  auxPieceJoint_mem_left c hc hcodd P

/-- The outgoing joint of one piece is literally the incoming joint of its
cyclic successor. -/
lemma auxPieceRight_eq_left_successor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) :
    auxPieceRight c hc hcodd P =
      auxPieceLeft c hc hcodd (auxPieceSuccessor c hc P) := by
  unfold auxPieceRight auxPieceLeft
  rw [auxPiecePredecessor_successor]

/-- Canonical lower-path endpoints chain along every rotation of the piece
order. -/
lemma auxPieceOrderSubtype_rotate_isChain {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (n : ℕ) :
    (auxPieceOrderSubtype c hc).rotate n |>.IsChain
      (fun P Q => auxPieceRight c hc hcodd P =
        auxPieceLeft c hc hcodd Q) := by
  apply list_rotate_isChain_of_rel_next _ (auxPieceOrderSubtype c hc)
    (auxPieceOrderSubtype_nodup c hc)
  intro P hP
  have hnext := auxPieceOrderSubtype_next_eq_successor c hc P
  have h := auxPieceRight_eq_left_successor c hc hcodd P
  rw [← hnext] at h
  exact h

/-- The successor arc of `P` has parity equal to the sum of the two colour
bits at the common joint.  This is the local parity invariant used when all
successor arcs are added around the auxiliary cycle. -/
theorem exists_successor_arc_with_parity {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) :
    let Q := auxPieceSuccessor c hc P
    ∃ p : (familyAuxGraph D).Walk (.inr (.inl P.1)) (.inr (.inl Q.1)),
      p.IsPath ∧
      (∀ R ∈ auxPiecesInWalk p, R = P.1 ∨ R = Q.1) ∧
      p.length % 2 =
        (((D P.1).color (auxPieceRight c hc hcodd P)).val +
          ((D Q.1).color (auxPieceLeft c hc hcodd Q)).val) % 2 := by
  classical
  dsimp only
  let Q := auxPieceSuccessor c hc P
  obtain ⟨p, hp, honly, hsnd, _hpen⟩ :=
    exists_piece_free_successor_arc c hc hcodd P
  refine ⟨p, hp, honly, ?_⟩
  have hPQ : P.1 ≠ Q.1 := by
    intro h
    exact auxPieceSuccessor_ne c hc hcodd P (Subtype.ext h.symm)
  have honly' : ∀ R : ↥A,
      (.inr (.inl R) : FamilyAuxVertex V A) ∈ p.support →
        R = P.1 ∨ R = Q.1 := by
    intro R hR
    exact honly R (mem_auxPiecesInWalk_iff.mpr hR)
  have hroot : familyAuxRoot p.snd =
      some (auxPieceJoint c hc hcodd P) := by
    rw [hsnd]
    exact auxPieceJoint_root_snd c hc hcodd P
  have hparity := piece_free_auxPath_length_mod_two D P.1 Q.1 hPQ p hp
    honly' hroot
  simpa [auxPieceRight, auxPieceLeft, Q] using hparity

/-- The oriented dart leaving a piece node on the auxiliary cycle. -/
noncomputable def auxPieceOutgoingDart {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (P : ↥(auxPiecesInWalk c)) : (familyAuxGraph D).Dart :=
  let pnode : FamilyAuxVertex V A := .inr (.inl P.1)
  let hpnode : pnode ∈ c.support := mem_auxPiecesInWalk_iff.mp P.2
  let cr := c.rotate pnode hpnode
  cr.firstDart (hc.rotate hpnode).not_nil

/-- The oriented dart entering a piece node on the auxiliary cycle. -/
noncomputable def auxPieceIncomingDart {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (P : ↥(auxPiecesInWalk c)) : (familyAuxGraph D).Dart :=
  let pnode : FamilyAuxVertex V A := .inr (.inl P.1)
  let hpnode : pnode ∈ c.support := mem_auxPiecesInWalk_iff.mp P.2
  let cr := c.rotate pnode hpnode
  cr.lastDart (hc.rotate hpnode).not_nil

@[simp] lemma auxPieceOutgoingDart_fst {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (P : ↥(auxPiecesInWalk c)) :
    (auxPieceOutgoingDart c hc P).fst = .inr (.inl P.1) := by
  rfl

@[simp] lemma auxPieceOutgoingDart_snd {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (P : ↥(auxPiecesInWalk c)) :
    (auxPieceOutgoingDart c hc P).snd =
      (c.rotate (.inr (.inl P.1))
        (mem_auxPiecesInWalk_iff.mp P.2)).snd := by
  rfl

@[simp] lemma auxPieceIncomingDart_fst {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (P : ↥(auxPiecesInWalk c)) :
    (auxPieceIncomingDart c hc P).fst =
      (c.rotate (.inr (.inl P.1))
        (mem_auxPiecesInWalk_iff.mp P.2)).penultimate := by
  rfl

@[simp] lemma auxPieceIncomingDart_snd {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (P : ↥(auxPiecesInWalk c)) :
    (auxPieceIncomingDart c hc P).snd = .inr (.inl P.1) := by
  rfl

lemma auxPieceOutgoingDart_mem {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (P : ↥(auxPiecesInWalk c)) :
    auxPieceOutgoingDart c hc P ∈ c.darts := by
  let pnode : FamilyAuxVertex V A := .inr (.inl P.1)
  have hpnode : pnode ∈ c.support := mem_auxPiecesInWalk_iff.mp P.2
  let cr := c.rotate pnode hpnode
  have hm : auxPieceOutgoingDart c hc P ∈ cr.darts := by
    exact cr.firstDart_mem_darts (hc.rotate hpnode).not_nil
  exact (c.rotate_darts pnode hpnode).mem_iff.mp hm

lemma auxPieceIncomingDart_mem {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (P : ↥(auxPiecesInWalk c)) :
    auxPieceIncomingDart c hc P ∈ c.darts := by
  let pnode : FamilyAuxVertex V A := .inr (.inl P.1)
  have hpnode : pnode ∈ c.support := mem_auxPiecesInWalk_iff.mp P.2
  let cr := c.rotate pnode hpnode
  have hm : auxPieceIncomingDart c hc P ∈ cr.darts := by
    exact cr.lastDart_mem_darts (hc.rotate hpnode).not_nil
  exact (c.rotate_darts pnode hpnode).mem_iff.mp hm

/-- The two directed colour-zero incidences at a piece node add to that
piece's required path residue. -/
lemma piece_incidence_bits_eq_residue {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) :
    let pnode : FamilyAuxVertex V A := .inr (.inl P.1)
    let cr := c.rotate pnode (mem_auxPiecesInWalk_iff.mp P.2)
    familyAuxZeroIncidence D pnode cr.snd +
        familyAuxZeroIncidence D pnode cr.penultimate =
      ((D P.1).residue (auxPieceRight c hc hcodd P)
        (auxPieceLeft c hc hcodd P) : ZMod 2) := by
  classical
  dsimp only
  let pnode : FamilyAuxVertex V A := .inr (.inl P.1)
  have hpnode : pnode ∈ c.support := mem_auxPiecesInWalk_iff.mp P.2
  let cr := c.rotate pnode hpnode
  have hsnd : familyAuxRoot cr.snd =
      some (auxPieceRight c hc hcodd P) := auxPieceJoint_root_snd c hc hcodd P
  have hpen : familyAuxRoot cr.penultimate =
      some (auxPieceLeft c hc hcodd P) := by
    unfold auxPieceLeft
    have h := auxPieceJoint_root_penultimate c hc hcodd
      (auxPiecePredecessor c hc P)
    rw [auxPieceSuccessor_predecessor] at h
    simpa [cr, pnode] using h
  simp only [familyAuxZeroIncidence]
  rw [hsnd, hpen]
  rcases fin_two_eq_zero_or_one
      ((D P.1).color (auxPieceRight c hc hcodd P)) with hR | hR <;>
    rcases fin_two_eq_zero_or_one
      ((D P.1).color (auxPieceLeft c hc hcodd P)) with hL | hL <;>
    simp only [Fin.isValue] <;> decide

/-- Double-counting the directed darts of a simple auxiliary cycle groups
its incidence sum into the two incidences at each piece node. -/
lemma familyAuxZeroSum_eq_sum_piece_residue {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) :
    familyAuxZeroSum D c =
      ∑ P : ↥(auxPiecesInWalk c),
        ((D P.1).residue (auxPieceRight c hc hcodd P)
          (auxPieceLeft c hc hcodd P) : ZMod 2) := by
  classical
  let darts : Finset (familyAuxGraph D).Dart := c.darts.toFinset
  let outDarts : Finset (familyAuxGraph D).Dart := darts.filter fun d =>
    ∃ P : ↥A, d.fst = (.inr (.inl P) : FamilyAuxVertex V A)
  let inDarts : Finset (familyAuxGraph D).Dart := darts.filter fun d =>
    ∃ P : ↥A, d.snd = (.inr (.inl P) : FamilyAuxVertex V A)
  let outTerm : (familyAuxGraph D).Dart → ZMod 2 := fun d =>
    familyAuxZeroIncidence D d.fst d.snd
  let inTerm : (familyAuxGraph D).Dart → ZMod 2 := fun d =>
    familyAuxZeroIncidence D d.snd d.fst
  have hdarts : c.darts.Nodup := by
    apply List.Nodup.of_map (fun d : (familyAuxGraph D).Dart => d.fst)
    rw [c.map_fst_darts]
    exact hc.nodup_dropLast_support
  have houtSupport :
      (∑ d ∈ darts, outTerm d) = ∑ d ∈ outDarts, outTerm d := by
    symm
    apply Finset.sum_subset (by
      intro d hd
      exact (Finset.mem_filter.mp hd).1)
    intro d hd hdo
    have hnot : ¬∃ P : ↥A,
        d.fst = (.inr (.inl P) : FamilyAuxVertex V A) := by
      intro h
      apply hdo
      exact Finset.mem_filter.mpr ⟨hd, h⟩
    cases hfst : d.fst with
    | inl v => simp [outTerm, familyAuxZeroIncidence, hfst]
    | inr q =>
        cases q with
        | inl P => exact (hnot ⟨P, hfst⟩).elim
        | inr Pv => simp [outTerm, familyAuxZeroIncidence, hfst]
  have hinSupport :
      (∑ d ∈ darts, inTerm d) = ∑ d ∈ inDarts, inTerm d := by
    symm
    apply Finset.sum_subset (by
      intro d hd
      exact (Finset.mem_filter.mp hd).1)
    intro d hd hdi
    have hnot : ¬∃ P : ↥A,
        d.snd = (.inr (.inl P) : FamilyAuxVertex V A) := by
      intro h
      apply hdi
      exact Finset.mem_filter.mpr ⟨hd, h⟩
    cases hsnd : d.snd with
    | inl v => simp [inTerm, familyAuxZeroIncidence, hsnd]
    | inr q =>
        cases q with
        | inl P => exact (hnot ⟨P, hsnd⟩).elim
        | inr Pv => simp [inTerm, familyAuxZeroIncidence, hsnd]
  have houtBijection :
      (∑ d ∈ outDarts, outTerm d) =
        ∑ P : ↥(auxPiecesInWalk c), outTerm (auxPieceOutgoingDart c hc P) := by
    symm
    apply Finset.sum_bij (fun P _ => auxPieceOutgoingDart c hc P)
    · intro P _
      apply Finset.mem_filter.mpr
      refine ⟨?_, ⟨P.1, by simp⟩⟩
      simpa [darts] using auxPieceOutgoingDart_mem c hc P
    · intro P _ Q _ hPQ
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun d : (familyAuxGraph D).Dart => d.fst) hPQ
      simpa using this
    · intro d hd
      have hdDarts : d ∈ c.darts := by
        simpa [darts] using (Finset.mem_filter.mp hd).1
      obtain ⟨R, hR⟩ := (Finset.mem_filter.mp hd).2
      have hRsupport :
          (.inr (.inl R) : FamilyAuxVertex V A) ∈ c.support := by
        rw [← hR]
        exact c.dart_fst_mem_support_of_mem_darts hdDarts
      let P : ↥(auxPiecesInWalk c) :=
        ⟨R, mem_auxPiecesInWalk_iff.mpr hRsupport⟩
      refine ⟨P, Finset.mem_univ P, ?_⟩
      apply cycle_dart_eq_of_fst_eq hc
        (auxPieceOutgoingDart_mem c hc P) hdDarts
      simpa [P] using hR.symm
    · intro P _
      rfl
  have hinBijection :
      (∑ d ∈ inDarts, inTerm d) =
        ∑ P : ↥(auxPiecesInWalk c), inTerm (auxPieceIncomingDart c hc P) := by
    symm
    apply Finset.sum_bij (fun P _ => auxPieceIncomingDart c hc P)
    · intro P _
      apply Finset.mem_filter.mpr
      refine ⟨?_, ⟨P.1, by simp⟩⟩
      simpa [darts] using auxPieceIncomingDart_mem c hc P
    · intro P _ Q _ hPQ
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun d : (familyAuxGraph D).Dart => d.snd) hPQ
      simpa using this
    · intro d hd
      have hdDarts : d ∈ c.darts := by
        simpa [darts] using (Finset.mem_filter.mp hd).1
      obtain ⟨R, hR⟩ := (Finset.mem_filter.mp hd).2
      have hRsupport :
          (.inr (.inl R) : FamilyAuxVertex V A) ∈ c.support := by
        rw [← hR]
        exact c.dart_snd_mem_support_of_mem_darts hdDarts
      let P : ↥(auxPiecesInWalk c) :=
        ⟨R, mem_auxPiecesInWalk_iff.mpr hRsupport⟩
      refine ⟨P, Finset.mem_univ P, ?_⟩
      apply cycle_dart_eq_of_snd_eq hc
        (auxPieceIncomingDart_mem c hc P) hdDarts
      simpa [P] using hR.symm
    · intro P _
      rfl
  calc
    familyAuxZeroSum D c =
        (∑ d ∈ darts, outTerm d) + ∑ d ∈ darts, inTerm d := by
      unfold familyAuxZeroSum
      rw [← List.sum_toFinset
        (fun d : (familyAuxGraph D).Dart => outTerm d + inTerm d) hdarts]
      exact Finset.sum_add_distrib
    _ = (∑ d ∈ outDarts, outTerm d) + ∑ d ∈ inDarts, inTerm d := by
      rw [houtSupport, hinSupport]
    _ = (∑ P : ↥(auxPiecesInWalk c),
          outTerm (auxPieceOutgoingDart c hc P)) +
        ∑ P : ↥(auxPiecesInWalk c),
          inTerm (auxPieceIncomingDart c hc P) := by
      rw [houtBijection, hinBijection]
    _ = ∑ P : ↥(auxPiecesInWalk c),
        (outTerm (auxPieceOutgoingDart c hc P) +
          inTerm (auxPieceIncomingDart c hc P)) := Finset.sum_add_distrib.symm
    _ = ∑ P : ↥(auxPiecesInWalk c),
        ((D P.1).residue (auxPieceRight c hc hcodd P)
          (auxPieceLeft c hc hcodd P) : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro P _
      simpa [outTerm, inTerm] using piece_incidence_bits_eq_residue c hc hcodd P

/-- The lower parity-adjusted lengths of all pieces on an odd auxiliary
cycle have odd total. -/
lemma odd_sum_parityStart_auxPieces {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) :
    Odd (∑ P : ↥(auxPiecesInWalk c),
      parityStart (D P.1).base
        ((D P.1).residue (auxPieceLeft c hc hcodd P)
          (auxPieceRight c hc hcodd P))) := by
  let L := ∑ P : ↥(auxPiecesInWalk c),
    parityStart (D P.1).base
      ((D P.1).residue (auxPieceLeft c hc hcodd P)
        (auxPieceRight c hc hcodd P))
  have hresidue :
      (∑ P : ↥(auxPiecesInWalk c),
        ((D P.1).residue (auxPieceLeft c hc hcodd P)
          (auxPieceRight c hc hcodd P) : ZMod 2)) = 1 := by
    calc
      (∑ P : ↥(auxPiecesInWalk c),
          ((D P.1).residue (auxPieceLeft c hc hcodd P)
            (auxPieceRight c hc hcodd P) : ZMod 2)) =
          ∑ P : ↥(auxPiecesInWalk c),
            ((D P.1).residue (auxPieceRight c hc hcodd P)
              (auxPieceLeft c hc hcodd P) : ZMod 2) := by
        apply Finset.sum_congr rfl
        intro P _
        rw [(D P.1).residue_comm]
      _ = familyAuxZeroSum D c :=
        (familyAuxZeroSum_eq_sum_piece_residue c hc hcodd).symm
      _ = 1 := familyAux_cycle_zeroSum_eq_one_of_odd D c hcodd
  have hterm (P : ↥(auxPiecesInWalk c)) :
      (parityStart (D P.1).base
        ((D P.1).residue (auxPieceLeft c hc hcodd P)
          (auxPieceRight c hc hcodd P)) : ZMod 2) =
      ((D P.1).residue (auxPieceLeft c hc hcodd P)
        (auxPieceRight c hc hcodd P) : ZMod 2) := by
    let r := (D P.1).residue (auxPieceLeft c hc hcodd P)
      (auxPieceRight c hc hcodd P)
    calc
      (parityStart (D P.1).base r : ZMod 2) =
          ((parityStart (D P.1).base r % 2 : ℕ) : ZMod 2) :=
        (ZMod.natCast_mod (parityStart (D P.1).base r) 2).symm
      _ = (r : ZMod 2) := by
        rw [parityStart_mod_two ((D P.1).residue_lt_two
          (auxPieceLeft c hc hcodd P) (auxPieceRight c hc hcodd P))]
  apply odd_of_zmod_two_natCast_eq_one
  change (L : ZMod 2) = 1
  calc
    (L : ZMod 2) = ∑ P : ↥(auxPiecesInWalk c),
        (parityStart (D P.1).base
          ((D P.1).residue (auxPieceLeft c hc hcodd P)
            (auxPieceRight c hc hcodd P)) : ZMod 2) := by
      simp [L]
    _ = ∑ P : ↥(auxPiecesInWalk c),
        ((D P.1).residue (auxPieceLeft c hc hcodd P)
          (auxPieceRight c hc hcodd P) : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro P _
      exact hterm P
    _ = 1 := hresidue

/-- Regrouping the two incidences at every piece is the same, modulo two,
as grouping the two incidences along every successor arc. -/
lemma sum_piece_residue_eq_sum_successor_bits {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) :
    (∑ P : ↥(auxPiecesInWalk c),
        ((D P.1).residue (auxPieceLeft c hc hcodd P)
          (auxPieceRight c hc hcodd P) : ZMod 2)) =
      ∑ P : ↥(auxPiecesInWalk c), (
        (((D P.1).color (auxPieceRight c hc hcodd P)).val : ZMod 2) +
          (((D (auxPieceSuccessor (D := D) c hc P).1).color
            (auxPieceLeft (D := D) c hc hcodd
              (auxPieceSuccessor (D := D) c hc P))).val : ZMod 2)) := by
  classical
  let succEquiv : ↥(auxPiecesInWalk c) ≃ ↥(auxPiecesInWalk c) :=
    Equiv.ofBijective (auxPieceSuccessor c hc)
      ⟨auxPieceSuccessor_injective c hc,
        (Finite.injective_iff_surjective.mp (auxPieceSuccessor_injective c hc))⟩
  let leftBit : ↥(auxPiecesInWalk c) → ZMod 2 := fun P =>
    ((D P.1).color (auxPieceLeft c hc hcodd P)).val
  let rightBit : ↥(auxPiecesInWalk c) → ZMod 2 := fun P =>
    ((D P.1).color (auxPieceRight c hc hcodd P)).val
  have hresidue (P : ↥(auxPiecesInWalk c)) :
      ((D P.1).residue (auxPieceLeft c hc hcodd P)
        (auxPieceRight c hc hcodd P) : ZMod 2) = leftBit P + rightBit P := by
    rcases fin_two_eq_zero_or_one
        ((D P.1).color (auxPieceLeft c hc hcodd P)) with hL | hL <;>
      rcases fin_two_eq_zero_or_one
        ((D P.1).color (auxPieceRight c hc hcodd P)) with hR | hR <;>
      simp [leftBit, rightBit, FlexiblePathData.residue, hL, hR] <;> decide
  have hsuccEquiv_apply (P : ↥(auxPiecesInWalk c)) :
      succEquiv P = auxPieceSuccessor c hc P := rfl
  have hleft :
      (∑ P : ↥(auxPiecesInWalk c), leftBit (auxPieceSuccessor c hc P)) =
        ∑ P : ↥(auxPiecesInWalk c), leftBit P := by
    simpa only [hsuccEquiv_apply] using succEquiv.sum_comp leftBit
  calc
    (∑ P : ↥(auxPiecesInWalk c),
        ((D P.1).residue (auxPieceLeft c hc hcodd P)
          (auxPieceRight c hc hcodd P) : ZMod 2)) =
        ∑ P : ↥(auxPiecesInWalk c), (leftBit P + rightBit P) := by
          apply Finset.sum_congr rfl
          intro P _
          exact hresidue P
    _ = (∑ P : ↥(auxPiecesInWalk c), leftBit P) +
        ∑ P : ↥(auxPiecesInWalk c), rightBit P := Finset.sum_add_distrib
    _ = (∑ P : ↥(auxPiecesInWalk c), rightBit P) +
        ∑ P : ↥(auxPiecesInWalk c), leftBit P := add_comm _ _
    _ = (∑ P : ↥(auxPiecesInWalk c), rightBit P) +
        ∑ P : ↥(auxPiecesInWalk c),
          leftBit (auxPieceSuccessor c hc P) := by rw [hleft]
    _ = ∑ P : ↥(auxPiecesInWalk c),
        (rightBit P + leftBit (auxPieceSuccessor c hc P)) :=
      Finset.sum_add_distrib.symm
    _ = ∑ P : ↥(auxPiecesInWalk c), (
        (((D P.1).color (auxPieceRight c hc hcodd P)).val : ZMod 2) +
          (((D (auxPieceSuccessor (D := D) c hc P).1).color
            (auxPieceLeft (D := D) c hc hcodd
              (auxPieceSuccessor (D := D) c hc P))).val : ZMod 2)) := by
      rfl

lemma auxPieceLeft_ne_right {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (P : ↥(auxPiecesInWalk c)) :
    auxPieceLeft c hc hcodd P ≠ auxPieceRight c hc hcodd P := by
  let pnode : FamilyAuxVertex V A := .inr (.inl P.1)
  have hpnode : pnode ∈ c.support := mem_auxPiecesInWalk_iff.mp P.2
  let cr := c.rotate pnode hpnode
  have hcycle : cr.IsCycle := hc.rotate hpnode
  have hsndRoot : familyAuxRoot cr.snd = some (auxPieceRight c hc hcodd P) := by
    exact auxPieceJoint_root_snd c hc hcodd P
  have hpenRoot : familyAuxRoot cr.penultimate = some (auxPieceLeft c hc hcodd P) := by
    unfold auxPieceLeft
    have h := auxPieceJoint_root_penultimate c hc hcodd
      (auxPiecePredecessor c hc P)
    have hsucc :
        auxPieceSuccessor c hc (auxPiecePredecessor c hc P) = P :=
      auxPieceSuccessor_predecessor c hc P
    rw [hsucc] at h
    simpa [cr, pnode] using h
  intro heq
  apply hcycle.snd_ne_penultimate
  apply familyAuxNeighbor_eq_of_root D P.1
  · exact cr.adj_snd hcycle.not_nil
  · exact (cr.adj_penultimate hcycle.not_nil).symm
  · exact hsndRoot
  · simpa [heq] using hpenRoot

/-! ### Three-colouring the carrier-overlap graph of a minimal piece cycle -/

/-- Two piece occurrences on an auxiliary cycle are adjacent when their
underlying carriers meet.  Distinctness is included explicitly to make this
an irreflexive graph. -/
noncomputable def auxPieceOverlapGraph {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z) :
    SimpleGraph ↥(auxPiecesInWalk c) where
  Adj P Q := P ≠ Q ∧ ∃ v : V, v ∈ P.1.1.1 ∧ v ∈ Q.1.1.1
  symm := ⟨by
    rintro P Q ⟨hPQ, v, hvP, hvQ⟩
    exact ⟨hPQ.symm, v, hvQ, hvP⟩⟩
  loopless := ⟨by
    intro P h
    exact h.1 rfl⟩

noncomputable instance auxPieceOverlapGraph_decidableRel
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z) :
    DecidableRel (auxPieceOverlapGraph c).Adj := by
  classical
  infer_instance

/-- Every piece on a minimum-piece odd auxiliary cycle overlaps at most two
other pieces of that cycle: at most one in each cyclic direction. -/
theorem auxPieceOverlapGraph_filtered_degree_le_two {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A}
    (c : (familyAuxGraph D).Walk z z) (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (P : ↥(auxPiecesInWalk c)) :
    ((Finset.univ : Finset ↥(auxPiecesInWalk c)).filter
      (fun Q ↦ (auxPieceOverlapGraph c).Adj P Q)).card ≤ 2 := by
  classical
  let pnode : FamilyAuxVertex V A := .inr (.inl P.1)
  have hpnode : pnode ∈ c.support := mem_auxPiecesInWalk_iff.mp P.2
  let cr := c.rotate pnode hpnode
  have hnode (Q : ↥(auxPiecesInWalk c)) :
      (.inr (.inl Q.1) : FamilyAuxVertex V A) ∈ cr.support := by
    apply (SimpleGraph.Walk.mem_support_rotate_iff c pnode hpnode).2
    exact mem_auxPiecesInWalk_iff.mp Q.2
  let Front : ↥(auxPiecesInWalk c) → Prop := fun Q ↦
    ∀ R ∈ auxPiecesInWalk
      (cr.takeUntil (.inr (.inl Q.1)) (hnode Q)), R = P.1 ∨ R = Q.1
  let Back : ↥(auxPiecesInWalk c) → Prop := fun Q ↦
    ∀ R ∈ auxPiecesInWalk
      (cr.dropUntil (.inr (.inl Q.1)) (hnode Q)), R = P.1 ∨ R = Q.1
  let direction : ↥(auxPiecesInWalk c) → Bool := fun Q ↦
    if Front Q then false else true
  let neighbors := (Finset.univ : Finset ↥(auxPiecesInWalk c)).filter
    (fun Q ↦ (auxPieceOverlapGraph c).Adj P Q)
  have hconsecutive (Q : ↥(auxPiecesInWalk c))
      (hQ : Q ∈ neighbors) : Front Q ∨ Back Q := by
    have hAdj : (auxPieceOverlapGraph c).Adj P Q := by
      simpa [neighbors] using (Finset.mem_filter.mp hQ).2
    obtain ⟨hPQ, v, hvP, hvQ⟩ := hAdj
    have hbase : P.1 ≠ Q.1 := by
      intro h
      apply hPQ
      exact Subtype.ext h
    have h := shared_vertex_consecutive_on_minimal_odd_cycle
      c hc hcodd hminimal P.1 Q.1 hbase P.2 Q.2 v hvP hvQ
    simpa only [Front, Back, cr, pnode, hpnode, hnode] using h
  have hinjective : Set.InjOn direction
      (↑neighbors : Set ↥(auxPiecesInWalk c)) := by
    intro Q hQ R hR hdir
    have hAdjQ : (auxPieceOverlapGraph c).Adj P Q := by
      simpa [neighbors] using (Finset.mem_filter.mp hQ).2
    have hAdjR : (auxPieceOverlapGraph c).Adj P R := by
      simpa [neighbors] using (Finset.mem_filter.mp hR).2
    have hQP : Q.1 ≠ P.1 := by
      intro h
      exact hAdjQ.1 (Subtype.ext h.symm)
    have hRP : R.1 ≠ P.1 := by
      intro h
      exact hAdjR.1 (Subtype.ext h.symm)
    have hQcr : Q.1 ∈ auxPiecesInWalk cr := by
      rw [auxPiecesInWalk_rotate c hpnode]
      exact Q.2
    have hRcr : R.1 ∈ auxPiecesInWalk cr := by
      rw [auxPiecesInWalk_rotate c hpnode]
      exact R.2
    by_cases hQfront : Front Q
    · have hRfront : Front R := by
        by_contra hRfront
        have : direction Q ≠ direction R := by
          simp [direction, hQfront, hRfront]
        exact this hdir
      apply Subtype.ext
      exact unique_piece_with_piece_free_takeUntil cr P.1 Q.1 R.1 rfl
        hQP hRP hQcr hRcr hQfront hRfront
    · have hQback : Back Q := (hconsecutive Q hQ).resolve_left hQfront
      have hRfrontNot : ¬Front R := by
        intro hRfront
        have : direction Q ≠ direction R := by
          simp [direction, hQfront, hRfront]
        exact this hdir
      have hRback : Back R := (hconsecutive R hR).resolve_left hRfrontNot
      apply Subtype.ext
      exact unique_piece_with_piece_free_dropUntil cr P.1 Q.1 R.1 rfl
        hQP hRP hQcr hRcr hQback hRback
  have hmaps : Set.MapsTo direction
      (↑neighbors : Set ↥(auxPiecesInWalk c))
      (↑(Finset.univ : Finset Bool) : Set Bool) := by
    intro Q hQ
    simp
  have hcard := Finset.card_le_card_of_injOn direction hmaps hinjective
  simpa [neighbors] using hcard

/-- Once the predecessor and successor of a piece are distinct, minimality
forces every other carrier meeting that piece to be one of those two cyclic
neighbors. -/
theorem overlapping_piece_eq_predecessor_or_successor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A}
    (c : (familyAuxGraph D).Walk z z) (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (P Q : ↥(auxPiecesInWalk c))
    (hneighbors : auxPiecePredecessor c hc P ≠ auxPieceSuccessor c hc P)
    (hQP : Q ≠ P) (v : V) (hvQ : v ∈ Q.1.1.1) (hvP : v ∈ P.1.1.1) :
    Q = auxPiecePredecessor c hc P ∨ Q = auxPieceSuccessor c hc P := by
  classical
  let N := (Finset.univ : Finset ↥(auxPiecesInWalk c)).filter
    (fun R => (auxPieceOverlapGraph c).Adj P R)
  have hcard : N.card ≤ 2 := by
    exact auxPieceOverlapGraph_filtered_degree_le_two c hc hcodd hminimal P
  have hprev : auxPiecePredecessor c hc P ∈ N := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hadj : (auxPieceOverlapGraph c).Adj (auxPiecePredecessor c hc P) P := by
      refine ⟨(by simpa using
          (auxPieceSuccessor_ne c hc hcodd (auxPiecePredecessor c hc P)).symm),
      auxPieceJoint c hc hcodd (auxPiecePredecessor c hc P),
      auxPieceJoint_mem_left c hc hcodd (auxPiecePredecessor c hc P), ?_⟩
      simpa using auxPieceJoint_mem_right c hc hcodd (auxPiecePredecessor c hc P)
    exact hadj.symm
  have hsucc : auxPieceSuccessor c hc P ∈ N := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨(auxPieceSuccessor_ne c hc hcodd P).symm,
      auxPieceJoint c hc hcodd P,
      auxPieceJoint_mem_left c hc hcodd P,
      auxPieceJoint_mem_right c hc hcodd P⟩
  have hQ : Q ∈ N := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hQP.symm, v, hvP, hvQ⟩
  exact finset_mem_eq_of_card_le_two N hcard hprev hsucc hneighbors hQ

/-- The carrier-overlap graph of the minimal auxiliary odd cycle admits a
proper three-colouring. -/
theorem auxPieceOverlapGraph_colorable_three {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A}
    (c : (familyAuxGraph D).Walk z z) (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card) :
    (auxPieceOverlapGraph c).Colorable 3 := by
  classical
  apply Erdos760.SimpleGraph.colorable_of_degenerate
    (auxPieceOverlapGraph c) 3 (by omega)
  intro S hS
  obtain ⟨P, hPS⟩ := hS
  refine ⟨P, hPS, ?_⟩
  calc
    (S.filter (fun Q ↦ (auxPieceOverlapGraph c).Adj P Q)).card ≤
        ((Finset.univ : Finset ↥(auxPiecesInWalk c)).filter
          (fun Q ↦ (auxPieceOverlapGraph c).Adj P Q)).card := by
      apply Finset.card_le_card
      intro Q hQ
      rw [Finset.mem_filter] at hQ ⊢
      exact ⟨Finset.mem_univ Q, hQ.2⟩
    _ ≤ 2 := auxPieceOverlapGraph_filtered_degree_le_two
      c hc hcodd hminimal P
    _ < 3 := by omega

/-- Weighted pigeonhole principle for three colours. -/
lemma exists_fin_three_large_weight_fiber {I : Type*} [DecidableEq I]
    (s : Finset I) (color : I → Fin 3) (weight : I → ℕ) :
    ∃ i : Fin 3,
      (∑ x ∈ s, weight x) ≤
        3 * ∑ x ∈ s with color x = i, weight x := by
  classical
  let W : Fin 3 → ℕ := fun i ↦ ∑ x ∈ s with color x = i, weight x
  have hpartition : ∑ x ∈ s, weight x = W 0 + W 1 + W 2 := by
    have hfiber := Finset.sum_fiberwise s color weight
    have hexpand : (∑ i : Fin 3, W i) = W 0 + W 1 + W 2 := by
      simp [Fin.sum_univ_succ, add_assoc]
    rw [← hfiber, hexpand]
  by_cases h0 : (∑ x ∈ s, weight x) ≤ 3 * W 0
  · exact ⟨0, by simpa [W] using h0⟩
  by_cases h1 : (∑ x ∈ s, weight x) ≤ 3 * W 1
  · exact ⟨1, by simpa [W] using h1⟩
  refine ⟨2, ?_⟩
  have h2 : (∑ x ∈ s, weight x) ≤ 3 * W 2 := by omega
  simpa [W] using h2

/-- A maximum-weight colour class contains at least one third of the total
base weight and its piece carriers are pairwise disjoint. -/
theorem exists_weighted_carrier_disjoint_piece_class {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A}
    (c : (familyAuxGraph D).Walk z z) (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card) :
    ∃ S : Finset ↥(auxPiecesInWalk c),
      S.Nonempty ∧
      (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
        (fun P Q ↦ Disjoint P.1.1.1 Q.1.1.1) ∧
      (∑ P : ↥(auxPiecesInWalk c), ((D P.1).base + 1)) ≤
        3 * ∑ P ∈ S, ((D P.1).base + 1) := by
  classical
  let coloring : (auxPieceOverlapGraph c).Coloring (Fin 3) :=
    Classical.choice (auxPieceOverlapGraph_colorable_three c hc hcodd hminimal)
  obtain ⟨i, hi⟩ := exists_fin_three_large_weight_fiber
    (Finset.univ : Finset ↥(auxPiecesInWalk c)) coloring
    (fun P ↦ (D P.1).base + 1)
  let S := (Finset.univ : Finset ↥(auxPiecesInWalk c)).filter
    (fun P ↦ coloring P = i)
  have hweight :
      (∑ P : ↥(auxPiecesInWalk c), ((D P.1).base + 1)) ≤
        3 * ∑ P ∈ S, ((D P.1).base + 1) := by
    simpa [S] using hi
  have htotalPos : 0 <
      ∑ P : ↥(auxPiecesInWalk c), ((D P.1).base + 1) := by
    obtain ⟨P, hP⟩ := auxPiecesInWalk_nonempty_of_odd c hcodd
    let P' : ↥(auxPiecesInWalk c) := ⟨P, hP⟩
    have hterm : 0 < (D P'.1).base + 1 := by omega
    exact hterm.trans_le (Finset.single_le_sum
      (s := (Finset.univ : Finset ↥(auxPiecesInWalk c)))
      (f := fun Q ↦ (D Q.1).base + 1)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ P'))
  have hSnonempty : S.Nonempty := by
    by_contra hS
    rw [Finset.not_nonempty_iff_eq_empty] at hS
    have hsumZero : ∑ P ∈ S, ((D P.1).base + 1) = 0 := by
      rw [hS]
      simp
    have hzero := hweight
    rw [hsumZero] at hzero
    omega
  refine ⟨S, hSnonempty, ?_, hweight⟩
  intro P hPS Q hQS hPQ
  apply Finset.disjoint_left.mpr
  intro v hvP hvQ
  have hAdj : (auxPieceOverlapGraph c).Adj P Q :=
    ⟨hPQ, v, hvP, hvQ⟩
  have hne := coloring.valid hAdj
  have hPi : coloring P = i := (Finset.mem_filter.mp hPS).2
  have hQi : coloring Q = i := (Finset.mem_filter.mp hQS).2
  exact hne (hPi.trans hQi.symm)

/-- Two carrier-disjoint selected pieces force the auxiliary cycle to use
at least three pieces.  With at most two pieces, the cyclic successor of one
of them would have to be the other selected piece, although consecutive
piece carriers meet at their canonical joint. -/
lemma three_le_auxPiecesInWalk_card_of_two_selected
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hScard : 2 ≤ S.card)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1)) :
    3 ≤ (auxPiecesInWalk c).card := by
  classical
  by_contra hcard
  have hle : (auxPiecesInWalk c).card ≤ 2 := by omega
  obtain ⟨P, Q, hPS, hQS, hPQ⟩ :=
    Finset.one_lt_card_iff.mp (show 1 < S.card by omega)
  let P' : ↥(auxPiecesInWalk c) := ⟨P.1, P.2⟩
  let Q' : ↥(auxPiecesInWalk c) := ⟨Q.1, Q.2⟩
  have hP'Q' : P' ≠ Q' := by
    intro h
    exact hPQ (Subtype.ext (congrArg Subtype.val h))
  have hleUniv : (Finset.univ : Finset ↥(auxPiecesInWalk c)).card ≤ 2 := by
    simpa using hle
  have hcases := finset_mem_eq_of_card_le_two
    (Finset.univ : Finset ↥(auxPiecesInWalk c)) hleUniv
    (Finset.mem_univ P') (Finset.mem_univ Q') hP'Q'
    (Finset.mem_univ (auxPieceSuccessor c hc P'))
  rcases hcases with hself | hother
  · exact (auxPieceSuccessor_ne c hc hcodd P') hself
  · have hd : Disjoint P'.1.1.1 Q'.1.1.1 := by
      exact hpair hPS hQS hP'Q'
    exact (Finset.disjoint_left.mp hd)
      (auxPieceJoint_mem_left c hc hcodd P')
      (by simpa [hother] using auxPieceJoint_mem_right c hc hcodd P')

/-- A carrier-disjoint selected class cannot contain two cyclically
consecutive pieces: their canonical joint belongs to both carriers. -/
lemma auxPieceSuccessor_not_mem_selected {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c))
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥(auxPiecesInWalk c)) (hPS : P ∈ S) :
    auxPieceSuccessor c hc P ∉ S := by
  intro hQS
  have hdisj := hpair hPS hQS (auxPieceSuccessor_ne c hc hcodd P).symm
  exact (Finset.disjoint_left.mp hdisj)
    (auxPieceJoint_mem_left c hc hcodd P)
    (auxPieceJoint_mem_right c hc hcodd P)

/-! ### Grouping the complementary runs between selected pieces -/

noncomputable def auxSelectedAnchor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty) :
    ↥(auxPiecesInWalk c) := hS.choose

@[simp] lemma auxSelectedAnchor_mem {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty) :
    auxSelectedAnchor c S hS ∈ S := hS.choose_spec

/-- Rotate the complete cyclic piece order so that it begins at a selected
piece. -/
noncomputable def auxRotatedPieceOrder {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) : List ↥(auxPiecesInWalk c) :=
  listRotateTo (auxPieceOrderSubtype c hc) (auxSelectedAnchor c S hS)

lemma auxRotatedPieceOrder_ne_nil {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) : auxRotatedPieceOrder c hc S hS ≠ [] := by
  apply listRotateTo_ne_nil
  exact mem_auxPieceOrderSubtype_iff c hc (auxSelectedAnchor c S hS)

lemma auxRotatedPieceOrder_head_mem {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) :
    (auxRotatedPieceOrder c hc S hS).head
      (auxRotatedPieceOrder_ne_nil c hc S hS) ∈ S := by
  have hhead := listRotateTo_head (auxPieceOrderSubtype c hc)
    (auxSelectedAnchor c S hS)
    (mem_auxPieceOrderSubtype_iff c hc (auxSelectedAnchor c S hS))
  have heq : (auxRotatedPieceOrder c hc S hS).head
      (auxRotatedPieceOrder_ne_nil c hc S hS) =
        auxSelectedAnchor c S hS := by
    simpa [auxRotatedPieceOrder] using hhead
  rw [heq]
  exact auxSelectedAnchor_mem c S hS

lemma auxRotatedPieceOrder_nodup {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) : (auxRotatedPieceOrder c hc S hS).Nodup := by
  have hrot : auxPieceOrderSubtype c hc ~r
      auxRotatedPieceOrder c hc S hS := by
    unfold auxRotatedPieceOrder listRotateTo
    exact ⟨_, rfl⟩
  exact hrot.nodup_iff.mp (auxPieceOrderSubtype_nodup c hc)

lemma auxRotatedPieceOrder_next_eq_successor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (P : ↥(auxPiecesInWalk c))
    (hP : P ∈ auxRotatedPieceOrder c hc S hS) :
    (auxRotatedPieceOrder c hc S hS).next P hP =
      auxPieceSuccessor c hc P := by
  have hrot : auxPieceOrderSubtype c hc ~r
      auxRotatedPieceOrder c hc S hS := by
    unfold auxRotatedPieceOrder listRotateTo
    exact ⟨_, rfl⟩
  have hPl : P ∈ auxPieceOrderSubtype c hc := mem_auxPieceOrderSubtype_iff c hc P
  exact (List.isRotated_next_eq hrot (auxPieceOrderSubtype_nodup c hc) hPl).symm.trans
    (auxPieceOrderSubtype_next_eq_successor c hc P)

lemma mem_auxRotatedPieceOrder {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (P : ↥(auxPiecesInWalk c)) :
    P ∈ auxRotatedPieceOrder c hc S hS := by
  have hrot : auxPieceOrderSubtype c hc ~r
      auxRotatedPieceOrder c hc S hS := by
    unfold auxRotatedPieceOrder listRotateTo
    exact ⟨_, rfl⟩
  exact hrot.mem_iff.mp (mem_auxPieceOrderSubtype_iff c hc P)

noncomputable def auxPieceGroups {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) : List (List ↥(auxPiecesInWalk c)) :=
  (auxRotatedPieceOrder c hc S hS).splitBy
    (fun _ Q => decide (Q ∉ S))

lemma auxPieceGroups_ne_nil {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) : auxPieceGroups c hc S hS ≠ [] := by
  exact (List.splitBy_ne_nil).2 (auxRotatedPieceOrder_ne_nil c hc S hS)

lemma auxPieceGroup_ne_nil {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) {g : List ↥(auxPiecesInWalk c)}
    (hg : g ∈ auxPieceGroups c hc S hS) : g ≠ [] := by
  exact List.ne_nil_of_mem_splitBy hg

lemma auxPieceGroup_head_mem {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) {g : List ↥(auxPiecesInWalk c)}
    (hg : g ∈ auxPieceGroups c hc S hS) :
    g.head (auxPieceGroup_ne_nil c hc S hS hg) ∈ S := by
  exact splitBy_group_head (fun P => P ∈ S)
    (auxRotatedPieceOrder c hc S hS)
    (auxRotatedPieceOrder_ne_nil c hc S hS)
    (auxRotatedPieceOrder_head_mem c hc S hS) g hg

lemma auxPieceGroup_tail_not_mem {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) {g : List ↥(auxPiecesInWalk c)}
    (hg : g ∈ auxPieceGroups c hc S hS) :
    ∀ P ∈ g.tail, P ∉ S := by
  exact splitBy_group_tail_not (fun P => P ∈ S)
    (auxRotatedPieceOrder c hc S hS) g hg

lemma auxPieceGroup_isChain {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    {g : List ↥(auxPiecesInWalk c)}
    (hg : g ∈ auxPieceGroups c hc S hS) :
    g.IsChain (fun P Q => auxPieceRight c hc hcodd P =
      auxPieceLeft c hc hcodd Q) := by
  have hinfix : g <:+: (auxPieceGroups c hc S hS).flatten :=
    List.infix_of_mem_flatten hg
  rw [auxPieceGroups, List.flatten_splitBy] at hinfix
  exact (auxPieceOrderSubtype_rotate_isChain c hc hcodd _).infix hinfix

@[simp] lemma auxPieceGroups_flatten {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) :
    (auxPieceGroups c hc S hS).flatten = auxRotatedPieceOrder c hc S hS := by
  simp [auxPieceGroups]

lemma auxPieceGroups_nodup {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) : (auxPieceGroups c hc S hS).Nodup := by
  classical
  let gs := auxPieceGroups c hc S hS
  have hpair : gs.Pairwise List.Disjoint := by
    exact (List.nodup_flatten.mp (by
      change (auxPieceGroups c hc S hS).flatten.Nodup
      rw [auxPieceGroups_flatten c hc S hS]
      exact auxRotatedPieceOrder_nodup c hc S hS)).2
  rw [List.nodup_iff_injective_getElem]
  intro i j heq
  change gs[i.1] = gs[j.1] at heq
  by_contra hij
  have hijval : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hijval with hijlt | hjilt
  · have hd : List.Disjoint gs[i.1] gs[j.1] :=
      hpair.rel_get_of_lt (a := i) (b := j) hijlt
    have hne : gs[i.1] ≠ [] :=
      auxPieceGroup_ne_nil c hc S hS (List.get_mem gs i)
    have hx := List.head_mem hne
    have hxj : gs[i.1].head hne ∈ gs[j.1] := by
      rw [← heq]
      exact hx
    exact (List.disjoint_left.mp hd hx hxj)
  · have hd : List.Disjoint gs[j.1] gs[i.1] :=
      hpair.rel_get_of_lt (a := j) (b := i) hjilt
    have hne : gs[i.1] ≠ [] :=
      auxPieceGroup_ne_nil c hc S hS (List.get_mem gs i)
    have hx := List.head_mem hne
    have hxj : gs[i.1].head hne ∈ gs[j.1] := by
      rw [← heq]
      exact hx
    exact (List.disjoint_left.mp hd hxj hx)

lemma auxPieceGroups_eq_of_common_mem {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    {g q : List ↥(auxPiecesInWalk c)}
    (hg : g ∈ auxPieceGroups c hc S hS)
    (hq : q ∈ auxPieceGroups c hc S hS)
    {P : ↥(auxPiecesInWalk c)} (hPg : P ∈ g) (hPq : P ∈ q) : g = q := by
  classical
  by_contra hne
  have hpairGroups : (auxPieceGroups c hc S hS).Pairwise List.Disjoint := by
    have hflat : (auxPieceGroups c hc S hS).flatten =
        auxRotatedPieceOrder c hc S hS :=
      auxPieceGroups_flatten c hc S hS
    exact (List.nodup_flatten.mp (hflat ▸
      auxRotatedPieceOrder_nodup c hc S hS)).2
  obtain ⟨i, hi, hig⟩ := List.getElem_of_mem hg
  obtain ⟨j, hj, hjq⟩ := List.getElem_of_mem hq
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hne (hig.symm.trans hjq)
  rcases Nat.lt_or_gt_of_ne hij with hij | hji
  · have hd : List.Disjoint g q := by
      simpa [hig, hjq] using
        (hpairGroups.rel_get_of_lt (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij)
    exact (List.disjoint_left.mp hd hPg hPq)
  · have hd : List.Disjoint q g := by
      simpa [hig, hjq] using
        (hpairGroups.rel_get_of_lt (a := ⟨j, hj⟩) (b := ⟨i, hi⟩) hji)
    exact (List.disjoint_left.mp hd hPq hPg)

/-- Every selected piece is followed by at least one complementary piece.
Indeed, the groups start at selected pieces, while carrier-disjointness rules
out two selected pieces being cyclically consecutive. -/
lemma auxPieceGroup_tail_ne_nil {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    {g : List ↥(auxPiecesInWalk c)}
    (hg : g ∈ auxPieceGroups c hc S hS) : g.tail ≠ [] := by
  classical
  let R := auxRotatedPieceOrder c hc S hS
  have hRne : R ≠ [] := auxRotatedPieceOrder_ne_nil c hc S hS
  have hRnd : R.Nodup := auxRotatedPieceOrder_nodup c hc S hS
  have hgne : g ≠ [] := auxPieceGroup_ne_nil c hc S hS hg
  let P := g.head hgne
  have hPS : P ∈ S := auxPieceGroup_head_mem c hc S hS hg
  have hPR : P ∈ R := by
    change P ∈ auxRotatedPieceOrder c hc S hS
    rw [← auxPieceGroups_flatten c hc S hS]
    exact List.mem_flatten.mpr ⟨g, hg, List.head_mem hgne⟩
  intro htail
  have hg_eq : g = [P] := by
    calc
      g = P :: g.tail := (List.cons_head_tail hgne).symm
      _ = [P] := by rw [htail]
  obtain ⟨pre, post, hgroups⟩ := List.mem_iff_append.mp hg
  cases post with
  | cons q qs =>
      have hqmem : q ∈ auxPieceGroups c hc S hS := by
        rw [hgroups]
        simp
      have hqne : q ≠ [] := auxPieceGroup_ne_nil c hc S hS hqmem
      let Q := q.head hqne
      have hQS : Q ∈ S := auxPieceGroup_head_mem c hc S hS hqmem
      have hqcons : Q :: q.tail = q := by
        exact List.cons_head_tail hqne
      have hflat : R = pre.flatten ++ P :: Q :: (q.tail ++ qs.flatten) := by
        change auxRotatedPieceOrder c hc S hS =
          pre.flatten ++ P :: Q :: (q.tail ++ qs.flatten)
        rw [← auxPieceGroups_flatten c hc S hS]
        rw [hgroups, hg_eq, ← hqcons]
        simp [List.append_assoc]
      have hnext : R.next P hPR = Q := by
        have hn : (pre.flatten ++ P :: Q :: (q.tail ++ qs.flatten)).Nodup := by
          simpa only [← hflat] using hRnd
        exact (list_next_eq_of_eq hflat P hPR (by simp)).trans
          (list_next_of_append_cons_cons pre.flatten
            (q.tail ++ qs.flatten) P Q hn)
      have hsucc : auxPieceSuccessor c hc P = Q :=
        (auxRotatedPieceOrder_next_eq_successor c hc S hS P hPR).symm.trans hnext
      exact (auxPieceSuccessor_not_mem_selected c hc hcodd S hpair P hPS)
        (hsucc.symm ▸ hQS)
  | nil =>
      have hflat : R = pre.flatten ++ [P] := by
        change auxRotatedPieceOrder c hc S hS = pre.flatten ++ [P]
        rw [← auxPieceGroups_flatten c hc S hS]
        rw [hgroups, hg_eq]
        simp
      have hn : (pre.flatten ++ [P]).Nodup := by
        simpa only [← hflat] using hRnd
      have hnext : R.next P hPR = R.head hRne := by
        calc
          R.next P hPR = (pre.flatten ++ [P]).next P (by simp) :=
            list_next_eq_of_eq hflat P hPR (by simp)
          _ = (pre.flatten ++ [P]).head (by simp) :=
            list_next_of_append_singleton pre.flatten P hn
          _ = R.head hRne := by simpa only [hflat]
      have hheadS : R.head hRne ∈ S :=
        auxRotatedPieceOrder_head_mem c hc S hS
      have hsucc : auxPieceSuccessor c hc P = R.head hRne :=
        (auxRotatedPieceOrder_next_eq_successor c hc S hS P hPR).symm.trans hnext
      exact (auxPieceSuccessor_not_mem_selected c hc hcodd S hpair P hPS)
        (hsucc.symm ▸ hheadS)

/-- The cyclic successor of the last piece of a complementary block is the
head of the next block, hence is selected.  This includes the wrap from the
last block back to the head of the rotated order. -/
lemma auxPieceGroup_next_mem_selected {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) {g : List ↥(auxPiecesInWalk c)}
    (hg : g ∈ auxPieceGroups c hc S hS) :
    let hgne := auxPieceGroup_ne_nil c hc S hS hg
    let L := g.getLast hgne
    let hLR : L ∈ auxRotatedPieceOrder c hc S hS := by
      rw [← auxPieceGroups_flatten c hc S hS]
      exact List.mem_flatten.mpr ⟨g, hg, List.getLast_mem hgne⟩
    (auxRotatedPieceOrder c hc S hS).next L hLR ∈ S := by
  classical
  let R := auxRotatedPieceOrder c hc S hS
  have hRne : R ≠ [] := auxRotatedPieceOrder_ne_nil c hc S hS
  have hRnd : R.Nodup := auxRotatedPieceOrder_nodup c hc S hS
  have hgne : g ≠ [] := auxPieceGroup_ne_nil c hc S hS hg
  let L := g.getLast hgne
  have hLR : L ∈ R := by
    change L ∈ auxRotatedPieceOrder c hc S hS
    rw [← auxPieceGroups_flatten c hc S hS]
    exact List.mem_flatten.mpr ⟨g, hg, List.getLast_mem hgne⟩
  dsimp only
  obtain ⟨pre, post, hgroups⟩ := List.mem_iff_append.mp hg
  cases post with
  | cons q qs =>
      have hqmem : q ∈ auxPieceGroups c hc S hS := by
        rw [hgroups]
        simp
      have hqne : q ≠ [] := auxPieceGroup_ne_nil c hc S hS hqmem
      let Q := q.head hqne
      have hQS : Q ∈ S := auxPieceGroup_head_mem c hc S hS hqmem
      have hgparts : g.dropLast ++ [L] = g := by
        exact List.dropLast_append_getLast hgne
      have hqcons : Q :: q.tail = q := List.cons_head_tail hqne
      have hflat : R = (pre.flatten ++ g.dropLast) ++
          L :: Q :: (q.tail ++ qs.flatten) := by
        change auxRotatedPieceOrder c hc S hS =
          (pre.flatten ++ g.dropLast) ++ L :: Q :: (q.tail ++ qs.flatten)
        rw [← auxPieceGroups_flatten c hc S hS]
        rw [hgroups, ← hgparts, ← hqcons]
        simp [List.append_assoc]
      have hn : ((pre.flatten ++ g.dropLast) ++
          L :: Q :: (q.tail ++ qs.flatten)).Nodup := by
        simpa only [← hflat] using hRnd
      have hnext : R.next L hLR = Q :=
        (list_next_eq_of_eq hflat L hLR (by simp)).trans
          (list_next_of_append_cons_cons (pre.flatten ++ g.dropLast)
            (q.tail ++ qs.flatten) L Q hn)
      exact hnext.symm ▸ hQS
  | nil =>
      have hgparts : g.dropLast ++ [L] = g :=
        List.dropLast_append_getLast hgne
      have hflat : R = (pre.flatten ++ g.dropLast) ++ [L] := by
        change auxRotatedPieceOrder c hc S hS =
          (pre.flatten ++ g.dropLast) ++ [L]
        rw [← auxPieceGroups_flatten c hc S hS]
        rw [hgroups, ← hgparts]
        simp [List.append_assoc]
      have hn : ((pre.flatten ++ g.dropLast) ++ [L]).Nodup := by
        simpa only [← hflat] using hRnd
      have hnext : R.next L hLR = R.head hRne := by
        calc
          R.next L hLR = ((pre.flatten ++ g.dropLast) ++ [L]).next L (by simp) :=
            list_next_eq_of_eq hflat L hLR (by simp)
          _ = ((pre.flatten ++ g.dropLast) ++ [L]).head (by simp) :=
            list_next_of_append_singleton (pre.flatten ++ g.dropLast) L hn
          _ = R.head hRne := by simpa only [hflat]
      exact hnext.symm ▸ auxRotatedPieceOrder_head_mem c hc S hS

/-- A cyclic successor which is still unselected remains in the same
`splitBy` block. -/
lemma auxPieceGroup_successor_mem_of_not_selected
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    {g : List ↥(auxPiecesInWalk c)}
    (hg : g ∈ auxPieceGroups c hc S hS)
    {R : ↥(auxPiecesInWalk c)} (hRg : R ∈ g)
    (hnextNot : auxPieceSuccessor c hc R ∉ S) :
    auxPieceSuccessor c hc R ∈ g := by
  classical
  let O := auxRotatedPieceOrder c hc S hS
  have hOne : g <:+: O := by
    change g <:+: auxRotatedPieceOrder c hc S hS
    rw [← auxPieceGroups_flatten c hc S hS]
    exact List.infix_of_mem_flatten hg
  obtain ⟨outerPre, outerPost, hO⟩ := hOne
  obtain ⟨pre, post, hgshape⟩ := List.mem_iff_append.mp hRg
  cases post with
  | cons U us =>
      have hshape : O = (outerPre ++ pre) ++ R :: U :: (us ++ outerPost) := by
        rw [← hO, hgshape]
        simp [List.append_assoc]
      have hRO : R ∈ O := by rw [hshape]; simp
      have hnext : O.next R hRO = U :=
        (list_next_eq_of_eq hshape R hRO (by simp)).trans
          (list_next_of_append_cons_cons (outerPre ++ pre)
            (us ++ outerPost) R U (by
              simpa only [← hshape] using auxRotatedPieceOrder_nodup c hc S hS))
      have hsucc : auxPieceSuccessor c hc R = U :=
        (auxRotatedPieceOrder_next_eq_successor c hc S hS R hRO).symm.trans hnext
      rw [hsucc]
      rw [hgshape]
      simp
  | nil =>
      have hgne : g ≠ [] := auxPieceGroup_ne_nil c hc S hS hg
      have hRlast : R = g.getLast hgne := by
        have hlast := List.getLast_congr hgne (by simp) hgshape
        simpa using hlast.symm
      have hLR : g.getLast hgne ∈ O := by
        change g.getLast hgne ∈ auxRotatedPieceOrder c hc S hS
        rw [← auxPieceGroups_flatten c hc S hS]
        exact List.mem_flatten.mpr ⟨g, hg, List.getLast_mem hgne⟩
      have hselected := auxPieceGroup_next_mem_selected c hc S hS hg
      have hsuccEq : auxPieceSuccessor c hc R =
          O.next (g.getLast hgne) hLR := by
        rw [hRlast]
        exact (auxRotatedPieceOrder_next_eq_successor
          c hc S hS (g.getLast hgne) hLR).symm
      exact (hnextNot (hsuccEq ▸ hselected)).elim

/-- The cyclic predecessor of an unselected member lies in the same block.
It belongs to some block by flattening; that block also contains its
unselected successor, hence uniqueness of blocks identifies it with the
given one. -/
lemma auxPieceGroup_predecessor_mem_of_mem_unselected
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    {g : List ↥(auxPiecesInWalk c)}
    (hg : g ∈ auxPieceGroups c hc S hS)
    {R : ↥(auxPiecesInWalk c)} (hRg : R ∈ g) (hRnot : R ∉ S) :
    auxPiecePredecessor c hc R ∈ g := by
  classical
  have hprevOrder : auxPiecePredecessor c hc R ∈
      auxRotatedPieceOrder c hc S hS :=
    mem_auxRotatedPieceOrder c hc S hS (auxPiecePredecessor c hc R)
  have hprevFlat : auxPiecePredecessor c hc R ∈
      (auxPieceGroups c hc S hS).flatten := by
    simpa using hprevOrder
  obtain ⟨q, hq, hprevq⟩ := List.mem_flatten.mp hprevFlat
  have hRq : R ∈ q := by
    have hsucc := auxPieceGroup_successor_mem_of_not_selected
      c hc S hS hq hprevq (by simpa using hRnot)
    simpa using hsucc
  have hqg : q = g :=
    auxPieceGroups_eq_of_common_mem c hc S hS hq hg hRq hRg
  simpa [hqg] using hprevq

/-- Each selected piece is the unique distinguished head of a block in the
rotated complementary grouping. -/
lemma exists_auxPieceGroup_head_eq {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (P : ↥S) :
    ∃ g, ∃ hg : g ∈ auxPieceGroups c hc S hS,
      g.head (auxPieceGroup_ne_nil c hc S hS hg) = P.1 := by
  exact exists_splitBy_group_head_eq (fun Q => Q ∈ S)
    (auxRotatedPieceOrder c hc S hS) P.1
    (mem_auxRotatedPieceOrder c hc S hS P.1) P.2

noncomputable def auxSelectedPieceGroup {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (P : ↥S) : List ↥(auxPiecesInWalk c) :=
  Classical.choose (exists_auxPieceGroup_head_eq c hc S hS P)

lemma auxSelectedPieceGroup_mem {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (P : ↥S) :
    auxSelectedPieceGroup c hc S hS P ∈ auxPieceGroups c hc S hS :=
  Classical.choose_spec (exists_auxPieceGroup_head_eq c hc S hS P) |>.choose

@[simp] lemma auxSelectedPieceGroup_head {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (P : ↥S) :
    (auxSelectedPieceGroup c hc S hS P).head
        (auxPieceGroup_ne_nil c hc S hS (auxSelectedPieceGroup_mem c hc S hS P)) = P.1 :=
  Classical.choose_spec (exists_auxPieceGroup_head_eq c hc S hS P) |>.choose_spec

lemma auxSelectedPieceGroup_injective {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty) :
    Function.Injective (auxSelectedPieceGroup c hc S hS) := by
  intro P Q h
  apply Subtype.ext
  have hPmem := auxSelectedPieceGroup_mem c hc S hS P
  have hQmem := auxSelectedPieceGroup_mem c hc S hS Q
  have hPne := auxPieceGroup_ne_nil c hc S hS hPmem
  have hQne := auxPieceGroup_ne_nil c hc S hS hQmem
  have hheads := list_head_eq_of_eq h hPne hQne
  exact (auxSelectedPieceGroup_head c hc S hS P).symm.trans
    (hheads.trans (auxSelectedPieceGroup_head c hc S hS Q))

lemma auxSelectedPieceGroup_of_group_head {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    {g : List ↥(auxPiecesInWalk c)} (hg : g ∈ auxPieceGroups c hc S hS) :
    let hgne := auxPieceGroup_ne_nil c hc S hS hg
    let P : ↥S := ⟨g.head hgne, auxPieceGroup_head_mem c hc S hS hg⟩
    auxSelectedPieceGroup c hc S hS P = g := by
  let hgne := auxPieceGroup_ne_nil c hc S hS hg
  let P : ↥S := ⟨g.head hgne, auxPieceGroup_head_mem c hc S hS hg⟩
  apply auxPieceGroups_eq_of_common_mem c hc S hS (P := P.1)
    (auxSelectedPieceGroup_mem c hc S hS P) hg
  · have hhead := auxSelectedPieceGroup_head c hc S hS P
    rw [← hhead]
    exact List.head_mem (auxPieceGroup_ne_nil c hc S hS
      (auxSelectedPieceGroup_mem c hc S hS P))
  · exact List.head_mem hgne

noncomputable def auxPieceGroupSelectedHead {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (g : {g // g ∈ auxPieceGroups c hc S hS}) : ↥S :=
  ⟨g.1.head (auxPieceGroup_ne_nil c hc S hS g.2),
    auxPieceGroup_head_mem c hc S hS g.2⟩

lemma auxPieceGroupSelectedHead_injective {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty) :
    Function.Injective (auxPieceGroupSelectedHead c hc S hS) := by
  intro g q heq
  apply Subtype.ext
  let P := g.1.head (auxPieceGroup_ne_nil c hc S hS g.2)
  have hPq : P ∈ q.1 := by
    have hval := congrArg Subtype.val heq
    change P = q.1.head (auxPieceGroup_ne_nil c hc S hS q.2) at hval
    rw [hval]
    exact List.head_mem (auxPieceGroup_ne_nil c hc S hS q.2)
  exact auxPieceGroups_eq_of_common_mem c hc S hS g.2 q.2
    (List.head_mem (auxPieceGroup_ne_nil c hc S hS g.2)) hPq

/-- The selected pieces ordered by their complementary blocks. -/
noncomputable def auxSelectedGroupOrder {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) : List ↥S :=
  (auxPieceGroups c hc S hS).attach.map
    (auxPieceGroupSelectedHead c hc S hS)

lemma auxSelectedGroupOrder_nodup {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) : (auxSelectedGroupOrder c hc S hS).Nodup := by
  apply List.Nodup.map (auxPieceGroupSelectedHead_injective c hc S hS)
  exact (auxPieceGroups_nodup c hc S hS).attach

lemma mem_auxSelectedGroupOrder {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (P : ↥S) : P ∈ auxSelectedGroupOrder c hc S hS := by
  obtain ⟨g, hg, hhead⟩ := exists_auxPieceGroup_head_eq c hc S hS P
  apply List.mem_map.mpr
  let ga : {g // g ∈ auxPieceGroups c hc S hS} := ⟨g, hg⟩
  refine ⟨ga, List.mem_attach _ _, ?_⟩
  apply Subtype.ext
  exact hhead

lemma auxSelectedGroupOrder_ne_nil {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) : auxSelectedGroupOrder c hc S hS ≠ [] := by
  let P : ↥S := ⟨hS.choose, hS.choose_spec⟩
  exact List.ne_nil_of_mem (mem_auxSelectedGroupOrder c hc S hS P)

@[simp] lemma auxSelectedGroupOrder_toFinset {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) : (auxSelectedGroupOrder c hc S hS).toFinset = Finset.univ := by
  ext P
  simp [mem_auxSelectedGroupOrder c hc S hS P]

lemma auxSelectedGroupOrder_length {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) : (auxSelectedGroupOrder c hc S hS).length = S.card := by
  have hcard := List.toFinset_card_of_nodup
    (auxSelectedGroupOrder_nodup c hc S hS)
  rw [auxSelectedGroupOrder_toFinset c hc S hS, Finset.card_univ,
    Fintype.card_coe] at hcard
  exact hcard.symm

lemma auxSelectedPieceGroups_disjoint {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    {P Q : ↥S} (hPQ : P ≠ Q) :
    List.Disjoint (auxSelectedPieceGroup c hc S hS P)
      (auxSelectedPieceGroup c hc S hS Q) := by
  classical
  let gs := auxPieceGroups c hc S hS
  let gP := auxSelectedPieceGroup c hc S hS P
  let gQ := auxSelectedPieceGroup c hc S hS Q
  have hgP : gP ∈ gs := auxSelectedPieceGroup_mem c hc S hS P
  have hgQ : gQ ∈ gs := auxSelectedPieceGroup_mem c hc S hS Q
  have hgne : gP ≠ gQ := fun h =>
    hPQ (auxSelectedPieceGroup_injective c hc S hS h)
  have hpairGroups : gs.Pairwise List.Disjoint := by
    exact (List.nodup_flatten.mp (by
      change (auxPieceGroups c hc S hS).flatten.Nodup
      rw [auxPieceGroups_flatten c hc S hS]
      exact auxRotatedPieceOrder_nodup c hc S hS)).2
  obtain ⟨i, hi, higP⟩ := List.getElem_of_mem hgP
  obtain ⟨j, hj, hjgQ⟩ := List.getElem_of_mem hgQ
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hgne (higP.symm.trans hjgQ)
  rcases Nat.lt_or_gt_of_ne hij with hij | hji
  · simpa [higP, hjgQ] using
      (hpairGroups.rel_get_of_lt (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij)
  · have hd : List.Disjoint gQ gP := by
      simpa [higP, hjgQ] using
        (hpairGroups.rel_get_of_lt (a := ⟨j, hj⟩) (b := ⟨i, hi⟩) hji)
    exact hd.symm

noncomputable def auxSelectedNextPiece {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (P : ↥S) : ↥(auxPiecesInWalk c) :=
  let g := auxSelectedPieceGroup c hc S hS P
  let hg := auxSelectedPieceGroup_mem c hc S hS P
  let hgne := auxPieceGroup_ne_nil c hc S hS hg
  let L := g.getLast hgne
  let hLR : L ∈ auxRotatedPieceOrder c hc S hS := by
    rw [← auxPieceGroups_flatten c hc S hS]
    exact List.mem_flatten.mpr ⟨g, hg, List.getLast_mem hgne⟩
  (auxRotatedPieceOrder c hc S hS).next L hLR

lemma auxSelectedNextPiece_mem {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (P : ↥S) : auxSelectedNextPiece c hc S hS P ∈ S := by
  unfold auxSelectedNextPiece
  exact auxPieceGroup_next_mem_selected c hc S hS
    (auxSelectedPieceGroup_mem c hc S hS P)

noncomputable def auxSelectedGroupSuccessor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (P : ↥S) : ↥S :=
  ⟨auxSelectedNextPiece c hc S hS P,
    auxSelectedNextPiece_mem c hc S hS P⟩

theorem auxSelectedGroupSuccessor_injective {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) :
    Function.Injective (auxSelectedGroupSuccessor c hc S hS) := by
  classical
  intro P Q hPQ
  let R := auxRotatedPieceOrder c hc S hS
  let gs := auxPieceGroups c hc S hS
  let gP := auxSelectedPieceGroup c hc S hS P
  let gQ := auxSelectedPieceGroup c hc S hS Q
  have hgP : gP ∈ gs := auxSelectedPieceGroup_mem c hc S hS P
  have hgQ : gQ ∈ gs := auxSelectedPieceGroup_mem c hc S hS Q
  have hgPne : gP ≠ [] := auxPieceGroup_ne_nil c hc S hS hgP
  have hgQne : gQ ≠ [] := auxPieceGroup_ne_nil c hc S hS hgQ
  let LP := gP.getLast hgPne
  let LQ := gQ.getLast hgQne
  have hLPR : LP ∈ R := by
    change LP ∈ auxRotatedPieceOrder c hc S hS
    rw [← auxPieceGroups_flatten c hc S hS]
    exact List.mem_flatten.mpr ⟨gP, hgP, List.getLast_mem hgPne⟩
  have hLQR : LQ ∈ R := by
    change LQ ∈ auxRotatedPieceOrder c hc S hS
    rw [← auxPieceGroups_flatten c hc S hS]
    exact List.mem_flatten.mpr ⟨gQ, hgQ, List.getLast_mem hgQne⟩
  have hnext : R.next LP hLPR = R.next LQ hLQR := by
    have hval := congrArg Subtype.val hPQ
    change auxSelectedNextPiece c hc S hS P =
      auxSelectedNextPiece c hc S hS Q at hval
    change R.next LP hLPR = R.next LQ hLQR at hval
    exact hval
  have hlast : LP = LQ := by
    calc
      LP = R.prev (R.next LP hLPR) (List.next_mem R LP hLPR) :=
        (List.prev_next R (auxRotatedPieceOrder_nodup c hc S hS) LP hLPR).symm
      _ = R.prev (R.next LQ hLQR) (List.next_mem R LQ hLQR) :=
        list_prev_eq_of_eq R hnext _ _
      _ = LQ := List.prev_next R (auxRotatedPieceOrder_nodup c hc S hS) LQ hLQR
  have hgsPair : gs.Pairwise List.Disjoint := by
    exact (List.nodup_flatten.mp (by
      change (auxPieceGroups c hc S hS).flatten |>.Nodup
      rw [auxPieceGroups_flatten c hc S hS]
      exact auxRotatedPieceOrder_nodup c hc S hS)).2
  have hgEq : gP = gQ := by
    by_contra hne
    obtain ⟨i, hi, higP⟩ := List.getElem_of_mem hgP
    obtain ⟨j, hj, hjgQ⟩ := List.getElem_of_mem hgQ
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hne (higP.symm.trans hjgQ)
    rcases Nat.lt_or_gt_of_ne hij with hij | hji
    · have hd : List.Disjoint gP gQ := by
        simpa [higP, hjgQ] using
          (hgsPair.rel_get_of_lt (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij)
      exact (List.disjoint_left.mp hd (List.getLast_mem hgPne))
        (by simpa [LP, LQ, hlast] using List.getLast_mem hgQne)
    · have hd : List.Disjoint gQ gP := by
        simpa [higP, hjgQ] using
          (hgsPair.rel_get_of_lt (a := ⟨j, hj⟩) (b := ⟨i, hi⟩) hji)
      exact (List.disjoint_left.mp hd (List.getLast_mem hgQne))
        (by simpa [LP, LQ, hlast] using List.getLast_mem hgPne)
  apply Subtype.ext
  have hheadP := auxSelectedPieceGroup_head c hc S hS P
  have hheadQ := auxSelectedPieceGroup_head c hc S hS Q
  change gP.head hgPne = P.1 at hheadP
  change gQ.head hgQne = Q.1 at hheadQ
  have hheads : gP.head hgPne = gQ.head hgQne :=
    list_head_eq_of_eq hgEq hgPne hgQne
  exact hheadP.symm.trans (hheads.trans hheadQ)

/-- The cyclic next block in `auxPieceGroups` begins at precisely the
selected piece named by `auxSelectedNextPiece`. -/
lemma auxPieceGroups_next_head_eq_selectedNext
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (P : ↥S) :
    let gs := auxPieceGroups c hc S hS
    let g := auxSelectedPieceGroup c hc S hS P
    let hg := auxSelectedPieceGroup_mem c hc S hS P
    let gn := gs.next g hg
    gn.head (auxPieceGroup_ne_nil c hc S hS (List.next_mem gs g hg)) =
      auxSelectedNextPiece c hc S hS P := by
  classical
  let gs := auxPieceGroups c hc S hS
  let O := auxRotatedPieceOrder c hc S hS
  let g := auxSelectedPieceGroup c hc S hS P
  have hgsne : gs ≠ [] := auxPieceGroups_ne_nil c hc S hS
  have hgsnd : gs.Nodup := auxPieceGroups_nodup c hc S hS
  have hg : g ∈ gs := auxSelectedPieceGroup_mem c hc S hS P
  have hgne : g ≠ [] := auxPieceGroup_ne_nil c hc S hS hg
  let L := g.getLast hgne
  have hLR : L ∈ O := by
    change L ∈ auxRotatedPieceOrder c hc S hS
    rw [← auxPieceGroups_flatten c hc S hS]
    exact List.mem_flatten.mpr ⟨g, hg, List.getLast_mem hgne⟩
  obtain ⟨pre, post, hgs⟩ := List.mem_iff_append.mp hg
  cases post with
  | cons q qs =>
      have hqmem : q ∈ gs := by rw [hgs]; simp
      have hqne : q ≠ [] := auxPieceGroup_ne_nil c hc S hS hqmem
      let Q := q.head hqne
      have hgparts : g.dropLast ++ [L] = g :=
        List.dropLast_append_getLast hgne
      have hqparts : Q :: q.tail = q := List.cons_head_tail hqne
      have hflat : O = (pre.flatten ++ g.dropLast) ++
          L :: Q :: (q.tail ++ qs.flatten) := by
        calc
          O = gs.flatten := (auxPieceGroups_flatten c hc S hS).symm
          _ = _ := by
            rw [hgs, ← hgparts, ← hqparts]
            simp [List.append_assoc]
      have hnextPiece : O.next L hLR = Q :=
        (list_next_eq_of_eq hflat L hLR (by simp)).trans
          (list_next_of_append_cons_cons (pre.flatten ++ g.dropLast)
            (q.tail ++ qs.flatten) L Q (by
              simpa only [← hflat] using auxRotatedPieceOrder_nodup c hc S hS))
      have hnextGroup : gs.next g hg = q := by
        have hshape : gs = pre ++ g :: q :: qs := by simpa using hgs
        exact (list_next_eq_of_eq hshape g hg (by simp)).trans
          (list_next_of_append_cons_cons pre qs g q (by
            simpa only [← hshape] using hgsnd))
      dsimp only
      let hnnext := auxPieceGroup_ne_nil c hc S hS (List.next_mem gs g hg)
      have hheadNext : (gs.next g hg).head hnnext = Q :=
        list_head_eq_of_eq hnextGroup hnnext hqne
      calc
        (gs.next g hg).head hnnext = Q := hheadNext
        _ = auxSelectedNextPiece c hc S hS P := by
          unfold auxSelectedNextPiece
          exact hnextPiece.symm
  | nil =>
      have hgparts : g.dropLast ++ [L] = g :=
        List.dropLast_append_getLast hgne
      have hflat : O = (pre.flatten ++ g.dropLast) ++ [L] := by
        calc
          O = gs.flatten := (auxPieceGroups_flatten c hc S hS).symm
          _ = _ := by
            rw [hgs, ← hgparts]
            simp [List.append_assoc]
      have hOn : O.Nodup := auxRotatedPieceOrder_nodup c hc S hS
      have hOne : O ≠ [] := auxRotatedPieceOrder_ne_nil c hc S hS
      have hnextPiece : O.next L hLR = O.head hOne := by
        calc
          O.next L hLR = ((pre.flatten ++ g.dropLast) ++ [L]).next L (by simp) :=
            list_next_eq_of_eq hflat L hLR (by simp)
          _ = ((pre.flatten ++ g.dropLast) ++ [L]).head (by simp) :=
            list_next_of_append_singleton (pre.flatten ++ g.dropLast) L (by
              simpa only [← hflat] using hOn)
          _ = O.head hOne := by simpa only [hflat]
      have hnextGroup : gs.next g hg = gs.head hgsne := by
        have hshape : gs = pre ++ [g] := by simpa using hgs
        calc
          gs.next g hg = (pre ++ [g]).next g (by simp) :=
            list_next_eq_of_eq hshape g hg (by simp)
          _ = (pre ++ [g]).head (by simp) :=
            list_next_of_append_singleton pre g (by
              simpa only [← hshape] using hgsnd)
          _ = gs.head hgsne := by simpa only [hshape]
      have hheadFlatten :
          (gs.head hgsne).head
              (auxPieceGroup_ne_nil c hc S hS (List.head_mem hgsne)) =
            O.head hOne := by
        have hh := List.head_head_eq_head_flatten hgsne
          (auxPieceGroup_ne_nil c hc S hS (List.head_mem hgsne))
        have hflatEq : gs.flatten = O := auxPieceGroups_flatten c hc S hS
        have hflattenNe : gs.flatten ≠ [] := by
          rw [hflatEq]
          exact hOne
        have hheads : gs.flatten.head hflattenNe = O.head hOne :=
          list_head_eq_of_eq hflatEq hflattenNe hOne
        exact hh.trans hheads
      dsimp only
      let hnnext := auxPieceGroup_ne_nil c hc S hS (List.next_mem gs g hg)
      let hnhead := auxPieceGroup_ne_nil c hc S hS (List.head_mem hgsne)
      have hheadNext : (gs.next g hg).head hnnext = (gs.head hgsne).head hnhead :=
        list_head_eq_of_eq hnextGroup hnnext hnhead
      calc
        (gs.next g hg).head hnnext = (gs.head hgsne).head hnhead := hheadNext
        _ = O.head hOne := hheadFlatten
        _ = auxSelectedNextPiece c hc S hS P := by
          unfold auxSelectedNextPiece
          exact hnextPiece.symm

/-- The cyclic successor in the list of selected group heads is the selected
group successor defined from the intervening complementary block. -/
lemma auxSelectedGroupOrder_next_eq_successor
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (P : ↥S) :
    let O := auxSelectedGroupOrder c hc S hS
    O.next P (mem_auxSelectedGroupOrder c hc S hS P) =
      auxSelectedGroupSuccessor c hc S hS P := by
  classical
  let gs := auxPieceGroups c hc S hS
  let g := auxSelectedPieceGroup c hc S hS P
  have hg : g ∈ gs := auxSelectedPieceGroup_mem c hc S hS P
  let ga : {q // q ∈ gs} := ⟨g, hg⟩
  have hga : ga ∈ gs.attach := List.mem_attach gs ga
  let f := auxPieceGroupSelectedHead c hc S hS
  have hfga : f ga = P := by
    apply Subtype.ext
    exact auxSelectedPieceGroup_head c hc S hS P
  have hmapNext := list_map_next_of_injective f
    (auxPieceGroupSelectedHead_injective c hc S hS)
    gs.attach (auxPieceGroups_nodup c hc S hS).attach ga hga
  have hvalNext := list_map_next_of_injective Subtype.val
    Subtype.val_injective gs.attach
    (auxPieceGroups_nodup c hc S hS).attach ga hga
  have hnextGroup : (gs.attach.next ga hga).1 = gs.next g hg := by
    symm
    simpa [ga, gs] using hvalNext
  have hhead := auxPieceGroups_next_head_eq_selectedNext c hc S hS P
  have hfNext : f (gs.attach.next ga hga) =
      auxSelectedGroupSuccessor c hc S hS P := by
    apply Subtype.ext
    dsimp only [f, auxPieceGroupSelectedHead,
      auxSelectedGroupSuccessor]
    exact (list_head_eq_of_eq hnextGroup
      (auxPieceGroup_ne_nil c hc S hS (gs.attach.next ga hga).2)
      (auxPieceGroup_ne_nil c hc S hS (List.next_mem gs g hg))).trans hhead
  calc
    (auxSelectedGroupOrder c hc S hS).next P
        (mem_auxSelectedGroupOrder c hc S hS P) =
      (auxSelectedGroupOrder c hc S hS).next (f ga) (by
        simpa only [hfga] using mem_auxSelectedGroupOrder c hc S hS P) := by
          congr
          exact hfga.symm
    _ = f (gs.attach.next ga hga) := by
      simpa [auxSelectedGroupOrder, gs, f] using hmapNext
    _ = auxSelectedGroupSuccessor c hc S hS P := hfNext

lemma auxSelectedNextPiece_ne_of_two_le_card
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (hScard : 2 ≤ S.card) (P : ↥S) :
    auxSelectedNextPiece c hc S hS P ≠ P.1 := by
  classical
  let gs := auxPieceGroups c hc S hS
  let g := auxSelectedPieceGroup c hc S hS P
  have hg : g ∈ gs := auxSelectedPieceGroup_mem c hc S hS P
  have hlen : 2 ≤ gs.length := by
    have horderLen := auxSelectedGroupOrder_length c hc S hS
    simpa [auxSelectedGroupOrder] using hScard.trans_eq horderLen.symm
  have hnextNe : gs.next g hg ≠ g :=
    list_next_ne_self_of_nodup (auxPieceGroups_nodup c hc S hS) hlen g hg
  let ga : {q // q ∈ gs} := ⟨g, hg⟩
  let gn : {q // q ∈ gs} := ⟨gs.next g hg, List.next_mem gs g hg⟩
  have hheadG : auxPieceGroupSelectedHead c hc S hS ga = P := by
    apply Subtype.ext
    exact auxSelectedPieceGroup_head c hc S hS P
  have hheadN : (auxPieceGroupSelectedHead c hc S hS gn).1 =
      auxSelectedNextPiece c hc S hS P := by
    exact auxPieceGroups_next_head_eq_selectedNext c hc S hS P
  intro hself
  have hheads : auxPieceGroupSelectedHead c hc S hS gn =
      auxPieceGroupSelectedHead c hc S hS ga := by
    apply Subtype.ext
    exact hheadN.trans (hself.trans (congrArg Subtype.val hheadG).symm)
  have hga : gn = ga :=
    auxPieceGroupSelectedHead_injective c hc S hS hheads
  exact hnextNe (congrArg Subtype.val hga)

noncomputable def auxSelectedGroupPredecessor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (P : ↥S) : ↥S :=
  Classical.choose
    ((Finite.injective_iff_surjective.mp
      (auxSelectedGroupSuccessor_injective c hc S hS)) P)

@[simp] lemma auxSelectedGroupSuccessor_predecessor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (P : ↥S) :
    auxSelectedGroupSuccessor c hc S hS
      (auxSelectedGroupPredecessor c hc S hS P) = P :=
  Classical.choose_spec
    ((Finite.injective_iff_surjective.mp
      (auxSelectedGroupSuccessor_injective c hc S hS)) P)

noncomputable def auxSelectedUnderlying {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} {c : (familyAuxGraph D).Walk z z}
    (S : Finset ↥(auxPiecesInWalk c)) : Finset ↥A :=
  S.map ⟨fun P => P.1, fun P Q h => Subtype.ext h⟩

@[simp] lemma mem_auxSelectedUnderlying_iff {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} {c : (familyAuxGraph D).Walk z z}
    (S : Finset ↥(auxPiecesInWalk c)) (P : ↥A) :
    P ∈ auxSelectedUnderlying S ↔ ∃ hP : P ∈ auxPiecesInWalk c,
      (⟨P, hP⟩ : ↥(auxPiecesInWalk c)) ∈ S := by
  classical
  constructor
  · intro hP
    obtain ⟨Q, hQS, hQP⟩ := Finset.mem_map.mp hP
    have hval : Q.1 = P := hQP
    subst P
    refine ⟨Q.2, ?_⟩
    convert hQS using 1
    exact Subtype.ext hval.symm
  · rintro ⟨hP, hPS⟩
    exact Finset.mem_map.mpr ⟨⟨P, hP⟩, hPS, rfl⟩

noncomputable def auxComplementUnderlying {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (S : Finset ↥(auxPiecesInWalk c)) : Finset ↥A :=
  auxPiecesInWalk c \ auxSelectedUnderlying S

noncomputable def auxComplementPackedFamily {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (S : Finset ↥(auxPiecesInWalk c)) : Finset (PackedSubgraph V) :=
  (auxComplementUnderlying c S).image Subtype.val

noncomputable def auxComplementGraph {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (S : Finset ↥(auxPiecesInWalk c)) : SimpleGraph V :=
  packedUnion (auxComplementPackedFamily c S)

lemma auxComplementGraph_le_packedUnion {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (S : Finset ↥(auxPiecesInWalk c)) :
    auxComplementGraph c S ≤ packedUnion A := by
  intro u v huv
  obtain ⟨P, hPF, hPuv⟩ := exists_piece_adj_of_packedUnion_adj huv
  rw [auxComplementPackedFamily] at hPF
  obtain ⟨Q, hQ, hQP⟩ := Finset.mem_image.mp hPF
  subst P
  exact le_packedUnion Q.2 hPuv

lemma mem_auxComplementPackedFamily_of_mem_tail {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) {g : List ↥(auxPiecesInWalk c)}
    (hg : g ∈ auxPieceGroups c hc S hS) {Q : ↥(auxPiecesInWalk c)}
    (hQg : Q ∈ g.tail) : Q.1.1 ∈ auxComplementPackedFamily c S := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨Q.1, ?_, rfl⟩
  rw [auxComplementUnderlying, Finset.mem_sdiff]
  refine ⟨Q.2, ?_⟩
  intro hQ
  rw [mem_auxSelectedUnderlying_iff] at hQ
  have hQS : Q ∈ S := by
    convert hQ.choose_spec using 1
  exact (auxPieceGroup_tail_not_mem c hc S hS hg Q hQg) hQS

def familyAuxAllowed {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} (B : Finset ↥A) :
    FamilyAuxVertex V A → Prop
  | .inl _ => True
  | .inr (.inl P) => P ∈ B
  | .inr (.inr (P, _)) => P ∈ B

/-- Removing a nonempty selected class from a minimum-piece odd auxiliary
cycle leaves a bipartite signed-incidence graph.  Otherwise an odd cycle in
the induced remainder would use strictly fewer piece nodes. -/
theorem familyAuxComplement_colorable_two {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty) :
    ((familyAuxGraph D).induce
      {x | familyAuxAllowed (auxComplementUnderlying c S) x}).Colorable 2 := by
  classical
  apply Erdos58.colorable_two_of_no_odd_isCycle
  intro x d hd hodd
  let e : (familyAuxGraph D).induce
      {x | familyAuxAllowed (auxComplementUnderlying c S) x} ↪g
        familyAuxGraph D :=
    SimpleGraph.Embedding.induce
      {x | familyAuxAllowed (auxComplementUnderlying c S) x}
  let d' := d.map e.toHom
  have hd' : d'.IsCycle := hd.map e.injective
  have hlen : d'.length = d.length := SimpleGraph.Walk.length_map _ _
  have hpieces : auxPiecesInWalk d' ⊆ auxComplementUnderlying c S := by
    intro P hP
    rw [mem_auxPiecesInWalk_iff] at hP
    dsimp [d'] at hP
    rw [SimpleGraph.Walk.support_map] at hP
    obtain ⟨y, hy, hyP⟩ := List.mem_map.mp hP
    have hyval : y.1 = (.inr (.inl P) : FamilyAuxVertex V A) := hyP
    have hyallowed := y.2
    simpa [familyAuxAllowed, hyval] using hyallowed
  have hselectedSub : auxSelectedUnderlying S ⊆ auxPiecesInWalk c := by
    intro P hP
    rw [mem_auxSelectedUnderlying_iff] at hP
    exact hP.choose
  have hselectedPos : 0 < (auxSelectedUnderlying S).card := by
    rw [auxSelectedUnderlying, Finset.card_map]
    exact Finset.card_pos.mpr hS
  have hcomplementCard : (auxComplementUnderlying c S).card <
      (auxPiecesInWalk c).card := by
    have hcardle := Finset.card_le_card hselectedSub
    rw [auxComplementUnderlying, Finset.card_sdiff_of_subset hselectedSub]
    omega
  have hsmall : (auxPiecesInWalk d').card < (auxPiecesInWalk c).card :=
    (Finset.card_le_card hpieces).trans_lt hcomplementCard
  have hodd' : Odd d'.length := by simpa [hlen] using hodd
  exact (Nat.not_lt_of_ge (hminimal _ d' hd' hodd')) hsmall

noncomputable def auxComplementColor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty) : V → Fin 2 :=
  let coloring : ((familyAuxGraph D).induce
      {x | familyAuxAllowed (auxComplementUnderlying c S) x}).Coloring (Fin 2) :=
    Classical.choice
      (familyAuxComplement_colorable_two c hc hcodd hminimal S hS)
  fun v => coloring ⟨.inl v, trivial⟩

/-- The induced auxiliary coloring restricts to a proper coloring of each
unselected piece. -/
lemma auxComplementColor_ne_of_piece_adj {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (Q : ↥(auxPiecesInWalk c)) (hQS : Q ∉ S)
    {u v : V} (hu : u ∈ Q.1.1.1) (hv : v ∈ Q.1.1.1)
    (huv : Q.1.1.2.Adj u v) :
    auxComplementColor c hc hcodd hminimal S hS u ≠
      auxComplementColor c hc hcodd hminimal S hS v := by
  classical
  let B := auxComplementUnderlying c S
  let H := (familyAuxGraph D).induce {x | familyAuxAllowed B x}
  let coloring : H.Coloring (Fin 2) := Classical.choice
    (familyAuxComplement_colorable_two c hc hcodd hminimal S hS)
  have hQnotUnderlying : Q.1 ∉ auxSelectedUnderlying S := by
    intro hQ
    rw [mem_auxSelectedUnderlying_iff] at hQ
    exact hQS (by simpa using hQ.choose_spec)
  have hQB : Q.1 ∈ B := by
    exact Finset.mem_sdiff.mpr ⟨Q.2, hQnotUnderlying⟩
  let qnode : {x | familyAuxAllowed B x} :=
    ⟨.inr (.inl Q.1), by simpa [familyAuxAllowed] using hQB⟩
  have heq_zero (w : V) (hw : w ∈ Q.1.1.1)
      (hzero : (D Q.1).color w = 0) :
      coloring ⟨.inl w, trivial⟩ = coloring qnode := by
    let dummy : {x | familyAuxAllowed B x} :=
      ⟨.inr (.inr (Q.1, w)), by simpa [familyAuxAllowed] using hQB⟩
    have hwd : H.Adj ⟨.inl w, trivial⟩ dummy := by
      simpa [H, dummy, familyAuxAllowed] using
        (show (familyAuxGraph D).Adj (.inl w) (.inr (.inr (Q.1, w))) by
          simp [hw, hzero])
    have hdq : H.Adj dummy qnode := by
      simpa [H, dummy, qnode, familyAuxAllowed] using
        (show (familyAuxGraph D).Adj (.inr (.inr (Q.1, w)))
            (.inr (.inl Q.1)) by
          exact ⟨rfl, hw, hzero⟩)
    exact fin_two_eq_of_ne_of_ne (coloring.valid hwd) (coloring.valid hdq)
  have hne_one (w : V) (hw : w ∈ Q.1.1.1)
      (hone : (D Q.1).color w = 1) :
      coloring ⟨.inl w, trivial⟩ ≠ coloring qnode := by
    apply coloring.valid
    simpa [H, qnode, familyAuxAllowed] using
      (show (familyAuxGraph D).Adj (.inl w) (.inr (.inl Q.1)) by
        simp [hw, hone])
  have hpieceNe : (D Q.1).color u ≠ (D Q.1).color v :=
    (D Q.1).color.valid huv
  change coloring ⟨.inl u, trivial⟩ ≠ coloring ⟨.inl v, trivial⟩
  rcases fin_two_eq_zero_or_one ((D Q.1).color u) with hu0 | hu1 <;>
    rcases fin_two_eq_zero_or_one ((D Q.1).color v) with hv0 | hv1
  · exact (hpieceNe (hu0.trans hv0.symm)).elim
  · have hcu := heq_zero u hu hu0
    have hcv := hne_one v hv hv1
    intro h
    exact hcv (h.symm.trans hcu)
  · have hcu := hne_one u hu hu1
    have hcv := heq_zero v hv hv0
    intro h
    exact hcu (h.trans hcv)
  · exact (hpieceNe (hu1.trans hv1.symm)).elim

/-- On every unselected piece, the auxiliary complement coloring and the
piece's own bipartition coloring induce the same equality relation.  The two
colorings may differ by swapping the names `0` and `1`. -/
lemma auxComplementColor_eq_iff_pieceColor_eq {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (Q : ↥(auxPiecesInWalk c)) (hQS : Q ∉ S)
    {u v : V} (hu : u ∈ Q.1.1.1) (hv : v ∈ Q.1.1.1) :
    (auxComplementColor c hc hcodd hminimal S hS u =
        auxComplementColor c hc hcodd hminimal S hS v ↔
      (D Q.1).color u = (D Q.1).color v) := by
  classical
  let B := auxComplementUnderlying c S
  let H := (familyAuxGraph D).induce {x | familyAuxAllowed B x}
  let coloring : H.Coloring (Fin 2) := Classical.choice
    (familyAuxComplement_colorable_two c hc hcodd hminimal S hS)
  have hQnotUnderlying : Q.1 ∉ auxSelectedUnderlying S := by
    intro hQ
    rw [mem_auxSelectedUnderlying_iff] at hQ
    exact hQS (by simpa using hQ.choose_spec)
  have hQB : Q.1 ∈ B :=
    Finset.mem_sdiff.mpr ⟨Q.2, hQnotUnderlying⟩
  let qnode : {x | familyAuxAllowed B x} :=
    ⟨.inr (.inl Q.1), by simpa [familyAuxAllowed] using hQB⟩
  have heq_zero (w : V) (hw : w ∈ Q.1.1.1)
      (hzero : (D Q.1).color w = 0) :
      coloring ⟨.inl w, trivial⟩ = coloring qnode := by
    let dummy : {x | familyAuxAllowed B x} :=
      ⟨.inr (.inr (Q.1, w)), by simpa [familyAuxAllowed] using hQB⟩
    have hwd : H.Adj ⟨.inl w, trivial⟩ dummy := by
      simpa [H, dummy, familyAuxAllowed] using
        (show (familyAuxGraph D).Adj (.inl w) (.inr (.inr (Q.1, w))) by
          simp [hw, hzero])
    have hdq : H.Adj dummy qnode := by
      simpa [H, dummy, qnode, familyAuxAllowed] using
        (show (familyAuxGraph D).Adj (.inr (.inr (Q.1, w)))
            (.inr (.inl Q.1)) by
          exact ⟨rfl, hw, hzero⟩)
    exact fin_two_eq_of_ne_of_ne (coloring.valid hwd) (coloring.valid hdq)
  have hne_one (w : V) (hw : w ∈ Q.1.1.1)
      (hone : (D Q.1).color w = 1) :
      coloring ⟨.inl w, trivial⟩ ≠ coloring qnode := by
    apply coloring.valid
    simpa [H, qnode, familyAuxAllowed] using
      (show (familyAuxGraph D).Adj (.inl w) (.inr (.inl Q.1)) by
        simp [hw, hone])
  change coloring ⟨.inl u, trivial⟩ = coloring ⟨.inl v, trivial⟩ ↔
    (D Q.1).color u = (D Q.1).color v
  rcases fin_two_eq_zero_or_one ((D Q.1).color u) with hu0 | hu1 <;>
    rcases fin_two_eq_zero_or_one ((D Q.1).color v) with hv0 | hv1
  · constructor
    · intro _
      exact hu0.trans hv0.symm
    · intro _
      exact (heq_zero u hu hu0).trans (heq_zero v hv hv0).symm
  · constructor
    · intro huvColor
      exact (hne_one v hv hv1
        (huvColor.symm.trans (heq_zero u hu hu0))).elim
    · intro huvPiece
      exact ((by decide : (0 : Fin 2) ≠ 1)
        (hu0.symm.trans (huvPiece.trans hv1))).elim
  · constructor
    · intro huvColor
      exact (hne_one u hu hu1
        (huvColor.trans (heq_zero v hv hv0))).elim
    · intro huvPiece
      exact ((by decide : (0 : Fin 2) ≠ 1)
        (hv0.symm.trans (huvPiece.symm.trans hu1))).elim
  · constructor
    · intro _
      exact hu1.trans hv1.symm
    · intro _
      exact fin_two_eq_of_ne_of_ne
        (hne_one u hu hu1) (hne_one v hv hv1).symm

noncomputable def auxComplementGraphColoring {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty) :
    (auxComplementGraph c S).Coloring (Fin 2) := by
  classical
  refine SimpleGraph.Coloring.mk
    (auxComplementColor c hc hcodd hminimal S hS) ?_
  intro u v huv
  obtain ⟨P, hPF, hPuv⟩ := exists_piece_adj_of_packedUnion_adj huv
  rw [auxComplementPackedFamily] at hPF
  obtain ⟨Q, hQB, hQP⟩ := Finset.mem_image.mp hPF
  subst P
  rw [auxComplementUnderlying, Finset.mem_sdiff] at hQB
  let Q' : ↥(auxPiecesInWalk c) := ⟨Q, hQB.1⟩
  have hQnotS : Q' ∉ S := by
    intro hQS
    apply hQB.2
    rw [mem_auxSelectedUnderlying_iff]
    exact ⟨hQB.1, by simpa [Q'] using hQS⟩
  have hmem := hcarrier Q hPuv
  exact auxComplementColor_ne_of_piece_adj c hc hcodd hminimal S hS
    Q' hQnotS hmem.1 hmem.2 hPuv

/-- A proof-independent, total choice of a two-coloring on the auxiliary
complement.  When the complement is colorable this chooses such a coloring;
otherwise it is the constant zero label.  Minimality will always put us in
the first branch, but keeping the definition total lets the trimming sets be
defined without carrying proof arguments. -/
noncomputable def auxCanonicalComplementColor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (S : Finset ↥(auxPiecesInWalk c)) : V → Fin 2 := by
  classical
  exact if h : ((familyAuxGraph D).induce
      {x | familyAuxAllowed (auxComplementUnderlying c S) x}).Colorable 2 then
    let coloring : ((familyAuxGraph D).induce
        {x | familyAuxAllowed (auxComplementUnderlying c S) x}).Coloring (Fin 2) :=
      Classical.choice h
    fun v => coloring ⟨.inl v, trivial⟩
  else fun _ => 0

lemma auxCanonicalComplementColor_eq {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty) :
    auxCanonicalComplementColor c S =
      auxComplementColor c hc hcodd hminimal S hS := by
  classical
  let hcol := familyAuxComplement_colorable_two c hc hcodd hminimal S hS
  unfold auxCanonicalComplementColor
  rw [dif_pos hcol]
  rfl

lemma auxCanonicalComplementColor_eq_iff_pieceColor_eq
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (Q : ↥(auxPiecesInWalk c)) (hQS : Q ∉ S)
    {u v : V} (hu : u ∈ Q.1.1.1) (hv : v ∈ Q.1.1.1) :
    (auxCanonicalComplementColor c S u =
        auxCanonicalComplementColor c S v ↔
      (D Q.1).color u = (D Q.1).color v) := by
  rw [auxCanonicalComplementColor_eq c hc hcodd hminimal S hS]
  exact auxComplementColor_eq_iff_pieceColor_eq
    c hc hcodd hminimal S hS Q hQS hu hv

noncomputable def auxCanonicalComplementGraphColoring {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty) :
    (auxComplementGraph c S).Coloring (Fin 2) := by
  let old := auxComplementGraphColoring c hc hcodd hminimal hcarrier S hS
  refine SimpleGraph.Coloring.mk (auxCanonicalComplementColor c S) ?_
  intro u v huv
  rw [auxCanonicalComplementColor_eq c hc hcodd hminimal S hS]
  exact old.valid huv

@[simp] lemma auxCanonicalComplementGraphColoring_apply {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty) (v : V) :
    auxCanonicalComplementGraphColoring c hc hcodd hminimal hcarrier S hS v =
      auxCanonicalComplementColor c S v := rfl

/-- Numerical length assigned to the complementary (fixed) pieces of a
selected variable class. -/
noncomputable def auxSelectedFixedLength {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) : ℕ :=
  ∑ P ∈ (Finset.univ : Finset ↥(auxPiecesInWalk c)) \ S,
    parityStart (D P.1).base
      ((D P.1).residue (auxPieceLeft c hc hcodd P)
        (auxPieceRight c hc hcodd P))

lemma auxSelectedFixedLength_weight {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c))
    (hweight :
      (∑ P : ↥(auxPiecesInWalk c), ((D P.1).base + 1)) ≤
        3 * ∑ P ∈ S, ((D P.1).base + 1)) :
    auxSelectedFixedLength c hc hcodd S +
        (∑ P ∈ S, ((D P.1).base + 1)) ≤
      3 * ∑ P ∈ S, ((D P.1).base + 1) := by
  let C := (Finset.univ : Finset ↥(auxPiecesInWalk c)) \ S
  have hfixed : auxSelectedFixedLength c hc hcodd S ≤
      ∑ P ∈ C, ((D P.1).base + 1) := by
    unfold auxSelectedFixedLength
    apply Finset.sum_le_sum
    intro P hP
    exact (parityStart_bounds (D P.1).base
      ((D P.1).residue (auxPieceLeft c hc hcodd P)
        (auxPieceRight c hc hcodd P))).2
  have hpartition :
      (∑ P ∈ C, ((D P.1).base + 1)) +
          (∑ P ∈ S, ((D P.1).base + 1)) =
        ∑ P : ↥(auxPiecesInWalk c), ((D P.1).base + 1) := by
    simpa [C] using (Finset.sum_sdiff (f := fun P : ↥(auxPiecesInWalk c) =>
      (D P.1).base + 1) (Finset.subset_univ S))
  calc
    auxSelectedFixedLength c hc hcodd S +
        (∑ P ∈ S, ((D P.1).base + 1)) ≤
      (∑ P ∈ C, ((D P.1).base + 1)) +
        ∑ P ∈ S, ((D P.1).base + 1) := Nat.add_le_add_right hfixed _
    _ = ∑ P : ↥(auxPiecesInWalk c), ((D P.1).base + 1) := hpartition
    _ ≤ 3 * ∑ P ∈ S, ((D P.1).base + 1) := hweight

lemma auxSelectedFixedLength_lower_odd {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) :
    Odd (auxSelectedFixedLength c hc hcodd S +
      ∑ P ∈ S, parityStart (D P.1).base
        ((D P.1).residue (auxPieceLeft c hc hcodd P)
          (auxPieceRight c hc hcodd P))) := by
  have hpartition : auxSelectedFixedLength c hc hcodd S +
      (∑ P ∈ S, parityStart (D P.1).base
        ((D P.1).residue (auxPieceLeft c hc hcodd P)
          (auxPieceRight c hc hcodd P))) =
      ∑ P : ↥(auxPiecesInWalk c), parityStart (D P.1).base
        ((D P.1).residue (auxPieceLeft c hc hcodd P)
          (auxPieceRight c hc hcodd P)) := by
    unfold auxSelectedFixedLength
    simpa using (Finset.sum_sdiff (f := fun P : ↥(auxPiecesInWalk c) =>
      parityStart (D P.1).base
        ((D P.1).residue (auxPieceLeft c hc hcodd P)
          (auxPieceRight c hc hcodd P))) (Finset.subset_univ S))
  rw [hpartition]
  exact odd_sum_parityStart_auxPieces c hc hcodd

/-! ### Canonical paths attached to a minimal auxiliary piece cycle -/

/-- The parity-adjusted lower endpoint in a piece of the auxiliary cycle is
realized by a canonical simple path in that piece.  Keeping this path in the
piece graph (rather than immediately mapping it to the ambient graph) makes
its carrier and edge-disjointness information available to the later
trimming construction. -/
noncomputable def auxPieceLowerPath {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (P : ↥(auxPiecesInWalk c)) :
    P.1.1.2.Walk (auxPieceLeft c hc hcodd P)
      (auxPieceRight c hc hcodd P) :=
  Classical.choose ((D P.1).exists_parityStart_path hT
    (auxPieceLeft_mem c hc hcodd P) (auxPieceRight_mem c hc hcodd P)
    (auxPieceLeft_ne_right c hc hcodd P))

lemma auxPieceLowerPath_isPath {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (P : ↥(auxPiecesInWalk c)) :
    (auxPieceLowerPath c hc hcodd hT P).IsPath :=
  (Classical.choose_spec ((D P.1).exists_parityStart_path hT
    (auxPieceLeft_mem c hc hcodd P) (auxPieceRight_mem c hc hcodd P)
    (auxPieceLeft_ne_right c hc hcodd P))).1

lemma auxPieceLowerPath_length {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (P : ↥(auxPiecesInWalk c)) :
    (auxPieceLowerPath c hc hcodd hT P).length =
      parityStart (D P.1).base
        ((D P.1).residue (auxPieceLeft c hc hcodd P)
          (auxPieceRight c hc hcodd P)) :=
  (Classical.choose_spec ((D P.1).exists_parityStart_path hT
    (auxPieceLeft_mem c hc hcodd P) (auxPieceRight_mem c hc hcodd P)
    (auxPieceLeft_ne_right c hc hcodd P))).2.1

lemma auxPieceLowerPath_support_subset {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (P : ↥(auxPiecesInWalk c)) :
    ∀ x ∈ (auxPieceLowerPath c hc hcodd hT P).support, x ∈ P.1.1.1 :=
  (Classical.choose_spec ((D P.1).exists_parityStart_path hT
    (auxPieceLeft_mem c hc hcodd P) (auxPieceRight_mem c hc hcodd P)
    (auxPieceLeft_ne_right c hc hcodd P))).2.2

/-- The same canonical path, regarded as a path in the union of every packed
piece. -/
noncomputable def auxPieceLowerPathInUnion {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (P : ↥(auxPiecesInWalk c)) :
    (packedUnion A).Walk (auxPieceLeft c hc hcodd P)
      (auxPieceRight c hc hcodd P) :=
  (auxPieceLowerPath c hc hcodd hT P).mapLe (le_packedUnion P.1.2)

lemma auxPieceLowerPathInUnion_isPath {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (P : ↥(auxPiecesInWalk c)) :
    (auxPieceLowerPathInUnion c hc hcodd hT P).IsPath := by
  exact (auxPieceLowerPath_isPath c hc hcodd hT P).mapLe
    (le_packedUnion P.1.2)

@[simp] lemma auxPieceLowerPathInUnion_length {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (P : ↥(auxPiecesInWalk c)) :
    (auxPieceLowerPathInUnion c hc hcodd hT P).length =
      parityStart (D P.1).base
        ((D P.1).residue (auxPieceLeft c hc hcodd P)
          (auxPieceRight c hc hcodd P)) := by
  rw [auxPieceLowerPathInUnion, SimpleGraph.Walk.length_mapLe]
  exact auxPieceLowerPath_length c hc hcodd hT P

lemma auxPieceLowerPathInUnion_support_subset {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (P : ↥(auxPiecesInWalk c)) :
    ∀ x ∈ (auxPieceLowerPathInUnion c hc hcodd hT P).support,
      x ∈ P.1.1.1 := by
  intro x hx
  rw [auxPieceLowerPathInUnion,
    SimpleGraph.Walk.support_mapLe_eq_support] at hx
  exact auxPieceLowerPath_support_subset c hc hcodd hT P x hx

lemma auxSelectedPieceGroup_tail_ne_nil {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) : (auxSelectedPieceGroup c hc S hS P).tail ≠ [] :=
  auxPieceGroup_tail_ne_nil c hc hcodd S hS hpair
    (auxSelectedPieceGroup_mem c hc S hS P)

lemma auxSelectedPieceGroup_tail_isChain {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (P : ↥S) :
    (auxSelectedPieceGroup c hc S hS P).tail.IsChain
      (fun Q R => auxPieceRight c hc hcodd Q =
        auxPieceLeft c hc hcodd R) :=
  (auxPieceGroup_isChain c hc hcodd S hS
    (auxSelectedPieceGroup_mem c hc S hS P)).tail

/-- The first complementary piece following a selected group head is its
actual cyclic successor. -/
lemma auxSelectedPieceGroup_tail_head_eq_successor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    (auxSelectedPieceGroup c hc S hS P).tail.head
        (auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P) =
      auxPieceSuccessor c hc P.1 := by
  classical
  let R := auxRotatedPieceOrder c hc S hS
  let g := auxSelectedPieceGroup c hc S hS P
  have hgmem := auxSelectedPieceGroup_mem c hc S hS P
  have hgne := auxPieceGroup_ne_nil c hc S hS hgmem
  have htail := auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P
  let Q := g.tail.head htail
  have hgshape : g = P.1 :: Q :: g.tail.tail := by
    calc
      g = g.head hgne :: g.tail := (List.cons_head_tail hgne).symm
      _ = P.1 :: g.tail := by rw [auxSelectedPieceGroup_head]
      _ = P.1 :: Q :: g.tail.tail := by
        rw [List.cons_head_tail htail]
  have hinfix : g <:+: R := by
    change g <:+: auxRotatedPieceOrder c hc S hS
    rw [← auxPieceGroups_flatten c hc S hS]
    exact List.infix_of_mem_flatten hgmem
  obtain ⟨pre, post, hR⟩ := hinfix
  have hshape : R = pre ++ P.1 :: Q :: (g.tail.tail ++ post) := by
    rw [← hR, hgshape]
    simp only [List.append_assoc, List.cons_append, List.tail_cons]
  have hPR : P.1 ∈ R := mem_auxRotatedPieceOrder c hc S hS P.1
  have hnext : R.next P.1 hPR = Q := by
    exact (list_next_eq_of_eq hshape P.1 hPR (by simp)).trans
      (list_next_of_append_cons_cons pre (g.tail.tail ++ post) P.1 Q (by
        simpa only [← hshape] using auxRotatedPieceOrder_nodup c hc S hS))
  change Q = auxPieceSuccessor c hc P.1
  exact hnext.symm.trans (auxRotatedPieceOrder_next_eq_successor c hc S hS P.1 hPR)

/-- The last complementary piece in a selected block has the next selected
piece as its actual cyclic successor. -/
lemma auxSelectedPieceGroup_tail_last_successor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    auxPieceSuccessor c hc
        ((auxSelectedPieceGroup c hc S hS P).tail.getLast
          (auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P)) =
      auxSelectedNextPiece c hc S hS P := by
  let g := auxSelectedPieceGroup c hc S hS P
  have hgmem := auxSelectedPieceGroup_mem c hc S hS P
  have hgne := auxPieceGroup_ne_nil c hc S hS hgmem
  have htail := auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P
  let L := g.tail.getLast htail
  have hlast : L = g.getLast hgne := list_getLast_tail_eq_getLast htail
  have hLR : L ∈ auxRotatedPieceOrder c hc S hS := by
    rw [hlast, ← auxPieceGroups_flatten c hc S hS]
    exact List.mem_flatten.mpr ⟨g, hgmem, List.getLast_mem hgne⟩
  change auxPieceSuccessor c hc L = auxSelectedNextPiece c hc S hS P
  rw [hlast]
  unfold auxSelectedNextPiece
  exact (auxRotatedPieceOrder_next_eq_successor c hc S hS (g.getLast hgne)
    (by simpa only [← hlast] using hLR)).symm

/-- The first complementary piece begins at the outgoing joint of the
selected head piece. -/
lemma auxSelectedPieceGroup_start_eq {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    auxPieceRight c hc hcodd P.1 =
      auxPieceLeft c hc hcodd
        ((auxSelectedPieceGroup c hc S hS P).tail.head
          (auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P)) := by
  let g := auxSelectedPieceGroup c hc S hS P
  have hgmem := auxSelectedPieceGroup_mem c hc S hS P
  have hgne := auxPieceGroup_ne_nil c hc S hS hgmem
  have hhead := auxSelectedPieceGroup_head c hc S hS P
  have htail := auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P
  have hchain := auxPieceGroup_isChain c hc hcodd S hS hgmem
  cases hg : g with
  | nil => exact (hgne hg).elim
  | cons a rest =>
      cases hrest : rest with
      | nil =>
          have : g.tail = [] := by simp [hg, hrest]
          exact (htail this).elim
      | cons b rest' =>
          have hab : auxPieceRight c hc hcodd a =
              auxPieceLeft c hc hcodd b := by
            change g.IsChain (fun Q R => auxPieceRight c hc hcodd Q =
              auxPieceLeft c hc hcodd R) at hchain
            rw [hg, hrest] at hchain
            exact (List.isChain_cons_cons.mp hchain).1
          have ha : a = P.1 := by
            simpa [g, hg] using hhead
          simpa [g, hg, hrest, ha] using hab

/-- The last complementary piece ends at the incoming joint of the next
selected piece. -/
lemma auxSelectedPieceGroup_end_eq {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    auxPieceRight c hc hcodd
        ((auxSelectedPieceGroup c hc S hS P).tail.getLast
          (auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P)) =
      auxPieceLeft c hc hcodd (auxSelectedNextPiece c hc S hS P) := by
  let g := auxSelectedPieceGroup c hc S hS P
  have hgmem := auxSelectedPieceGroup_mem c hc S hS P
  have hgne := auxPieceGroup_ne_nil c hc S hS hgmem
  have htail := auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P
  let L := g.getLast hgne
  have hLR : L ∈ auxRotatedPieceOrder c hc S hS := by
    rw [← auxPieceGroups_flatten c hc S hS]
    exact List.mem_flatten.mpr ⟨g, hgmem, List.getLast_mem hgne⟩
  have hnext : auxSelectedNextPiece c hc S hS P =
      auxPieceSuccessor c hc L := by
    unfold auxSelectedNextPiece
    exact auxRotatedPieceOrder_next_eq_successor c hc S hS L hLR
  have hlast : g.tail.getLast htail = L := by
    exact list_getLast_tail_eq_getLast htail
  rw [hlast, hnext]
  exact auxPieceRight_eq_left_successor c hc hcodd L

/-- If a selected block does not wrap directly back to its own head, then a
piece in that block's complementary tail can meet the head carrier only when
it is the first tail piece.  Minimality gives degree at most two in the
carrier-overlap graph; the cyclic predecessor belongs to the preceding
selected block and is therefore excluded by disjointness of the groups. -/
lemma auxSelectedPieceGroup_tail_overlap_head_eq_first
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcard : 3 ≤ (auxPiecesInWalk c).card)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) (hnext : auxSelectedNextPiece c hc S hS P ≠ P.1)
    {Q : ↥(auxPiecesInWalk c)}
    (hQtail : Q ∈ (auxSelectedPieceGroup c hc S hS P).tail)
    {v : V} (hvQ : v ∈ Q.1.1.1) (hvP : v ∈ P.1.1.1.1) :
    Q = (auxSelectedPieceGroup c hc S hS P).tail.head
      (auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P) := by
  classical
  let R := auxSelectedGroupPredecessor c hc S hS P
  let gP := auxSelectedPieceGroup c hc S hS P
  let gR := auxSelectedPieceGroup c hc S hS R
  have hRP : R ≠ P := by
    intro h
    have hsucc := congrArg Subtype.val
      (auxSelectedGroupSuccessor_predecessor c hc S hS P)
    change auxSelectedNextPiece c hc S hS R = P.1 at hsucc
    rw [h] at hsucc
    exact hnext hsucc
  have hgdisj : List.Disjoint gR gP :=
    auxSelectedPieceGroups_disjoint c hc S hS hRP
  have htP := auxSelectedPieceGroup_tail_ne_nil
    c hc hcodd S hS hpair P
  have htR := auxSelectedPieceGroup_tail_ne_nil
    c hc hcodd S hS hpair R
  let B := gP.tail.head htP
  let Ap := gR.tail.getLast htR
  have hBmem : B ∈ gP.tail := List.head_mem htP
  have hAmem : Ap ∈ gR.tail := List.getLast_mem htR
  have hsuccP : auxPieceSuccessor c hc P.1 = B :=
    (auxSelectedPieceGroup_tail_head_eq_successor
      c hc hcodd S hS hpair P).symm
  have hnextR : auxSelectedNextPiece c hc S hS R = P.1 :=
    congrArg Subtype.val
      (auxSelectedGroupSuccessor_predecessor c hc S hS P)
  have hsuccA : auxPieceSuccessor c hc Ap = P.1 :=
    (auxSelectedPieceGroup_tail_last_successor
      c hc hcodd S hS hpair R).trans hnextR
  have hAprev : Ap = auxPiecePredecessor c hc P.1 := by
    apply auxPieceSuccessor_injective c hc
    exact hsuccA.trans (auxPieceSuccessor_predecessor c hc P.1).symm
  have hQneP : Q ≠ P.1 := by
    intro h
    have hQS : Q ∈ S := by simpa [h] using P.2
    exact (auxPieceGroup_tail_not_mem c hc S hS
      (auxSelectedPieceGroup_mem c hc S hS P) Q hQtail) hQS
  have hneighbors := auxPiecePredecessor_ne_successor_of_three_le_card
    c hc hcodd hcard P.1
  have hcases := overlapping_piece_eq_predecessor_or_successor
    c hc hcodd hminimal P.1 Q hneighbors hQneP v hvQ hvP
  have hQneA : Q ≠ Ap := by
    intro h
    exact (List.disjoint_left.mp hgdisj
      (List.mem_of_mem_tail hAmem)
      (by simpa [h] using List.mem_of_mem_tail hQtail))
  rcases hcases with hprev | hsucc
  · exact (hQneA (hprev.trans hAprev.symm)).elim
  · exact hsucc.trans hsuccP

/-- Symmetrically, a complementary piece in a non-wrapping selected block
can meet the next selected carrier only when it is the last tail piece. -/
lemma auxSelectedPieceGroup_tail_overlap_next_eq_last
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcard : 3 ≤ (auxPiecesInWalk c).card)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) (hnext : auxSelectedNextPiece c hc S hS P ≠ P.1)
    {Q : ↥(auxPiecesInWalk c)}
    (hQtail : Q ∈ (auxSelectedPieceGroup c hc S hS P).tail)
    {v : V} (hvQ : v ∈ Q.1.1.1)
    (hvNext : v ∈ (auxSelectedNextPiece c hc S hS P).1.1.1) :
    Q = (auxSelectedPieceGroup c hc S hS P).tail.getLast
      (auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P) := by
  classical
  let N := auxSelectedGroupSuccessor c hc S hS P
  let gP := auxSelectedPieceGroup c hc S hS P
  let gN := auxSelectedPieceGroup c hc S hS N
  have hPN : P ≠ N := by
    intro h
    apply hnext
    have hval := congrArg Subtype.val h
    exact hval.symm
  have hgdisj : List.Disjoint gP gN :=
    auxSelectedPieceGroups_disjoint c hc S hS hPN
  have htP := auxSelectedPieceGroup_tail_ne_nil
    c hc hcodd S hS hpair P
  have htN := auxSelectedPieceGroup_tail_ne_nil
    c hc hcodd S hS hpair N
  let Ap := gP.tail.getLast htP
  let B := gN.tail.head htN
  have hAmem : Ap ∈ gP.tail := List.getLast_mem htP
  have hBmem : B ∈ gN.tail := List.head_mem htN
  have hsuccA : auxPieceSuccessor c hc Ap = N.1 := by
    exact auxSelectedPieceGroup_tail_last_successor c hc hcodd S hS hpair P
  have hAprev : Ap = auxPiecePredecessor c hc N.1 := by
    apply auxPieceSuccessor_injective c hc
    exact hsuccA.trans (auxPieceSuccessor_predecessor c hc N.1).symm
  have hsuccN : auxPieceSuccessor c hc N.1 = B :=
    (auxSelectedPieceGroup_tail_head_eq_successor
      c hc hcodd S hS hpair N).symm
  have hQneN : Q ≠ N.1 := by
    intro h
    have hQS : Q ∈ S := by simpa [h] using N.2
    exact (auxPieceGroup_tail_not_mem c hc S hS
      (auxSelectedPieceGroup_mem c hc S hS P) Q hQtail) hQS
  have hneighbors := auxPiecePredecessor_ne_successor_of_three_le_card
    c hc hcodd hcard N.1
  have hcases := overlapping_piece_eq_predecessor_or_successor
    c hc hcodd hminimal N.1 Q hneighbors hQneN _ hvQ (by
      change v ∈ N.1.1.1.1
      exact hvNext)
  have hQneB : Q ≠ B := by
    intro h
    exact (List.disjoint_left.mp hgdisj
      (List.mem_of_mem_tail hQtail)
      (by simpa [h] using List.mem_of_mem_tail hBmem))
  rcases hcases with hprev | hsucc
  · exact hprev.trans hAprev.symm
  · exact (hQneB (hsucc.trans hsuccN)).elim

/-- If the successor of a complementary tail piece is selected, that tail
piece is the last one in its block and the selected successor is the next
block head. -/
lemma auxPieceGroup_selected_successor_eq_selectedNext
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) {R : ↥(auxPiecesInWalk c)}
    (hRtail : R ∈ (auxSelectedPieceGroup c hc S hS P).tail)
    (hsuccS : auxPieceSuccessor c hc R ∈ S) :
    auxPieceSuccessor c hc R = auxSelectedNextPiece c hc S hS P := by
  classical
  let g := auxSelectedPieceGroup c hc S hS P
  have hg := auxSelectedPieceGroup_mem c hc S hS P
  have hgne := auxPieceGroup_ne_nil c hc S hS hg
  have htne := auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P
  have hRmem : R ∈ g := List.mem_of_mem_tail hRtail
  obtain ⟨pre, post, hgshape⟩ := List.mem_iff_append.mp hRmem
  cases post with
  | nil =>
      have hRlast : R = g.tail.getLast htne := by
        have hlastG : R = g.getLast hgne := by
          have hlast := List.getLast_congr hgne (by simp) hgshape
          simpa using hlast.symm
        exact hlastG.trans (list_getLast_tail_eq_getLast htne).symm
      rw [hRlast]
      exact auxSelectedPieceGroup_tail_last_successor
        c hc hcodd S hS hpair P
  | cons U us =>
      let O := auxRotatedPieceOrder c hc S hS
      have hginfix : g <:+: O := by
        change g <:+: auxRotatedPieceOrder c hc S hS
        rw [← auxPieceGroups_flatten c hc S hS]
        exact List.infix_of_mem_flatten hg
      obtain ⟨outerPre, outerPost, hO⟩ := hginfix
      have hshape : O = (outerPre ++ pre) ++ R :: U :: (us ++ outerPost) := by
        rw [← hO, hgshape]
        simp [List.append_assoc]
      have hRO : R ∈ O := by rw [hshape]; simp
      have hnext : O.next R hRO = U :=
        (list_next_eq_of_eq hshape R hRO (by simp)).trans
          (list_next_of_append_cons_cons (outerPre ++ pre)
            (us ++ outerPost) R U (by
              simpa only [← hshape] using auxRotatedPieceOrder_nodup c hc S hS))
      have hsuccU : auxPieceSuccessor c hc R = U :=
        (auxRotatedPieceOrder_next_eq_successor c hc S hS R hRO).symm.trans hnext
      have hUtail : U ∈ g.tail := by
        cases pre <;> simp [hgshape]
      have hUnot := auxPieceGroup_tail_not_mem c hc S hS hg U hUtail
      exact (hUnot (hsuccU ▸ hsuccS)).elim

/-- Concatenation of the canonical lower paths through all complementary
pieces following a selected piece. -/
noncomputable def auxComplementaryRawWalk {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    (packedUnion A).Walk (auxPieceRight c hc hcodd P.1)
      (auxPieceLeft c hc hcodd (auxSelectedNextPiece c hc S hS P)) :=
  let l := (auxSelectedPieceGroup c hc S hS P).tail
  let hne := auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P
  let hchain := auxSelectedPieceGroup_tail_isChain c hc hcodd S hS P
  let w := appendWalkList
    (auxPieceLeft c hc hcodd) (auxPieceRight c hc hcodd)
    (auxPieceLowerPathInUnion c hc hcodd hT) l hne hchain
  w.copy (auxSelectedPieceGroup_start_eq c hc hcodd S hS hpair P).symm
    (auxSelectedPieceGroup_end_eq c hc hcodd S hS hpair P)

@[simp] lemma auxComplementaryRawWalk_length {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length =
      ((auxSelectedPieceGroup c hc S hS P).tail.map fun Q =>
        parityStart (D Q.1).base
          ((D Q.1).residue (auxPieceLeft c hc hcodd Q)
            (auxPieceRight c hc hcodd Q))).sum := by
  simp [auxComplementaryRawWalk, appendWalkList_length]

lemma auxComplementaryRawWalk_support_subset {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    ∀ x ∈ (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).support,
      ∃ Q ∈ (auxSelectedPieceGroup c hc S hS P).tail, x ∈ Q.1.1.1 := by
  intro x hx
  have hx' := appendWalkList_support_subset
    (auxPieceLeft c hc hcodd) (auxPieceRight c hc hcodd)
    (auxPieceLowerPathInUnion c hc hcodd hT)
    (auxSelectedPieceGroup c hc S hS P).tail
    (auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P)
    (auxSelectedPieceGroup_tail_isChain c hc hcodd S hS P) x
  have hxw : x ∈ (appendWalkList
      (auxPieceLeft c hc hcodd) (auxPieceRight c hc hcodd)
      (auxPieceLowerPathInUnion c hc hcodd hT)
      (auxSelectedPieceGroup c hc S hS P).tail
      (auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P)
      (auxSelectedPieceGroup_tail_isChain c hc hcodd S hS P)).support := by
    simpa [auxComplementaryRawWalk] using hx
  obtain ⟨Q, hQl, hxQ⟩ := hx' hxw
  exact ⟨Q, hQl, auxPieceLowerPathInUnion_support_subset
    c hc hcodd hT Q x hxQ⟩

lemma auxComplementaryRawWalk_edges_subset {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    ∀ e ∈ (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).edges,
      ∃ Q ∈ (auxSelectedPieceGroup c hc S hS P).tail,
        e ∈ (auxPieceLowerPathInUnion c hc hcodd hT Q).edges := by
  intro e he
  have he' := appendWalkList_edges_subset
    (auxPieceLeft c hc hcodd) (auxPieceRight c hc hcodd)
    (auxPieceLowerPathInUnion c hc hcodd hT)
    (auxSelectedPieceGroup c hc S hS P).tail
    (auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P)
    (auxSelectedPieceGroup_tail_isChain c hc hcodd S hS P) e
  have hew : e ∈ (appendWalkList
      (auxPieceLeft c hc hcodd) (auxPieceRight c hc hcodd)
      (auxPieceLowerPathInUnion c hc hcodd hT)
      (auxSelectedPieceGroup c hc S hS P).tail
      (auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P)
      (auxSelectedPieceGroup_tail_isChain c hc hcodd S hS P)).edges := by
    simpa [auxComplementaryRawWalk] using he
  exact he' hew

lemma auxComplementaryRawWalk_edges_in_complement {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    ∀ e ∈ (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).edges,
      e ∈ (auxComplementGraph c S).edgeSet := by
  classical
  intro e he
  obtain ⟨Q, hQg, heQ⟩ := auxComplementaryRawWalk_edges_subset
    c hc hcodd hT S hS hpair P e he
  have hQfam : Q.1.1 ∈ auxComplementPackedFamily c S :=
    mem_auxComplementPackedFamily_of_mem_tail c hc S hS
      (auxSelectedPieceGroup_mem c hc S hS P) hQg
  have heQ' : e ∈ (auxPieceLowerPath c hc hcodd hT Q).edges := by
    simpa [auxPieceLowerPathInUnion] using heQ
  have hePiece : e ∈ Q.1.1.2.edgeSet :=
    (auxPieceLowerPath c hc hcodd hT Q).edges_subset_edgeSet heQ'
  exact (by
    simpa [auxComplementGraph] using
      (SimpleGraph.edgeSet_mono (le_packedUnion hQfam) hePiece))

noncomputable def auxComplementaryRawWalkInComplement {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    (auxComplementGraph c S).Walk (auxPieceRight c hc hcodd P.1)
      (auxPieceLeft c hc hcodd (auxSelectedNextPiece c hc S hS P)) :=
  (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).transfer
    (auxComplementGraph c S)
    (auxComplementaryRawWalk_edges_in_complement
      c hc hcodd hT S hS hpair P)

noncomputable def auxComplementaryPathInComplement {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    (auxComplementGraph c S).Walk (auxPieceRight c hc hcodd P.1)
      (auxPieceLeft c hc hcodd (auxSelectedNextPiece c hc S hS P)) :=
  (auxComplementaryRawWalkInComplement c hc hcodd hT S hS hpair P).bypass

lemma auxComplementaryPathInComplement_support_subset_raw {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    ∀ x ∈ (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P).support,
      x ∈ (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).support := by
  intro x hx
  have hsub :=
    (auxComplementaryRawWalkInComplement c hc hcodd hT S hS hpair P).support_bypass_subset_support
  have hx' := hsub hx
  simpa [auxComplementaryPathInComplement,
    auxComplementaryRawWalkInComplement, SimpleGraph.Walk.support_transfer] using hx'

lemma auxComplementaryPathInComplement_isPath {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P).IsPath :=
  (auxComplementaryRawWalkInComplement c hc hcodd hT S hS hpair P).bypass_isPath

lemma auxComplementaryPathInComplement_length_le {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P).length ≤
      (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length := by
  exact (SimpleGraph.Walk.length_bypass_le_length
    (auxComplementaryRawWalkInComplement c hc hcodd hT S hS hpair P)).trans_eq
      (by simp [auxComplementaryRawWalkInComplement])

lemma auxComplementaryPathInComplement_mod_two {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P).length % 2 =
      (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length % 2 := by
  let raw := auxComplementaryRawWalkInComplement c hc hcodd hT S hS hpair P
  let path := auxComplementaryPathInComplement c hc hcodd hT S hS hpair P
  let coloringFin := auxComplementGraphColoring c hc hcodd hminimal hcarrier S hS
  let coloring : (auxComplementGraph c S).Coloring Bool :=
    SimpleGraph.recolorOfEquiv (auxComplementGraph c S) finTwoEquiv coloringFin
  have hraw := coloring.even_length_iff_congr raw
  have hpath := coloring.even_length_iff_congr path
  have heven : Even path.length ↔ Even raw.length := hpath.trans hraw.symm
  rw [Nat.even_iff, Nat.even_iff] at heven
  have hp := Nat.mod_two_eq_zero_or_one path.length
  have hr := Nat.mod_two_eq_zero_or_one raw.length
  change path.length % 2 =
    (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length % 2
  calc
    path.length % 2 = raw.length % 2 := by omega
    _ = (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length % 2 := by
      simp [raw, auxComplementaryRawWalkInComplement]

noncomputable def auxConnectorStartSet {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (P : ↥S) : Finset V :=
  if auxSelectedNextPiece c hc S hS P = P.1 then
    {auxPieceRight c hc hcodd P.1}
  else P.1.1.1.1.filter fun v =>
    ((D P.1.1).color v =
        (D P.1.1).color (auxPieceRight c hc hcodd P.1)) ↔
      (auxCanonicalComplementColor c S v =
        auxCanonicalComplementColor c S (auxPieceRight c hc hcodd P.1))

noncomputable def auxConnectorEndSet {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (P : ↥S) : Finset V :=
  if auxSelectedNextPiece c hc S hS P = P.1 then
    (P.1.1.1.1.filter fun v =>
      ((D P.1.1).color v =
          (D P.1.1).color (auxPieceLeft c hc hcodd P.1)) ↔
        (auxCanonicalComplementColor c S v =
          auxCanonicalComplementColor c S (auxPieceLeft c hc hcodd P.1))).erase
      (auxPieceRight c hc hcodd P.1)
  else
    let Q := auxSelectedNextPiece c hc S hS P
    Q.1.1.1.filter fun v =>
      ((D Q.1).color v = (D Q.1).color (auxPieceLeft c hc hcodd Q)) ↔
        (auxCanonicalComplementColor c S v =
          auxCanonicalComplementColor c S (auxPieceLeft c hc hcodd Q))

lemma auxConnectorStart_mem {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (P : ↥S) : auxPieceRight c hc hcodd P.1 ∈
      auxConnectorStartSet c hc hcodd S hS P := by
  classical
  by_cases h : auxSelectedNextPiece c hc S hS P = P.1 <;>
    simp [auxConnectorStartSet, h, auxPieceRight_mem]

lemma auxConnectorEnd_mem {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (P : ↥S) :
    auxPieceLeft c hc hcodd (auxSelectedNextPiece c hc S hS P) ∈
      auxConnectorEndSet c hc hcodd S hS P := by
  classical
  by_cases h : auxSelectedNextPiece c hc S hS P = P.1
  · simp [auxConnectorEndSet, h, auxPieceLeft_ne_right,
      auxPieceLeft_mem]
  · simp [auxConnectorEndSet, h, auxPieceLeft_mem]

lemma auxConnectorStartSet_colorAgreement {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (P : ↥S) {v : V} (hv : v ∈ auxConnectorStartSet c hc hcodd S hS P) :
    ((D P.1.1).color v =
        (D P.1.1).color (auxPieceRight c hc hcodd P.1)) ↔
      (auxCanonicalComplementColor c S v =
        auxCanonicalComplementColor c S (auxPieceRight c hc hcodd P.1)) := by
  classical
  by_cases h : auxSelectedNextPiece c hc S hS P = P.1
  · have hv' : v = auxPieceRight c hc hcodd P.1 := by
      simpa [auxConnectorStartSet, h] using hv
    rw [hv']
    simp
  · have hvFilter : v ∈ P.1.1.1.1.filter fun w =>
        ((D P.1.1).color w =
            (D P.1.1).color (auxPieceRight c hc hcodd P.1)) ↔
          (auxCanonicalComplementColor c S w =
            auxCanonicalComplementColor c S (auxPieceRight c hc hcodd P.1)) := by
      simpa only [auxConnectorStartSet, h, if_false] using hv
    exact (Finset.mem_filter.mp hvFilter).2

lemma auxConnectorEndSet_colorAgreement {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (P : ↥S) {v : V} (hv : v ∈ auxConnectorEndSet c hc hcodd S hS P) :
    let Q := auxSelectedNextPiece c hc S hS P
    ((D Q.1).color v = (D Q.1).color (auxPieceLeft c hc hcodd Q)) ↔
      (auxCanonicalComplementColor c S v =
        auxCanonicalComplementColor c S (auxPieceLeft c hc hcodd Q)) := by
  classical
  by_cases h : auxSelectedNextPiece c hc S hS P = P.1
  · rw [h]
    have hvErase : v ∈ (P.1.1.1.1.filter fun w =>
        ((D P.1.1).color w = (D P.1.1).color (auxPieceLeft c hc hcodd P.1)) ↔
          (auxCanonicalComplementColor c S w =
            auxCanonicalComplementColor c S (auxPieceLeft c hc hcodd P.1))).erase
          (auxPieceRight c hc hcodd P.1) := by
      simpa only [auxConnectorEndSet, h, if_pos] using hv
    have hvFilter := Finset.mem_of_mem_erase hvErase
    have hvColor := (Finset.mem_filter.mp hvFilter).2
    exact hvColor
  · let Q := auxSelectedNextPiece c hc S hS P
    have hvFilter : v ∈ Q.1.1.1.filter fun w =>
        ((D Q.1).color w = (D Q.1).color (auxPieceLeft c hc hcodd Q)) ↔
          (auxCanonicalComplementColor c S w =
            auxCanonicalComplementColor c S (auxPieceLeft c hc hcodd Q)) := by
      simpa only [auxConnectorEndSet, h, if_false] using hv
    exact (Finset.mem_filter.mp hvFilter).2

lemma auxConnectorSets_disjoint {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    Disjoint (auxConnectorStartSet c hc hcodd S hS P)
      (auxConnectorEndSet c hc hcodd S hS P) := by
  classical
  by_cases h : auxSelectedNextPiece c hc S hS P = P.1
  · simp [auxConnectorStartSet, auxConnectorEndSet, h]
  · simp only [auxConnectorStartSet, auxConnectorEndSet, h, if_false]
    let Q : ↥S := ⟨auxSelectedNextPiece c hc S hS P,
      auxSelectedNextPiece_mem c hc S hS P⟩
    have hPQ : P.1 ≠ Q.1 := Ne.symm h
    exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (hpair P.2 Q.2 hPQ)

noncomputable def auxTrimmedConnector {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :=
  trimWalkBetween
    (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P)
    (fun x => x ∈ auxConnectorStartSet c hc hcodd S hS P)
    (fun x => x ∈ auxConnectorEndSet c hc hcodd S hS P)
    (auxConnectorStart_mem c hc hcodd S hS P)
    (auxConnectorEnd_mem c hc hcodd S hS P)

lemma auxTrimmedConnector_isPath {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    (auxTrimmedConnector c hc hcodd hT S hS hpair P).IsPath := by
  exact trimWalkBetween_isPath
    (auxComplementaryPathInComplement_isPath c hc hcodd hT S hS hpair P)
    _ _ _ _

lemma auxTrimmedConnector_pos {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) : 0 < (auxTrimmedConnector c hc hcodd hT S hS hpair P).length := by
  exact trimWalkBetween_pos_of_disjoint
    (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P)
    (auxConnectorStartSet c hc hcodd S hS P)
    (auxConnectorEndSet c hc hcodd S hS P)
    (auxConnectorStart_mem c hc hcodd S hS P)
    (auxConnectorEnd_mem c hc hcodd S hS P)
    (auxConnectorSets_disjoint c hc hcodd S hS hpair P)

lemma auxTrimmedConnector_length_le {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    (auxTrimmedConnector c hc hcodd hT S hS hpair P).length ≤
      (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length :=
  (trimWalkBetween_length_le
    (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P)
    _ _ _ _).trans
    (auxComplementaryPathInComplement_length_le c hc hcodd hT S hS hpair P)

lemma auxTrimmedConnector_vertex_in_group_tail {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    ∀ x ∈ (auxTrimmedConnector c hc hcodd hT S hS hpair P).support,
      ∃ Q ∈ (auxSelectedPieceGroup c hc S hS P).tail, x ∈ Q.1.1.1 := by
  intro x hx
  have hpath := trimWalkBetween_support_subset
    (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P)
    (fun y => y ∈ auxConnectorStartSet c hc hcodd S hS P)
    (fun y => y ∈ auxConnectorEndSet c hc hcodd S hS P)
    (auxConnectorStart_mem c hc hcodd S hS P)
    (auxConnectorEnd_mem c hc hcodd S hS P) x
  have hxPath : x ∈
      (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P).support := by
    exact hpath (by simpa [auxTrimmedConnector] using hx)
  have hxRaw := auxComplementaryPathInComplement_support_subset_raw
    c hc hcodd hT S hS hpair P x hxPath
  exact auxComplementaryRawWalk_support_subset
    c hc hcodd hT S hS hpair P x hxRaw

/-- In a non-wrapping selected block with at least three pieces, every
connector vertex that lies in the starting selected carrier belongs to the
start trimming set. -/
lemma auxTrimmedConnector_mem_startSet_of_mem_start_carrier
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcard : 3 ≤ (auxPiecesInWalk c).card) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) (hnext : auxSelectedNextPiece c hc S hS P ≠ P.1)
    {x : V} (hxSupport : x ∈
      (auxTrimmedConnector c hc hcodd hT S hS hpair P).support)
    (hxP : x ∈ P.1.1.1.1) :
    x ∈ auxConnectorStartSet c hc hcodd S hS P := by
  classical
  obtain ⟨Q, hQtail, hxQ⟩ :=
    auxTrimmedConnector_vertex_in_group_tail
      c hc hcodd hT S hS hpair P x hxSupport
  have hQfirst := auxSelectedPieceGroup_tail_overlap_head_eq_first
    c hc hcodd hminimal hcard S hS hpair P hnext hQtail hxQ hxP
  let B := (auxSelectedPieceGroup c hc S hS P).tail.head
    (auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P)
  have hQB : Q = B := hQfirst
  subst Q
  have hBtail : B ∈ (auxSelectedPieceGroup c hc S hS P).tail :=
    List.head_mem (auxSelectedPieceGroup_tail_ne_nil
      c hc hcodd S hS hpair P)
  have hBnotS : B ∉ S :=
    auxPieceGroup_tail_not_mem c hc S hS
      (auxSelectedPieceGroup_mem c hc S hS P) B hBtail
  let a := auxPieceRight c hc hcodd P.1
  have haP : a ∈ P.1.1.1.1 := auxPieceRight_mem c hc hcodd P.1
  have haB : a ∈ B.1.1.1 := by
    have hstart := auxSelectedPieceGroup_start_eq
      c hc hcodd S hS hpair P
    change auxPieceRight c hc hcodd P.1 ∈ B.1.1.1
    rw [hstart]
    exact auxPieceLeft_mem c hc hcodd B
  have hPB : P.1 ≠ B := by
    have hBsucc := auxSelectedPieceGroup_tail_head_eq_successor
      c hc hcodd S hS hpair P
    have hBsucc' : B = auxPieceSuccessor c hc P.1 := by
      exact hBsucc
    intro hPB
    exact auxPieceSuccessor_ne c hc hcodd P.1
      (hBsucc'.symm.trans hPB.symm)
  have hpiece := two_piece_color_relation_on_minimal_cycle
    c hc hcodd hminimal hcard P.1 B hPB a x haP haB hxP hxQ
  have hcomp := auxCanonicalComplementColor_eq_iff_pieceColor_eq
    c hc hcodd hminimal S hS B hBnotS hxQ haB
  simp only [auxConnectorStartSet, hnext, if_false, Finset.mem_filter]
  exact ⟨hxP, hpiece.trans hcomp.symm⟩

/-- The corresponding statement at the terminal selected carrier. -/
lemma auxTrimmedConnector_mem_endSet_of_mem_next_carrier
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcard : 3 ≤ (auxPiecesInWalk c).card) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) (hnext : auxSelectedNextPiece c hc S hS P ≠ P.1)
    {x : V} (hxSupport : x ∈
      (auxTrimmedConnector c hc hcodd hT S hS hpair P).support)
    (hxNext : x ∈ (auxSelectedNextPiece c hc S hS P).1.1.1) :
    x ∈ auxConnectorEndSet c hc hcodd S hS P := by
  classical
  obtain ⟨Q, hQtail, hxQ⟩ :=
    auxTrimmedConnector_vertex_in_group_tail
      c hc hcodd hT S hS hpair P x hxSupport
  have hQlast := auxSelectedPieceGroup_tail_overlap_next_eq_last
    c hc hcodd hminimal hcard S hS hpair P hnext hQtail hxQ hxNext
  let L := (auxSelectedPieceGroup c hc S hS P).tail.getLast
    (auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P)
  have hQL : Q = L := hQlast
  subst Q
  have hLtail : L ∈ (auxSelectedPieceGroup c hc S hS P).tail :=
    List.getLast_mem (auxSelectedPieceGroup_tail_ne_nil
      c hc hcodd S hS hpair P)
  have hLnotS : L ∉ S :=
    auxPieceGroup_tail_not_mem c hc S hS
      (auxSelectedPieceGroup_mem c hc S hS P) L hLtail
  let N := auxSelectedNextPiece c hc S hS P
  let a := auxPieceLeft c hc hcodd N
  have haN : a ∈ N.1.1.1 := auxPieceLeft_mem c hc hcodd N
  have haL : a ∈ L.1.1.1 := by
    have hend := auxSelectedPieceGroup_end_eq
      c hc hcodd S hS hpair P
    change auxPieceLeft c hc hcodd N ∈ L.1.1.1
    rw [← hend]
    exact auxPieceRight_mem c hc hcodd L
  have hNL : N ≠ L := by
    have hLsucc := auxSelectedPieceGroup_tail_last_successor
      c hc hcodd S hS hpair P
    have hLsucc' : auxPieceSuccessor c hc L = N := by
      exact hLsucc
    intro hNL
    exact auxPieceSuccessor_ne c hc hcodd L (hLsucc'.trans hNL)
  have hpiece := two_piece_color_relation_on_minimal_cycle
    c hc hcodd hminimal hcard N L hNL a x haN haL hxNext hxQ
  have hcomp := auxCanonicalComplementColor_eq_iff_pieceColor_eq
    c hc hcodd hminimal S hS L hLnotS hxQ haL
  simp only [auxConnectorEndSet, hnext, if_false, Finset.mem_filter]
  exact ⟨hxNext, hpiece.trans hcomp.symm⟩

lemma auxTrimmedConnector_tail_support_not_mem_start_carrier
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcard : 3 ≤ (auxPiecesInWalk c).card) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) (hnext : auxSelectedNextPiece c hc S hS P ≠ P.1) :
    ∀ x ∈ (auxTrimmedConnector c hc hcodd hT S hS hpair P).support.tail,
      x ∉ P.1.1.1.1 := by
  intro x hxTail hxP
  have hxSupport : x ∈
      (auxTrimmedConnector c hc hcodd hT S hS hpair P).support :=
    List.mem_of_mem_tail hxTail
  have hxStart := auxTrimmedConnector_mem_startSet_of_mem_start_carrier
    c hc hcodd hminimal hcard hT S hS hpair P hnext hxSupport hxP
  have hnot := trimWalkBetween_tail_support_not_mem_start
    (auxComplementaryPathInComplement_isPath
      c hc hcodd hT S hS hpair P)
    (fun y => y ∈ auxConnectorStartSet c hc hcodd S hS P)
    (fun y => y ∈ auxConnectorEndSet c hc hcodd S hS P)
    (auxConnectorStart_mem c hc hcodd S hS P)
    (auxConnectorEnd_mem c hc hcodd S hS P)
  exact hnot x (by simpa [auxTrimmedConnector] using hxTail) hxStart

lemma auxTrimmedConnector_dropLast_support_not_mem_next_carrier
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcard : 3 ≤ (auxPiecesInWalk c).card) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) (hnext : auxSelectedNextPiece c hc S hS P ≠ P.1) :
    ∀ x ∈ (auxTrimmedConnector c hc hcodd hT S hS hpair P).support.dropLast,
      x ∉ (auxSelectedNextPiece c hc S hS P).1.1.1 := by
  intro x hxDrop hxNext
  have hxSupport : x ∈
      (auxTrimmedConnector c hc hcodd hT S hS hpair P).support :=
    List.mem_of_mem_dropLast hxDrop
  have hxEnd := auxTrimmedConnector_mem_endSet_of_mem_next_carrier
    c hc hcodd hminimal hcard hT S hS hpair P hnext hxSupport hxNext
  have hnot := trimWalkBetween_dropLast_support_not_mem_end
    (auxComplementaryPathInComplement_isPath
      c hc hcodd hT S hS hpair P)
    (fun y => y ∈ auxConnectorStartSet c hc hcodd S hS P)
    (fun y => y ∈ auxConnectorEndSet c hc hcodd S hS P)
    (auxConnectorStart_mem c hc hcodd S hS P)
    (auxConnectorEnd_mem c hc hcodd S hS P)
  exact hnot x (by simpa [auxTrimmedConnector] using hxDrop) hxEnd

/-- Connectors assigned to distinct selected blocks have vertex-disjoint
supports.  A common vertex would make two complementary pieces overlap;
minimality forces them to be cyclic neighbors, while adjacent unselected
pieces lie in one and the same split block. -/
lemma auxTrimmedConnector_support_disjoint
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcard : 3 ≤ (auxPiecesInWalk c).card) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    {P Q : ↥S} (hPQ : P ≠ Q) :
    List.Disjoint
      (auxTrimmedConnector c hc hcodd hT S hS hpair P).support
      (auxTrimmedConnector c hc hcodd hT S hS hpair Q).support := by
  classical
  apply List.disjoint_left.mpr
  intro x hxP hxQ
  obtain ⟨R, hRtail, hxR⟩ :=
    auxTrimmedConnector_vertex_in_group_tail
      c hc hcodd hT S hS hpair P x hxP
  obtain ⟨U, hUtail, hxU⟩ :=
    auxTrimmedConnector_vertex_in_group_tail
      c hc hcodd hT S hS hpair Q x hxQ
  let gP := auxSelectedPieceGroup c hc S hS P
  let gQ := auxSelectedPieceGroup c hc S hS Q
  have hgP := auxSelectedPieceGroup_mem c hc S hS P
  have hgQ := auxSelectedPieceGroup_mem c hc S hS Q
  have hgdisj : List.Disjoint gP gQ :=
    auxSelectedPieceGroups_disjoint c hc S hS hPQ
  have hRmem : R ∈ gP := List.mem_of_mem_tail hRtail
  have hUmem : U ∈ gQ := List.mem_of_mem_tail hUtail
  have hUR : U ≠ R := by
    intro h
    exact (List.disjoint_left.mp hgdisj hRmem (by simpa [h] using hUmem))
  have hRnot : R ∉ S :=
    auxPieceGroup_tail_not_mem c hc S hS hgP R hRtail
  have hUnot : U ∉ S :=
    auxPieceGroup_tail_not_mem c hc S hS hgQ U hUtail
  have hneighbors := auxPiecePredecessor_ne_successor_of_three_le_card
    c hc hcodd hcard R
  have hcases := overlapping_piece_eq_predecessor_or_successor
    c hc hcodd hminimal R U hneighbors hUR _ hxU hxR
  rcases hcases with hprev | hsucc
  · have hprevMem := auxPieceGroup_predecessor_mem_of_mem_unselected
      c hc S hS hgP hRmem hRnot
    have hUinP : U ∈ gP := by simpa [hprev] using hprevMem
    exact (List.disjoint_left.mp hgdisj hUinP hUmem)
  · have hsuccMem := auxPieceGroup_successor_mem_of_not_selected
      c hc S hS hgP hRmem (by simpa [hsucc] using hUnot)
    have hUinP : U ∈ gP := by simpa [hsucc] using hsuccMem
    exact (List.disjoint_left.mp hgdisj hUinP hUmem)

/-- Every selected carrier met by a connector is one of its two boundary
carriers. -/
lemma auxTrimmedConnector_selected_carrier_eq_start_or_next
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcard : 3 ≤ (auxPiecesInWalk c).card) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P Q : ↥S) {x : V}
    (hxSupport : x ∈
      (auxTrimmedConnector c hc hcodd hT S hS hpair P).support)
    (hxQ : x ∈ Q.1.1.1.1) :
    Q = P ∨ Q = auxSelectedGroupSuccessor c hc S hS P := by
  classical
  by_cases hQP : Q = P
  · exact Or.inl hQP
  obtain ⟨R, hRtail, hxR⟩ :=
    auxTrimmedConnector_vertex_in_group_tail
      c hc hcodd hT S hS hpair P x hxSupport
  let gP := auxSelectedPieceGroup c hc S hS P
  let gQ := auxSelectedPieceGroup c hc S hS Q
  have hgP := auxSelectedPieceGroup_mem c hc S hS P
  have hgQ := auxSelectedPieceGroup_mem c hc S hS Q
  have hRnot : R ∉ S :=
    auxPieceGroup_tail_not_mem c hc S hS hgP R hRtail
  have hRneQ : R ≠ Q.1 := by
    intro h
    exact hRnot (by simpa [h] using Q.2)
  have hneighbors := auxPiecePredecessor_ne_successor_of_three_le_card
    c hc hcodd hcard Q.1
  have hcases := overlapping_piece_eq_predecessor_or_successor
    c hc hcodd hminimal Q.1 R hneighbors hRneQ x hxR hxQ
  rcases hcases with hprev | hsucc
  · have hsuccR : auxPieceSuccessor c hc R = Q.1 := by
      rw [hprev]
      exact auxPieceSuccessor_predecessor c hc Q.1
    have hnext := auxPieceGroup_selected_successor_eq_selectedNext
      c hc hcodd S hS hpair P hRtail (by simpa [hsuccR] using Q.2)
    right
    apply Subtype.ext
    exact hsuccR.symm.trans hnext
  · have hRinQ := auxPieceGroup_successor_mem_of_not_selected
      c hc S hS hgQ (R := Q.1) (by
        have hhead := auxSelectedPieceGroup_head c hc S hS Q
        rw [← hhead]
        exact List.head_mem (auxPieceGroup_ne_nil c hc S hS hgQ))
        (by simpa [← hsucc] using hRnot)
    have hRinP : R ∈ gP := List.mem_of_mem_tail hRtail
    have hgEq : gQ = gP :=
      auxPieceGroups_eq_of_common_mem c hc S hS hgQ hgP
        (by simpa [hsucc] using hRinQ) hRinP
    exact (hQP (auxSelectedPieceGroup_injective c hc S hS hgEq)).elim

lemma auxConnectorStartSet_subset_carrier {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (P : ↥S) : auxConnectorStartSet c hc hcodd S hS P ⊆ P.1.1.1.1 := by
  classical
  intro v hv
  by_cases h : auxSelectedNextPiece c hc S hS P = P.1
  · simp only [auxConnectorStartSet, h, if_pos, Finset.mem_singleton] at hv
    rw [hv]
    exact auxPieceRight_mem c hc hcodd P.1
  · exact (Finset.mem_filter.mp (by
      simpa only [auxConnectorStartSet, h, if_false] using hv)).1

lemma auxConnectorEndSet_subset_next_carrier {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (P : ↥S) : auxConnectorEndSet c hc hcodd S hS P ⊆
      (auxSelectedNextPiece c hc S hS P).1.1.1 := by
  classical
  intro v hv
  by_cases h : auxSelectedNextPiece c hc S hS P = P.1
  · simp only [auxConnectorEndSet, h, if_pos] at hv
    rw [h]
    exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase hv)).1
  · exact (Finset.mem_filter.mp (by
      simpa only [auxConnectorEndSet, h, if_false] using hv)).1

noncomputable def auxVariableRight {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) : V :=
  (auxTrimmedConnector c hc hcodd hT S hS hpair P).getVert 0

noncomputable def auxVariableLeft {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) : V :=
  let Q := auxSelectedGroupPredecessor c hc S hS P
  let q := auxTrimmedConnector c hc hcodd hT S hS hpair Q
  q.getVert q.length

lemma auxVariableRight_mem_startSet {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) : auxVariableRight c hc hcodd hT S hS hpair P ∈
      auxConnectorStartSet c hc hcodd S hS P := by
  have hmem := trimWalkBetween_start_mem
    (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P)
    (fun x => x ∈ auxConnectorStartSet c hc hcodd S hS P)
    (fun x => x ∈ auxConnectorEndSet c hc hcodd S hS P)
    (auxConnectorStart_mem c hc hcodd S hS P)
    (auxConnectorEnd_mem c hc hcodd S hS P)
  simpa [auxVariableRight, auxTrimmedConnector] using hmem

lemma auxVariableLeft_mem_predecessor_endSet {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    let Q := auxSelectedGroupPredecessor c hc S hS P
    auxVariableLeft c hc hcodd hT S hS hpair P ∈
      auxConnectorEndSet c hc hcodd S hS Q := by
  let Q := auxSelectedGroupPredecessor c hc S hS P
  have hmem := trimWalkBetween_end_mem
    (auxComplementaryPathInComplement c hc hcodd hT S hS hpair Q)
    (fun x => x ∈ auxConnectorStartSet c hc hcodd S hS Q)
    (fun x => x ∈ auxConnectorEndSet c hc hcodd S hS Q)
    (auxConnectorStart_mem c hc hcodd S hS Q)
    (auxConnectorEnd_mem c hc hcodd S hS Q)
  have hend : (auxTrimmedConnector c hc hcodd hT S hS hpair Q).getVert
      (auxTrimmedConnector c hc hcodd hT S hS hpair Q).length ∈
        auxConnectorEndSet c hc hcodd S hS Q := by
    rw [auxTrimmedConnector, trimWalkBetween_getVert_length]
    exact hmem
  exact hend

lemma auxVariableRight_mem {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) : auxVariableRight c hc hcodd hT S hS hpair P ∈ P.1.1.1.1 := by
  apply auxConnectorStartSet_subset_carrier c hc hcodd S hS P
  exact auxVariableRight_mem_startSet c hc hcodd hT S hS hpair P

lemma auxVariableLeft_mem {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) : auxVariableLeft c hc hcodd hT S hS hpair P ∈ P.1.1.1.1 := by
  let Q := auxSelectedGroupPredecessor c hc S hS P
  have hsucc : auxSelectedNextPiece c hc S hS Q = P.1 := by
    have h := congrArg Subtype.val
      (auxSelectedGroupSuccessor_predecessor c hc S hS P)
    exact h
  have hend := auxVariableLeft_mem_predecessor_endSet
    c hc hcodd hT S hS hpair P
  have hcarrier := auxConnectorEndSet_subset_next_carrier c hc hcodd S hS Q hend
  have hset : (auxSelectedNextPiece c hc S hS Q).1.1.1 = P.1.1.1.1 :=
    congrArg (fun R : ↥(auxPiecesInWalk c) => R.1.1.1) hsucc
  change (auxTrimmedConnector c hc hcodd hT S hS hpair Q).getVert
      (auxTrimmedConnector c hc hcodd hT S hS hpair Q).length ∈ P.1.1.1.1
  exact hset ▸ hcarrier

lemma auxVariableRight_colorAgreement {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    ((D P.1.1).color (auxVariableRight c hc hcodd hT S hS hpair P) =
        (D P.1.1).color (auxPieceRight c hc hcodd P.1)) ↔
      (auxCanonicalComplementColor c S
          (auxVariableRight c hc hcodd hT S hS hpair P) =
        auxCanonicalComplementColor c S
          (auxPieceRight c hc hcodd P.1)) :=
  auxConnectorStartSet_colorAgreement c hc hcodd S hS P
    (auxVariableRight_mem_startSet c hc hcodd hT S hS hpair P)

lemma auxVariableLeft_colorAgreement {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    ((D P.1.1).color (auxVariableLeft c hc hcodd hT S hS hpair P) =
        (D P.1.1).color (auxPieceLeft c hc hcodd P.1)) ↔
      (auxCanonicalComplementColor c S
          (auxVariableLeft c hc hcodd hT S hS hpair P) =
        auxCanonicalComplementColor c S
          (auxPieceLeft c hc hcodd P.1)) := by
  let Q := auxSelectedGroupPredecessor c hc S hS P
  have hsucc : auxSelectedNextPiece c hc S hS Q = P.1 :=
    congrArg Subtype.val (auxSelectedGroupSuccessor_predecessor c hc S hS P)
  have hcolor := auxConnectorEndSet_colorAgreement c hc hcodd S hS Q
    (auxVariableLeft_mem_predecessor_endSet c hc hcodd hT S hS hpair P)
  rw [hsucc] at hcolor
  exact hcolor

lemma auxSelectedGroupPredecessor_successor {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (P : ↥S) :
    auxSelectedGroupPredecessor c hc S hS
        (auxSelectedGroupSuccessor c hc S hS P) = P := by
  apply auxSelectedGroupSuccessor_injective c hc S hS
  exact (auxSelectedGroupSuccessor_predecessor c hc S hS
    (auxSelectedGroupSuccessor c hc S hS P)).trans rfl

lemma auxTrimmedConnector_end_eq_nextVariableLeft {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    (auxTrimmedConnector c hc hcodd hT S hS hpair P).getVert
        (auxTrimmedConnector c hc hcodd hT S hS hpair P).length =
      auxVariableLeft c hc hcodd hT S hS hpair
        (auxSelectedGroupSuccessor c hc S hS P) := by
  rw [auxVariableLeft]
  rw [auxSelectedGroupPredecessor_successor c hc S hS P]

lemma auxTrimmedConnector_length_cast {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    ((auxTrimmedConnector c hc hcodd hT S hS hpair P).length : ZMod 2) =
      ((auxCanonicalComplementColor c S
          (auxVariableRight c hc hcodd hT S hS hpair P)).val : ZMod 2) +
        (auxCanonicalComplementColor c S
          (auxVariableLeft c hc hcodd hT S hS hpair
            (auxSelectedGroupSuccessor c hc S hS P))).val := by
  let color := auxCanonicalComplementGraphColoring
    c hc hcodd hminimal hcarrier S hS
  have h0 := coloring_walk_length_cast_eq_color_val_add color
    (auxTrimmedConnector c hc hcodd hT S hS hpair P)
  have h : ((auxTrimmedConnector c hc hcodd hT S hS hpair P).length : ZMod 2) =
      ((color ((auxTrimmedConnector c hc hcodd hT S hS hpair P).getVert 0)).val :
        ZMod 2) +
      (color ((auxTrimmedConnector c hc hcodd hT S hS hpair P).getVert
        (auxTrimmedConnector c hc hcodd hT S hS hpair P).length)).val := by
    simpa only [SimpleGraph.Walk.getVert_zero,
      SimpleGraph.Walk.getVert_length] using h0
  rw [auxTrimmedConnector_end_eq_nextVariableLeft
    c hc hcodd hT S hS hpair P] at h
  simpa [color, auxVariableRight] using h

lemma auxRawConnector_length_cast {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    ((auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length : ZMod 2) =
      ((auxCanonicalComplementColor c S
          (auxPieceRight c hc hcodd P.1)).val : ZMod 2) +
        (auxCanonicalComplementColor c S
          (auxPieceLeft c hc hcodd
            (auxSelectedNextPiece c hc S hS P))).val := by
  let path := auxComplementaryPathInComplement c hc hcodd hT S hS hpair P
  let color := auxCanonicalComplementGraphColoring
    c hc hcodd hminimal hcarrier S hS
  have hpath := coloring_walk_length_cast_eq_color_val_add color path
  have hmod := auxComplementaryPathInComplement_mod_two
    c hc hcodd hminimal hcarrier hT S hS hpair P
  calc
    ((auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length : ZMod 2) =
        (((auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length % 2 : ℕ) :
          ZMod 2) := (ZMod.natCast_mod _ 2).symm
    _ = (((path.length % 2 : ℕ) : ZMod 2)) := by rw [hmod]
    _ = (path.length : ZMod 2) := ZMod.natCast_mod _ 2
    _ = _ := hpath

noncomputable def auxTrimmedFixedLength {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1)) : ℕ :=
  ∑ P : ↥S, (auxTrimmedConnector c hc hcodd hT S hS hpair P).length

noncomputable def auxSelectedTailSet {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (P : ↥S) : Finset ↥(auxPiecesInWalk c) :=
  (auxSelectedPieceGroup c hc S hS P).tail.toFinset

lemma auxSelectedTailSet_biUnion {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty) :
    (Finset.univ : Finset ↥S).biUnion (auxSelectedTailSet c hc S hS) =
      (Finset.univ : Finset ↥(auxPiecesInWalk c)) \ S := by
  classical
  apply Finset.Subset.antisymm
  · intro Q hQ
    obtain ⟨P, _, hQtail⟩ := Finset.mem_biUnion.mp hQ
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hQlist : Q ∈ (auxSelectedPieceGroup c hc S hS P).tail := by
      simpa [auxSelectedTailSet] using hQtail
    exact auxPieceGroup_tail_not_mem c hc S hS
      (auxSelectedPieceGroup_mem c hc S hS P) Q hQlist
  · intro Q hQ
    rw [Finset.mem_sdiff] at hQ
    have hQR : Q ∈ auxRotatedPieceOrder c hc S hS :=
      mem_auxRotatedPieceOrder c hc S hS Q
    rw [← auxPieceGroups_flatten c hc S hS] at hQR
    obtain ⟨g, hg, hQg⟩ := List.mem_flatten.mp hQR
    have hgne := auxPieceGroup_ne_nil c hc S hS hg
    let P : ↥S := ⟨g.head hgne, auxPieceGroup_head_mem c hc S hS hg⟩
    have hQne : Q ≠ g.head hgne := by
      intro h
      apply hQ.2
      rw [h]
      exact auxPieceGroup_head_mem c hc S hS hg
    have hQtail : Q ∈ g.tail := by
      cases hgshape : g with
      | nil => exact (hgne hgshape).elim
      | cons a rest =>
          rw [hgshape] at hQg
          simp only [List.mem_cons] at hQg
          have hhead : g.head hgne = a := by simp [hgshape]
          exact hQg.resolve_left (fun hQa => hQne (hQa.trans hhead.symm))
    have hchosen : auxSelectedPieceGroup c hc S hS P = g :=
      auxSelectedPieceGroup_of_group_head c hc S hS hg
    apply Finset.mem_biUnion.mpr
    refine ⟨P, Finset.mem_univ _, ?_⟩
    simpa [auxSelectedTailSet, hchosen] using hQtail

lemma auxSelectedTailSet_pairwiseDisjoint {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty) :
    (↑(Finset.univ : Finset ↥S) : Set ↥S).PairwiseDisjoint
      (auxSelectedTailSet c hc S hS) := by
  intro P _ Q _ hPQ
  apply Finset.disjoint_left.mpr
  intro R hRP hRQ
  have hd := auxSelectedPieceGroups_disjoint c hc S hS hPQ
  exact (List.disjoint_left.mp hd
    (List.mem_of_mem_tail (by simpa [auxSelectedTailSet] using hRP))
    (List.mem_of_mem_tail (by simpa [auxSelectedTailSet] using hRQ)))

lemma auxRawConnectorSum_eq_selectedFixedLength {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1)) :
    (∑ P : ↥S,
      (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length) =
      auxSelectedFixedLength c hc hcodd S := by
  classical
  let weight : ↥(auxPiecesInWalk c) → ℕ := fun Q =>
    parityStart (D Q.1).base
      ((D Q.1).residue (auxPieceLeft c hc hcodd Q)
        (auxPieceRight c hc hcodd Q))
  have htailNodup (P : ↥S) :
      (auxSelectedPieceGroup c hc S hS P).tail.Nodup := by
    have hinfix : auxSelectedPieceGroup c hc S hS P <:+:
        auxRotatedPieceOrder c hc S hS := by
      rw [← auxPieceGroups_flatten c hc S hS]
      exact List.infix_of_mem_flatten
        (auxSelectedPieceGroup_mem c hc S hS P)
    obtain ⟨pre, post, horder⟩ := hinfix
    have hall : (pre ++ auxSelectedPieceGroup c hc S hS P ++ post).Nodup := by
      rw [horder]
      exact auxRotatedPieceOrder_nodup c hc S hS
    exact (hall.of_append_left.of_append_right).tail
  calc
    (∑ P : ↥S,
        (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length) =
        ∑ P : ↥S, ∑ Q ∈ auxSelectedTailSet c hc S hS P, weight Q := by
      apply Finset.sum_congr rfl
      intro P _
      rw [auxComplementaryRawWalk_length]
      change ((auxSelectedPieceGroup c hc S hS P).tail.map weight).sum =
        ∑ Q ∈ auxSelectedTailSet c hc S hS P, weight Q
      exact (List.sum_toFinset weight (htailNodup P)).symm
    _ = ∑ Q ∈ (Finset.univ : Finset ↥S).biUnion
        (auxSelectedTailSet c hc S hS), weight Q := by
      rw [Finset.sum_biUnion (auxSelectedTailSet_pairwiseDisjoint c hc S hS)]
    _ = ∑ Q ∈ (Finset.univ : Finset ↥(auxPiecesInWalk c)) \ S,
        weight Q := by rw [auxSelectedTailSet_biUnion c hc S hS]
    _ = auxSelectedFixedLength c hc hcodd S := rfl

lemma auxTrimmedFixedLength_le_selectedFixedLength {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1)) :
    auxTrimmedFixedLength c hc hcodd hT S hS hpair ≤
      auxSelectedFixedLength c hc hcodd S := by
  classical
  let weight : ↥(auxPiecesInWalk c) → ℕ := fun Q =>
    parityStart (D Q.1).base
      ((D Q.1).residue (auxPieceLeft c hc hcodd Q)
        (auxPieceRight c hc hcodd Q))
  let tailSet : ↥S → Finset ↥(auxPiecesInWalk c) := fun P =>
    (auxSelectedPieceGroup c hc S hS P).tail.toFinset
  have htailNodup (P : ↥S) :
      (auxSelectedPieceGroup c hc S hS P).tail.Nodup := by
    have hinfix : auxSelectedPieceGroup c hc S hS P <:+:
        auxRotatedPieceOrder c hc S hS := by
      rw [← auxPieceGroups_flatten c hc S hS]
      exact List.infix_of_mem_flatten
        (auxSelectedPieceGroup_mem c hc S hS P)
    obtain ⟨pre, post, horder⟩ := hinfix
    have hall : (pre ++ auxSelectedPieceGroup c hc S hS P ++ post).Nodup := by
      rw [horder]
      exact auxRotatedPieceOrder_nodup c hc S hS
    exact (hall.of_append_left.of_append_right).tail
  have hpairTail : (↑(Finset.univ : Finset ↥S) : Set ↥S).PairwiseDisjoint tailSet := by
    intro P _ Q _ hPQ
    apply Finset.disjoint_left.mpr
    intro R hRP hRQ
    have hd := auxSelectedPieceGroups_disjoint c hc S hS hPQ
    exact (List.disjoint_left.mp hd
      (List.mem_of_mem_tail (by simpa [tailSet] using hRP))
      (List.mem_of_mem_tail (by simpa [tailSet] using hRQ)))
  have hunion : (Finset.univ : Finset ↥S).biUnion tailSet ⊆
      (Finset.univ : Finset ↥(auxPiecesInWalk c)) \ S := by
    intro Q hQ
    obtain ⟨P, _, hQtail⟩ := Finset.mem_biUnion.mp hQ
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hQlist : Q ∈ (auxSelectedPieceGroup c hc S hS P).tail := by
      simpa [tailSet] using hQtail
    exact auxPieceGroup_tail_not_mem c hc S hS
      (auxSelectedPieceGroup_mem c hc S hS P) Q hQlist
  have hrawSum :
      (∑ P : ↥S,
        (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length) =
      ∑ Q ∈ (Finset.univ : Finset ↥S).biUnion tailSet, weight Q := by
    rw [Finset.sum_biUnion hpairTail]
    apply Finset.sum_congr rfl
    intro P _
    rw [auxComplementaryRawWalk_length]
    change ((auxSelectedPieceGroup c hc S hS P).tail.map weight).sum =
      ∑ Q ∈ tailSet P, weight Q
    exact (List.sum_toFinset weight (htailNodup P)).symm
  calc
    auxTrimmedFixedLength c hc hcodd hT S hS hpair =
        ∑ P : ↥S, (auxTrimmedConnector c hc hcodd hT S hS hpair P).length := rfl
    _ ≤ ∑ P : ↥S,
        (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length := by
      exact Finset.sum_le_sum fun P _ =>
        auxTrimmedConnector_length_le c hc hcodd hT S hS hpair P
    _ = ∑ Q ∈ (Finset.univ : Finset ↥S).biUnion tailSet, weight Q := hrawSum
    _ ≤ ∑ Q ∈ (Finset.univ : Finset ↥(auxPiecesInWalk c)) \ S,
        weight Q := Finset.sum_le_sum_of_subset_of_nonneg hunion (fun _ _ _ => Nat.zero_le _)
    _ = auxSelectedFixedLength c hc hcodd S := rfl

lemma auxTrimmedFixedLength_weight {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (hweight : (∑ P : ↥(auxPiecesInWalk c), ((D P.1).base + 1)) ≤
      3 * ∑ P ∈ S, ((D P.1).base + 1)) :
    auxTrimmedFixedLength c hc hcodd hT S hS hpair +
        (∑ P : ↥S, ((D P.1.1).base + 1)) ≤
      3 * ∑ P : ↥S, ((D P.1.1).base + 1) := by
  have hle := auxTrimmedFixedLength_le_selectedFixedLength
    c hc hcodd hT S hS hpair
  have hold := auxSelectedFixedLength_weight c hc hcodd S hweight
  have hsum : (∑ P : ↥S, ((D P.1.1).base + 1)) =
      ∑ P ∈ S, ((D P.1).base + 1) := by
    exact Finset.sum_attach S (fun P => (D P.1).base + 1)
  rw [hsum]
  exact (Nat.add_le_add_right hle _).trans hold

lemma auxTrimmedFixedLength_lower_odd {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1)) :
    Odd (auxTrimmedFixedLength c hc hcodd hT S hS hpair +
      ∑ P : ↥S, parityStart (D P.1.1).base
        ((D P.1.1).residue
          (auxVariableLeft c hc hcodd hT S hS hpair P)
          (auxVariableRight c hc hcodd hT S hS hpair P))) := by
  classical
  let f := auxSelectedGroupSuccessor c hc S hS
  let pieceVarLeft : ↥S → ZMod 2 := fun P =>
    ((D P.1.1).color (auxVariableLeft c hc hcodd hT S hS hpair P)).val
  let pieceVarRight : ↥S → ZMod 2 := fun P =>
    ((D P.1.1).color (auxVariableRight c hc hcodd hT S hS hpair P)).val
  let pieceCanonLeft : ↥S → ZMod 2 := fun P =>
    ((D P.1.1).color (auxPieceLeft c hc hcodd P.1)).val
  let pieceCanonRight : ↥S → ZMod 2 := fun P =>
    ((D P.1.1).color (auxPieceRight c hc hcodd P.1)).val
  let compVarLeft : ↥S → ZMod 2 := fun P =>
    (auxCanonicalComplementColor c S
      (auxVariableLeft c hc hcodd hT S hS hpair P)).val
  let compVarRight : ↥S → ZMod 2 := fun P =>
    (auxCanonicalComplementColor c S
      (auxVariableRight c hc hcodd hT S hS hpair P)).val
  let compCanonLeft : ↥S → ZMod 2 := fun P =>
    (auxCanonicalComplementColor c S (auxPieceLeft c hc hcodd P.1)).val
  let compCanonRight : ↥S → ZMod 2 := fun P =>
    (auxCanonicalComplementColor c S (auxPieceRight c hc hcodd P.1)).val
  let variableTerm : ↥S → ℕ := fun P =>
    parityStart (D P.1.1).base
      ((D P.1.1).residue
        (auxVariableLeft c hc hcodd hT S hS hpair P)
        (auxVariableRight c hc hcodd hT S hS hpair P))
  let canonicalTerm : ↥S → ℕ := fun P =>
    parityStart (D P.1.1).base
      ((D P.1.1).residue (auxPieceLeft c hc hcodd P.1)
        (auxPieceRight c hc hcodd P.1))
  let fEquiv : ↥S ≃ ↥S := Equiv.ofBijective f
    ⟨auxSelectedGroupSuccessor_injective c hc S hS,
      Finite.injective_iff_surjective.mp
        (auxSelectedGroupSuccessor_injective c hc S hS)⟩
  have hfEquiv (P : ↥S) : fEquiv P = f P := rfl
  have hfval (P : ↥S) : (f P).1 = auxSelectedNextPiece c hc S hS P := rfl
  have hsumF (g : ↥S → ZMod 2) : (∑ P : ↥S, g (f P)) = ∑ P : ↥S, g P := by
    simpa only [hfEquiv] using fEquiv.sum_comp g
  have htrimFixed :
      (auxTrimmedFixedLength c hc hcodd hT S hS hpair : ZMod 2) =
        ∑ P : ↥S, (compVarRight P + compVarLeft P) := by
    calc
      (auxTrimmedFixedLength c hc hcodd hT S hS hpair : ZMod 2) =
          ∑ P : ↥S,
            ((auxTrimmedConnector c hc hcodd hT S hS hpair P).length :
              ZMod 2) := by simp [auxTrimmedFixedLength]
      _ = ∑ P : ↥S, (compVarRight P + compVarLeft (f P)) := by
        apply Finset.sum_congr rfl
        intro P _
        simpa [f, compVarRight, compVarLeft] using
          auxTrimmedConnector_length_cast c hc hcodd hminimal hcarrier
            hT S hS hpair P
      _ = (∑ P : ↥S, compVarRight P) +
          ∑ P : ↥S, compVarLeft (f P) := Finset.sum_add_distrib
      _ = (∑ P : ↥S, compVarRight P) +
          ∑ P : ↥S, compVarLeft P := by rw [hsumF]
      _ = ∑ P : ↥S, (compVarRight P + compVarLeft P) :=
        Finset.sum_add_distrib.symm
  have hrawFixed :
      (auxSelectedFixedLength c hc hcodd S : ZMod 2) =
        ∑ P : ↥S, (compCanonRight P + compCanonLeft P) := by
    calc
      (auxSelectedFixedLength c hc hcodd S : ZMod 2) =
          ((∑ P : ↥S,
            (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length) :
              ZMod 2) := by
        simpa using congrArg (fun n : ℕ => (n : ZMod 2))
          (auxRawConnectorSum_eq_selectedFixedLength
            c hc hcodd hT S hS hpair).symm
      _ = ∑ P : ↥S,
          ((auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length :
            ZMod 2) := by simp
      _ = ∑ P : ↥S, (compCanonRight P + compCanonLeft (f P)) := by
        apply Finset.sum_congr rfl
        intro P _
        simpa only [compCanonRight, compCanonLeft, hfval] using
          auxRawConnector_length_cast c hc hcodd hminimal hcarrier
            hT S hS hpair P
      _ = (∑ P : ↥S, compCanonRight P) +
          ∑ P : ↥S, compCanonLeft (f P) := Finset.sum_add_distrib
      _ = (∑ P : ↥S, compCanonRight P) +
          ∑ P : ↥S, compCanonLeft P := by rw [hsumF]
      _ = ∑ P : ↥S, (compCanonRight P + compCanonLeft P) :=
        Finset.sum_add_distrib.symm
  have hvariableCast : ((∑ P : ↥S, variableTerm P : ℕ) : ZMod 2) =
      ∑ P : ↥S, (pieceVarLeft P + pieceVarRight P) := by
    calc
      ((∑ P : ↥S, variableTerm P : ℕ) : ZMod 2) =
          ∑ P : ↥S, (variableTerm P : ZMod 2) := by simp
      _ = ∑ P : ↥S, (pieceVarLeft P + pieceVarRight P) := by
        apply Finset.sum_congr rfl
        intro P _
        rw [show (variableTerm P : ZMod 2) =
            ((D P.1.1).residue
              (auxVariableLeft c hc hcodd hT S hS hpair P)
              (auxVariableRight c hc hcodd hT S hS hpair P) : ZMod 2) by
          exact parityStart_cast_eq_residue
            ((D P.1.1).residue_lt_two _ _)]
        exact (D P.1.1).residue_cast_eq_color_val_add _ _
  have hcanonicalCast : ((∑ P : ↥S, canonicalTerm P : ℕ) : ZMod 2) =
      ∑ P : ↥S, (pieceCanonLeft P + pieceCanonRight P) := by
    calc
      ((∑ P : ↥S, canonicalTerm P : ℕ) : ZMod 2) =
          ∑ P : ↥S, (canonicalTerm P : ZMod 2) := by simp
      _ = ∑ P : ↥S, (pieceCanonLeft P + pieceCanonRight P) := by
        apply Finset.sum_congr rfl
        intro P _
        rw [show (canonicalTerm P : ZMod 2) =
            ((D P.1.1).residue (auxPieceLeft c hc hcodd P.1)
              (auxPieceRight c hc hcodd P.1) : ZMod 2) by
          exact parityStart_cast_eq_residue
            ((D P.1.1).residue_lt_two _ _)]
        exact (D P.1.1).residue_cast_eq_color_val_add _ _
  have hright (P : ↥S) :
      pieceVarRight P + compVarRight P =
        pieceCanonRight P + compCanonRight P := by
    exact finTwo_cross_val_add_eq_of_eq_iff_eq _ _ _ _
      (auxVariableRight_colorAgreement c hc hcodd hT S hS hpair P)
  have hleft (P : ↥S) :
      pieceVarLeft P + compVarLeft P =
        pieceCanonLeft P + compCanonLeft P := by
    exact finTwo_cross_val_add_eq_of_eq_iff_eq _ _ _ _
      (auxVariableLeft_colorAgreement c hc hcodd hT S hS hpair P)
  have htotalCast :
      ((auxTrimmedFixedLength c hc hcodd hT S hS hpair +
          ∑ P : ↥S, variableTerm P : ℕ) : ZMod 2) =
        ((auxSelectedFixedLength c hc hcodd S +
          ∑ P : ↥S, canonicalTerm P : ℕ) : ZMod 2) := by
    rw [Nat.cast_add, Nat.cast_add, htrimFixed, hrawFixed,
      hvariableCast, hcanonicalCast]
    calc
      (∑ P : ↥S, (compVarRight P + compVarLeft P)) +
          ∑ P : ↥S, (pieceVarLeft P + pieceVarRight P) =
          ∑ P : ↥S,
            ((pieceVarRight P + compVarRight P) +
              (pieceVarLeft P + compVarLeft P)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro P _
            ring
      _ = ∑ P : ↥S,
          ((pieceCanonRight P + compCanonRight P) +
            (pieceCanonLeft P + compCanonLeft P)) := by
            apply Finset.sum_congr rfl
            intro P _
            rw [hright P, hleft P]
      _ = (∑ P : ↥S, (compCanonRight P + compCanonLeft P)) +
          ∑ P : ↥S, (pieceCanonLeft P + pieceCanonRight P) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro P _
            ring
  have hcanonicalSum : (∑ P : ↥S, canonicalTerm P) =
      ∑ P ∈ S, parityStart (D P.1).base
        ((D P.1).residue (auxPieceLeft c hc hcodd P)
          (auxPieceRight c hc hcodd P)) := by
    exact Finset.sum_attach S (fun P => parityStart (D P.1).base
      ((D P.1).residue (auxPieceLeft c hc hcodd P)
        (auxPieceRight c hc hcodd P)))
  have hold : Odd (auxSelectedFixedLength c hc hcodd S +
      ∑ P : ↥S, canonicalTerm P) := by
    rw [hcanonicalSum]
    exact auxSelectedFixedLength_lower_odd c hc hcodd S
  apply odd_of_zmod_two_natCast_eq_one
  rw [htotalCast]
  exact hold.natCast_zmod_two

/-- The incoming and outgoing trimmed connectors meet a selected carrier at
distinct vertices.  In the only nontrivial case, equality would make the
cyclic predecessor and successor carriers meet.  Degree two of the overlap
graph would then close a three-piece cycle, contradicting the next selected
block. -/
theorem auxVariableLeft_ne_right {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    auxVariableLeft c hc hcodd hT S hS hpair P ≠
      auxVariableRight c hc hcodd hT S hS hpair P := by
  classical
  let f := auxSelectedGroupSuccessor c hc S hS
  let Qs := auxSelectedGroupPredecessor c hc S hS P
  by_cases hself : auxSelectedNextPiece c hc S hS P = P.1
  · have hfP : f P = P := by
      apply Subtype.ext
      exact hself
    have hQsP : Qs = P := by
      apply auxSelectedGroupSuccessor_injective c hc S hS
      exact (auxSelectedGroupSuccessor_predecessor c hc S hS P).trans hfP.symm
    have hleft := auxVariableLeft_mem_predecessor_endSet
      c hc hcodd hT S hS hpair P
    have hleftP : auxVariableLeft c hc hcodd hT S hS hpair P ∈
        auxConnectorEndSet c hc hcodd S hS P := by
      change auxVariableLeft c hc hcodd hT S hS hpair P ∈
        auxConnectorEndSet c hc hcodd S hS Qs at hleft
      rw [hQsP] at hleft
      exact hleft
    have hright := auxVariableRight_mem_startSet
      c hc hcodd hT S hS hpair P
    have hdisj := auxConnectorSets_disjoint c hc hcodd S hS hpair P
    intro heq
    exact (Finset.disjoint_left.mp hdisj) hright (by
      rw [← heq]
      exact hleftP)
  · have hQsP : Qs ≠ P := by
      intro h
      have hfQs : f Qs = P :=
        auxSelectedGroupSuccessor_predecessor c hc S hS P
      rw [h] at hfQs
      exact hself (congrArg Subtype.val hfQs)
    let gP := auxSelectedPieceGroup c hc S hS P
    let gQ := auxSelectedPieceGroup c hc S hS Qs
    have hgPmem := auxSelectedPieceGroup_mem c hc S hS P
    have hgQmem := auxSelectedPieceGroup_mem c hc S hS Qs
    have hgPne := auxPieceGroup_ne_nil c hc S hS hgPmem
    have hgQne := auxPieceGroup_ne_nil c hc S hS hgQmem
    have hgPQ : gQ ≠ gP := by
      intro heq
      have hheads := list_head_eq_of_eq heq hgQne hgPne
      have hQhead := auxSelectedPieceGroup_head c hc S hS Qs
      have hPhead := auxSelectedPieceGroup_head c hc S hS P
      have hval : Qs.1 = P.1 := hQhead.symm.trans (hheads.trans hPhead)
      exact hQsP (Subtype.ext hval)
    have hgroupsPair : (auxPieceGroups c hc S hS).Pairwise List.Disjoint := by
      exact (List.nodup_flatten.mp (by
        rw [auxPieceGroups_flatten c hc S hS]
        exact auxRotatedPieceOrder_nodup c hc S hS)).2
    have hgdisj : List.Disjoint gQ gP := by
      obtain ⟨i, hi, higQ⟩ := List.getElem_of_mem hgQmem
      obtain ⟨j, hj, hjgP⟩ := List.getElem_of_mem hgPmem
      have hij : i ≠ j := by
        intro hij
        subst j
        exact hgPQ (higQ.symm.trans hjgP)
      rcases Nat.lt_or_gt_of_ne hij with hij | hji
      · simpa [higQ, hjgP] using
          (hgroupsPair.rel_get_of_lt (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij)
      · have hd : List.Disjoint gP gQ := by
          simpa [higQ, hjgP] using
            (hgroupsPair.rel_get_of_lt (a := ⟨j, hj⟩) (b := ⟨i, hi⟩) hji)
        exact hd.symm
    have htP := auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair P
    have htQ := auxSelectedPieceGroup_tail_ne_nil c hc hcodd S hS hpair Qs
    let B := gP.tail.head htP
    let Ap := gQ.tail.getLast htQ
    have hBmem : B ∈ gP.tail := List.head_mem htP
    have hAmem : Ap ∈ gQ.tail := List.getLast_mem htQ
    have hsuccP : auxPieceSuccessor c hc P.1 = B := by
      exact (auxSelectedPieceGroup_tail_head_eq_successor
        c hc hcodd S hS hpair P).symm
    have hnextQs : auxSelectedNextPiece c hc S hS Qs = P.1 := by
      exact congrArg Subtype.val
        (auxSelectedGroupSuccessor_predecessor c hc S hS P)
    have hsuccA : auxPieceSuccessor c hc Ap = P.1 := by
      exact (auxSelectedPieceGroup_tail_last_successor
        c hc hcodd S hS hpair Qs).trans hnextQs
    have hAprev : Ap = auxPiecePredecessor c hc P.1 := by
      apply auxPieceSuccessor_injective c hc
      exact hsuccA.trans (auxPieceSuccessor_predecessor c hc P.1).symm
    have hAB : Ap ≠ B := by
      intro h
      exact (List.disjoint_left.mp hgdisj (List.mem_of_mem_tail hAmem)
        (by simpa [h] using List.mem_of_mem_tail hBmem))
    have hprevsucc : auxPiecePredecessor c hc P.1 ≠
        auxPieceSuccessor c hc P.1 := by
      intro h
      exact hAB (hAprev.trans (h.trans hsuccP))
    have hrightTrim : auxVariableRight c hc hcodd hT S hS hpair P ∈
        (auxTrimmedConnector c hc hcodd hT S hS hpair P).support := by
      exact SimpleGraph.Walk.getVert_mem_support _ 0
    obtain ⟨X, hXmem, hrightX⟩ := auxTrimmedConnector_vertex_in_group_tail
      c hc hcodd hT S hS hpair P _ hrightTrim
    have hXneP : X ≠ P.1 := by
      intro h
      have hXS : X ∈ S := by simpa [h] using P.2
      exact (auxPieceGroup_tail_not_mem c hc S hS hgPmem X hXmem) hXS
    have hrightP := auxVariableRight_mem c hc hcodd hT S hS hpair P
    have hXcases := overlapping_piece_eq_predecessor_or_successor
      c hc hcodd hminimal P.1 X hprevsucc hXneP _ hrightX hrightP
    have hXneA : X ≠ Ap := by
      intro h
      exact (List.disjoint_left.mp hgdisj (List.mem_of_mem_tail hAmem)
        (by simpa [h] using List.mem_of_mem_tail hXmem))
    have hXB : X = B := by
      rcases hXcases with hXprev | hXsucc
      · exact (hXneA (hXprev.trans hAprev.symm)).elim
      · exact hXsucc.trans hsuccP
    have hleftTrim : auxVariableLeft c hc hcodd hT S hS hpair P ∈
        (auxTrimmedConnector c hc hcodd hT S hS hpair Qs).support := by
      change (auxTrimmedConnector c hc hcodd hT S hS hpair Qs).getVert
          (auxTrimmedConnector c hc hcodd hT S hS hpair Qs).length ∈ _
      exact SimpleGraph.Walk.getVert_mem_support _ _
    obtain ⟨Y, hYmem, hleftY⟩ := auxTrimmedConnector_vertex_in_group_tail
      c hc hcodd hT S hS hpair Qs _ hleftTrim
    have hYneP : Y ≠ P.1 := by
      intro h
      have hYS : Y ∈ S := by simpa [h] using P.2
      exact (auxPieceGroup_tail_not_mem c hc S hS hgQmem Y hYmem) hYS
    have hleftP := auxVariableLeft_mem c hc hcodd hT S hS hpair P
    have hYcases := overlapping_piece_eq_predecessor_or_successor
      c hc hcodd hminimal P.1 Y hprevsucc hYneP _ hleftY hleftP
    have hYneB : Y ≠ B := by
      intro h
      exact (List.disjoint_left.mp hgdisj (List.mem_of_mem_tail hYmem)
        (by simpa [h] using List.mem_of_mem_tail hBmem))
    have hYA : Y = Ap := by
      rcases hYcases with hYprev | hYsucc
      · exact hYprev.trans hAprev.symm
      · exact (hYneB (hYsucc.trans hsuccP)).elim
    intro heq
    have hvA : auxVariableRight c hc hcodd hT S hS hpair P ∈ Ap.1.1.1 := by
      rw [← heq, ← hYA]
      exact hleftY
    have hvB : auxVariableRight c hc hcodd hT S hS hpair P ∈ B.1.1.1 := by
      rw [← hXB]
      exact hrightX
    have hpredAsucc : auxPiecePredecessor c hc Ap ≠ auxPieceSuccessor c hc Ap := by
      intro h
      have hpredA : auxPiecePredecessor c hc Ap = P.1 := h.trans hsuccA
      have hsuccPA : auxPieceSuccessor c hc P.1 = Ap := by
        rw [← hpredA]
        exact auxPieceSuccessor_predecessor c hc Ap
      exact hAB (hsuccPA.symm.trans hsuccP)
    have hBneA : B ≠ Ap := hAB.symm
    have hBcases := overlapping_piece_eq_predecessor_or_successor
      c hc hcodd hminimal Ap B hpredAsucc hBneA _ hvB hvA
    have hBneP : B ≠ P.1 := by
      rw [← hsuccP]
      exact auxPieceSuccessor_ne c hc hcodd P.1
    have hBpred : B = auxPiecePredecessor c hc Ap := by
      exact hBcases.resolve_right (fun h => hBneP (h.trans hsuccA))
    have hsuccB : auxPieceSuccessor c hc B = Ap := by
      rw [hBpred]
      exact auxPieceSuccessor_predecessor c hc Ap
    have hAneP : Ap ≠ P.1 := by
      rw [← hsuccA]
      exact (auxPieceSuccessor_ne c hc hcodd Ap).symm
    have hPneB : P.1 ≠ B := hBneP.symm
    have hexhaust := list_mem_of_three_cycle
      (auxPieceOrderSubtype c hc) (auxPieceOrderSubtype_nodup c hc)
      (mem_auxPieceOrderSubtype_iff c hc Ap) hAneP hPneB hBneA
      (by simpa [auxPieceOrderSubtype_next_eq_successor] using hsuccA)
      (by simpa [auxPieceOrderSubtype_next_eq_successor] using hsuccP)
      (by simpa [auxPieceOrderSubtype_next_eq_successor] using hsuccB)
    have hQcases := hexhaust Qs.1 (mem_auxPieceOrderSubtype_iff c hc Qs.1)
    have hQneA : Qs.1 ≠ Ap := by
      intro h
      have hAS : Ap ∈ S := by simpa [← h] using Qs.2
      exact (auxPieceGroup_tail_not_mem c hc S hS hgQmem Ap hAmem) hAS
    have hQneB : Qs.1 ≠ B := by
      intro h
      have hBS : B ∈ S := by simpa [← h] using Qs.2
      exact (auxPieceGroup_tail_not_mem c hc S hS hgPmem B hBmem) hBS
    rcases hQcases with hQA | hQP | hQB
    · exact (hQneA hQA).elim
    · exact (hQsP (Subtype.ext hQP)).elim
    · exact (hQneB hQB).elim

noncomputable def auxChosenVariablePath {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (x : ↥S → ℕ)
    (hx : ∀ P, (D P.1.1).base ≤ x P ∧
      x P ≤ (D P.1.1).base * T ∧
      x P % 2 = (D P.1.1).residue
        (auxVariableLeft c hc hcodd hT S hS hpair P)
        (auxVariableRight c hc hcodd hT S hS hpair P))
    (P : ↥S) : P.1.1.1.2.Walk
      (auxVariableLeft c hc hcodd hT S hS hpair P)
      (auxVariableRight c hc hcodd hT S hS hpair P) :=
  Classical.choose ((D P.1.1).hasPath_of_modEq
    (auxVariableLeft_mem c hc hcodd hT S hS hpair P)
    (auxVariableRight_mem c hc hcodd hT S hS hpair P)
    (auxVariableLeft_ne_right c hc hcodd hminimal hT S hS hpair P)
    (hx P).1 (hx P).2.1 (hx P).2.2)

lemma auxChosenVariablePath_isPath {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (x : ↥S → ℕ)
    (hx : ∀ P, (D P.1.1).base ≤ x P ∧
      x P ≤ (D P.1.1).base * T ∧
      x P % 2 = (D P.1.1).residue
        (auxVariableLeft c hc hcodd hT S hS hpair P)
        (auxVariableRight c hc hcodd hT S hS hpair P))
    (P : ↥S) :
    (auxChosenVariablePath c hc hcodd hminimal hT S hS hpair x hx P).IsPath :=
  (Classical.choose_spec ((D P.1.1).hasPath_of_modEq
    (auxVariableLeft_mem c hc hcodd hT S hS hpair P)
    (auxVariableRight_mem c hc hcodd hT S hS hpair P)
    (auxVariableLeft_ne_right c hc hcodd hminimal hT S hS hpair P)
    (hx P).1 (hx P).2.1 (hx P).2.2)).1

@[simp] lemma auxChosenVariablePath_length {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (x : ↥S → ℕ)
    (hx : ∀ P, (D P.1.1).base ≤ x P ∧
      x P ≤ (D P.1.1).base * T ∧
      x P % 2 = (D P.1.1).residue
        (auxVariableLeft c hc hcodd hT S hS hpair P)
        (auxVariableRight c hc hcodd hT S hS hpair P))
    (P : ↥S) :
    (auxChosenVariablePath c hc hcodd hminimal hT S hS hpair x hx P).length = x P :=
  (Classical.choose_spec ((D P.1.1).hasPath_of_modEq
    (auxVariableLeft_mem c hc hcodd hT S hS hpair P)
    (auxVariableRight_mem c hc hcodd hT S hS hpair P)
    (auxVariableLeft_ne_right c hc hcodd hminimal hT S hS hpair P)
    (hx P).1 (hx P).2.1 (hx P).2.2)).2.1

lemma auxChosenVariablePath_support_subset {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (x : ↥S → ℕ)
    (hx : ∀ P, (D P.1.1).base ≤ x P ∧
      x P ≤ (D P.1.1).base * T ∧
      x P % 2 = (D P.1.1).residue
        (auxVariableLeft c hc hcodd hT S hS hpair P)
        (auxVariableRight c hc hcodd hT S hS hpair P))
    (P : ↥S) : ∀ v ∈
      (auxChosenVariablePath c hc hcodd hminimal hT S hS hpair x hx P).support,
      v ∈ P.1.1.1.1 :=
  (Classical.choose_spec ((D P.1.1).hasPath_of_modEq
    (auxVariableLeft_mem c hc hcodd hT S hS hpair P)
    (auxVariableRight_mem c hc hcodd hT S hS hpair P)
    (auxVariableLeft_ne_right c hc hcodd hminimal hT S hS hpair P)
    (hx P).1 (hx P).2.1 (hx P).2.2)).2.2

noncomputable def auxTrimmedConnectorInGraph
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (hunion : packedUnion A ≤ G) (P : ↥S) :
    G.Walk (auxVariableRight c hc hcodd hT S hS hpair P)
      (auxVariableLeft c hc hcodd hT S hS hpair
        (auxSelectedGroupSuccessor c hc S hS P)) :=
  let w := (auxTrimmedConnector c hc hcodd hT S hS hpair P).mapLe
    ((auxComplementGraph_le_packedUnion c S).trans hunion)
  w.copy (by simp [w, auxVariableRight]) (by
    simpa [w] using
      auxTrimmedConnector_end_eq_nextVariableLeft
        c hc hcodd hT S hS hpair P)

@[simp] lemma auxTrimmedConnectorInGraph_length
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (hunion : packedUnion A ≤ G) (P : ↥S) :
    (auxTrimmedConnectorInGraph c hc hcodd hT S hS hpair hunion P).length =
      (auxTrimmedConnector c hc hcodd hT S hS hpair P).length := by
  simp [auxTrimmedConnectorInGraph]

lemma auxTrimmedConnectorInGraph_isPath
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (hunion : packedUnion A ≤ G) (P : ↥S) :
    (auxTrimmedConnectorInGraph c hc hcodd hT S hS hpair hunion P).IsPath := by
  simpa [auxTrimmedConnectorInGraph] using
    auxTrimmedConnector_isPath c hc hcodd hT S hS hpair P

@[simp] lemma auxTrimmedConnectorInGraph_support
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (hunion : packedUnion A ≤ G) (P : ↥S) :
    (auxTrimmedConnectorInGraph c hc hcodd hT S hS hpair hunion P).support =
      (auxTrimmedConnector c hc hcodd hT S hS hpair P).support := by
  simp [auxTrimmedConnectorInGraph]

noncomputable def auxSelectedSegmentInGraph
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (hpiece : ∀ P : ↥A, P.1.2 ≤ G) (hunion : packedUnion A ≤ G)
    (x : ↥S → ℕ)
    (hx : ∀ P, (D P.1.1).base ≤ x P ∧
      x P ≤ (D P.1.1).base * T ∧
      x P % 2 = (D P.1.1).residue
        (auxVariableLeft c hc hcodd hT S hS hpair P)
        (auxVariableRight c hc hcodd hT S hS hpair P))
    (P : ↥S) :
    G.Walk (auxVariableLeft c hc hcodd hT S hS hpair P)
      (auxVariableLeft c hc hcodd hT S hS hpair
        (auxSelectedGroupSuccessor c hc S hS P)) :=
  (auxChosenVariablePath c hc hcodd hminimal hT S hS hpair x hx P).mapLe
      (hpiece P.1.1) |>.append
    (auxTrimmedConnectorInGraph c hc hcodd hT S hS hpair hunion P)

@[simp] lemma auxSelectedSegmentInGraph_length
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (hpiece : ∀ P : ↥A, P.1.2 ≤ G) (hunion : packedUnion A ≤ G)
    (x : ↥S → ℕ)
    (hx : ∀ P, (D P.1.1).base ≤ x P ∧
      x P ≤ (D P.1.1).base * T ∧
      x P % 2 = (D P.1.1).residue
        (auxVariableLeft c hc hcodd hT S hS hpair P)
        (auxVariableRight c hc hcodd hT S hS hpair P))
    (P : ↥S) :
    (auxSelectedSegmentInGraph c hc hcodd hminimal hT S hS hpair
      hpiece hunion x hx P).length = x P +
      (auxTrimmedConnector c hc hcodd hT S hS hpair P).length := by
  simp [auxSelectedSegmentInGraph]

lemma auxSelectedSegmentInGraph_isPath_of_two_le_card
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcard : 3 ≤ (auxPiecesInWalk c).card)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : 2 ≤ S.card)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (hpiece : ∀ P : ↥A, P.1.2 ≤ G) (hunion : packedUnion A ≤ G)
    (x : ↥S → ℕ)
    (hx : ∀ P, (D P.1.1).base ≤ x P ∧
      x P ≤ (D P.1.1).base * T ∧
      x P % 2 = (D P.1.1).residue
        (auxVariableLeft c hc hcodd hT S hS hpair P)
        (auxVariableRight c hc hcodd hT S hS hpair P))
    (P : ↥S) :
    (auxSelectedSegmentInGraph c hc hcodd hminimal hT S hS hpair
      hpiece hunion x hx P).IsPath := by
  let vp := (auxChosenVariablePath
    c hc hcodd hminimal hT S hS hpair x hx P).mapLe (hpiece P.1.1)
  let cp := auxTrimmedConnectorInGraph c hc hcodd hT S hS hpair hunion P
  have hvp : vp.IsPath := by
    simpa [vp] using auxChosenVariablePath_isPath
      c hc hcodd hminimal hT S hS hpair x hx P
  have hcp : cp.IsPath := auxTrimmedConnectorInGraph_isPath
    c hc hcodd hT S hS hpair hunion P
  have hnext := auxSelectedNextPiece_ne_of_two_le_card c hc S hS hScard P
  have hdisj : List.Disjoint vp.support cp.support.tail := by
    apply List.disjoint_left.mpr
    intro v hvv hvc
    have hvCarrier : v ∈ P.1.1.1.1 := by
      apply auxChosenVariablePath_support_subset
        c hc hcodd hminimal hT S hS hpair x hx P v
      simpa [vp] using hvv
    have hnot := auxTrimmedConnector_tail_support_not_mem_start_carrier
      c hc hcodd hminimal hcard hT S hS hpair P hnext v
    exact hnot (by simpa [cp] using hvc) hvCarrier
  rw [SimpleGraph.Walk.isPath_def]
  change (vp.append cp).support.Nodup
  rw [SimpleGraph.Walk.support_append, List.nodup_append]
  refine ⟨hvp.support_nodup, hcp.support_nodup.tail, ?_⟩
  intro a ha b hb hab
  subst b
  exact (List.disjoint_left.mp hdisj) ha hb

lemma auxSelectedSegmentInGraph_tail_support_disjoint
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcard : 3 ≤ (auxPiecesInWalk c).card)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : 2 ≤ S.card)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (hpiece : ∀ P : ↥A, P.1.2 ≤ G) (hunion : packedUnion A ≤ G)
    (x : ↥S → ℕ)
    (hx : ∀ P, (D P.1.1).base ≤ x P ∧
      x P ≤ (D P.1.1).base * T ∧
      x P % 2 = (D P.1.1).residue
        (auxVariableLeft c hc hcodd hT S hS hpair P)
        (auxVariableRight c hc hcodd hT S hS hpair P))
    {P Q : ↥S} (hPQ : P ≠ Q) :
    List.Disjoint
      (auxSelectedSegmentInGraph c hc hcodd hminimal hT S hS hpair
        hpiece hunion x hx P).support.tail
      (auxSelectedSegmentInGraph c hc hcodd hminimal hT S hS hpair
        hpiece hunion x hx Q).support.tail := by
  classical
  let vp : ∀ R : ↥S, G.Walk
      (auxVariableLeft c hc hcodd hT S hS hpair R)
      (auxVariableRight c hc hcodd hT S hS hpair R) := fun R =>
    (auxChosenVariablePath c hc hcodd hminimal hT S hS hpair x hx R).mapLe
      (hpiece R.1.1)
  let cp : ∀ R : ↥S, G.Walk
      (auxVariableRight c hc hcodd hT S hS hpair R)
      (auxVariableLeft c hc hcodd hT S hS hpair
        (auxSelectedGroupSuccessor c hc S hS R)) := fun R =>
    auxTrimmedConnectorInGraph c hc hcodd hT S hS hpair hunion R
  have hvpPath (R : ↥S) : (vp R).IsPath := by
    simpa [vp] using auxChosenVariablePath_isPath
      c hc hcodd hminimal hT S hS hpair x hx R
  have hnext (R : ↥S) : auxSelectedNextPiece c hc S hS R ≠ R.1 :=
    auxSelectedNextPiece_ne_of_two_le_card c hc S hS hScard R
  have hvarConn (R U : ↥S) (hRU : R ≠ U) :
      List.Disjoint (vp R).support.tail (cp U).support.tail := by
    apply List.disjoint_left.mpr
    intro v hvVar hvConn
    have hvCarrier : v ∈ R.1.1.1.1 := by
      apply auxChosenVariablePath_support_subset
        c hc hcodd hminimal hT S hS hpair x hx R v
      exact List.mem_of_mem_tail (by simpa [vp] using hvVar)
    have hcontact := auxTrimmedConnector_selected_carrier_eq_start_or_next
      c hc hcodd hminimal hcard hT S hS hpair U R
      (by
        apply List.mem_of_mem_tail
        simpa [cp] using hvConn)
      hvCarrier
    rcases hcontact with hRUeq | hRnext
    · exact hRU hRUeq
    · have hvCases := SimpleGraph.Walk.mem_dropLast_support_or_eq_end
        (cp U) (List.mem_of_mem_tail hvConn)
      rcases hvCases with hvDrop | hvEnd
      · have havoid :=
          auxTrimmedConnector_dropLast_support_not_mem_next_carrier
            c hc hcodd hminimal hcard hT S hS hpair U (hnext U) v
        have hvDrop' : v ∈
            (auxTrimmedConnector c hc hcodd hT S hS hpair U).support.dropLast := by
          simpa [cp] using hvDrop
        have hvNext : v ∈
            (auxSelectedNextPiece c hc S hS U).1.1.1 := by
          have hval := congrArg Subtype.val hRnext
          change R.1 = auxSelectedNextPiece c hc S hS U at hval
          rw [← hval]
          exact hvCarrier
        exact havoid hvDrop' hvNext
      · have hvStart : v =
            auxVariableLeft c hc hcodd hT S hS hpair R := by
          have hleft := congrArg
            (auxVariableLeft c hc hcodd hT S hS hpair) hRnext
          exact hvEnd.trans hleft.symm
        exact SimpleGraph.Walk.IsPath.start_not_mem_tail_support
          (hvpPath R) (hvStart ▸ hvVar)
  have htail (R : ↥S) :
      (auxSelectedSegmentInGraph c hc hcodd hminimal hT S hS hpair
        hpiece hunion x hx R).support.tail =
      (vp R).support.tail ++ (cp R).support.tail := by
    simp [auxSelectedSegmentInGraph, vp, cp,
      SimpleGraph.Walk.support_append]
  apply List.disjoint_left.mpr
  intro v hvP hvQ
  rw [htail] at hvP hvQ
  simp only [List.mem_append] at hvP hvQ
  rcases hvP with hvPV | hvPC <;> rcases hvQ with hvQV | hvQC
  · have hPQval : P.1 ≠ Q.1 := fun h => hPQ (Subtype.ext h)
    have hd := hpair P.2 Q.2 hPQval
    exact (Finset.disjoint_left.mp hd)
      (auxChosenVariablePath_support_subset
        c hc hcodd hminimal hT S hS hpair x hx P v
        (List.mem_of_mem_tail (by simpa [vp] using hvPV)))
      (auxChosenVariablePath_support_subset
        c hc hcodd hminimal hT S hS hpair x hx Q v
        (List.mem_of_mem_tail (by simpa [vp] using hvQV)))
  · exact (List.disjoint_left.mp (hvarConn P Q hPQ)) hvPV hvQC
  · exact (List.disjoint_left.mp (hvarConn Q P hPQ.symm)) hvQV hvPC
  · have hd := auxTrimmedConnector_support_disjoint
      c hc hcodd hminimal hcard hT S hS hpair hPQ
    exact (List.disjoint_left.mp hd)
      (List.mem_of_mem_tail (by simpa [cp] using hvPC))
      (List.mem_of_mem_tail (by simpa [cp] using hvQC))

/-- When the selected independent class has at least two pieces, the trimmed
variable paths and complementary connectors concatenate cyclically to a
simple ambient cycle of exactly the prescribed length. -/
theorem auxSelectedPieces_realize_cycle_of_two_le_card
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcard : 3 ≤ (auxPiecesInWalk c).card)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : 2 ≤ S.card)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (hpiece : ∀ P : ↥A, P.1.2 ≤ G) (hunion : packedUnion A ≤ G)
    (x : ↥S → ℕ)
    (hx : ∀ P, (D P.1.1).base ≤ x P ∧
      x P ≤ (D P.1.1).base * T ∧
      x P % 2 = (D P.1.1).residue
        (auxVariableLeft c hc hcodd hT S hS hpair P)
        (auxVariableRight c hc hcodd hT S hS hpair P)) :
    HasCycleLength G
      (auxTrimmedFixedLength c hc hcodd hT S hS hpair + ∑ P, x P) := by
  classical
  let O := auxSelectedGroupOrder c hc S hS
  let left : ↥S → V := fun P =>
    auxVariableLeft c hc hcodd hT S hS hpair P
  let right : ↥S → V := fun P =>
    left (auxSelectedGroupSuccessor c hc S hS P)
  let path : ∀ P : ↥S, G.Walk (left P) (right P) := fun P =>
    auxSelectedSegmentInGraph c hc hcodd hminimal hT S hS hpair
      hpiece hunion x hx P
  have hOne : O ≠ [] := auxSelectedGroupOrder_ne_nil c hc S hS
  have hOnodup : O.Nodup := auxSelectedGroupOrder_nodup c hc S hS
  have hnext (P : ↥S) (hP : P ∈ O) :
      right P = left (O.next P hP) := by
    change left (auxSelectedGroupSuccessor c hc S hS P) =
      left (O.next P hP)
    congr 1
    symm
    exact auxSelectedGroupOrder_next_eq_successor c hc S hS P
  have hchain : O.IsChain (fun P Q => right P = left Q) := by
    simpa using list_rotate_isChain_of_rel_next
      (fun P Q => right P = left Q) O hOnodup hnext 0
  let p := appendWalkList left right path O hOne hchain
  have hlastNext :
      O.next (O.getLast hOne) (List.getLast_mem hOne) = O.head hOne :=
    List.next_getLast_eq_head O hOne hOnodup
  have hlastSucc :
      auxSelectedGroupSuccessor c hc S hS (O.getLast hOne) = O.head hOne :=
    (auxSelectedGroupOrder_next_eq_successor c hc S hS
      (O.getLast hOne)).symm.trans hlastNext
  have hclosed : right (O.getLast hOne) = left (O.head hOne) := by
    change left (auxSelectedGroupSuccessor c hc S hS (O.getLast hOne)) =
      left (O.head hOne)
    rw [hlastSucc]
  let w : G.Walk (left (O.head hOne)) (left (O.head hOne)) :=
    p.copy rfl hclosed
  have hpath (P : ↥S) : (path P).IsPath := by
    exact auxSelectedSegmentInGraph_isPath_of_two_le_card
      c hc hcodd hminimal hcard hT S hS hScard hpair hpiece hunion x hx P
  have hdisjoint (P Q : ↥S) (hPQ : P ≠ Q) :
      List.Disjoint (path P).support.tail (path Q).support.tail := by
    exact auxSelectedSegmentInGraph_tail_support_disjoint
      c hc hcodd hminimal hcard hT S hS hScard hpair hpiece hunion x hx hPQ
  have hpTail : p.support.tail.Nodup := by
    exact appendWalkList_tail_support_nodup left right path O hOne hchain
      hOnodup hpath hdisjoint
  have hpathLength (P : ↥S) : (path P).length = x P +
      (auxTrimmedConnector c hc hcodd hT S hS hpair P).length := by
    exact auxSelectedSegmentInGraph_length
      c hc hcodd hminimal hT S hS hpair hpiece hunion x hx P
  have hpLength : p.length =
      auxTrimmedFixedLength c hc hcodd hT S hS hpair + ∑ P, x P := by
    rw [show p = appendWalkList left right path O hOne hchain from rfl,
      appendWalkList_length]
    calc
      (O.map fun P => (path P).length).sum =
          (O.map fun P => x P +
            (auxTrimmedConnector c hc hcodd hT S hS hpair P).length).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro P hP
        exact hpathLength P
      _ = ∑ P ∈ O.toFinset,
          (x P + (auxTrimmedConnector c hc hcodd hT S hS hpair P).length) :=
        (List.sum_toFinset _ hOnodup).symm
      _ = ∑ P : ↥S,
          (x P + (auxTrimmedConnector c hc hcodd hT S hS hpair P).length) := by
        rw [auxSelectedGroupOrder_toFinset c hc S hS]
      _ = auxTrimmedFixedLength c hc hcodd hT S hS hpair + ∑ P, x P := by
        rw [Finset.sum_add_distrib]
        simp only [auxTrimmedFixedLength]
        omega
  have hsegmentLower (P : ↥S) : 2 ≤ x P +
      (auxTrimmedConnector c hc hcodd hT S hS hpair P).length := by
    have hbase : 0 < (D P.1.1).base := (D P.1.1).base_pos
    have hxlow := (hx P).1
    have hconn := auxTrimmedConnector_pos c hc hcodd hT S hS hpair P
    omega
  have hsumLower : 2 * S.card ≤ ∑ P : ↥S,
      (x P + (auxTrimmedConnector c hc hcodd hT S hS hpair P).length) := by
    calc
      2 * S.card = ∑ _P : ↥S, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ P : ↥S,
          (x P + (auxTrimmedConnector c hc hcodd hT S hS hpair P).length) :=
        Finset.sum_le_sum fun P _ => hsegmentLower P
  have hpThree : 3 ≤ p.length := by
    rw [hpLength]
    have hsumEq : (∑ P : ↥S,
        (x P + (auxTrimmedConnector c hc hcodd hT S hS hpair P).length)) =
        auxTrimmedFixedLength c hc hcodd hT S hS hpair + ∑ P, x P := by
      rw [Finset.sum_add_distrib]
      simp only [auxTrimmedFixedLength]
      omega
    have : 4 ≤ auxTrimmedFixedLength c hc hcodd hT S hS hpair + ∑ P, x P := by
      rw [← hsumEq]
      exact (show 4 ≤ 2 * S.card by omega).trans hsumLower
    omega
  refine ⟨left (O.head hOne), w, ?_, ?_⟩
  · apply isCycle_of_three_le_length_of_tail_support_nodup w
    · simpa [w] using hpThree
    · simpa [w] using hpTail
  · simpa [w] using hpLength

/-- Package a selected class of auxiliary-cycle pieces once the geometric
realization statement has been proved.  All numerical, parity, endpoint,
and finite-index bookkeeping is discharged here, leaving the later trimming
argument with exactly one obligation: that every permitted choice of path
lengths really forms a simple ambient cycle. -/
theorem variableCycleAssembly_of_selectedAuxPieces
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (left right : ↥S → V)
    (hleft : ∀ P, left P ∈ P.1.1.1.1)
    (hright : ∀ P, right P ∈ P.1.1.1.1)
    (hne : ∀ P, left P ≠ right P)
    (fixedLength : ℕ)
    (hweight : fixedLength + (∑ P : ↥S, ((D P.1.1).base + 1)) ≤
      3 * ∑ P : ↥S, ((D P.1.1).base + 1))
    (hlower : Odd (fixedLength + ∑ P : ↥S,
      parityStart (D P.1.1).base ((D P.1.1).residue (left P) (right P))))
    (hrealizes : ∀ x : ↥S → ℕ,
      (∀ P, (D P.1.1).base ≤ x P ∧
        x P ≤ (D P.1.1).base * T ∧
        x P % 2 = (D P.1.1).residue (left P) (right P)) →
      HasCycleLength G (fixedLength + ∑ P, x P)) :
    Nonempty (VariableCycleAssembly G T) := by
  classical
  let i₀ : ↥S := ⟨hS.choose, hS.choose_spec⟩
  refine ⟨{
    Index := ↥S
    indexFintype := inferInstance
    indexNonempty := ⟨i₀⟩
    piece := fun P => P.1.1.1
    data := fun P => D P.1.1
    left := left
    right := right
    left_mem := hleft
    right_mem := hright
    endpoints_ne := hne
    fixedLength := fixedLength
    weight := hweight
    lower_odd := hlower
    realizes := hrealizes
  }⟩

/-- The selected-class construction yields the required variable-cycle
assembly whenever the selected class has at least two members. -/
theorem variableCycleAssembly_of_selectedAuxPieces_two_le
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : 2 ≤ S.card)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (hweight : (∑ P : ↥(auxPiecesInWalk c), ((D P.1).base + 1)) ≤
      3 * ∑ P ∈ S, ((D P.1).base + 1))
    (hpiece : ∀ P : ↥A, P.1.2 ≤ G) (hunion : packedUnion A ≤ G) :
    Nonempty (VariableCycleAssembly G T) := by
  have hcard : 3 ≤ (auxPiecesInWalk c).card :=
    three_le_auxPiecesInWalk_card_of_two_selected c hc hcodd S hScard hpair
  refine variableCycleAssembly_of_selectedAuxPieces c S hS
    (auxVariableLeft c hc hcodd hT S hS hpair)
    (auxVariableRight c hc hcodd hT S hS hpair)
    ?_ ?_ ?_ (auxTrimmedFixedLength c hc hcodd hT S hS hpair) ?_ ?_ ?_
  · exact auxVariableLeft_mem c hc hcodd hT S hS hpair
  · exact auxVariableRight_mem c hc hcodd hT S hS hpair
  · exact auxVariableLeft_ne_right
      c hc hcodd hminimal hT S hS hpair
  · exact auxTrimmedFixedLength_weight
      c hc hcodd hT S hS hpair hweight
  · exact auxTrimmedFixedLength_lower_odd
      c hc hcodd hminimal hcarrier hT S hS hpair
  · intro x hx
    exact auxSelectedPieces_realize_cycle_of_two_le_card
      c hc hcodd hminimal hcard hT S hS hScard hpair
      hpiece hunion x hx

/-! ### The singleton selected-class case -/

lemma auxSingleton_unique
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} {c : (familyAuxGraph D).Walk z z}
    {S : Finset ↥(auxPiecesInWalk c)} (hScard : S.card = 1)
    (P Q : ↥S) : P = Q := by
  apply Subtype.ext
  obtain ⟨R, hR⟩ := Finset.card_eq_one.mp hScard
  have hP : P.1 = R := by simpa [hR] using P.2
  have hQ : Q.1 = R := by simpa [hR] using Q.2
  exact hP.trans hQ.symm

lemma auxSelectedNextPiece_eq_self_of_card_eq_one
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (S : Finset ↥(auxPiecesInWalk c))
    (hS : S.Nonempty) (hScard : S.card = 1) (P : ↥S) :
    auxSelectedNextPiece c hc S hS P = P.1 := by
  let Q : ↥S := ⟨auxSelectedNextPiece c hc S hS P,
    auxSelectedNextPiece_mem c hc S hS P⟩
  exact congrArg Subtype.val (auxSingleton_unique hScard Q P)

lemma auxRawConnector_length_eq_selectedFixedLength_of_card_eq_one
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length =
      auxSelectedFixedLength c hc hcodd S := by
  have hsumOne :
      (∑ Q : ↥S,
        (auxComplementaryRawWalk c hc hcodd hT S hS hpair Q).length) =
        (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length := by
    rw [Finset.sum_eq_single P]
    · intro Q _ hQP
      exact (hQP (auxSingleton_unique hScard Q P)).elim
    · simp
  have hsum := auxRawConnectorSum_eq_selectedFixedLength
    c hc hcodd hT S hS hpair
  rw [hsumOne] at hsum
  exact hsum

lemma auxSingleton_canonical_combined_relations_ne
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    ¬(((D P.1.1).color (auxPieceRight c hc hcodd P.1) =
          (D P.1.1).color (auxPieceLeft c hc hcodd P.1)) ↔
        (auxCanonicalComplementColor c S (auxPieceRight c hc hcodd P.1) =
          auxCanonicalComplementColor c S (auxPieceLeft c hc hcodd P.1))) := by
  obtain ⟨Q, hSsingle⟩ := Finset.card_eq_one.mp hScard
  have hPQ : P.1 = Q := by simpa [hSsingle] using P.2
  subst Q
  have hraw := auxRawConnector_length_eq_selectedFixedLength_of_card_eq_one
    c hc hcodd hT S hS hScard hpair P
  have hnext := auxSelectedNextPiece_eq_self_of_card_eq_one
    c hc S hS hScard P
  have hoddRaw : Odd
      ((auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length +
        parityStart (D P.1.1).base
          ((D P.1.1).residue (auxPieceLeft c hc hcodd P.1)
            (auxPieceRight c hc hcodd P.1))) := by
    have hodd := auxSelectedFixedLength_lower_odd c hc hcodd S
    simpa [hSsingle, hraw] using hodd
  have hcast := hoddRaw.natCast_zmod_two
  rw [Nat.cast_add,
    auxRawConnector_length_cast c hc hcodd hminimal hcarrier
      hT S hS hpair P,
    parityStart_cast_eq_residue ((D P.1.1).residue_lt_two _ _),
    (D P.1.1).residue_cast_eq_color_val_add] at hcast
  rw [hnext] at hcast
  have hne := finTwo_pair_relations_ne_of_val_sum_eq_one
    (auxCanonicalComplementColor c S (auxPieceRight c hc hcodd P.1))
    (auxCanonicalComplementColor c S (auxPieceLeft c hc hcodd P.1))
    ((D P.1.1).color (auxPieceLeft c hc hcodd P.1))
    ((D P.1.1).color (auxPieceRight c hc hcodd P.1))
    (by simpa [add_assoc] using hcast)
  intro hrel
  apply hne
  constructor
  · intro hcomp
    exact (hrel.mpr hcomp).symm
  · intro hpiece
    exact hrel.mp hpiece.symm

noncomputable def auxSingletonStartSet
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (P : ↥S) : Finset V :=
  P.1.1.1.1.filter fun v =>
    ((D P.1.1).color v =
        (D P.1.1).color (auxPieceRight c hc hcodd P.1)) ↔
      (auxCanonicalComplementColor c S v =
        auxCanonicalComplementColor c S (auxPieceRight c hc hcodd P.1))

noncomputable def auxSingletonEndSet
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (P : ↥S) : Finset V :=
  P.1.1.1.1.filter fun v =>
    ((D P.1.1).color v =
        (D P.1.1).color (auxPieceLeft c hc hcodd P.1)) ↔
      (auxCanonicalComplementColor c S v =
        auxCanonicalComplementColor c S (auxPieceLeft c hc hcodd P.1))

lemma auxSingletonStart_mem
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (P : ↥S) :
    auxPieceRight c hc hcodd P.1 ∈ auxSingletonStartSet c hc hcodd S P := by
  simp [auxSingletonStartSet, auxPieceRight_mem]

lemma auxSingletonEnd_mem
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (S : Finset ↥(auxPiecesInWalk c)) (P : ↥S) :
    auxPieceLeft c hc hcodd P.1 ∈ auxSingletonEndSet c hc hcodd S P := by
  simp [auxSingletonEndSet, auxPieceLeft_mem]

lemma auxSingletonSets_disjoint
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    Disjoint (auxSingletonStartSet c hc hcodd S P)
      (auxSingletonEndSet c hc hcodd S P) := by
  apply Finset.disjoint_left.mpr
  intro v hvStart hvEnd
  have hs := (Finset.mem_filter.mp hvStart).2
  have he := (Finset.mem_filter.mp hvEnd).2
  have hcenters := auxSingleton_canonical_combined_relations_ne
    c hc hcodd hminimal hcarrier hT S hS hScard hpair P
  exact (finTwo_combined_relations_complementary
    ((D P.1.1).color v) (auxCanonicalComplementColor c S v)
    ((D P.1.1).color (auxPieceRight c hc hcodd P.1))
    (auxCanonicalComplementColor c S (auxPieceRight c hc hcodd P.1))
    ((D P.1.1).color (auxPieceLeft c hc hcodd P.1))
    (auxCanonicalComplementColor c S (auxPieceLeft c hc hcodd P.1))
    hcenters).mp hs he

lemma auxSingleton_mem_start_or_end
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) {v : V} (hv : v ∈ P.1.1.1.1) :
    v ∈ auxSingletonStartSet c hc hcodd S P ∨
      v ∈ auxSingletonEndSet c hc hcodd S P := by
  let Arel :=
    ((D P.1.1).color v =
        (D P.1.1).color (auxPieceRight c hc hcodd P.1)) ↔
      (auxCanonicalComplementColor c S v =
        auxCanonicalComplementColor c S (auxPieceRight c hc hcodd P.1))
  let Brel :=
    ((D P.1.1).color v =
        (D P.1.1).color (auxPieceLeft c hc hcodd P.1)) ↔
      (auxCanonicalComplementColor c S v =
        auxCanonicalComplementColor c S (auxPieceLeft c hc hcodd P.1))
  have hcenters := auxSingleton_canonical_combined_relations_ne
    c hc hcodd hminimal hcarrier hT S hS hScard hpair P
  have hcomp : Arel ↔ ¬Brel := finTwo_combined_relations_complementary
    ((D P.1.1).color v) (auxCanonicalComplementColor c S v)
    ((D P.1.1).color (auxPieceRight c hc hcodd P.1))
    (auxCanonicalComplementColor c S (auxPieceRight c hc hcodd P.1))
    ((D P.1.1).color (auxPieceLeft c hc hcodd P.1))
    (auxCanonicalComplementColor c S (auxPieceLeft c hc hcodd P.1))
    hcenters
  by_cases ha : Arel
  · left
    exact Finset.mem_filter.mpr ⟨hv, ha⟩
  · right
    apply Finset.mem_filter.mpr
    refine ⟨hv, ?_⟩
    by_contra hb
    exact ha (hcomp.mpr hb)

noncomputable def auxSingletonConnector
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :=
  trimWalkBetween
    (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P)
    (fun x => x ∈ auxSingletonStartSet c hc hcodd S P)
    (fun x => x ∈ auxSingletonEndSet c hc hcodd S P)
    (auxSingletonStart_mem c hc hcodd S P)
    (by
      have hnext := auxSelectedNextPiece_eq_self_of_card_eq_one
        c hc S hS hScard P
      simpa [hnext] using auxSingletonEnd_mem c hc hcodd S P)

lemma auxSingletonConnector_isPath
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    (auxSingletonConnector c hc hcodd hT S hS hScard hpair P).IsPath := by
  exact trimWalkBetween_isPath
    (auxComplementaryPathInComplement_isPath c hc hcodd hT S hS hpair P)
    _ _ _ _

lemma auxSingletonConnector_length_le
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    (auxSingletonConnector c hc hcodd hT S hS hScard hpair P).length ≤
      (auxComplementaryRawWalk c hc hcodd hT S hS hpair P).length := by
  exact (trimWalkBetween_length_le
    (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P)
    _ _ _ _).trans
      (auxComplementaryPathInComplement_length_le
        c hc hcodd hT S hS hpair P)

lemma auxSingletonConnector_pos
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    0 < (auxSingletonConnector c hc hcodd hT S hS hScard hpair P).length := by
  exact trimWalkBetween_pos_of_disjoint
    (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P)
    (auxSingletonStartSet c hc hcodd S P)
    (auxSingletonEndSet c hc hcodd S P)
    (auxSingletonStart_mem c hc hcodd S P)
    (by
      have hnext := auxSelectedNextPiece_eq_self_of_card_eq_one
        c hc S hS hScard P
      simpa [hnext] using auxSingletonEnd_mem c hc hcodd S P)
    (auxSingletonSets_disjoint c hc hcodd hminimal hcarrier
      hT S hS hScard hpair P)

noncomputable def auxSingletonRight
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) : V :=
  (auxSingletonConnector c hc hcodd hT S hS hScard hpair P).getVert 0

noncomputable def auxSingletonLeft
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) : V :=
  let q := auxSingletonConnector c hc hcodd hT S hS hScard hpair P
  q.getVert q.length

lemma auxSingletonRight_mem_startSet
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    auxSingletonRight c hc hcodd hT S hS hScard hpair P ∈
      auxSingletonStartSet c hc hcodd S P := by
  have hmem := trimWalkBetween_start_mem
    (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P)
    (fun x => x ∈ auxSingletonStartSet c hc hcodd S P)
    (fun x => x ∈ auxSingletonEndSet c hc hcodd S P)
    (auxSingletonStart_mem c hc hcodd S P)
    (by
      have hnext := auxSelectedNextPiece_eq_self_of_card_eq_one
        c hc S hS hScard P
      simpa [hnext] using auxSingletonEnd_mem c hc hcodd S P)
  simpa [auxSingletonRight, auxSingletonConnector] using hmem

lemma auxSingletonLeft_mem_endSet
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    auxSingletonLeft c hc hcodd hT S hS hScard hpair P ∈
      auxSingletonEndSet c hc hcodd S P := by
  have hmem := trimWalkBetween_end_mem
    (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P)
    (fun x => x ∈ auxSingletonStartSet c hc hcodd S P)
    (fun x => x ∈ auxSingletonEndSet c hc hcodd S P)
    (auxSingletonStart_mem c hc hcodd S P)
    (by
      have hnext := auxSelectedNextPiece_eq_self_of_card_eq_one
        c hc S hS hScard P
      simpa [hnext] using auxSingletonEnd_mem c hc hcodd S P)
  have hend := trimWalkBetween_getVert_length
    (auxComplementaryPathInComplement c hc hcodd hT S hS hpair P)
    (fun x => x ∈ auxSingletonStartSet c hc hcodd S P)
    (fun x => x ∈ auxSingletonEndSet c hc hcodd S P)
    (auxSingletonStart_mem c hc hcodd S P)
    (by
      have hnext := auxSelectedNextPiece_eq_self_of_card_eq_one
        c hc S hS hScard P
      simpa [hnext] using auxSingletonEnd_mem c hc hcodd S P)
  simpa [auxSingletonLeft, auxSingletonConnector, hend] using hmem

lemma auxSingletonRight_mem
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    auxSingletonRight c hc hcodd hT S hS hScard hpair P ∈ P.1.1.1.1 :=
  (Finset.mem_filter.mp
    (auxSingletonRight_mem_startSet c hc hcodd hT S hS hScard hpair P)).1

lemma auxSingletonLeft_mem
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    auxSingletonLeft c hc hcodd hT S hS hScard hpair P ∈ P.1.1.1.1 :=
  (Finset.mem_filter.mp
    (auxSingletonLeft_mem_endSet c hc hcodd hT S hS hScard hpair P)).1

lemma auxSingletonLeft_ne_right
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    auxSingletonLeft c hc hcodd hT S hS hScard hpair P ≠
      auxSingletonRight c hc hcodd hT S hS hScard hpair P := by
  intro h
  have hs := auxSingletonRight_mem_startSet
    c hc hcodd hT S hS hScard hpair P
  have he := auxSingletonLeft_mem_endSet
    c hc hcodd hT S hS hScard hpair P
  exact (Finset.disjoint_left.mp
    (auxSingletonSets_disjoint c hc hcodd hminimal hcarrier
      hT S hS hScard hpair P)) (h.symm ▸ hs) he

lemma auxSingletonRight_colorAgreement
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    ((D P.1.1).color
        (auxSingletonRight c hc hcodd hT S hS hScard hpair P) =
        (D P.1.1).color (auxPieceRight c hc hcodd P.1)) ↔
      (auxCanonicalComplementColor c S
          (auxSingletonRight c hc hcodd hT S hS hScard hpair P) =
        auxCanonicalComplementColor c S
          (auxPieceRight c hc hcodd P.1)) :=
  (Finset.mem_filter.mp
    (auxSingletonRight_mem_startSet c hc hcodd hT S hS hScard hpair P)).2

lemma auxSingletonLeft_colorAgreement
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length) (hT : 3 ≤ T)
    (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    ((D P.1.1).color
        (auxSingletonLeft c hc hcodd hT S hS hScard hpair P) =
        (D P.1.1).color (auxPieceLeft c hc hcodd P.1)) ↔
      (auxCanonicalComplementColor c S
          (auxSingletonLeft c hc hcodd hT S hS hScard hpair P) =
        auxCanonicalComplementColor c S
          (auxPieceLeft c hc hcodd P.1)) :=
  (Finset.mem_filter.mp
    (auxSingletonLeft_mem_endSet c hc hcodd hT S hS hScard hpair P)).2

lemma auxSingletonConnector_length_cast
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    ((auxSingletonConnector c hc hcodd hT S hS hScard hpair P).length :
        ZMod 2) =
      ((auxCanonicalComplementColor c S
          (auxSingletonRight c hc hcodd hT S hS hScard hpair P)).val :
        ZMod 2) +
      (auxCanonicalComplementColor c S
        (auxSingletonLeft c hc hcodd hT S hS hScard hpair P)).val := by
  let color := auxCanonicalComplementGraphColoring
    c hc hcodd hminimal hcarrier S hS
  have h := coloring_walk_length_cast_eq_color_val_add color
    (auxSingletonConnector c hc hcodd hT S hS hScard hpair P)
  simpa [color, auxSingletonRight, auxSingletonLeft] using h

lemma auxSingleton_lower_odd
    {V : Type*} [Fintype V]
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (P : ↥S) :
    Odd ((auxSingletonConnector c hc hcodd hT S hS hScard hpair P).length +
      parityStart (D P.1.1).base
        ((D P.1.1).residue
          (auxSingletonLeft c hc hcodd hT S hS hScard hpair P)
          (auxSingletonRight c hc hcodd hT S hS hScard hpair P))) := by
  let newL := auxSingletonLeft c hc hcodd hT S hS hScard hpair P
  let newR := auxSingletonRight c hc hcodd hT S hS hScard hpair P
  let oldL := auxPieceLeft c hc hcodd P.1
  let oldR := auxPieceRight c hc hcodd P.1
  let comp := auxCanonicalComplementColor c S
  let piece := (D P.1.1).color
  let conn := auxSingletonConnector c hc hcodd hT S hS hScard hpair P
  let raw := auxComplementaryRawWalk c hc hcodd hT S hS hpair P
  obtain ⟨Q, hSsingle⟩ := Finset.card_eq_one.mp hScard
  have hPQ : P.1 = Q := by simpa [hSsingle] using P.2
  subst Q
  have hrawEq := auxRawConnector_length_eq_selectedFixedLength_of_card_eq_one
    c hc hcodd hT S hS hScard hpair P
  have hoddRaw : Odd (raw.length +
      parityStart (D P.1.1).base ((D P.1.1).residue oldL oldR)) := by
    have hodd := auxSelectedFixedLength_lower_odd c hc hcodd S
    simpa [hSsingle, hrawEq, raw, oldL, oldR] using hodd
  have hconnCast : (conn.length : ZMod 2) =
      ((comp newR).val : ZMod 2) + (comp newL).val := by
    simpa [conn, comp, newR, newL] using
      auxSingletonConnector_length_cast c hc hcodd hminimal hcarrier
        hT S hS hScard hpair P
  have hrawCast : (raw.length : ZMod 2) =
      ((comp oldR).val : ZMod 2) + (comp oldL).val := by
    have hnext := auxSelectedNextPiece_eq_self_of_card_eq_one
      c hc S hS hScard P
    simpa [raw, comp, oldR, oldL, hnext] using
      auxRawConnector_length_cast c hc hcodd hminimal hcarrier
        hT S hS hpair P
  have hright : ((piece newR).val : ZMod 2) + (comp newR).val =
      ((piece oldR).val : ZMod 2) + (comp oldR).val := by
    exact finTwo_cross_val_add_eq_of_eq_iff_eq _ _ _ _
      (by simpa [piece, comp, newR, oldR] using
        (auxSingletonRight_colorAgreement
          c hc hcodd hT S hS hScard hpair P))
  have hleft : ((piece newL).val : ZMod 2) + (comp newL).val =
      ((piece oldL).val : ZMod 2) + (comp oldL).val := by
    exact finTwo_cross_val_add_eq_of_eq_iff_eq _ _ _ _
      (by simpa [piece, comp, newL, oldL] using
        (auxSingletonLeft_colorAgreement
          c hc hcodd hT S hS hScard hpair P))
  apply odd_of_zmod_two_natCast_eq_one
  calc
    ((conn.length +
        parityStart (D P.1.1).base ((D P.1.1).residue newL newR) : ℕ) :
        ZMod 2) =
      (((comp newR).val : ZMod 2) + (comp newL).val) +
        (((piece newL).val : ZMod 2) + (piece newR).val) := by
          rw [Nat.cast_add, hconnCast,
            parityStart_cast_eq_residue ((D P.1.1).residue_lt_two _ _),
            (D P.1.1).residue_cast_eq_color_val_add]
    _ = (((piece newR).val : ZMod 2) + (comp newR).val) +
        (((piece newL).val : ZMod 2) + (comp newL).val) := by ring
    _ = (((piece oldR).val : ZMod 2) + (comp oldR).val) +
        (((piece oldL).val : ZMod 2) + (comp oldL).val) := by
          rw [hright, hleft]
    _ = (((comp oldR).val : ZMod 2) + (comp oldL).val) +
        (((piece oldL).val : ZMod 2) + (piece oldR).val) := by ring
    _ = ((raw.length +
        parityStart (D P.1.1).base ((D P.1.1).residue oldL oldR) : ℕ) :
        ZMod 2) := by
          rw [Nat.cast_add, hrawCast,
            parityStart_cast_eq_residue ((D P.1.1).residue_lt_two _ _),
            (D P.1.1).residue_cast_eq_color_val_add]
    _ = 1 := hoddRaw.natCast_zmod_two

theorem auxSingleton_realize_cycle
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (hpiece : ∀ P : ↥A, P.1.2 ≤ G) (hunion : packedUnion A ≤ G)
    (P : ↥S) (n : ℕ)
    (hn : (D P.1.1).base ≤ n ∧ n ≤ (D P.1.1).base * T ∧
      n % 2 = (D P.1.1).residue
        (auxSingletonLeft c hc hcodd hT S hS hScard hpair P)
        (auxSingletonRight c hc hcodd hT S hS hScard hpair P)) :
    HasCycleLength G
      ((auxSingletonConnector c hc hcodd hT S hS hScard hpair P).length + n) := by
  let L := auxSingletonLeft c hc hcodd hT S hS hScard hpair P
  let R := auxSingletonRight c hc hcodd hT S hS hScard hpair P
  let conn := auxSingletonConnector c hc hcodd hT S hS hScard hpair P
  obtain ⟨vp₀, hvpPath₀, hvpLen, hvpSupp⟩ :=
    (D P.1.1).hasPath_of_modEq
      (auxSingletonLeft_mem c hc hcodd hT S hS hScard hpair P)
      (auxSingletonRight_mem c hc hcodd hT S hS hScard hpair P)
      (auxSingletonLeft_ne_right c hc hcodd hminimal hcarrier
        hT S hS hScard hpair P)
      hn.1 hn.2.1 hn.2.2
  let vp : G.Walk L R := vp₀.mapLe (hpiece P.1.1)
  let cp : G.Walk R L :=
    (conn.mapLe ((auxComplementGraph_le_packedUnion c S).trans hunion)).copy
      (by simp [R, conn, auxSingletonRight])
      (by simp [L, conn, auxSingletonLeft])
  have hvpPath : vp.IsPath := by simpa [vp] using hvpPath₀
  have hcpPath : cp.IsPath := by
    simpa [cp, conn] using
      auxSingletonConnector_isPath c hc hcodd hT S hS hScard hpair P
  have hend :
      auxPieceLeft c hc hcodd P.1 ∈ auxSingletonEndSet c hc hcodd S P :=
    auxSingletonEnd_mem c hc hcodd S P
  have hnext := auxSelectedNextPiece_eq_self_of_card_eq_one
    c hc S hS hScard P
  have hendRaw : auxPieceLeft c hc hcodd
      (auxSelectedNextPiece c hc S hS P) ∈
        auxSingletonEndSet c hc hcodd S P := by simpa [hnext] using hend
  have hnoStart : ∀ v ∈ conn.support.tail,
      v ∉ auxSingletonStartSet c hc hcodd S P := by
    simpa [conn, auxSingletonConnector] using
      (trimWalkBetween_tail_support_not_mem_start
        (auxComplementaryPathInComplement_isPath
          c hc hcodd hT S hS hpair P)
        (fun x => x ∈ auxSingletonStartSet c hc hcodd S P)
        (fun x => x ∈ auxSingletonEndSet c hc hcodd S P)
        (auxSingletonStart_mem c hc hcodd S P) hendRaw)
  have hnoEnd : ∀ v ∈ conn.support.dropLast,
      v ∉ auxSingletonEndSet c hc hcodd S P := by
    simpa [conn, auxSingletonConnector] using
      (trimWalkBetween_dropLast_support_not_mem_end
        (auxComplementaryPathInComplement_isPath
          c hc hcodd hT S hS hpair P)
        (fun x => x ∈ auxSingletonStartSet c hc hcodd S P)
        (fun x => x ∈ auxSingletonEndSet c hc hcodd S P)
        (auxSingletonStart_mem c hc hcodd S P) hendRaw)
  have hcross : List.Disjoint vp.support.tail cp.support.tail := by
    apply List.disjoint_left.mpr
    intro v hvp hvcp
    have hvCarrier : v ∈ P.1.1.1.1 := by
      apply hvpSupp
      exact List.mem_of_mem_tail (by simpa [vp] using hvp)
    have hvConnTail : v ∈ conn.support.tail := by simpa [cp] using hvcp
    rcases auxSingleton_mem_start_or_end
      c hc hcodd hminimal hcarrier hT S hS hScard hpair P hvCarrier with
      hvStart | hvEnd
    · exact hnoStart v hvConnTail hvStart
    · have hvCases := SimpleGraph.Walk.mem_dropLast_support_or_eq_end
        cp (List.mem_of_mem_tail hvcp)
      rcases hvCases with hvDrop | hvLast
      · have hvDropConn : v ∈ conn.support.dropLast := by simpa [cp] using hvDrop
        exact hnoEnd v hvDropConn hvEnd
      · have hvL : v = L := hvLast
        exact SimpleGraph.Walk.IsPath.start_not_mem_tail_support
          hvpPath (hvL ▸ hvp)
  let w : G.Walk L L := vp.append cp
  have hwTail : w.support.tail.Nodup := by
    rw [show w = vp.append cp from rfl, SimpleGraph.Walk.support_append,
      ← vp.cons_tail_support]
    change (vp.support.tail ++ cp.support.tail).Nodup
    rw [List.nodup_append]
    refine ⟨hvpPath.support_nodup.tail, hcpPath.support_nodup.tail, ?_⟩
    intro a ha b hb hab
    subst b
    exact (List.disjoint_left.mp hcross) ha hb
  have hlower := auxSingleton_lower_odd
    c hc hcodd hminimal hcarrier hT S hS hScard hpair P
  have hnCast : (n : ZMod 2) =
      (parityStart (D P.1.1).base ((D P.1.1).residue L R) : ZMod 2) := by
    calc
      (n : ZMod 2) = ((n % 2 : ℕ) : ZMod 2) := (ZMod.natCast_mod _ 2).symm
      _ = ((D P.1.1).residue L R : ZMod 2) := by
        exact congrArg (fun k : ℕ => (k : ZMod 2))
          (by simpa [L, R] using hn.2.2)
      _ = (parityStart (D P.1.1).base ((D P.1.1).residue L R) :
          ZMod 2) := (parityStart_cast_eq_residue
            ((D P.1.1).residue_lt_two L R)).symm
  have hodd : Odd (conn.length + n) := by
    apply odd_of_zmod_two_natCast_eq_one
    rw [Nat.cast_add, hnCast]
    simpa [conn, L, R] using hlower.natCast_zmod_two
  have hwLen : w.length = conn.length + n := by
    simp [w, vp, cp, hvpLen, Nat.add_comm]
  have hwThree : 3 ≤ w.length := by
    have hconnPos : 0 < conn.length := by
      simpa [conn] using auxSingletonConnector_pos
        c hc hcodd hminimal hcarrier hT S hS hScard hpair P
    have hbasePos := (D P.1.1).base_pos
    have hnPos : 0 < n := hbasePos.trans_le hn.1
    have hmod := mod_two_eq_one_of_odd hodd
    rw [hwLen]
    omega
  refine ⟨L, w, ?_, ?_⟩
  · exact isCycle_of_three_le_length_of_tail_support_nodup w hwThree hwTail
  · simpa [conn] using hwLen

theorem variableCycleAssembly_of_selectedAuxPieces_card_eq_one
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    {A : Finset (PackedSubgraph V)} {T : ℕ}
    {D : (P : ↥A) → FlexiblePathData T P.1}
    {z : FamilyAuxVertex V A} (c : (familyAuxGraph D).Walk z z)
    (hc : c.IsCycle) (hcodd : Odd c.length)
    (hminimal : ∀ z' (c' : (familyAuxGraph D).Walk z' z'),
      c'.IsCycle → Odd c'.length →
        (auxPiecesInWalk c).card ≤ (auxPiecesInWalk c').card)
    (hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1)
    (hT : 3 ≤ T) (S : Finset ↥(auxPiecesInWalk c)) (hS : S.Nonempty)
    (hScard : S.card = 1)
    (hpair : (↑S : Set ↥(auxPiecesInWalk c)).Pairwise
      (fun P Q => Disjoint P.1.1.1 Q.1.1.1))
    (hweight : (∑ P : ↥(auxPiecesInWalk c), ((D P.1).base + 1)) ≤
      3 * ∑ P ∈ S, ((D P.1).base + 1))
    (hpiece : ∀ P : ↥A, P.1.2 ≤ G) (hunion : packedUnion A ≤ G) :
    Nonempty (VariableCycleAssembly G T) := by
  let P : ↥S := ⟨hS.choose, hS.choose_spec⟩
  let fixed := (auxSingletonConnector c hc hcodd hT S hS hScard hpair P).length
  let left := auxSingletonLeft c hc hcodd hT S hS hScard hpair P
  let right := auxSingletonRight c hc hcodd hT S hS hScard hpair P
  obtain ⟨Q, hSsingle⟩ := Finset.card_eq_one.mp hScard
  have hPQ : P.1 = Q := by simpa [hSsingle] using P.2
  subst Q
  have hrawEq := auxRawConnector_length_eq_selectedFixedLength_of_card_eq_one
    c hc hcodd hT S hS hScard hpair P
  have hfixedLe : fixed ≤ auxSelectedFixedLength c hc hcodd S := by
    exact (auxSingletonConnector_length_le
      c hc hcodd hT S hS hScard hpair P).trans_eq hrawEq
  have hselectedWeight := auxSelectedFixedLength_weight
    c hc hcodd S hweight
  have hselectedWeight' :
      auxSelectedFixedLength c hc hcodd S + ((D P.1.1).base + 1) ≤
        3 * ((D P.1.1).base + 1) := by
    simpa [hSsingle] using hselectedWeight
  have hfinalWeight : fixed + ((D P.1.1).base + 1) ≤
      3 * ((D P.1.1).base + 1) :=
    (Nat.add_le_add_right hfixedLe _).trans hselectedWeight'
  have hlower : Odd (fixed +
      parityStart (D P.1.1).base ((D P.1.1).residue left right)) := by
    simpa [fixed, left, right] using auxSingleton_lower_odd
      c hc hcodd hminimal hcarrier hT S hS hScard hpair P
  refine ⟨{
    Index := ULift.{u} Unit
    indexFintype := inferInstance
    indexNonempty := inferInstance
    piece := fun _ => P.1.1.1
    data := fun _ => D P.1.1
    left := fun _ => left
    right := fun _ => right
    left_mem := fun _ => auxSingletonLeft_mem
      c hc hcodd hT S hS hScard hpair P
    right_mem := fun _ => auxSingletonRight_mem
      c hc hcodd hT S hS hScard hpair P
    endpoints_ne := fun _ => auxSingletonLeft_ne_right
      c hc hcodd hminimal hcarrier hT S hS hScard hpair P
    fixedLength := fixed
    weight := by simpa using hfinalWeight
    lower_odd := by simpa using hlower
    realizes := by
      intro x hx
      have hcycle := auxSingleton_realize_cycle
        c hc hcodd hminimal hcarrier hT S hS hScard hpair
        hpiece hunion P (x (ULift.up ())) (by simpa using hx (ULift.up ()))
      simpa [fixed] using hcycle
  }⟩

/-- Formal Liu--Montgomery Section 5 assembly theorem.  A minimum-piece odd
cycle in the signed incidence graph supplies a maximum-weight separated
class.  The preceding two constructions cover respectively its singleton
and multi-piece cases. -/
theorem flexiblePackingAssembly : FlexiblePackingAssembly := by
  intro T hT V _ G A hgood hfamilyPair hunion
  obtain ⟨z, c, hc, hcodd, hminimal⟩ :=
    exists_minimal_odd_familyAux_cycle hgood hunion
  obtain ⟨S, hS, hpair, hweight⟩ :=
    exists_weighted_carrier_disjoint_piece_class c hc hcodd hminimal
  have hcarrier : ∀ P : ↥A, ∀ {u v : V}, P.1.2.Adj u v →
      u ∈ P.1.1 ∧ v ∈ P.1.1 := by
    intro P u v huv
    exact (hgood P.1 P.2).2.2.2.1 huv
  have hpiece : ∀ P : ↥A, P.1.2 ≤ G := by
    intro P
    exact (hgood P.1 P.2).2.2.1
  have hunionLe : packedUnion A ≤ G := packedUnion_le hgood
  by_cases hScard : S.card = 1
  · exact variableCycleAssembly_of_selectedAuxPieces_card_eq_one
      c hc hcodd hminimal hcarrier hT S hS hScard hpair hweight
      hpiece hunionLe
  · have htwo : 2 ≤ S.card := by
      have hpos := hS.card_pos
      omega
    exact variableCycleAssembly_of_selectedAuxPieces_two_le
      c hc hcodd hminimal hcarrier hT S hS htwo hpair hweight
      hpiece hunionLe

/-! ### Quantitative harmonic mass in long odd intervals -/

/-- A block of `M` consecutive odd numbers, all lying strictly between `2*M` and `4*M`. -/
def oddBlock (M : ℕ) : Finset ℕ :=
  (Finset.range M).image fun j => 2 * M + 2 * j + 1

lemma mem_oddBlock_iff {M n : ℕ} :
    n ∈ oddBlock M ↔ ∃ j < M, n = 2 * M + 2 * j + 1 := by
  simp [oddBlock, eq_comm]

lemma oddBlock_card (M : ℕ) : (oddBlock M).card = M := by
  rw [oddBlock, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    dsimp at hab
    omega

lemma odd_of_mem_oddBlock {M n : ℕ} (hn : n ∈ oddBlock M) : Odd n := by
  obtain ⟨j, hj, rfl⟩ := mem_oddBlock_iff.mp hn
  exact ⟨M + j, by omega⟩

lemma two_mul_lt_of_mem_oddBlock {M n : ℕ} (hn : n ∈ oddBlock M) : 2 * M < n := by
  obtain ⟨j, hj, rfl⟩ := mem_oddBlock_iff.mp hn
  omega

lemma lt_four_mul_of_mem_oddBlock {M n : ℕ} (hn : n ∈ oddBlock M) : n < 4 * M := by
  obtain ⟨j, hj, rfl⟩ := mem_oddBlock_iff.mp hn
  omega

/-- Every nonempty odd block carries at least `1/4` of harmonic mass. -/
lemma quarter_le_sum_oddBlock_inv {M : ℕ} (hM : 0 < M) :
    (1 / 4 : ℝ) ≤ ∑ n ∈ oddBlock M, (n : ℝ)⁻¹ := by
  have hterm : ∀ n ∈ oddBlock M, ((4 * M : ℕ) : ℝ)⁻¹ ≤ (n : ℝ)⁻¹ := by
    intro n hn
    apply (inv_le_inv₀ (by positivity) (by
      exact_mod_cast Nat.zero_lt_of_lt (two_mul_lt_of_mem_oddBlock hn))).2
    exact_mod_cast lt_four_mul_of_mem_oddBlock hn |>.le
  calc
    (1 / 4 : ℝ) = (M : ℝ) * ((4 * M : ℕ) : ℝ)⁻¹ := by
      norm_num [Nat.cast_mul, hM.ne']
    _ = ∑ _n ∈ oddBlock M, ((4 * M : ℕ) : ℝ)⁻¹ := by
      simp [oddBlock_card]
    _ ≤ ∑ n ∈ oddBlock M, (n : ℝ)⁻¹ := Finset.sum_le_sum hterm

/-- The scale of the `i`-th separated odd block. -/
def blockScale (L i : ℕ) : ℕ := 4 ^ i * L

lemma blockScale_pos {L : ℕ} (hL : 0 < L) (i : ℕ) : 0 < blockScale L i := by
  exact Nat.mul_pos (pow_pos (by norm_num) _) hL

lemma four_mul_blockScale_le {L i j : ℕ} (hij : i < j) :
    4 * blockScale L i ≤ blockScale L j := by
  have hp : 4 ^ (i + 1) ≤ 4 ^ j :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa [blockScale, pow_succ', mul_assoc, mul_left_comm, mul_comm] using
    Nat.mul_le_mul_right L hp

lemma oddBlock_disjoint_of_lt {L i j : ℕ} (hL : 0 < L) (hij : i < j) :
    Disjoint (oddBlock (blockScale L i)) (oddBlock (blockScale L j)) := by
  apply Finset.disjoint_left.mpr
  intro n hni hnj
  have hi := lt_four_mul_of_mem_oddBlock hni
  have hj := two_mul_lt_of_mem_oddBlock hnj
  have hscale := four_mul_blockScale_le (L := L) hij
  have hpos := blockScale_pos hL j
  omega

/-- The union of `q + 1` separated blocks of odd integers. -/
def oddBlocks (q L : ℕ) : Finset ℕ :=
  (Finset.range (q + 1)).biUnion fun i => oddBlock (blockScale L i)

lemma pairwiseDisjoint_oddBlock (q : ℕ) {L : ℕ} (hL : 0 < L) :
    (↑(Finset.range (q + 1)) : Set ℕ).PairwiseDisjoint
      (fun i => oddBlock (blockScale L i)) := by
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact oddBlock_disjoint_of_lt hL hij
  · exact (oddBlock_disjoint_of_lt hL hji).symm

/-- `q + 1` separated blocks carry at least `(q+1)/4` of harmonic mass. -/
lemma div_four_le_sum_oddBlocks_inv (q : ℕ) {L : ℕ} (hL : 0 < L) :
    ((q + 1 : ℕ) : ℝ) / 4 ≤ ∑ n ∈ oddBlocks q L, (n : ℝ)⁻¹ := by
  rw [oddBlocks, Finset.sum_biUnion (pairwiseDisjoint_oddBlock q hL)]
  calc
    ((q + 1 : ℕ) : ℝ) / 4 = ∑ i ∈ Finset.range (q + 1), (1 / 4 : ℝ) := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ i ∈ Finset.range (q + 1),
        ∑ n ∈ oddBlock (blockScale L i), (n : ℝ)⁻¹ := by
      exact Finset.sum_le_sum fun i _ => quarter_le_sum_oddBlock_inv (blockScale_pos hL i)

lemma one_le_blockScale {L i : ℕ} : L ≤ blockScale L i := by
  have hp : 1 ≤ 4 ^ i := one_le_pow₀ (by norm_num : 1 ≤ (4 : ℕ))
  simpa [blockScale] using Nat.mul_le_mul_right L hp

lemma mem_oddBlocks_bounds {q L n : ℕ} (hn : n ∈ oddBlocks q L) :
    L ≤ n ∧ n < 4 ^ (q + 1) * L := by
  obtain ⟨i, hi, hni⟩ := Finset.mem_biUnion.mp hn
  have hiq : i ≤ q := by simpa using hi
  have hlower : L ≤ blockScale L i := one_le_blockScale
  have hnlow := two_mul_lt_of_mem_oddBlock hni
  have hnup := lt_four_mul_of_mem_oddBlock hni
  have hp : 4 ^ (i + 1) ≤ 4 ^ (q + 1) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_right hiq 1)
  constructor
  · omega
  · calc
      n < 4 * blockScale L i := hnup
      _ = 4 ^ (i + 1) * L := by simp [blockScale, pow_succ']; ring
      _ ≤ 4 ^ (q + 1) * L := Nat.mul_le_mul_right L hp

lemma odd_of_mem_oddBlocks {q L n : ℕ} (hn : n ∈ oddBlocks q L) : Odd n := by
  obtain ⟨i, hi, hni⟩ := Finset.mem_biUnion.mp hn
  exact odd_of_mem_oddBlock hni

lemma oddCycleReciprocal_nonneg {V : Type*} (G : SimpleGraph V) (n : ℕ) :
    0 ≤ oddCycleReciprocal G n := by
  classical
  simp only [oddCycleReciprocal]
  split <;> positivity

lemma oddCycleReciprocal_eq_inv {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (hn : IsOddCycleLength G n) : oddCycleReciprocal G n = (n : ℝ)⁻¹ := by
  classical
  simp [oddCycleReciprocal, hn]

/-! ### Unconditional flexible-piece extraction -/

open Erdos63 in
theorem flexiblePieceTheorem : FlexiblePieceTheorem := by
  intro R
  obtain ⟨dExact, hExact⟩ := liuMontgomery_theorem2_7
  obtain ⟨nScale, hScale⟩ := eventually_atTop.1
    (FlexibleGadgets.eventually_ceil_log_seven_mul_le_pathScale R)
  let D := max 2 (max dExact (max nScale (12 * R + 12)))
  refine ⟨8 * D, ?_⟩
  intro W _ G hnotcolor
  classical
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  have hDpos : 0 < D := by simp [D]
  have hEightDpos : 0 < 8 * D := by positivity
  obtain ⟨S, hS, hdegree⟩ :=
    exists_induced_core G hEightDpos hnotcolor
  let : Nonempty (S : Set W) := Finset.nonempty_coe_sort.mpr hS
  let K : SimpleGraph (S : Set W) := G.induce (S : Set W)
  have havg : AvgDegreeAtLeast K (8 * D) := by
    exact induced_core_average_degree G S hdegree
  obtain ⟨H, U, hHK, hHbip, hU, hexp, _havgH, hmin⟩ :=
    exists_bipartite_liu_montgomery_expander K hDpos
      (by positivity : (0 : ℝ) < (1 / 64) * (D : ℝ)) havg
  let J : SimpleGraph (U : Set (S : Set W)) := H.induce (U : Set (S : Set W))
  let : Nonempty (U : Set (S : Set W)) := Finset.nonempty_coe_sort.mpr hU
  let : DecidableRel J.Adj := Classical.decRel J.Adj
  let B : Bipartition J :=
    Bipartition.ofIsBipartite (SimpleGraph.IsBipartite.induce hHbip _)
  have hDExact : dExact ≤ D := by simp [D]
  have hDNScale : nScale ≤ D := by simp [D]
  have hDsub : 6 * R + 6 ≤ D / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    dsimp [D]
    omega
  have hDcard : D < Fintype.card (U : Set (S : Set W)) := by
    let v : (U : Set (S : Set W)) := Classical.choice inferInstance
    have hv : D ≤ J.degree v := by
      exact_mod_cast hmin v
    exact hv.trans_lt (J.degree_lt_card_verts v)
  have hcardThree : 3 ≤ Fintype.card (U : Set (S : Set W)) := by omega
  have hscale :
      (((⌈Real.log (Fintype.card (U : Set (S : Set W)) : ℝ) ^ 7⌉₊ * R : ℕ) : ℝ)) ≤
        Parameters.lmPathScale (Fintype.card (U : Set (S : Set W)) : ℝ) := by
    apply hScale
    exact hDNScale.trans hDcard.le
  have hedge : J.edgeSet.Nonempty := by
    let v : (U : Set (S : Set W)) := Classical.choice inferInstance
    have hvpos : 0 < J.degree v := by
      have hv : D ≤ J.degree v := by
        exact_mod_cast hmin v
      omega
    obtain ⟨w, hvw⟩ := (J.degree_pos_iff_exists_adj v).mp hvpos
    exact ⟨s(v, w), by simpa using hvw⟩
  let totalCopy : SimpleGraph.Copy J G :=
    (SimpleGraph.Copy.induce G (S : Set W)).comp
      ((SimpleGraph.Copy.ofLE H K hHK).comp
        (SimpleGraph.Copy.induce H (U : Set (S : Set W))))
  by_cases hsub : SimpleGraph.IsContained (oneSubdivisionClique (D / 2)) J
  · obtain ⟨subcopy⟩ := hsub
    have hpiece := FlexibleGadgets.subdivisionClique_isFlexible R (D / 2) hDsub
    exact ⟨_, hpiece.mapCopy (totalCopy.comp subcopy)⟩
  · have hexact : ∀ {x y : (U : Set (S : Set W))} {q : ℕ}, x ≠ y →
        ParityCompatible B x y q →
        Real.log (Fintype.card (U : Set (S : Set W)) : ℝ) ^ 7 ≤ q →
        (q : ℝ) ≤ Parameters.lmPathScale
          (Fintype.card (U : Set (S : Set W)) : ℝ) →
        HasPathBetweenLength J x y q := by
      apply hExact J B hDExact
      · simpa [J] using hexp
      · intro v
        have hv : D ≤ J.degree v := by
          exact_mod_cast hmin v
        exact_mod_cast hv
      · exact hsub
    have hpiece := FlexibleGadgets.exactPathGraph_isFlexible
      J B R hcardThree hedge hscale hexact
    exact ⟨_, hpiece.mapCopy totalCopy⟩


/-- The exact finite interval consequence of Liu--Montgomery needed below.

For each requested number of geometric blocks, sufficiently high finite chromatic number
forces every odd cycle length in an interval whose multiplicative width contains those blocks. -/
def FiniteOddCycleInterval.{u} : Prop :=
  ∀ q : ℕ, ∃ k : ℕ, ∀ {W : Type u} [Fintype W] (F : SimpleGraph W),
    ¬F.Colorable k →
      ∃ L : ℕ, 0 < L ∧
        ∀ n : ℕ, L ≤ n → n < 4 ^ (q + 1) * L → Odd n → HasCycleLength F n

/-- The robust-path theorem and the minimal odd gadget-cycle theorem together
give the exact finite odd-cycle interval used by Erdős 57. -/
theorem finiteOddCycleInterval_of_flexiblePieces.{u}
    (hextract : FlexiblePieceTheorem.{u})
    (hassembly : FlexiblePackingAssembly.{u}) :
    FiniteOddCycleInterval.{u} := by
  intro q
  let Q : ℕ := 4 ^ (q + 1)
  let T : ℕ := 6 * Q + 3
  obtain ⟨d, hd⟩ := hextract T
  refine ⟨d * 2, ?_⟩
  intro V _ F hF
  obtain ⟨A, hgood, hpair, hmax⟩ := exists_maximal_flexibleFamily F T
  have hnotTwo : ¬(packedUnion A).Colorable 2 :=
    packedUnion_not_colorable_two hd hgood hmax hF
  have hT : 3 ≤ T := by simp [T]
  let assembly : VariableCycleAssembly F T :=
    Classical.choice (hassembly T hT hgood hpair hnotTwo)
  obtain ⟨L, hL, hcycles⟩ :=
    oddCycleInterval_of_variableCycleAssembly Q assembly
  refine ⟨L, hL, ?_⟩
  intro n hnlow hnhigh hnodd
  apply hcycles n hnlow ?_ hnodd
  simpa [Q] using hnhigh.le

/-- Compactness and the dyadic harmonic estimate reduce Erdős 57 to the finite interval theorem. -/
theorem erdos57_of_finiteOddCycleInterval.{u} (hLM : FiniteOddCycleInterval.{u})
    {V : Type u} (G : SimpleGraph V) (hχ : G.chromaticNumber = ⊤) :
    ¬Summable (oddCycleReciprocal G) := by
  intro hsum
  obtain ⟨q : ℕ, hq⟩ := exists_nat_gt (4 * ∑' n, oddCycleReciprocal G n)
  obtain ⟨k, hk⟩ := hLM q
  obtain ⟨s, hs⟩ := exists_finite_induce_not_colorable G hχ k
  obtain ⟨L, hL, hcycles⟩ := hk (G.induce (s : Set V)) hs
  have hvalue : ∀ n ∈ oddBlocks q L,
      oddCycleReciprocal G n = (n : ℝ)⁻¹ := by
    intro n hn
    have hbounds := mem_oddBlocks_bounds hn
    have hodd := odd_of_mem_oddBlocks hn
    have hcycleInduced := hcycles n hbounds.1 hbounds.2 hodd
    have hcycleG := HasCycleLength.of_induce G (s : Set V) hcycleInduced
    exact oddCycleReciprocal_eq_inv ⟨hodd, hcycleG⟩
  have hlower : ((q + 1 : ℕ) : ℝ) / 4 ≤
      ∑ n ∈ oddBlocks q L, oddCycleReciprocal G n := by
    rw [Finset.sum_congr rfl hvalue]
    exact div_four_le_sum_oddBlocks_inv q hL
  have hupper : (∑ n ∈ oddBlocks q L, oddCycleReciprocal G n) ≤
      ∑' n, oddCycleReciprocal G n :=
    hsum.sum_le_tsum (oddBlocks q L) fun n _ => oddCycleReciprocal_nonneg G n
  have hlarge : (∑' n, oddCycleReciprocal G n) < ((q + 1 : ℕ) : ℝ) / 4 := by
    have hq' : 4 * (∑' n, oddCycleReciprocal G n) < (q : ℝ) := by
      exact_mod_cast hq
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  exact (not_lt_of_ge (hlower.trans hupper)) hlarge

/-- The unconditional finite odd-cycle interval theorem obtained from the
Liu--Montgomery flexible-piece extraction and the certified packing
assembly. -/
theorem finiteOddCycleInterval : FiniteOddCycleInterval :=
  finiteOddCycleInterval_of_flexiblePieces flexiblePieceTheorem
    flexiblePackingAssembly

/-- Erdős Problem 57 (Erdős--Hajnal, proved by Liu--Montgomery): in every
graph of infinite chromatic number, the sum of the reciprocals of its
distinct odd cycle lengths diverges.  The zero values of
`oddCycleReciprocal` merely extend that set-indexed sum to all naturals. -/
theorem erdos_57 {V : Type*} (G : SimpleGraph V)
    (hχ : G.chromaticNumber = ⊤) :
    ¬Summable (oddCycleReciprocal G) :=
  erdos57_of_finiteOddCycleInterval finiteOddCycleInterval G hχ

end Erdos57

#print axioms Erdos57.erdos_57
