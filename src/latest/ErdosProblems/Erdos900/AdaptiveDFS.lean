/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos900.AdaptiveTree

/-!
# The adaptive depth-first-search exposure

This file gives the executable finite search used for Erdős Problem 900.  A
state consists of processed, unseen, and stack vertices.  Silent moves start a
new component or pop a vertex whose possible edges to unseen vertices have all
been exposed.  A genuine move exposes one still-unread top-to-unseen edge.
Once DFS has finished, arbitrary remaining coordinates are exposed; this
makes the query plan a full adaptive tree and hence a permutation of the
Boolean cube.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos900

/-- The possible (non-loop) edges on `Fin n`. -/
abbrev Edge (n : ℕ) := ↥((⊤ : SimpleGraph (Fin n)).edgeFinset)

instance (n : ℕ) : DecidableEq (Edge n) := Classical.decEq _

@[simp] theorem card_edge (n : ℕ) : Fintype.card (Edge n) = n.choose 2 := by
  rw [Fintype.card_coe]
  simpa using SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n)

/-- A proof-free DFS state.  `positiveDFS` counts only positive queries made
before the arbitrary post-DFS completion of the exposure order. -/
structure DFSState (n : ℕ) where
  done : Finset (Fin n)
  unseen : Finset (Fin n)
  stack : List (Fin n)
  roots : Finset (Fin n)
  positiveDFS : ℕ
  fallback : Bool
  deriving DecidableEq

/-- Initial state: every vertex is unseen. -/
def DFSState.initial (n : ℕ) : DFSState n where
  done := ∅
  unseen := Finset.univ
  stack := []
  roots := ∅
  positiveDFS := 0
  fallback := false

/-- Start a new DFS component at `u`. -/
def DFSState.start {n : ℕ} (st : DFSState n) (u : Fin n) : DFSState n :=
  { st with
    unseen := st.unseen.erase u
    stack := [u]
    roots := insert u st.roots }

/-- Pop the exhausted top `x` from the stack. -/
def DFSState.pop {n : ℕ} (st : DFSState n) (x : Fin n)
    (xs : List (Fin n)) : DFSState n :=
  { st with done := insert x st.done, stack := xs }

def DFSState.silentMeasure {n : ℕ} (st : DFSState n) : ℕ :=
  2 * st.unseen.card + st.stack.length

theorem DFSState.silentMeasure_start_choose_lt {n : ℕ} (st : DFSState n)
    (hU : st.unseen.Nonempty) :
    (st.start hU.choose).silentMeasure < st.silentMeasure := by
  have hu : hU.choose ∈ st.unseen := hU.choose_spec
  have hpos : 0 < st.unseen.card := Finset.card_pos.mpr hU
  simp only [DFSState.silentMeasure, DFSState.start,
    Finset.card_erase_of_mem hu, List.length_cons, List.length_nil]
  omega

theorem DFSState.silentMeasure_pop_lt {n : ℕ} (st : DFSState n)
    (x : Fin n) (xs : List (Fin n)) (hs : st.stack = x :: xs) :
    (st.pop x xs).silentMeasure < st.silentMeasure := by
  have hlen := congrArg List.length hs
  simp only [List.length_cons] at hlen
  simp only [DFSState.silentMeasure, DFSState.pop]
  omega

/-- Still-unread coordinate/unseen-vertex pairs representing an edge from the
top of the current stack. -/
def DFSState.queryPairs {n r : ℕ} (available : Fin r → Edge n)
    (st : DFSState n) : Finset (Fin r × Fin n) := by
  classical
  match st.stack with
  | [] => exact ∅
  | x :: _ =>
      exact (Finset.univ ×ˢ st.unseen).filter fun z ↦
        (available z.1).1 = s(x, z.2)

/-- The bookkeeping invariants of the proof-free DFS state.  The last two
fields say that every processed--unseen edge and every edge between two roots
has already disappeared from the availability enumeration. -/
structure DFSState.WellFormed {n r : ℕ} (available : Fin r → Edge n)
    (st : DFSState n) : Prop where
  stack_nodup : st.stack.Nodup
  disjoint_done_unseen : Disjoint st.done st.unseen
  disjoint_done_stack : Disjoint st.done st.stack.toFinset
  disjoint_unseen_stack : Disjoint st.unseen st.stack.toFinset
  card_partition : st.done.card + st.unseen.card + st.stack.length = n
  roots_subset : st.roots ⊆ st.done ∪ st.stack.toFinset
  card_account : st.done.card + st.stack.length =
    st.positiveDFS + st.roots.card
  noAvailable_done_unseen : ∀ i d, d ∈ st.done → ∀ u, u ∈ st.unseen →
    (available i).1 ≠ s(d, u)
  noAvailable_roots : ∀ i x, x ∈ st.roots → ∀ y, y ∈ st.roots → x ≠ y →
    (available i).1 ≠ s(x, y)
  fallback_complete : st.fallback = true →
    st.done.card = n ∧ st.unseen = ∅ ∧ st.stack = []

theorem DFSState.wellFormed_initial (n r : ℕ) (available : Fin r → Edge n) :
    (DFSState.initial n).WellFormed available := by
  constructor <;> simp [DFSState.initial]

theorem DFSState.WellFormed.start {n r : ℕ} {available : Fin r → Edge n}
    {st : DFSState n} (h : st.WellFormed available) {root : Fin n}
    (hu : root ∈ st.unseen) (hstack : st.stack = []) :
    (st.start root).WellFormed available := by
  have huDone : root ∉ st.done := fun hud ↦
    Finset.disjoint_left.mp h.disjoint_done_unseen hud hu
  have huRoots : root ∉ st.roots := by
    intro hur
    have := h.roots_subset hur
    have : root ∈ st.done := by
      simpa only [hstack, List.toFinset_nil, Finset.union_empty] using this
    exact huDone this
  constructor
  · simp [DFSState.start]
  · exact h.disjoint_done_unseen.mono_right (Finset.erase_subset _ _)
  · simp [DFSState.start, huDone]
  · simp [DFSState.start]
  · have herase := Finset.card_erase_of_mem hu
    change st.done.card + (st.unseen.erase root).card + [root].length = n
    rw [herase]
    simp only [List.length_cons, List.length_nil]
    have hc := h.card_partition
    simp only [hstack, List.length_nil, add_zero] at hc
    have hpos : 0 < st.unseen.card := Finset.card_pos.mpr ⟨root, hu⟩
    omega
  · intro z hz
    simp only [DFSState.start, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · simp [DFSState.start]
    · have hz' := h.roots_subset hz
      simp [hstack] at hz'
      simp [DFSState.start, hz']
  · have hrootCard := Finset.card_insert_of_notMem huRoots
    change st.done.card + [root].length =
      st.positiveDFS + (insert root st.roots).card
    rw [hrootCard]
    simp only [List.length_cons, List.length_nil]
    have hc := h.card_account
    simp only [hstack, List.length_nil, add_zero] at hc
    omega
  · intro i d hd v hv
    exact h.noAvailable_done_unseen i d hd v (Finset.mem_of_mem_erase hv)
  · intro i x hx y hy hxy
    simp only [DFSState.start, Finset.mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · have hyDone : y ∈ st.done := by
        have := h.roots_subset hy
        simpa [hstack] using this
      simpa [Sym2.eq_swap] using
        h.noAvailable_done_unseen i y hyDone _ hu
    · have hxDone : x ∈ st.done := by
        have := h.roots_subset hx
        simpa [hstack] using this
      exact h.noAvailable_done_unseen i x hxDone _ hu
    · exact h.noAvailable_roots i x hx y hy hxy
  · intro hfb
    have hold : st.fallback = true := by simpa [DFSState.start] using hfb
    have hempty := (h.fallback_complete hold).2.1
    rw [hempty] at hu
    simp at hu

theorem DFSState.WellFormed.pop {n r : ℕ} {available : Fin r → Edge n}
    {st : DFSState n} (h : st.WellFormed available) {x : Fin n}
    {xs : List (Fin n)} (hstack : st.stack = x :: xs)
    (hready : ¬(st.queryPairs available).Nonempty) :
    (st.pop x xs).WellFormed available := by
  have hxStack : x ∈ st.stack.toFinset := by simp [hstack]
  have hxDone : x ∉ st.done := fun hxd ↦
    Finset.disjoint_left.mp h.disjoint_done_stack hxd hxStack
  have hxUnseen : x ∉ st.unseen := fun hxu ↦
    Finset.disjoint_left.mp h.disjoint_unseen_stack hxu hxStack
  have hxsSub : xs.toFinset ⊆ st.stack.toFinset := by
    intro z hz
    simp [hstack, hz]
  have hn : (x :: xs).Nodup := by simpa [hstack] using h.stack_nodup
  have hxTailNot : x ∉ xs.toFinset := by simpa using (List.nodup_cons.mp hn).1
  constructor
  · simpa [DFSState.pop] using hn.tail
  · rw [Finset.disjoint_left]
    intro z hzD hzU
    simp only [DFSState.pop, Finset.mem_insert] at hzD
    rcases hzD with rfl | hzD
    · exact hxUnseen hzU
    · exact Finset.disjoint_left.mp h.disjoint_done_unseen hzD hzU
  · rw [Finset.disjoint_left]
    intro z hzD hzS
    simp only [DFSState.pop, Finset.mem_insert] at hzD
    rcases hzD with rfl | hzD
    · exact hxTailNot (by simpa [DFSState.pop] using hzS)
    · exact Finset.disjoint_left.mp h.disjoint_done_stack hzD (hxsSub hzS)
  · exact h.disjoint_unseen_stack.mono_right hxsSub
  · have hdone := Finset.card_insert_of_notMem hxDone
    have hlen := congrArg List.length hstack
    simp only [List.length_cons] at hlen
    simp only [DFSState.pop, hdone]
    have hc := h.card_partition
    omega
  · intro z hz
    have hz' := h.roots_subset hz
    simp only [hstack, List.toFinset_cons, Finset.mem_union,
      Finset.mem_insert] at hz' ⊢
    rcases hz' with hz' | rfl | hz'
    · exact .inl (Finset.mem_insert_of_mem hz')
    · exact .inl (Finset.mem_insert_self _ _)
    · exact .inr hz'
  · have hdone := Finset.card_insert_of_notMem hxDone
    have hlen := congrArg List.length hstack
    simp only [List.length_cons] at hlen
    simp only [DFSState.pop, hdone]
    have hc := h.card_account
    omega
  · intro i d hd u hu
    simp only [DFSState.pop, Finset.mem_insert] at hd
    rcases hd with rfl | hd
    · intro heq
      have hu' : u ∈ st.unseen := by simpa [DFSState.pop] using hu
      apply hready
      refine ⟨(i, u), ?_⟩
      simp [DFSState.queryPairs, hstack, hu', heq]
    · exact h.noAvailable_done_unseen i d hd u (by simpa [DFSState.pop] using hu)
  · exact h.noAvailable_roots
  · intro hfb
    have hold : st.fallback = true := by simpa [DFSState.pop] using hfb
    have hc := h.fallback_complete hold
    have hlen := congrArg List.length hstack
    simp [hc.2.2] at hlen

/-- One silent DFS move.  It starts a component, pops an exhausted stack top,
or fixes a state at which an edge query is ready. -/
def DFSState.silentStep {n r : ℕ} (available : Fin r → Edge n)
    (st : DFSState n) : DFSState n := by
  classical
  match hs : st.stack with
  | [] =>
      if hU : st.unseen.Nonempty then
        let u := hU.choose
        exact st.start u
      else exact st
  | x :: xs =>
      if (st.queryPairs available).Nonempty then exact st
      else exact st.pop x xs

/-- Perform all silent moves, stopping exactly when a genuine query is ready
or every vertex has been processed.  The measure gives weight two to an
unseen vertex: starting a component changes one unseen vertex into one stack
vertex, while a pop deletes one stack vertex. -/
def DFSState.normalize {n r : ℕ} (available : Fin r → Edge n)
    (st : DFSState n) : DFSState n := by
  classical
  if (st.queryPairs available).Nonempty then exact st
  else
    match hs : st.stack with
    | [] =>
        if hU : st.unseen.Nonempty then
          let u := hU.choose
          let st' : DFSState n := st.start u
          exact st'.normalize available
        else exact st
    | x :: xs =>
        let st' : DFSState n := st.pop x xs
        exact st'.normalize available
termination_by st.silentMeasure
decreasing_by
  · exact st.silentMeasure_start_choose_lt hU
  · exact st.silentMeasure_pop_lt x xs hs

theorem DFSState.WellFormed.normalize {n r : ℕ} {available : Fin r → Edge n}
    {st : DFSState n} (h : st.WellFormed available) :
    (st.normalize available).WellFormed available := by
  rw [DFSState.normalize]
  split
  next hquery => exact h
  next hquery =>
    split
    next hs =>
      split
      next hU =>
        apply DFSState.WellFormed.normalize (h.start hU.choose_spec hs)
      next _hU => exact h
    next x xs hs =>
      apply DFSState.WellFormed.normalize (h.pop hs hquery)
termination_by st.silentMeasure
decreasing_by
  · exact DFSState.silentMeasure_start_choose_lt _ _
  · apply DFSState.silentMeasure_pop_lt
    assumption

/-- Normalization stops only at a genuine edge query or at the completed DFS
state. -/
theorem DFSState.normalize_ready_or_complete {n r : ℕ}
    {available : Fin r → Edge n} {st : DFSState n}
    (h : st.WellFormed available) :
    ((st.normalize available).queryPairs available).Nonempty ∨
      (st.normalize available).done.card = n ∧
      (st.normalize available).unseen = ∅ ∧
      (st.normalize available).stack = [] := by
  rw [DFSState.normalize]
  split
  next hquery => exact .inl hquery
  next hquery =>
    split
    next hs =>
      split
      next hU =>
        exact DFSState.normalize_ready_or_complete (h.start hU.choose_spec hs)
      next hU =>
        right
        have hempty : st.unseen = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
        have hc := h.card_partition
        simp only [hs, hempty, Finset.card_empty, List.length_nil, add_zero] at hc
        exact ⟨hc, hempty, hs⟩
    next x xs hs =>
      exact DFSState.normalize_ready_or_complete (h.pop hs hquery)
termination_by st.silentMeasure
decreasing_by
  · exact DFSState.silentMeasure_start_choose_lt _ _
  · apply DFSState.silentMeasure_pop_lt
    assumption

theorem DFSState.WellFormed.reindex {n r q : ℕ}
    {available : Fin r → Edge n} {st : DFSState n}
    (h : st.WellFormed available) (f : Fin q → Fin r) :
    st.WellFormed (fun i ↦ available (f i)) := by
  exact
    { h with
      noAvailable_done_unseen := fun i ↦ h.noAvailable_done_unseen (f i)
      noAvailable_roots := fun i ↦ h.noAvailable_roots (f i) }

/-- Coordinate and target vertex of the next genuine DFS query, if one
exists. -/
def DFSState.target {n r : ℕ} (available : Fin r → Edge n)
    (st : DFSState n) : Option (Fin r × Fin n) := by
  classical
  let t := st.normalize available
  if h : (t.queryPairs available).Nonempty then exact some h.choose else exact none

/-- Index of the next query.  A DFS candidate is used when available;
otherwise coordinate `0` begins or continues the arbitrary completion. -/
def DFSState.pivot {n r : ℕ} (available : Fin (r + 1) → Edge n)
    (st : DFSState n) : Fin (r + 1) :=
  match st.target available with
  | some z => z.1
  | none => 0

def DFSState.accept {n : ℕ} (st : DFSState n) (u : Fin n) : DFSState n :=
  { st with
    unseen := st.unseen.erase u
    stack := u :: st.stack
    positiveDFS := st.positiveDFS + 1 }

def DFSState.finish {n : ℕ} (st : DFSState n) : DFSState n :=
  { st with fallback := true }

/-- Update the normalized state after reading the selected bit. -/
def DFSState.advance {n r : ℕ} (available : Fin (r + 1) → Edge n)
    (st : DFSState n) (b : Bool) : DFSState n := by
  classical
  let t := st.normalize available
  match st.target available with
  | none => exact t.finish
  | some z =>
      if b then exact t.accept z.2 else exact t

/-- Delete the selected coordinate from an availability enumeration. -/
def removeAvailable {n r : ℕ} (available : Fin (r + 1) → Edge n)
    (pivot : Fin (r + 1)) : Fin r → Edge n :=
  fun i ↦ available (pivot.succAbove i)

theorem DFSState.WellFormed.removeAvailable {n r : ℕ}
    {available : Fin (r + 1) → Edge n} {st : DFSState n}
    (h : st.WellFormed available) (p : Fin (r + 1)) :
    st.WellFormed (removeAvailable available p) :=
  h.reindex p.succAbove

theorem DFSState.target_some_mem {n r : ℕ} {available : Fin r → Edge n}
    {st : DFSState n} {z : Fin r × Fin n} (hz : st.target available = some z) :
    z ∈ (st.normalize available).queryPairs available := by
  classical
  change (if h : ((st.normalize available).queryPairs available).Nonempty then
    some h.choose else none) = some z at hz
  by_cases h : ((st.normalize available).queryPairs available).Nonempty
  · rw [dif_pos h] at hz
    have := Option.some.inj hz
    subst z
    exact h.choose_spec
  · rw [dif_neg h] at hz
    simp at hz

theorem DFSState.target_none_iff {n r : ℕ} {available : Fin r → Edge n}
    {st : DFSState n} :
    st.target available = none ↔
      ¬((st.normalize available).queryPairs available).Nonempty := by
  classical
  change (if h : ((st.normalize available).queryPairs available).Nonempty then
    some h.choose else none) = none ↔ _
  by_cases h : ((st.normalize available).queryPairs available).Nonempty <;>
    simp [h]

theorem DFSState.queryPairs_target_mem {n r : ℕ} {available : Fin r → Edge n}
    {st : DFSState n} {z : Fin r × Fin n}
    (hz : z ∈ st.queryPairs available) : z.2 ∈ st.unseen := by
  classical
  cases hs : st.stack with
  | nil => simp [DFSState.queryPairs, hs] at hz
  | cons x xs =>
      have hz' : z.2 ∈ st.unseen ∧ (available z.1).1 = s(x, z.2) := by
        simpa [DFSState.queryPairs, hs] using hz
      exact hz'.1

theorem DFSState.WellFormed.accept {n r : ℕ} {available : Fin r → Edge n}
    {st : DFSState n} (h : st.WellFormed available) {u : Fin n}
    (hu : u ∈ st.unseen) : (st.accept u).WellFormed available := by
  have huDone : u ∉ st.done := fun hud ↦
    Finset.disjoint_left.mp h.disjoint_done_unseen hud hu
  have huStack : u ∉ st.stack.toFinset := fun hus ↦
    Finset.disjoint_left.mp h.disjoint_unseen_stack hu hus
  have huRoots : u ∉ st.roots := by
    intro hur
    rcases Finset.mem_union.mp (h.roots_subset hur) with hud | hus
    · exact huDone hud
    · exact huStack hus
  have huList : u ∉ st.stack := by simpa using huStack
  constructor
  · simpa [DFSState.accept] using h.stack_nodup.cons huList
  · exact h.disjoint_done_unseen.mono_right (Finset.erase_subset _ _)
  · rw [Finset.disjoint_left]
    intro d hd hz
    simp only [DFSState.accept, List.toFinset_cons, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact huDone hd
    · exact Finset.disjoint_left.mp h.disjoint_done_stack hd hz
  · rw [Finset.disjoint_left]
    intro v hv hz
    simp only [DFSState.accept, List.toFinset_cons, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact Finset.notMem_erase _ _ hv
    · exact Finset.disjoint_left.mp h.disjoint_unseen_stack
        (Finset.mem_of_mem_erase hv) hz
  · have herase := Finset.card_erase_of_mem hu
    have hpos : 0 < st.unseen.card := Finset.card_pos.mpr ⟨u, hu⟩
    change st.done.card + (st.unseen.erase u).card + (u :: st.stack).length = n
    rw [herase]
    simp only [List.length_cons]
    have hc := h.card_partition
    omega
  · intro z hz
    have hz' := h.roots_subset hz
    simp only [DFSState.accept, List.toFinset_cons, Finset.mem_union,
      Finset.mem_insert] at hz' ⊢
    rcases hz' with hz' | hz'
    · exact .inl hz'
    · exact .inr (.inr hz')
  · simp only [DFSState.accept, List.length_cons]
    have hc := h.card_account
    omega
  · intro i d hd v hv
    exact h.noAvailable_done_unseen i d hd v (Finset.mem_of_mem_erase hv)
  · exact h.noAvailable_roots
  · intro hfb
    have hold : st.fallback = true := by simpa [DFSState.accept] using hfb
    have hc := h.fallback_complete hold
    rw [hc.2.1] at hu
    simp at hu

theorem DFSState.WellFormed.finish {n r : ℕ} {available : Fin r → Edge n}
    {st : DFSState n} (h : st.WellFormed available)
    (hc : st.done.card = n ∧ st.unseen = ∅ ∧ st.stack = []) :
    st.finish.WellFormed available := by
  exact { h with fallback_complete := fun _ ↦ hc }

theorem DFSState.WellFormed.advance {n r : ℕ}
    {available : Fin (r + 1) → Edge n} {st : DFSState n}
    (h : st.WellFormed available) (b : Bool) :
    (st.advance available b).WellFormed
      (Erdos900.removeAvailable available (st.pivot available)) := by
  classical
  let t := st.normalize available
  have ht : t.WellFormed available := h.normalize
  cases hz : st.target available with
  | none =>
      have hnot := DFSState.target_none_iff.mp hz
      have hc := st.normalize_ready_or_complete h
      have hcomplete := hc.resolve_left hnot
      have hf := ht.finish hcomplete
      simpa [DFSState.advance, t, hz] using
        hf.removeAvailable (st.pivot available)
  | some z =>
      have hzmem := DFSState.target_some_mem hz
      have hu : z.2 ∈ t.unseen := DFSState.queryPairs_target_mem hzmem
      have hp : st.pivot available = z.1 := by simp [DFSState.pivot, hz]
      cases b
      · simpa [DFSState.advance, t, hz, hp] using ht.removeAvailable z.1
      · simpa [DFSState.advance, t, hz, hp] using
          (ht.accept hu).removeAvailable z.1

/-- Turn a non-loop unordered pair into an edge-coordinate. -/
def edgeOfNe {n : ℕ} (u v : Fin n) (h : u ≠ v) : Edge n :=
  ⟨s(u, v), by simpa [SimpleGraph.mem_edgeFinset] using h⟩

/-- The simple graph encoded by Boolean values on the possible edges. -/
def graphFromBits {n : ℕ} (G : Edge n → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet
    {e | ∃ h : e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
      G ⟨e, h⟩ = true}

theorem graphFromBits_adj_iff {n : ℕ} (G : Edge n → Bool)
    {u v : Fin n} (h : u ≠ v) :
    (graphFromBits G).Adj u v ↔ G (edgeOfNe u v h) = true := by
  rw [← SimpleGraph.mem_edgeSet]
  simp only [graphFromBits, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨he, hb⟩, _⟩
    simpa [edgeOfNe] using hb
  · intro hb
    refine ⟨⟨(edgeOfNe u v h).2, ?_⟩, ?_⟩
    · simpa [edgeOfNe] using hb
    · simpa using h

/-- The current stack is an actual graph path (possibly empty). -/
def DFSState.Realized {n : ℕ} (G : Edge n → Bool) (st : DFSState n) : Prop :=
  List.IsChain (graphFromBits G).Adj st.stack

theorem DFSState.realized_initial {n : ℕ} (G : Edge n → Bool) :
    (DFSState.initial n).Realized G := by
  simp [DFSState.Realized, DFSState.initial]

theorem DFSState.Realized.start {n : ℕ} {G : Edge n → Bool}
    {st : DFSState n} (u : Fin n) :
    (st.start u).Realized G := by
  simp [DFSState.Realized, DFSState.start]

theorem DFSState.Realized.pop {n : ℕ} {G : Edge n → Bool}
    {st : DFSState n} (h : st.Realized G) {x : Fin n} {xs : List (Fin n)}
    (hs : st.stack = x :: xs) : (st.pop x xs).Realized G := by
  have hc : List.IsChain (graphFromBits G).Adj (x :: xs) := by
    simpa [DFSState.Realized, hs] using h
  simpa [DFSState.Realized, DFSState.pop] using hc.tail

theorem DFSState.Realized.finish {n : ℕ} {G : Edge n → Bool}
    {st : DFSState n} (h : st.Realized G) : st.finish.Realized G := by
  simpa [DFSState.Realized, DFSState.finish] using h

theorem DFSState.Realized.normalize {n r : ℕ} {G : Edge n → Bool}
    {available : Fin r → Edge n} {st : DFSState n} (h : st.Realized G) :
    (st.normalize available).Realized G := by
  rw [DFSState.normalize]
  split
  next _hquery => exact h
  next _hquery =>
    split
    next hs =>
      split
      next hU =>
        apply DFSState.Realized.normalize (DFSState.Realized.start hU.choose)
      next _hU => exact h
    next x xs hs =>
      apply DFSState.Realized.normalize (h.pop hs)
termination_by st.silentMeasure
decreasing_by
  · exact DFSState.silentMeasure_start_choose_lt _ _
  · apply DFSState.silentMeasure_pop_lt
    assumption

theorem DFSState.normalize_positiveDFS {n r : ℕ} (available : Fin r → Edge n)
    (st : DFSState n) :
    (st.normalize available).positiveDFS = st.positiveDFS := by
  rw [DFSState.normalize]
  split
  next _ => rfl
  next _ =>
    split
    next _hs =>
      split
      next hU => exact DFSState.normalize_positiveDFS available (st.start hU.choose)
      next _ => rfl
    next x xs _hs => exact DFSState.normalize_positiveDFS available (st.pop x xs)
termination_by st.silentMeasure
decreasing_by
  · exact DFSState.silentMeasure_start_choose_lt _ _
  · apply DFSState.silentMeasure_pop_lt
    assumption

theorem DFSState.normalize_fallback {n r : ℕ} (available : Fin r → Edge n)
    (st : DFSState n) :
    (st.normalize available).fallback = st.fallback := by
  rw [DFSState.normalize]
  split
  next _ => rfl
  next _ =>
    split
    next _hs =>
      split
      next hU => exact DFSState.normalize_fallback available (st.start hU.choose)
      next _ => rfl
    next x xs _hs => exact DFSState.normalize_fallback available (st.pop x xs)
termination_by st.silentMeasure
decreasing_by
  · exact DFSState.silentMeasure_start_choose_lt _ _
  · apply DFSState.silentMeasure_pop_lt
    assumption

theorem DFSState.queryPairs_stack {n r : ℕ} {available : Fin r → Edge n}
    {st : DFSState n} {z : Fin r × Fin n}
    (hz : z ∈ st.queryPairs available) :
    ∃ x xs, st.stack = x :: xs ∧ (available z.1).1 = s(x, z.2) := by
  classical
  cases hs : st.stack with
  | nil => simp [DFSState.queryPairs, hs] at hz
  | cons x xs =>
      refine ⟨x, xs, by simp, ?_⟩
      have hz' : z.2 ∈ st.unseen ∧ (available z.1).1 = s(x, z.2) := by
        simpa [DFSState.queryPairs, hs] using hz
      exact hz'.2

theorem DFSState.Realized.advance {n r : ℕ} {G : Edge n → Bool}
    {available : Fin (r + 1) → Edge n} {st : DFSState n}
    (h : st.Realized G) (b : Bool)
    (hbit : b = G (available (st.pivot available))) :
    (st.advance available b).Realized G := by
  classical
  let t := st.normalize available
  have ht : t.Realized G := h.normalize
  cases hz : st.target available with
  | none => simpa [DFSState.advance, t, hz] using ht.finish
  | some z =>
      have hzmem := DFSState.target_some_mem hz
      obtain ⟨x, xs, hstack, hedge⟩ := DFSState.queryPairs_stack hzmem
      have hp : st.pivot available = z.1 := by simp [DFSState.pivot, hz]
      cases hb : b
      · simpa [DFSState.advance, t, hz, hb, DFSState.accept] using ht
      · have hG : G (available z.1) = true := by simpa [hb, hp] using hbit.symm
        have hne : x ≠ z.2 := by
          intro hxu
          subst x
          have hmem := (available z.1).2
          rw [hedge] at hmem
          simp at hmem
        have hadj : (graphFromBits G).Adj z.2 x := by
          apply SimpleGraph.Adj.symm
          apply (graphFromBits_adj_iff G hne).2
          have hecoord : edgeOfNe x z.2 hne = available z.1 := by
            apply Subtype.ext
            exact hedge.symm
          simpa [hecoord] using hG
        have hchain : List.IsChain (graphFromBits G).Adj (z.2 :: t.stack) := by
          change t.stack = x :: xs at hstack
          have ht' : List.IsChain (graphFromBits G).Adj (x :: xs) := by
            change List.IsChain (graphFromBits G).Adj t.stack at ht
            rwa [hstack] at ht
          rw [hstack]
          exact .cons_cons hadj ht'
        simpa [DFSState.advance, t, hz, hb, DFSState.accept,
          DFSState.Realized] using hchain

theorem DFSState.advance_positiveDFS_le {n r : ℕ}
    (available : Fin (r + 1) → Edge n) (st : DFSState n) (b : Bool) :
    (st.advance available b).positiveDFS ≤
      st.positiveDFS + (if b then 1 else 0) := by
  classical
  cases hz : st.target available with
  | none => simp [DFSState.advance, hz, DFSState.finish,
      DFSState.normalize_positiveDFS]
  | some z =>
      cases b <;> simp [DFSState.advance, hz, DFSState.accept,
        DFSState.normalize_positiveDFS]

theorem DFSState.advance_fallback_false_positiveDFS {n r : ℕ}
    (available : Fin (r + 1) → Edge n) (st : DFSState n) (b : Bool)
    (hfalse : (st.advance available b).fallback = false) :
    (st.advance available b).positiveDFS =
      st.positiveDFS + (if b then 1 else 0) := by
  classical
  cases hz : st.target available with
  | none => simp [DFSState.advance, hz, DFSState.finish] at hfalse
  | some z =>
      cases b <;> simp [DFSState.advance, hz, DFSState.accept,
        DFSState.normalize_positiveDFS]

theorem DFSState.fallback_le_advance {n r : ℕ}
    (available : Fin (r + 1) → Edge n) (st : DFSState n) (b : Bool) :
    st.fallback = true → (st.advance available b).fallback = true := by
  intro htrue
  classical
  have hn : (st.normalize available).fallback = true := by
    rw [DFSState.normalize_fallback, htrue]
  cases hz : st.target available with
  | none => simp [DFSState.advance, hz, DFSState.finish]
  | some z =>
      cases b <;> simpa [DFSState.advance, hz, DFSState.accept] using hn

/-- The full adaptive exposure tree generated by DFS. -/
def dfsTree {n : ℕ} : {r : ℕ} → (Fin r → Edge n) → DFSState n → AdaptiveTree r
  | 0, _available, _state => .nil
  | _ + 1, available, state =>
      let p := state.pivot available
      .node p fun b ↦
        dfsTree (removeAvailable available p) (state.advance available b)

/-- Data remaining after the first `q` adaptive queries. -/
structure DFSRunResult (n r q : ℕ) where
  available : Fin (r - q) → Edge n
  state : DFSState n
  bits : Fin (r - q) → Bool
  trueCount : ℕ

/-- Execute the first `q` queries of the adaptive DFS exposure. -/
def dfsRun {n : ℕ} : {r q : ℕ} → q ≤ r →
    (Fin r → Edge n) → DFSState n → (Fin r → Bool) → DFSRunResult n r q
  | r, 0, _h, available, state, bits =>
      ⟨available, state, bits, 0⟩
  | 0, q + 1, h, _available, _state, _bits => by omega
  | r + 1, q + 1, h, available, state, bits =>
      let p := state.pivot available
      let b := bits p
      let tailAvailable := removeAvailable available p
      let tailState := state.advance available b
      let tailBits := Fin.removeNth p bits
      let R := dfsRun (Nat.le_of_succ_le_succ h) tailAvailable tailState tailBits
      ⟨fun i ↦ R.available (Fin.cast (by omega) i), R.state,
        fun i ↦ R.bits (Fin.cast (by omega) i),
        (if b then 1 else 0) + R.trueCount⟩

/-- Number of `true` bits among the first `q` coordinates, with harmless
truncation if `q` exceeds the word length. -/
def prefixWeight : {r : ℕ} → (Fin r → Bool) → ℕ → ℕ
  | 0, _w, _q => 0
  | _r + 1, _w, 0 => 0
  | _ + 1, w, q + 1 => (if w 0 then 1 else 0) + prefixWeight (Fin.tail w) q

@[simp] theorem prefixWeight_zero {r : ℕ} (w : Fin r → Bool) :
    prefixWeight w 0 = 0 := by
  cases r <;> rfl

/-- `prefixWeight` is the indicator sum over coordinates whose index is
strictly smaller than the requested prefix length. -/
theorem prefixWeight_eq_sum {r : ℕ} (w : Fin r → Bool) (q : ℕ) :
    prefixWeight w q =
      ∑ i, if i.val < q then (if w i then 1 else 0) else 0 := by
  induction r generalizing q with
  | zero => simp [prefixWeight]
  | succ r ih =>
      cases q with
      | zero => simp [prefixWeight]
      | succ q =>
          rw [Fin.sum_univ_succ]
          simp only [prefixWeight, Fin.val_zero, Nat.zero_lt_succ, ↓reduceIte]
          rw [ih (Fin.tail w) q]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          simp [Fin.tail]
          rfl

theorem dfsRun_wellFormed {n r q : ℕ} (hq : q ≤ r)
    {available : Fin r → Edge n} {state : DFSState n} {bits : Fin r → Bool}
    (h : state.WellFormed available) :
    (dfsRun hq available state bits).state.WellFormed
      (dfsRun hq available state bits).available := by
  induction q generalizing r available state bits with
  | zero => simpa [dfsRun] using h
  | succ q ih =>
      cases r with
      | zero => omega
      | succ r =>
          simp only [dfsRun]
          have hi := ih (Nat.le_of_succ_le_succ hq)
            (bits := Fin.removeNth (state.pivot available) bits)
            (h.advance (bits (state.pivot available)))
          exact hi.reindex (fun i ↦ Fin.cast (by omega) i)

theorem dfsRun_realized {n r q : ℕ} (hq : q ≤ r)
    {available : Fin r → Edge n} {state : DFSState n} {bits : Fin r → Bool}
    {G : Edge n → Bool} (hreal : state.Realized G)
    (hbits : ∀ i, bits i = G (available i)) :
    (dfsRun hq available state bits).state.Realized G := by
  induction q generalizing r available state bits with
  | zero => simpa [dfsRun] using hreal
  | succ q ih =>
      cases r with
      | zero => omega
      | succ r =>
          simp only [dfsRun]
          let p := state.pivot available
          let b := bits p
          have hstep : (state.advance available b).Realized G :=
            hreal.advance b (hbits p)
          apply ih (Nat.le_of_succ_le_succ hq) hstep
          intro i
          exact hbits (p.succAbove i)

theorem dfsRun_available_injective {n r q : ℕ} (hq : q ≤ r)
    {available : Fin r → Edge n} {state : DFSState n} {bits : Fin r → Bool}
    (hinj : Function.Injective available) :
    Function.Injective (dfsRun hq available state bits).available := by
  induction q generalizing r available state bits with
  | zero => simpa [dfsRun] using hinj
  | succ q ih =>
      cases r with
      | zero => omega
      | succ r =>
          simp only [dfsRun]
          have hi := ih (Nat.le_of_succ_le_succ hq)
            (available := removeAvailable available (state.pivot available))
            (state := state.advance available (bits (state.pivot available)))
            (bits := Fin.removeNth (state.pivot available) bits)
            (hinj.comp (Fin.succAbove_right_injective
              (p := state.pivot available)))
          exact hi.comp (Fin.cast_injective _)

theorem dfsRun_trueCount {n r q : ℕ} (hq : q ≤ r)
    (available : Fin r → Edge n) (state : DFSState n) (bits : Fin r → Bool) :
    (dfsRun hq available state bits).trueCount =
      prefixWeight (AdaptiveTree.answerEquiv (dfsTree available state) bits) q := by
  induction q generalizing r available state bits with
  | zero => simp [dfsRun]
  | succ q ih =>
      cases r with
      | zero => omega
      | succ r =>
          simp only [dfsRun, dfsTree, prefixWeight,
            AdaptiveTree.answerEquiv_node_zero]
          rw [ih (Nat.le_of_succ_le_succ hq)]
          congr 1

theorem dfsRun_positiveDFS_le {n r q : ℕ} (hq : q ≤ r)
    (available : Fin r → Edge n) (state : DFSState n) (bits : Fin r → Bool) :
    (dfsRun hq available state bits).state.positiveDFS ≤
      state.positiveDFS + (dfsRun hq available state bits).trueCount := by
  induction q generalizing r available state bits with
  | zero => simp [dfsRun]
  | succ q ih =>
      cases r with
      | zero => omega
      | succ r =>
          simp only [dfsRun]
          have htail := ih (Nat.le_of_succ_le_succ hq)
            (removeAvailable available (state.pivot available))
            (state.advance available (bits (state.pivot available)))
            (Fin.removeNth (state.pivot available) bits)
          have hstep := state.advance_positiveDFS_le available
            (bits (state.pivot available))
          omega

theorem dfsRun_fallback_true {n r q : ℕ} (hq : q ≤ r)
    (available : Fin r → Edge n) (state : DFSState n) (bits : Fin r → Bool)
    (htrue : state.fallback = true) :
    (dfsRun hq available state bits).state.fallback = true := by
  induction q generalizing r available state bits with
  | zero => simpa [dfsRun] using htrue
  | succ q ih =>
      cases r with
      | zero => omega
      | succ r =>
          simp only [dfsRun]
          apply ih (Nat.le_of_succ_le_succ hq)
          exact state.fallback_le_advance available
            (bits (state.pivot available)) htrue

theorem dfsRun_positiveDFS_eq_of_fallback_false {n r q : ℕ} (hq : q ≤ r)
    (available : Fin r → Edge n) (state : DFSState n) (bits : Fin r → Bool)
    (hfalse : (dfsRun hq available state bits).state.fallback = false) :
    (dfsRun hq available state bits).state.positiveDFS =
      state.positiveDFS + (dfsRun hq available state bits).trueCount := by
  induction q generalizing r available state bits with
  | zero => simp [dfsRun]
  | succ q ih =>
      cases r with
      | zero => omega
      | succ r =>
          simp only [dfsRun] at hfalse ⊢
          let p := state.pivot available
          let b := bits p
          let tailAvailable := removeAvailable available p
          let tailState := state.advance available b
          let tailBits := Fin.removeNth p bits
          have htailFalse : tailState.fallback = false := by
            by_contra hnot
            have htrue : tailState.fallback = true := by
              cases h : tailState.fallback <;> simp_all
            have := dfsRun_fallback_true (Nat.le_of_succ_le_succ hq)
              tailAvailable tailState tailBits htrue
            rw [hfalse] at this
            contradiction
          have htail := ih (Nat.le_of_succ_le_succ hq)
            tailAvailable tailState tailBits hfalse
          have hstep := state.advance_fallback_false_positiveDFS available b htailFalse
          rw [htail, hstep]
          simp only [p, b, tailAvailable, tailState, tailBits, Nat.add_assoc]

theorem exists_path_with_support_of_chain {V : Type*} {G : SimpleGraph V}
    {l : List V} (hne : l ≠ []) (hchain : List.IsChain G.Adj l)
    (hnodup : l.Nodup) :
    ∃ u v, ∃ p : G.Walk u v, p.support = l ∧ p.IsPath := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons x xs =>
      cases xs with
      | nil => exact ⟨x, x, .nil, by simp, .nil⟩
      | cons y ys =>
          have hxy : G.Adj x y := hchain.rel
          have htailChain : List.IsChain G.Adj (y :: ys) := hchain.tail
          have htailNodup : (y :: ys).Nodup := hnodup.tail
          obtain ⟨u, v, p, hpSupport, hpPath⟩ :=
            exists_path_with_support_of_chain (l := y :: ys) (by simp)
              htailChain htailNodup
          have hu : u = y := by
            have hphead : p.support.head? = some u := by
              cases p <;> rfl
            have hshead := congrArg List.head? hpSupport
            rw [hphead] at hshead
            exact Option.some.inj hshead
          subst u
          refine ⟨x, v, p.cons hxy, ?_, ?_⟩
          · simp [hpSupport]
          · apply hpPath.cons
            have hxnot : x ∉ y :: ys := (List.nodup_cons.mp hnodup).1
            simpa [hpSupport] using hxnot
termination_by l.length

/-- A realized, duplicate-free DFS stack is a contained path on exactly its
number of vertices. -/
theorem DFSState.pathGraph_stack_length_isContained {n : ℕ}
    {G : Edge n → Bool} {st : DFSState n} (hreal : st.Realized G)
    (hnodup : st.stack.Nodup) :
    SimpleGraph.pathGraph st.stack.length ⊑ graphFromBits G := by
  by_cases hempty : st.stack = []
  · have hz : (⊥ : SimpleGraph (Fin 0)) ⊑ graphFromBits G :=
      ⟨SimpleGraph.Copy.bot .ofIsEmpty⟩
    have hpg : SimpleGraph.pathGraph 0 = (⊥ : SimpleGraph (Fin 0)) := by
      ext u
      exact Fin.elim0 u
    have hlen0 : st.stack.length = 0 := by simp [hempty]
    rw [hlen0, hpg]
    exact hz
  · obtain ⟨u, v, p, hpSupport, hpPath⟩ :=
      exists_path_with_support_of_chain hempty hreal hnodup
    have hc := hpPath.isContained_pathGraph
    have hlen : p.length + 1 = st.stack.length := by
      rw [← p.length_support, hpSupport]
    rw [hlen] at hc
    exact hc

/-- Initial vertices embed a shorter path into a longer path. -/
def pathInitialCopy {k l : ℕ} (hkl : k ≤ l) :
    (SimpleGraph.pathGraph k).Copy (SimpleGraph.pathGraph l) :=
  ⟨⟨Fin.castLE hkl, by
      intro i j hij
      rw [SimpleGraph.pathGraph_adj] at hij ⊢
      rcases hij with hij | hij
      · left; simpa using hij
      · right; simpa using hij⟩,
    Fin.castLE_injective hkl⟩

theorem DFSState.stack_length_lt_of_path_free {n k : ℕ}
    {G : Edge n → Bool} {st : DFSState n}
    (hwf : st.stack.Nodup) (hreal : st.Realized G)
    (hfree : ¬SimpleGraph.pathGraph k ⊑ graphFromBits G) :
    st.stack.length < k := by
  by_contra hnot
  have hkle : k ≤ st.stack.length := Nat.not_lt.mp hnot
  apply hfree
  have hs := st.pathGraph_stack_length_isContained hreal hwf
  exact ⟨hs.some.comp (pathInitialCopy hkle)⟩

/-- Counting already-exposed clique edges. -/
theorem choose_card_add_available_le {n r : ℕ} (R : Finset (Fin n))
    (available : Fin r → Edge n) (hinj : Function.Injective available)
    (hno : ∀ i x, x ∈ R → ∀ y, y ∈ R → x ≠ y →
      (available i).1 ≠ s(x, y)) :
    R.card.choose 2 + r ≤ n.choose 2 := by
  classical
  let f : ↥R ↪ Fin n := Function.Embedding.subtype _
  let K : SimpleGraph (Fin n) := (⊤ : SimpleGraph ↥R).map f
  let A : Finset (Sym2 (Fin n)) := K.edgeFinset
  let B : Finset (Sym2 (Fin n)) := Finset.univ.image fun i ↦ (available i).1
  have hcardA : A.card = R.card.choose 2 := by
    calc
      A.card = (⊤ : SimpleGraph ↥R).edgeFinset.card := by
        simp [A, K]
      _ = (Fintype.card ↥R).choose 2 :=
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two
      _ = R.card.choose 2 := by rw [Fintype.card_coe]
  have hcardB : B.card = r := by
    change (Finset.univ.image fun i ↦ (available i).1).card = r
    rw [Finset.card_image_of_injective _
      (fun _ _ h ↦ hinj (Subtype.ext h))]
    simp
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    obtain ⟨i, _hi, hie⟩ := Finset.mem_image.mp heB
    subst e
    have heA' : (available i).1 ∈
        ((⊤ : SimpleGraph ↥R).edgeFinset.map f.sym2Map) := by
      simpa [A, K, SimpleGraph.edgeFinset_map] using heA
    obtain ⟨e, he, hmap⟩ := Finset.mem_map.mp heA'
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy : x ≠ y := by
          intro h
          subst y
          exact (⊤ : SimpleGraph ↥R).not_isDiag_of_mem_edgeFinset he rfl
        apply hno i x.1 x.2 y.1 y.2 (Subtype.val_injective.ne hxy)
        simpa [f] using hmap.symm
  have hsubset : A ∪ B ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset := by
    intro e he
    rcases Finset.mem_union.mp he with heA | heB
    · exact SimpleGraph.edgeFinset_mono le_top heA
    · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp heB
      exact (available i).2
  have hcardUnion : (A ∪ B).card = A.card + B.card :=
    Finset.card_union_of_disjoint hdisj
  calc
    R.card.choose 2 + r = A.card + B.card := by rw [hcardA, hcardB]
    _ = (A ∪ B).card := hcardUnion.symm
    _ ≤ ((⊤ : SimpleGraph (Fin n)).edgeFinset).card := Finset.card_le_card hsubset
    _ = n.choose 2 := by
      simpa using SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n)

/-- Counting already-exposed edges between two disjoint vertex sets. -/
theorem card_mul_add_available_le {n r : ℕ} (D U : Finset (Fin n))
    (hDU : Disjoint D U) (available : Fin r → Edge n)
    (hinj : Function.Injective available)
    (hno : ∀ i d, d ∈ D → ∀ u, u ∈ U →
      (available i).1 ≠ s(d, u)) :
    D.card * U.card + r ≤ n.choose 2 := by
  classical
  let cross : ↥D × ↥U → Edge n := fun z ↦
    edgeOfNe z.1 z.2 (by
      intro h
      exact Finset.disjoint_left.mp hDU z.1.2 (h ▸ z.2.2))
  have hcross : Function.Injective cross := by
    rintro ⟨d, u⟩ ⟨d', u'⟩ h
    have he : s(d.1, u.1) = s(d'.1, u'.1) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp he with hstraight | hswap
    · apply Prod.ext <;> apply Subtype.ext
      · exact hstraight.1
      · exact hstraight.2
    · exfalso
      exact Finset.disjoint_left.mp hDU d.2 (hswap.1 ▸ u'.2)
  let A : Finset (Edge n) := Finset.univ.image cross
  let B : Finset (Edge n) := Finset.univ.image available
  have hcardA : A.card = D.card * U.card := by
    change (Finset.univ.image cross).card = D.card * U.card
    rw [Finset.card_image_of_injective _ hcross]
    simp
  have hcardB : B.card = r := by
    change (Finset.univ.image available).card = r
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    obtain ⟨⟨d, u⟩, _hdu, hde⟩ := Finset.mem_image.mp heA
    obtain ⟨i, _hi, hie⟩ := Finset.mem_image.mp heB
    have heq : cross (d, u) = available i := hde.trans hie.symm
    apply hno i d.1 d.2 u.1 u.2
    simpa [cross, edgeOfNe] using (congrArg Subtype.val heq).symm
  have hsubset : A ∪ B ⊆ (Finset.univ : Finset (Edge n)) :=
    Finset.subset_univ _
  have hcardUnion : (A ∪ B).card = A.card + B.card :=
    Finset.card_union_of_disjoint hdisj
  calc
    D.card * U.card + r = A.card + B.card := by rw [hcardA, hcardB]
    _ = (A ∪ B).card := hcardUnion.symm
    _ ≤ (Finset.univ : Finset (Edge n)).card := Finset.card_le_card hsubset
    _ = n.choose 2 := by simpa only [Finset.card_univ] using card_edge n


/-- Canonical enumeration of the possible graph edges. -/
def edgeEquiv (n : ℕ) : Fin (n.choose 2) ≃ Edge n :=
  (((⊤ : SimpleGraph (Fin n)).edgeFinset.equivFinOfCardEq
    (by simpa using
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n))).symm)

def edgeEnumeration (n : ℕ) : Fin (n.choose 2) → Edge n := edgeEquiv n

theorem edgeEnumeration_bijective (n : ℕ) :
    Function.Bijective (edgeEnumeration n) := by
  exact (edgeEquiv n).bijective

/-- The canonical adaptive DFS tree on graphs with vertex set `Fin n`. -/
def canonicalDFSTree (n : ℕ) : AdaptiveTree (n.choose 2) :=
  dfsTree (edgeEnumeration n) (DFSState.initial n)

/-- Interpret the canonical Boolean edge word as a graph. -/
def canonicalGraph (n : ℕ) (bits : Fin (n.choose 2) → Bool) :
    SimpleGraph (Fin n) :=
  graphFromBits fun e ↦ bits ((edgeEquiv n).symm e)

/-- The deterministic information delivered by the first `q` adaptive DFS
queries, under the hypothesis that the graph contains no `k`-vertex path.

The two final alternatives are the two possible DFS regimes.  In the
`fallback` regime DFS has already completed, so every discovered non-root
vertex was paid for by a positive answer.  Otherwise the usual DFS accounting
identity and the exposed `done`--`unseen` cut bound are available. -/
theorem canonicalDFS_certificate {n q k : ℕ} (hq : q ≤ n.choose 2)
    (bits : Fin (n.choose 2) → Bool)
    (hfree : ¬SimpleGraph.pathGraph k ⊑ canonicalGraph n bits) :
    let R := dfsRun hq (edgeEnumeration n) (DFSState.initial n) bits
    let X := prefixWeight
      (AdaptiveTree.answerEquiv (canonicalDFSTree n) bits) q
    R.state.roots.card.choose 2 ≤ q ∧
      R.state.stack.length < k ∧
      ((R.state.fallback = true ∧
          n ≤ X + R.state.roots.card) ∨
        (R.state.fallback = false ∧
          R.state.done.card + R.state.stack.length =
            X + R.state.roots.card ∧
          R.state.done.card + R.state.unseen.card +
              R.state.stack.length = n ∧
          R.state.done.card * R.state.unseen.card ≤ q)) := by
  dsimp only
  let R := dfsRun hq (edgeEnumeration n) (DFSState.initial n) bits
  have hwf : R.state.WellFormed R.available :=
    dfsRun_wellFormed hq
      (DFSState.wellFormed_initial n (n.choose 2) (edgeEnumeration n))
  have hinj : Function.Injective R.available :=
    dfsRun_available_injective hq (edgeEnumeration_bijective n).1
  have hreal : R.state.Realized
      (fun e ↦ bits ((edgeEquiv n).symm e)) := by
    apply dfsRun_realized hq
      (DFSState.realized_initial (fun e ↦ bits ((edgeEquiv n).symm e)))
    intro i
    simp [edgeEnumeration]
  have hrootRaw := choose_card_add_available_le R.state.roots R.available
    hinj hwf.noAvailable_roots
  have havailCard : n.choose 2 - q + q = n.choose 2 :=
    Nat.sub_add_cancel hq
  have hroot : R.state.roots.card.choose 2 ≤ q := by
    omega
  have hstack : R.state.stack.length < k := by
    apply R.state.stack_length_lt_of_path_free hwf.stack_nodup hreal
    simpa [canonicalGraph] using hfree
  refine ⟨hroot, hstack, ?_⟩
  have hX : R.trueCount = prefixWeight
      (AdaptiveTree.answerEquiv (canonicalDFSTree n) bits) q := by
    simpa [R, canonicalDFSTree] using
      dfsRun_trueCount hq (edgeEnumeration n) (DFSState.initial n) bits
  cases hf : R.state.fallback with
  | false =>
      right
      refine ⟨rfl, ?_, hwf.card_partition, ?_⟩
      · have hpos := dfsRun_positiveDFS_eq_of_fallback_false hq
          (edgeEnumeration n) (DFSState.initial n) bits hf
        change R.state.positiveDFS =
          (DFSState.initial n).positiveDFS + R.trueCount at hpos
        calc
          R.state.done.card + R.state.stack.length =
              R.state.positiveDFS + R.state.roots.card := hwf.card_account
          _ = R.trueCount + R.state.roots.card := by
            rw [hpos]
            simp [DFSState.initial]
          _ = prefixWeight
                (AdaptiveTree.answerEquiv (canonicalDFSTree n) bits) q +
              R.state.roots.card := by rw [hX]
      · have hcrossRaw := card_mul_add_available_le R.state.done
          R.state.unseen hwf.disjoint_done_unseen R.available hinj
          hwf.noAvailable_done_unseen
        have hcross : R.state.done.card * R.state.unseen.card ≤ q := by
          omega
        simpa [R] using hcross
  | true =>
      left
      refine ⟨rfl, ?_⟩
      obtain ⟨hdone, hunseen, hstackEmpty⟩ := hwf.fallback_complete hf
      have hpos := dfsRun_positiveDFS_le hq
        (edgeEnumeration n) (DFSState.initial n) bits
      change R.state.positiveDFS ≤
        (DFSState.initial n).positiveDFS + R.trueCount at hpos
      have hacc := hwf.card_account
      rw [hdone, hstackEmpty] at hacc
      simp only [List.length_nil, Nat.add_zero] at hacc
      have hgoal : n ≤ prefixWeight
          (AdaptiveTree.answerEquiv (canonicalDFSTree n) bits) q +
            R.state.roots.card := by
        simp only [DFSState.initial, Nat.zero_add] at hpos
        omega
      simpa [R] using hgoal

/-- A purely numerical corollary of the DFS certificate.  If the number of
positive answers in the adaptive prefix lies in `[lo,hi]`, the root set is
forced below `rootCap`, and the displayed rectangle has more than `q`
edges, then the graph has a `k`-vertex path.  This is the interface used by
the concentration argument. -/
theorem canonicalGraph_hasPath_of_prefix_window
    {n q k lo hi rootCap : ℕ} (hq : q ≤ n.choose 2)
    (hroot : ∀ r : ℕ, r.choose 2 ≤ q → r ≤ rootCap)
    (hfallback : hi + rootCap < n)
    (hrectangle : q < (lo - (k - 1)) * (n - hi - rootCap))
    (bits : Fin (n.choose 2) → Bool)
    (hlo : lo ≤ prefixWeight
      (AdaptiveTree.answerEquiv (canonicalDFSTree n) bits) q)
    (hhi : prefixWeight
      (AdaptiveTree.answerEquiv (canonicalDFSTree n) bits) q ≤ hi) :
    SimpleGraph.pathGraph k ⊑ canonicalGraph n bits := by
  by_contra hfree
  let R := dfsRun hq (edgeEnumeration n) (DFSState.initial n) bits
  let X := prefixWeight
    (AdaptiveTree.answerEquiv (canonicalDFSTree n) bits) q
  have hcert := canonicalDFS_certificate hq bits hfree
  change R.state.roots.card.choose 2 ≤ q ∧
      R.state.stack.length < k ∧
      ((R.state.fallback = true ∧ n ≤ X + R.state.roots.card) ∨
        (R.state.fallback = false ∧
          R.state.done.card + R.state.stack.length =
            X + R.state.roots.card ∧
          R.state.done.card + R.state.unseen.card +
              R.state.stack.length = n ∧
          R.state.done.card * R.state.unseen.card ≤ q)) at hcert
  obtain ⟨hrootChoose, hstack, hcase⟩ := hcert
  change lo ≤ X at hlo
  change X ≤ hi at hhi
  have hrootCap : R.state.roots.card ≤ rootCap := hroot _ hrootChoose
  rcases hcase with hdone | hrunning
  · rcases hdone with ⟨hf, hcomplete⟩
    have : n ≤ hi + rootCap := by omega
    omega
  · rcases hrunning with ⟨hf, haccount, hpartition, hcross⟩
    have hstackLe : R.state.stack.length ≤ k - 1 := by omega
    have hdoneLower : lo - (k - 1) ≤ R.state.done.card := by
      omega
    have hunseenLower : n - hi - rootCap ≤ R.state.unseen.card := by
      omega
    have hmul : (lo - (k - 1)) * (n - hi - rootCap) ≤
        R.state.done.card * R.state.unseen.card :=
      Nat.mul_le_mul hdoneLower hunseenLower
    have hleq := hmul.trans hcross
    omega

end Erdos900
