import ErdosProblems.Erdos767.LongestCycle

open scoped SimpleGraph

namespace Erdos767Scratch

open SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A cycle together with a simple path whose only cycle vertex is its
initial vertex.  The terminal vertex is allowed to equal the initial vertex,
so every cycle has the degenerate lollipop with a nil tail. -/
structure Lollipop (G : SimpleGraph V) where
  cycleBase : V
  cycle : G.Walk cycleBase cycleBase
  cycle_isCycle : cycle.IsCycle
  start : V
  terminal : V
  tail : G.Walk start terminal
  tail_isPath : tail.IsPath
  start_mem_cycle : start ∈ cycle.support
  cycle_tail_inter : ∀ {x : V}, x ∈ cycle.support → x ∈ tail.support → x = start

namespace Lollipop

/-- The degenerate lollipop with nil tail based at the base vertex of a
cycle. -/
def nilOfCycle {z : V} (c : G.Walk z z) (hc : c.IsCycle) : Lollipop G where
  cycleBase := z
  cycle := c
  cycle_isCycle := hc
  start := z
  terminal := z
  tail := .nil
  tail_isPath := by simp
  start_mem_cycle := c.start_mem_support
  cycle_tail_inter := by
    intro x _hxC hxP
    simpa using hxP

@[simp] lemma nilOfCycle_cycle {z : V} (c : G.Walk z z) (hc : c.IsCycle) :
    (nilOfCycle c hc).cycle = c := rfl

@[simp] lemma nilOfCycle_tail_length {z : V} (c : G.Walk z z) (hc : c.IsCycle) :
    (nilOfCycle c hc).tail.length = 0 := rfl

/-- Finset form of the defining intersection condition. -/
lemma cycle_support_inter_tail_support (L : Lollipop G) :
    L.cycle.support.toFinset ∩ L.tail.support.toFinset = {L.start} := by
  ext x
  constructor
  · intro hx
    have hxC : x ∈ L.cycle.support := List.mem_toFinset.mp (Finset.mem_inter.mp hx).1
    have hxP : x ∈ L.tail.support := List.mem_toFinset.mp (Finset.mem_inter.mp hx).2
    simpa using L.cycle_tail_inter hxC hxP
  · intro hx
    have hxs : x = L.start := by simpa using hx
    subst x
    exact Finset.mem_inter.mpr
      ⟨List.mem_toFinset.mpr L.start_mem_cycle,
        List.mem_toFinset.mpr L.tail.start_mem_support⟩

/-- The tail of a lollipop is shorter than the number of ambient vertices. -/
lemma tail_length_lt_card (L : Lollipop G) :
    L.tail.length < Fintype.card V :=
  L.tail_isPath.length_lt

end Lollipop

/-- A lexicographically best lollipop: its cycle is globally longest and,
among lollipops on a cycle of that length, its tail is globally longest. -/
structure BestLollipop (G : SimpleGraph V) extends Lollipop G where
  cycle_maximal : ∀ {z : V} (c : G.Walk z z), c.IsCycle → c.length ≤ cycle.length
  tail_maximal : ∀ (L : Lollipop G),
    L.cycle.length = cycle.length → L.tail.length ≤ tail.length

namespace BestLollipop

/-- A path from a vertex in a set to a vertex outside it contains an edge
crossing from the set to its complement. -/
lemma exists_crossing_edge_of_walk {a b : V} (S : Set V)
    (p : G.Walk a b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ x y : V, x ∈ S ∧ y ∉ S ∧ G.Adj x y := by
  induction p with
  | nil => exact (hb ha).elim
  | @cons a x b hax p ih =>
      by_cases hx : x ∈ S
      · exact ih hx hb
      · exact ⟨a, x, ha, hx, hax⟩

/-- In a connected graph, every nonempty proper vertex set has a crossing
edge. -/
lemma exists_crossing_edge_of_connected (hconn : G.Connected) (S : Set V)
    {a b : V} (ha : a ∈ S) (hb : b ∉ S) :
    ∃ x y : V, x ∈ S ∧ y ∉ S ∧ G.Adj x y := by
  obtain ⟨p, _hp⟩ := hconn.exists_isPath a b
  exact exists_crossing_edge_of_walk S p ha hb

/-- A crossing edge from a cycle to its complement is a positive lollipop
tail of length one. -/
def ofCycleCrossingEdge {z x y : V} (c : G.Walk z z) (hc : c.IsCycle)
    (hx : x ∈ c.support) (hy : y ∉ c.support) (hxy : G.Adj x y) : Lollipop G where
  cycleBase := z
  cycle := c
  cycle_isCycle := hc
  start := x
  terminal := y
  tail := hxy.toWalk
  tail_isPath := hxy.isPath_toWalk
  start_mem_cycle := hx
  cycle_tail_inter := by
    intro w hwC hwP
    simp only [Adj.support_toWalk, List.mem_cons] at hwP
    rcases hwP with rfl | hwP
    · rfl
    · rcases hwP with rfl | hwP
      · exact (hy hwC).elim
      · simp at hwP

@[simp] lemma ofCycleCrossingEdge_tail_length {z x y : V}
    (c : G.Walk z z) (hc : c.IsCycle) (hx : x ∈ c.support)
    (hy : y ∉ c.support) (hxy : G.Adj x y) :
    (ofCycleCrossingEdge c hc hx hy hxy).tail.length = 1 := by
  simp [ofCycleCrossingEdge]

/-- A lexicographically best lollipop exists in every finite two-connected
graph. -/
theorem exists_bestLollipop (hTwo : Erdos58.TwoConnected G) :
    Nonempty (BestLollipop G) := by
  obtain ⟨z, c, hc⟩ := Erdos767LongestCycle.exists_isLongestCycle hTwo
  let T : Set ℕ := {n | ∃ L : Lollipop G,
    L.cycle.length = c.length ∧ L.tail.length = n}
  have hTfinite : T.Finite := by
    apply Set.Finite.subset (Set.finite_le_nat (Fintype.card V))
    intro n hn
    obtain ⟨L, _hLc, rfl⟩ := hn
    exact L.tail_length_lt_card.le
  have hTnonempty : T.Nonempty := by
    refine ⟨0, Lollipop.nilOfCycle c hc.1, ?_, rfl⟩
    rfl
  obtain ⟨m, hm, hmmax⟩ := hTfinite.exists_maximal hTnonempty
  obtain ⟨L, hLcycle, hLtail⟩ := hm
  refine ⟨{
    toLollipop := L
    cycle_maximal := ?_
    tail_maximal := ?_ }⟩
  · intro z' c' hc'
    rw [hLcycle]
    exact hc.2 c' hc'
  · intro L' hL'cycle
    have hmem : L'.tail.length ∈ T := by
      exact ⟨L', hL'cycle.trans hLcycle, rfl⟩
    rw [hLtail]
    rcases le_total L'.tail.length m with hle | hge
    · exact hle
    · exact hmmax hmem hge

/-- The selected cycle is globally longest (standalone projection form). -/
lemma isLongestCycle (B : BestLollipop G) :
    Erdos767LongestCycle.IsLongestCycle B.cycle := by
  refine ⟨B.cycle_isCycle, ?_⟩
  intro z' c' hc'
  exact B.cycle_maximal c' hc'

/-- If the selected longest cycle is nonspanning, connectedness gives a
crossing edge and tail maximality forces the selected tail to be positive. -/
lemma tail_length_pos_of_cycle_not_spanning (hTwo : Erdos58.TwoConnected G)
    (B : BestLollipop G)
    (hnotspan : B.cycle.support.toFinset ≠ (Finset.univ : Finset V)) :
    0 < B.tail.length := by
  have hproper : ∃ y : V, y ∉ B.cycle.support := by
    by_contra h
    apply hnotspan
    ext y
    have hy : y ∈ B.cycle.support := not_not.mp (not_exists.mp h y)
    simp [hy]
  obtain ⟨y, hy⟩ := hproper
  obtain ⟨x, w, hx, hw, hxw⟩ := exists_crossing_edge_of_connected
    hTwo.connected ({v : V | v ∈ B.cycle.support})
    B.cycle.start_mem_support hy
  let L := ofCycleCrossingEdge B.cycle B.cycle_isCycle hx hw hxw
  have hle : L.tail.length ≤ B.tail.length := B.tail_maximal L rfl
  have hlen : L.tail.length = 1 := by
    simp [L, ofCycleCrossingEdge]
  omega

end BestLollipop

end

end Erdos767Scratch
