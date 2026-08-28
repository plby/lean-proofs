import ErdosProblems.Erdos577.Saturation

/-! Finite triangle-remainder partitions and Wang's two optimizing scores. -/

namespace Erdos577

open Finset
open scoped BigOperators

/-- The finite data on which the chain optimization is performed. -/
@[ext] structure TriangleData (V : Type*) where
  terminal : V
  triangle : Finset V
  blocks : Finset (Finset V)
  deriving DecidableEq, Fintype

variable {V : Type*} [Fintype V] [DecidableEq V]

def TriangleData.remainder (d : TriangleData V) : Finset V := insert d.terminal d.triangle

/-- All cycles and disjointness conditions are assertions about the actual graph. -/
structure TriangleData.Valid (G : SimpleGraph V) (d : TriangleData V) : Prop where
  triangle_clique : G.IsNClique 3 d.triangle
  terminal_not_mem : d.terminal ∉ d.triangle
  blocks_quad : ∀ b ∈ d.blocks, QuadOn G b
  blocks_disjoint : (d.blocks : Set (Finset V)).PairwiseDisjoint id
  remainder_disjoint : Disjoint d.remainder (d.blocks.biUnion id)
  cover : d.remainder ∪ d.blocks.biUnion id = univ

abbrev TriangleChain (G : SimpleGraph V) := {d : TriangleData V // d.Valid G}

noncomputable instance (G : SimpleGraph V) : Fintype (TriangleChain G) := Fintype.ofFinite _

namespace TriangleChain

variable {G : SimpleGraph V}

abbrev terminal (c : TriangleChain G) : V := c.val.terminal
abbrev triangle (c : TriangleChain G) : Finset V := c.val.triangle
abbrev blocks (c : TriangleChain G) : Finset (Finset V) := c.val.blocks
abbrev remainder (c : TriangleChain G) : Finset V := c.val.remainder
abbrev covered (c : TriangleChain G) : Finset V := c.blocks.biUnion id

def blockPartition (c : TriangleChain G) : BlockPartition G c.covered where
  blocks := c.blocks
  disjoint := c.property.blocks_disjoint
  cover := rfl
  quad := c.property.blocks_quad

lemma card_remainder (c : TriangleChain G) : c.remainder.card = 4 := by
  simp [remainder, TriangleData.remainder, c.property.terminal_not_mem,
    c.property.triangle_clique.card_eq]

lemma card_vertices (c : TriangleChain G) : Fintype.card V = 4 * (c.blocks.card + 1) := by
  have hc : (univ : Finset V).card = c.remainder.card + c.covered.card := by
    rw [← c.property.cover, card_union_of_disjoint c.property.remainder_disjoint]
  have hb := c.blockPartition.card
  have hr := c.card_remainder
  simp only [card_univ] at hc
  change c.covered.card = 4 * c.blocks.card at hb
  omega

lemma no_quad_remainder (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) : ¬QuadOn G c.remainder := by
  intro hq
  let p := (BlockPartition.single hq).union c.blockPartition c.property.remainder_disjoint
  apply hn
  apply p.hasPacking_of_card k
  have hc : c.remainder ∪ c.covered = univ := c.property.cover
  rw [hc, card_univ, hcard]

variable [DecidableRel G.Adj]

lemma terminal_degree_le_one (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    degreeIn G c.terminal c.triangle ≤ 1 := by
  by_contra hh
  have hd : 2 ≤ degreeIn G c.terminal c.triangle := by omega
  exact c.no_quad_remainder hcard hn
    (QuadOn.of_triangle c.property.triangle_clique c.property.terminal_not_mem hd)

def edgeScore (c : TriangleChain G) : ℕ := ∑ b ∈ c.blocks, edgeCount G b

def completeScore (c : TriangleChain G) : ℕ :=
  (c.blocks.filter fun b ↦ edgeCount G b = 6).card

/-- Only the first two maxima are retained in a feasible chain. -/
structure Feasible (c : TriangleChain G) : Prop where
  edge_max : ∀ d : TriangleChain G, d.edgeScore ≤ c.edgeScore
  complete_max : ∀ d : TriangleChain G, d.edgeScore = c.edgeScore →
    d.completeScore ≤ c.completeScore

/-- Both maxima are taken over an explicitly finite, nonempty collection. -/
theorem exists_feasible (hn : Nonempty (TriangleChain G)) :
    ∃ c : TriangleChain G, c.Feasible := by
  classical
  obtain ⟨c, _, hc⟩ := (univ : Finset (TriangleChain G)).exists_max_image
    edgeScore ⟨Classical.choice hn, mem_univ _⟩
  let firstMaxima : Finset (TriangleChain G) := univ.filter fun d ↦ d.edgeScore = c.edgeScore
  have hm : firstMaxima.Nonempty := ⟨c, by simp [firstMaxima]⟩
  obtain ⟨d, hd, hmax⟩ := firstMaxima.exists_max_image completeScore hm
  have hed : d.edgeScore = c.edgeScore := (mem_filter.mp hd).2
  refine ⟨d, ?_, ?_⟩
  · intro e
    rw [hed]
    exact hc e (mem_univ _)
  · intro e he
    apply hmax e
    exact mem_filter.mpr ⟨mem_univ _, he.trans hed⟩

end TriangleChain

end Erdos577
