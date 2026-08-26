import ErdosProblems.Erdos593.TripleSystem.Obligatory
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.SetTheory.Cardinal.Aleph

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The one-apex sequence lift

This module defines the sequence tree and the simple 3-uniform lift used in the
avoidance direction of Erdős Problem 593.  Sequence lengths range over a
concrete well-order of cardinality `ℵ₁`; a lift hyperedge consists of a graph
edge at a base node and one apex at a node extending the base by that edge.
-/

namespace Erdos593

open scoped Cardinal Ordinal

universe u

namespace SequenceLift

/-- A concrete well-ordered index type of cardinality `ℵ₁`. -/
abbrev Index : Type u := (ω₁ : Ordinal.{u}).ToType

noncomputable instance indexNonempty : Nonempty (Index : Type u) :=
  Ordinal.nonempty_toType_iff.mpr (Cardinal.isSuccLimit_omega 1).ne_bot

noncomputable instance indexOrderBot : OrderBot (Index : Type u) :=
  WellFoundedLT.toOrderBot (Index : Type u)

/-- A graph edge used as a letter in the sequence tree. -/
abbrev Alphabet {V : Type u} (G : _root_.SimpleGraph V) : Type u := G.edgeSet

/-- A sequence of graph edges of countable ordinal length. -/
structure Node {V : Type u} (G : _root_.SimpleGraph V) where
  length : Index
  entry : Set.Iio length → Alphabet G

namespace Node

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- `t` extends `q` by the prescribed next letter (and may then continue). -/
def ExtendsBy (q : Node G) (a : Alphabet G) (t : Node G) : Prop :=
  ∃ h : q.length < t.length,
    (∀ i : Set.Iio q.length,
      q.entry i = t.entry ⟨i.1, i.2.trans h⟩) ∧
    t.entry ⟨q.length, h⟩ = a

theorem ne_of_extendsBy {q t : Node G} {a : Alphabet G}
    (h : q.ExtendsBy a t) : q ≠ t := by
  intro hqt
  rcases h with ⟨hlen, _⟩
  exact hlen.ne (congrArg Node.length hqt)

end Node

/-- Vertices of the one-apex lift. -/
abbrev Point {V : Type u} (G : _root_.SimpleGraph V) : Type u := Node G × V

/-- Turn an adjacency witness into the corresponding alphabet letter. -/
def edgeLetter {V : Type u} {G : _root_.SimpleGraph V}
    {x y : V} (hxy : G.Adj x y) : Alphabet G :=
  ⟨s(x, y), hxy⟩

/-- The extensional edge sets admitted by the one-apex construction. -/
def IsEdgeSet {V : Type u} (G : _root_.SimpleGraph V)
    (S : Set (Point G)) : Prop :=
  ∃ (q t : Node G) (x y z : V) (hxy : G.Adj x y),
    q.ExtendsBy (edgeLetter hxy) t ∧
      S = {(q, x), (q, y), (t, z)}

/-- Hyperedges are represented by their vertex sets, making simplicity
definitionally transparent. -/
abbrev Edge {V : Type u} (G : _root_.SimpleGraph V) : Type u :=
  {S : Set (Point G) // IsEdgeSet G S}

/-- The lift hyperedge determined by explicit base and apex data. -/
def mkEdge {V : Type u} {G : _root_.SimpleGraph V}
    (q t : Node G) (x y z : V) (hxy : G.Adj x y)
    (hext : q.ExtendsBy (edgeLetter hxy) t) : Edge G :=
  ⟨{(q, x), (q, y), (t, z)}, ⟨q, t, x, y, z, hxy, hext, rfl⟩⟩

private theorem ncard_triple {α : Type u} {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Set α).ncard = 3 := by
  rw [Set.ncard_insert_of_notMem (by simp [hab, hac]), Set.ncard_pair hbc]

/-- The one-apex sequence lift of a graph. -/
noncomputable def system {V : Type u} (G : _root_.SimpleGraph V) :
    TripleSystem (Point G) (Edge G) where
  Inc p e := p ∈ e.1
  edge_ncard e := by
    rcases e.2 with ⟨q, t, x, y, z, hxy, hext, hset⟩
    simp only [Set.setOf_mem_eq]
    rw [hset]
    have hqt : q ≠ t := Node.ne_of_extendsBy hext
    apply ncard_triple
    · exact fun h ↦ hxy.ne (congrArg Prod.snd h)
    · exact fun h ↦ hqt (congrArg Prod.fst h)
    · exact fun h ↦ hqt (congrArg Prod.fst h)
  simple := by
    intro e f h
    apply Subtype.ext
    simpa only [Set.setOf_mem_eq] using! h

@[simp]
theorem inc_mkEdge_iff {V : Type u} {G : _root_.SimpleGraph V}
    {p : Point G} {q t : Node G} {x y z : V} {hxy : G.Adj x y}
    {hext : q.ExtendsBy (edgeLetter hxy) t} :
    (system G).Inc p (mkEdge q t x y z hxy hext) ↔
      p = (q, x) ∨ p = (q, y) ∨ p = (t, z) := by
  simp [system, mkEdge]

/-- Restrict a global branch to the initial segment below `α`. -/
def branchNode {V : Type u} {G : _root_.SimpleGraph V}
    (a : Index → Alphabet G) (α : Index) : Node G where
  length := α
  entry i := a i.1

/-- Two restrictions of one global branch have the exact extension relation
needed by a lift edge. -/
theorem branchNode_extendsBy {V : Type u} {G : _root_.SimpleGraph V}
    (a : Index → Alphabet G) {α β : Index} (hαβ : α < β) :
    (branchNode a α).ExtendsBy (a α) (branchNode a β) := by
  refine ⟨hαβ, ?_, rfl⟩
  intro i
  rfl

/-- Choose the next branch letter from the node formed by all earlier choices. -/
noncomputable def branchLetter {V : Type u} {G : _root_.SimpleGraph V}
    (pick : Node G → Alphabet G) : Index → Alphabet G :=
  WellFounded.fix (wellFounded_lt : WellFounded ((· < ·) : Index → Index → Prop))
    fun α earlier ↦ pick ⟨α, fun i ↦ earlier i.1 i.2⟩

theorem branchLetter_eq {V : Type u} {G : _root_.SimpleGraph V}
    (pick : Node G → Alphabet G) (α : Index) :
    branchLetter pick α = pick (branchNode (branchLetter pick) α) := by
  rw [branchLetter, WellFounded.fix_eq]
  rfl

end SequenceLift

end Erdos593
