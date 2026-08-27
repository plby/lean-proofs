import Arxiv.Arxiv2411_18291.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Common neighborhoods and typicality

The neighborhood definitions use uniformity `r + 1` and `r`-element faces,
so a vertex extension has the required cardinality by construction.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

def extendBlock (S : Block V r) (v : V) (hv : v ∉ S.val) : Block V (r + 1) :=
  ⟨insert v S.val, by rw [card_insert_of_notMem hv, S.property]⟩

omit [Fintype V] in
theorem extendBlock_injective (v : V) {S T : Block V r}
    (hS : v ∉ S.val) (hT : v ∉ T.val)
    (h : extendBlock S v hS = extendBlock T v hT) : S = T := by
  apply Subtype.ext
  have he := congrArg (fun e : Block V (r + 1) => e.val.erase v) h
  simpa [extendBlock, hS, hT] using he

def neighbors (G : Hypergraph V (r + 1)) (S : Block V r) : Finset V :=
  univ.filter fun v => ∃ hv : v ∉ S.val, extendBlock S v hv ∈ G

@[simp] theorem mem_neighbors (G : Hypergraph V (r + 1)) (S : Block V r) (v : V) :
    v ∈ neighbors G S ↔ ∃ hv : v ∉ S.val, extendBlock S v hv ∈ G := by
  simp [neighbors]

def commonNeighbors (G : Hypergraph V (r + 1)) (A : Finset (Block V r)) : Finset V :=
  univ.filter fun v => ∀ S ∈ A, v ∈ neighbors G S

@[simp] theorem mem_commonNeighbors (G : Hypergraph V (r + 1))
    (A : Finset (Block V r)) (v : V) :
    v ∈ commonNeighbors G A ↔ ∀ S ∈ A, v ∈ neighbors G S := by
  simp [commonNeighbors]

def faceVertices (A : Finset (Block V r)) : Finset V := A.biUnion Subtype.val

omit [Fintype V] in
@[simp] theorem mem_faceVertices (A : Finset (Block V r)) (v : V) :
    v ∈ faceVertices A ↔ ∃ S ∈ A, v ∈ S.val := by
  simp [faceVertices]

omit [Fintype V] in
theorem card_faceVertices_le (A : Finset (Block V r)) :
    (faceVertices A).card ≤ A.card * r := by
  calc
    _ ≤ ∑ S ∈ A, S.val.card := card_biUnion_le
    _ = ∑ _ ∈ A, r := sum_congr rfl fun S _ => S.property
    _ = _ := by simp

theorem commonNeighbors_not_mem_faceVertices (G : Hypergraph V (r + 1))
    (A : Finset (Block V r)) {v : V} (hv : v ∈ commonNeighbors G A) :
    v ∉ faceVertices A := by
  rintro h
  obtain ⟨S, hS, hvS⟩ := (mem_faceVertices A v).mp h
  obtain ⟨hnot, _⟩ := (mem_neighbors G S v).mp ((mem_commonNeighbors G A v).mp hv S hS)
  exact hnot hvS

abbrev OutsideFaces (A : Finset (Block V r)) := {v : V // v ∉ faceVertices A}

theorem card_outsideFaces (A : Finset (Block V r)) :
    Fintype.card (OutsideFaces A) = Fintype.card V - (faceVertices A).card := by
  simp only [OutsideFaces, Fintype.card_subtype_compl, Fintype.card_coe]

omit [Fintype V] in
theorem outside_not_mem (A : Finset (Block V r)) (v : OutsideFaces A)
    {S : Block V r} (hS : S ∈ A) : v.val ∉ S.val :=
  fun hv => v.property ((mem_faceVertices A v.val).mpr ⟨S, hS, hv⟩)

/-- The edges that must all occur for `v` to be a common neighbor of `A`. -/
def extensionEdges (A : Finset (Block V r)) (v : OutsideFaces A) : Hypergraph V (r + 1) :=
  A.attach.image fun S => extendBlock S.val v.val (outside_not_mem A v S.property)

omit [Fintype V] in
theorem mem_extensionEdges (A : Finset (Block V r)) (v : OutsideFaces A)
    (e : Block V (r + 1)) :
    e ∈ extensionEdges A v ↔
      ∃ S ∈ A, ∃ hS : v.val ∉ S.val, extendBlock S v.val hS = e := by
  constructor
  · intro h
    obtain ⟨S, _, rfl⟩ := mem_image.mp h
    exact ⟨S.val, S.property, outside_not_mem A v S.property, rfl⟩
  · rintro ⟨S, hS, hv, rfl⟩
    exact mem_image.mpr ⟨⟨S, hS⟩, mem_attach _ _, rfl⟩

omit [Fintype V] in
theorem card_extensionEdges (A : Finset (Block V r)) (v : OutsideFaces A) :
    (extensionEdges A v).card = A.card := by
  rw [extensionEdges, card_image_iff.mpr, card_attach]
  intro S _ T _ h
  exact Subtype.ext (extendBlock_injective v.val _ _ h)

omit [Fintype V] in
/-- Different candidate vertices outside all the faces use disjoint edge sets. -/
theorem extensionEdges_disjoint (A : Finset (Block V r)) :
    Pairwise fun v w : OutsideFaces A => Disjoint (extensionEdges A v) (extensionEdges A w) := by
  intro v w hvw
  apply disjoint_left.mpr
  intro e hev hew
  obtain ⟨S, hS, hvS, hve⟩ := (mem_extensionEdges A v e).mp hev
  obtain ⟨T, hT, hwT, hwe⟩ := (mem_extensionEdges A w e).mp hew
  have hmem : v.val ∈ e.val := by rw [← hve]; exact mem_insert_self _ _
  rw [← hwe] at hmem
  rcases mem_insert.mp hmem with h | h
  · exact hvw (Subtype.ext h)
  · exact outside_not_mem A v hT h

theorem commonNeighbors_iff_extensionEdges (G : Hypergraph V (r + 1))
    (A : Finset (Block V r)) (v : OutsideFaces A) :
    v.val ∈ commonNeighbors G A ↔ extensionEdges A v ⊆ G := by
  constructor
  · intro h e he
    obtain ⟨S, hS, hvS, rfl⟩ := (mem_extensionEdges A v e).mp he
    obtain ⟨_, he⟩ := (mem_neighbors G S v.val).mp
      ((mem_commonNeighbors G A v.val).mp h S hS)
    exact he
  · intro h
    apply (mem_commonNeighbors G A v.val).mpr
    intro S hS
    refine (mem_neighbors G S v.val).mpr ⟨outside_not_mem A v hS, h ?_⟩
    exact (mem_extensionEdges A v _).mpr ⟨S, hS, outside_not_mem A v hS, rfl⟩

theorem card_commonNeighbors_eq (G : Hypergraph V (r + 1)) (A : Finset (Block V r)) :
    (commonNeighbors G A).card =
      (univ.filter fun v : OutsideFaces A => extensionEdges A v ⊆ G).card := by
  apply card_bij (fun v hv =>
    (⟨v, commonNeighbors_not_mem_faceVertices G A hv⟩ : OutsideFaces A))
  · intro v hv
    simp only [mem_filter, mem_univ, true_and]
    exact (commonNeighbors_iff_extensionEdges G A _).mp hv
  · intro v hv w hw h
    exact congrArg Subtype.val h
  · intro v hv
    refine ⟨v.val, (commonNeighbors_iff_extensionEdges G A v).mpr (mem_filter.mp hv).2, ?_⟩
    rfl

def density (G : Hypergraph V r) : ℝ :=
  (G.card : ℝ) / (Fintype.card V).choose r

/-- Common-neighborhood counts relative to a specified reference density. -/
def IsTypicalAt (G : Hypergraph V (r + 1)) (p c : ℝ) (h : ℕ) : Prop :=
  ∀ A : Finset (Block V r), A.card ≤ h →
    |(commonNeighbors G A).card - Fintype.card V * p ^ A.card| ≤
      c * (Fintype.card V * p ^ A.card)

/-- Definition 5.2: common-neighborhood counts are close to the values
predicted by the graph's own edge density. -/
def IsTypical (G : Hypergraph V (r + 1)) (c : ℝ) (h : ℕ) : Prop :=
  IsTypicalAt G (density G) c h

end Arxiv2411_18291
