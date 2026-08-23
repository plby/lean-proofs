/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.PathCoverCycles

/-!
# The five-cycles in the KSSS path-cover augmentation

For three distinct old vertices `a,b,c`, one private two-edge path from
`a` to `b`, the old edge `bc`, and one private two-edge path from `c` to `a`
form a five-cycle.  These are the five-cycles occurring between consecutive
internal vertices of an augmented cycle in KSSS Lemma 4.3.

The second part of the file combines an arbitrary edge-disjoint realized
four-cycle and five-cycle into the exact nine-vertex quotient template used
by the full cycle-cover bank.
-/

namespace Erdos207

open Finset

noncomputable section

def pathCoverTwoEdgePath
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b : X) (hab : a ≠ b) (i : Fin k) :
    SimpleGraph (PathCoverVertex X k) :=
  SimpleGraph.edge (.root a) (pathCoverMiddleBetween a b hab i) ⊔
    SimpleGraph.edge (.root b) (pathCoverMiddleBetween a b hab i)

lemma pathCoverMiddleBetween_swap
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b : X) (hab : a ≠ b) (i : Fin k) :
    pathCoverMiddleBetween a b hab i =
      pathCoverMiddleBetween b a hab.symm i := by
  unfold pathCoverMiddleBetween
  congr 1
  apply Subtype.ext
  simp [pathCoverEdge]

lemma pathCoverTwoEdgePath_swap
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b : X) (hab : a ≠ b) (i : Fin k) :
    pathCoverTwoEdgePath a b hab i =
      pathCoverTwoEdgePath b a hab.symm i := by
  unfold pathCoverTwoEdgePath
  rw [← pathCoverMiddleBetween_swap a b hab i]
  ac_rfl

lemma pathCoverTwoEdgePath_eq_of_sym2_eq
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c d : X) (hab : a ≠ b) (hcd : c ≠ d)
    (h : s(a, b) = s(c, d)) (i : Fin k) :
    pathCoverTwoEdgePath a b hab i =
      pathCoverTwoEdgePath c d hcd i := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · subst c
    subst d
    rfl
  · subst d
    subst c
    exact pathCoverTwoEdgePath_swap a b hab i

lemma pathCoverTwoEdgePath_adj_iff
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b : X) (hab : a ≠ b) (i : Fin k)
    (u v : PathCoverVertex X k) :
    (pathCoverTwoEdgePath a b hab i).Adj u v ↔
      (u = .root a ∧ v = pathCoverMiddleBetween a b hab i) ∨
      (v = .root a ∧ u = pathCoverMiddleBetween a b hab i) ∨
      (u = .root b ∧ v = pathCoverMiddleBetween a b hab i) ∨
      (v = .root b ∧ u = pathCoverMiddleBetween a b hab i) := by
  simp only [pathCoverTwoEdgePath, SimpleGraph.sup_adj,
    SimpleGraph.edge_adj]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))
  · intro h
    rcases h with h | h | h | h
    · refine Or.inl ⟨Or.inl h, ?_⟩
      rcases h with ⟨rfl, rfl⟩
      simp [pathCoverMiddleBetween]
    · refine Or.inl ⟨Or.inr ⟨h.2, h.1⟩, ?_⟩
      rcases h with ⟨rfl, rfl⟩
      simp [pathCoverMiddleBetween]
    · refine Or.inr ⟨Or.inl h, ?_⟩
      rcases h with ⟨rfl, rfl⟩
      simp [pathCoverMiddleBetween]
    · refine Or.inr ⟨Or.inr ⟨h.2, h.1⟩, ?_⟩
      rcases h with ⟨rfl, rfl⟩
      simp [pathCoverMiddleBetween]

/-! ## Endpoint triangles -/

/-- The triangle consisting of an old edge and one private two-edge path
between its endpoints. -/
def pathTriangleEmbedding
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b : X) (hab : a ≠ b) (i : Fin k) :
    Fin 3 ↪ PathCoverVertex X k where
  toFun := ![.root a, pathCoverMiddleBetween a b hab i, .root b]
  inj' := by
    intro x y hxy
    have hba : b ≠ a := hab.symm
    fin_cases x <;> fin_cases y <;>
      simp_all [pathCoverMiddleBetween]

@[simp] lemma pathTriangleEmbedding_zero
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b : X) (hab : a ≠ b) (i : Fin k) :
    pathTriangleEmbedding a b hab i 0 = .root a := rfl

@[simp] lemma pathTriangleEmbedding_one
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b : X) (hab : a ≠ b) (i : Fin k) :
    pathTriangleEmbedding a b hab i 1 =
      pathCoverMiddleBetween a b hab i := rfl

@[simp] lemma pathTriangleEmbedding_two
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b : X) (hab : a ≠ b) (i : Fin k) :
    pathTriangleEmbedding a b hab i 2 = .root b := rfl

lemma pathTriangle_edgeFaithful
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b : X) (hab : a ≠ b) (i : Fin k) :
    EdgeFaithfulMap (SimpleGraph.cycleGraph 3)
      (pathTriangleEmbedding a b hab i) :=
  edgeFaithfulMap_of_injective (pathTriangleEmbedding a b hab i).injective

lemma cycleGraph_three_adj_iff (x y : Fin 3) :
    (SimpleGraph.cycleGraph 3).Adj x y ↔
      (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨
      (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨
      (x = 2 ∧ y = 0) ∨ (x = 0 ∧ y = 2) := by
  decide +revert

lemma pathTriangle_map_adj_iff
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b : X) (hab : a ≠ b) (i : Fin k)
    (u v : PathCoverVertex X k) :
    ((SimpleGraph.cycleGraph 3).map
      (pathTriangleEmbedding a b hab i)).Adj u v ↔
      (u = .root a ∧ v = pathCoverMiddleBetween a b hab i) ∨
      (v = .root a ∧ u = pathCoverMiddleBetween a b hab i) ∨
      (u = .root b ∧ v = pathCoverMiddleBetween a b hab i) ∨
      (v = .root b ∧ u = pathCoverMiddleBetween a b hab i) ∨
      (u = .root a ∧ v = .root b) ∨
      (u = .root b ∧ v = .root a) := by
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨x, y, hxy, rfl, rfl⟩
    rw [cycleGraph_three_adj_iff] at hxy
    rcases hxy with h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals simp
  · intro huv
    rcases huv with h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl⟩
    · exact ⟨0, 1, (cycleGraph_three_adj_iff 0 1).mpr (by simp), rfl, rfl⟩
    · exact ⟨1, 0, (cycleGraph_three_adj_iff 1 0).mpr (by simp), rfl, rfl⟩
    · exact ⟨2, 1, (cycleGraph_three_adj_iff 2 1).mpr (by simp), rfl, rfl⟩
    · exact ⟨1, 2, (cycleGraph_three_adj_iff 1 2).mpr (by simp), rfl, rfl⟩
    · exact ⟨0, 2, (cycleGraph_three_adj_iff 0 2).mpr (by simp), rfl, rfl⟩
    · exact ⟨2, 0, (cycleGraph_three_adj_iff 2 0).mpr (by simp), rfl, rfl⟩

lemma pathTriangle_map_le
    {X : Type*} [DecidableEq X] {k : ℕ}
    (G : SimpleGraph X) (a b : X) (hab : a ≠ b) (i : Fin k)
    (habG : G.Adj a b) :
    (SimpleGraph.cycleGraph 3).map (pathTriangleEmbedding a b hab i) ≤
      pathCoverGraph X k ⊔
        G.map (pathCoverRootEmbedding (X := X) (k := k)) := by
  rw [SimpleGraph.map_le_iff_le_comap]
  intro x y hxy
  rw [cycleGraph_three_adj_iff] at hxy
  rcases hxy with h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inl (pathCoverGraph_adj_left_middleBetween a b hab i)
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inl (pathCoverGraph_adj_left_middleBetween a b hab i).symm
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inl (pathCoverGraph_adj_right_middleBetween a b hab i).symm
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inl (pathCoverGraph_adj_right_middleBetween a b hab i)
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inr (SimpleGraph.map_adj_apply.mpr habG.symm)
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inr (SimpleGraph.map_adj_apply.mpr habG)

def pathTriangleMiddles
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b : X) (hab : a ≠ b) (i : Fin k) :
    Finset (PathCoverVertex X k) :=
  {pathCoverMiddleBetween a b hab i}

lemma pathCoverMiddleBetween_ne_of_slot_ne
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c d : X) (hab : a ≠ b) (hcd : c ≠ d)
    {i j : Fin k} (hij : i ≠ j) :
    pathCoverMiddleBetween a b hab i ≠
      pathCoverMiddleBetween c d hcd j := by
  intro h
  have hs := congrArg (fun v : PathCoverVertex X k ↦
    match v with
    | .root _ => none
    | .middle _ s => some s) h
  simp only [pathCoverMiddleBetween] at hs
  exact hij (Option.some.inj hs)

lemma pathCoverMiddleBetween_ne_of_edge_ne
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c d : X) (hab : a ≠ b) (hcd : c ≠ d)
    (i j : Fin k) (hedge : pathCoverEdge a b hab ≠ pathCoverEdge c d hcd) :
    pathCoverMiddleBetween a b hab i ≠
      pathCoverMiddleBetween c d hcd j := by
  intro h
  have he := congrArg (fun v : PathCoverVertex X k ↦
    match v with
    | .root _ => none
    | .middle e _ => some e) h
  simp only [pathCoverMiddleBetween] at he
  exact hedge (Option.some.inj he)

lemma pathCoverEdge_ne_of_sym2_ne
    {X : Type*} [DecidableEq X]
    (a b c d : X) (hab : a ≠ b) (hcd : c ≠ d)
    (h : s(a, b) ≠ s(c, d)) :
    pathCoverEdge a b hab ≠ pathCoverEdge c d hcd := by
  intro heq
  apply h
  exact congrArg Subtype.val heq

lemma pathTriangleMiddles_disjoint_of_ne
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c d : X) (hab : a ≠ b) (hcd : c ≠ d) (i j : Fin k)
    (h : pathCoverMiddleBetween a b hab i ≠
      pathCoverMiddleBetween c d hcd j) :
    Disjoint (pathTriangleMiddles a b hab i)
      (pathTriangleMiddles c d hcd j) := by
  rw [Finset.disjoint_left]
  simpa [pathTriangleMiddles] using h

def pathTriangleRoots
    {X : Type*} [DecidableEq X] {k : ℕ} (a b : X) :
    Finset (PathCoverVertex X k) :=
  {.root a, .root b}

def pathCoverRootEdgeGraph
    {X : Type*} [DecidableEq X] {k : ℕ} (a b : X) :
    SimpleGraph (PathCoverVertex X k) :=
  SimpleGraph.edge (.root a) (.root b)

lemma pathCoverRootEdgeGraph_disjoint_of_edge_ne
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c d : X) (hedge : s(a, b) ≠ s(c, d)) :
    Disjoint (pathCoverRootEdgeGraph (k := k) a b)
      (pathCoverRootEdgeGraph (k := k) c d) := by
  rw [SimpleGraph.disjoint_left]
  intro u v huv hw
  simp only [pathCoverRootEdgeGraph, SimpleGraph.edge_adj] at huv hw
  rcases huv.1 with huv | huv <;> rcases hw.1 with hw | hw
  all_goals
    apply hedge
    rw [Sym2.eq_iff]
    simp_all

lemma pathTriangle_map_adj_iff_mem
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b : X) (hab : a ≠ b) (i : Fin k)
    (u v : PathCoverVertex X k) :
    ((SimpleGraph.cycleGraph 3).map
      (pathTriangleEmbedding a b hab i)).Adj u v ↔
      (u ∈ pathTriangleRoots (k := k) a b ∧
        v ∈ pathTriangleMiddles a b hab i) ∨
      (v ∈ pathTriangleRoots (k := k) a b ∧
        u ∈ pathTriangleMiddles a b hab i) ∨
      (pathCoverRootEdgeGraph (k := k) a b).Adj u v := by
  rw [pathTriangle_map_adj_iff]
  simp only [pathTriangleRoots, pathTriangleMiddles, mem_insert,
    mem_singleton, pathCoverRootEdgeGraph, SimpleGraph.edge_adj]
  constructor <;> aesop

lemma pathTriangle_map_eq
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b : X) (hab : a ≠ b) (i : Fin k) :
    (SimpleGraph.cycleGraph 3).map (pathTriangleEmbedding a b hab i) =
      pathCoverTwoEdgePath a b hab i ⊔
        pathCoverRootEdgeGraph (k := k) a b := by
  ext u v
  rw [pathTriangle_map_adj_iff, SimpleGraph.sup_adj,
    pathCoverTwoEdgePath_adj_iff]
  simp only [pathCoverRootEdgeGraph, SimpleGraph.edge_adj]
  constructor <;> aesop

lemma pairedPathC4Middles_disjoint_pathTriangleMiddles_of_slot_ne
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y a b : X) (hxy : x ≠ y) (hab : a ≠ b)
    (i j r : Fin k) (hri : r ≠ i) (hrj : r ≠ j) :
    Disjoint (pairedPathC4Middles x y hxy i j)
      (pathTriangleMiddles a b hab r) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  simp only [pathTriangleMiddles, mem_singleton] at hz'
  subst z
  simp only [pairedPathC4Middles, mem_insert, mem_singleton] at hz
  rcases hz with hz | hz
  · have := congrArg (fun v : PathCoverVertex X k ↦
        match v with
        | .root _ => none
        | .middle _ s => some s) hz
    simp only [pathCoverMiddleBetween] at this
    exact hri (Option.some.inj this)
  · have := congrArg (fun v : PathCoverVertex X k ↦
        match v with
        | .root _ => none
        | .middle _ s => some s) hz
    simp only [pathCoverMiddleBetween] at this
    exact hrj (Option.some.inj this)

lemma pairedPathC4Middles_disjoint_of_ne
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y a b : X) (hxy : x ≠ y) (hab : a ≠ b)
    (i j r s : Fin k)
    (h₁₁ : pathCoverMiddleBetween x y hxy i ≠
      pathCoverMiddleBetween a b hab r)
    (h₁₂ : pathCoverMiddleBetween x y hxy i ≠
      pathCoverMiddleBetween a b hab s)
    (h₂₁ : pathCoverMiddleBetween x y hxy j ≠
      pathCoverMiddleBetween a b hab r)
    (h₂₂ : pathCoverMiddleBetween x y hxy j ≠
      pathCoverMiddleBetween a b hab s) :
    Disjoint (pairedPathC4Middles x y hxy i j)
      (pairedPathC4Middles a b hab r s) := by
  rw [Finset.disjoint_left]
  simp only [pairedPathC4Middles, mem_insert, mem_singleton]
  intro z hz hz'
  rcases hz with rfl | rfl <;> rcases hz' with h | h
  · exact h₁₁ h
  · exact h₁₂ h
  · exact h₂₁ h
  · exact h₂₂ h

lemma pairedPathC4Middles_disjoint_pathTriangleMiddles_of_ne
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y a b : X) (hxy : x ≠ y) (hab : a ≠ b)
    (i j r : Fin k)
    (h₁ : pathCoverMiddleBetween x y hxy i ≠
      pathCoverMiddleBetween a b hab r)
    (h₂ : pathCoverMiddleBetween x y hxy j ≠
      pathCoverMiddleBetween a b hab r) :
    Disjoint (pairedPathC4Middles x y hxy i j)
      (pathTriangleMiddles a b hab r) := by
  rw [Finset.disjoint_left]
  simp only [pairedPathC4Middles, pathTriangleMiddles,
    mem_insert, mem_singleton]
  intro z hz hz'
  subst z
  exact hz.elim h₁.symm h₂.symm

lemma pairedPathC4_disjoint_pathTriangle_of_middles_disjoint
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y a b : X) (hxy : x ≠ y) (hab : a ≠ b)
    (i j : Fin k) (hij : i ≠ j) (r : Fin k)
    (hmiddle : Disjoint (pairedPathC4Middles x y hxy i j)
      (pathTriangleMiddles a b hab r)) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map
        (pairedPathC4Embedding x y hxy i j hij))
      ((SimpleGraph.cycleGraph 3).map
        (pathTriangleEmbedding a b hab r)) := by
  rw [SimpleGraph.disjoint_left]
  intro u v huv4 huv3
  rw [pairedPathC4_map_adj_iff_mem] at huv4
  rw [SimpleGraph.map_adj] at huv3
  obtain ⟨s, t, hst, rfl, rfl⟩ := huv3
  rw [cycleGraph_three_adj_iff] at hst
  have hnot : pathCoverMiddleBetween a b hab r ∉
      pairedPathC4Middles x y hxy i j := by
    intro hmem
    exact Finset.disjoint_left.mp hmiddle hmem (by
      simp [pathTriangleMiddles])
  rcases hst with h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩
  all_goals rcases huv4 with huv4 | huv4
  all_goals
    first
    | exact hnot huv4.2
    | simpa [pairedPathC4Roots, pairedPathC4Middles,
        pathCoverMiddleBetween] using huv4.1
    | simpa [pairedPathC4Roots, pairedPathC4Middles,
        pathCoverMiddleBetween] using huv4.2

/-- Cyclic ordering `a -- m_ab -- b -- c -- m_ac -- a`. -/
def augmentedEdgeC5Embedding
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j : Fin k) : Fin 5 ↪ PathCoverVertex X k where
  toFun := ![.root a, pathCoverMiddleBetween a b hab i, .root b,
    .root c, pathCoverMiddleBetween a c hac j]
  inj' := by
    intro x y hxy
    have hba : b ≠ a := hab.symm
    have hca : c ≠ a := hac.symm
    fin_cases x <;> fin_cases y <;>
      simp_all [pathCoverMiddleBetween, pathCoverEdge]

@[simp] lemma augmentedEdgeC5Embedding_zero
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j : Fin k) :
    augmentedEdgeC5Embedding a b c hab hac hbc i j 0 = .root a := rfl

@[simp] lemma augmentedEdgeC5Embedding_one
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j : Fin k) :
    augmentedEdgeC5Embedding a b c hab hac hbc i j 1 =
      pathCoverMiddleBetween a b hab i := rfl

@[simp] lemma augmentedEdgeC5Embedding_two
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j : Fin k) :
    augmentedEdgeC5Embedding a b c hab hac hbc i j 2 = .root b := rfl

@[simp] lemma augmentedEdgeC5Embedding_three
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j : Fin k) :
    augmentedEdgeC5Embedding a b c hab hac hbc i j 3 = .root c := rfl

@[simp] lemma augmentedEdgeC5Embedding_four
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j : Fin k) :
    augmentedEdgeC5Embedding a b c hab hac hbc i j 4 =
      pathCoverMiddleBetween a c hac j := rfl

lemma cycleGraph_five_adj_iff (x y : Fin 5) :
    (SimpleGraph.cycleGraph 5).Adj x y ↔
      (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨
      (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨
      (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) ∨
      (x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 3) ∨
      (x = 4 ∧ y = 0) ∨ (x = 0 ∧ y = 4) := by
  decide +revert

lemma augmentedEdgeC5_map_adj_iff
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j : Fin k) (u v : PathCoverVertex X k) :
    ((SimpleGraph.cycleGraph 5).map
      (augmentedEdgeC5Embedding a b c hab hac hbc i j)).Adj u v ↔
      (u = .root a ∧ v = pathCoverMiddleBetween a b hab i) ∨
      (v = .root a ∧ u = pathCoverMiddleBetween a b hab i) ∨
      (u = .root b ∧ v = pathCoverMiddleBetween a b hab i) ∨
      (v = .root b ∧ u = pathCoverMiddleBetween a b hab i) ∨
      (u = .root b ∧ v = .root c) ∨
      (u = .root c ∧ v = .root b) ∨
      (u = .root c ∧ v = pathCoverMiddleBetween a c hac j) ∨
      (v = .root c ∧ u = pathCoverMiddleBetween a c hac j) ∨
      (u = .root a ∧ v = pathCoverMiddleBetween a c hac j) ∨
      (v = .root a ∧ u = pathCoverMiddleBetween a c hac j) := by
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨x, y, hxy, rfl, rfl⟩
    rw [cycleGraph_five_adj_iff] at hxy
    rcases hxy with h | h | h | h | h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals simp
  · intro huv
    rcases huv with h | h | h | h | h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl⟩
    · exact ⟨0, 1, (cycleGraph_five_adj_iff 0 1).mpr (by simp), rfl, rfl⟩
    · exact ⟨1, 0, (cycleGraph_five_adj_iff 1 0).mpr (by simp), rfl, rfl⟩
    · exact ⟨2, 1, (cycleGraph_five_adj_iff 2 1).mpr (by simp), rfl, rfl⟩
    · exact ⟨1, 2, (cycleGraph_five_adj_iff 1 2).mpr (by simp), rfl, rfl⟩
    · exact ⟨2, 3, (cycleGraph_five_adj_iff 2 3).mpr (by simp), rfl, rfl⟩
    · exact ⟨3, 2, (cycleGraph_five_adj_iff 3 2).mpr (by simp), rfl, rfl⟩
    · exact ⟨3, 4, (cycleGraph_five_adj_iff 3 4).mpr (by simp), rfl, rfl⟩
    · exact ⟨4, 3, (cycleGraph_five_adj_iff 4 3).mpr (by simp), rfl, rfl⟩
    · exact ⟨0, 4, (cycleGraph_five_adj_iff 0 4).mpr (by simp), rfl, rfl⟩
    · exact ⟨4, 0, (cycleGraph_five_adj_iff 4 0).mpr (by simp), rfl, rfl⟩

/-- The five-cycle realization is edge-faithful. -/
lemma augmentedEdgeC5_edgeFaithful
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j : Fin k) :
    EdgeFaithfulMap (SimpleGraph.cycleGraph 5)
      (augmentedEdgeC5Embedding a b c hab hac hbc i j) :=
  edgeFaithfulMap_of_injective
    (augmentedEdgeC5Embedding a b c hab hac hbc i j).injective

def augmentedEdgeC5Middles
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c)
    (i j : Fin k) : Finset (PathCoverVertex X k) :=
  {pathCoverMiddleBetween a b hab i,
    pathCoverMiddleBetween a c hac j}

lemma pathTriangleMiddles_disjoint_augmentedEdgeC5Middles_of_ne
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c d e : X) (hab : a ≠ b) (hcd : c ≠ d) (hce : c ≠ e)
    (i r s : Fin k)
    (h₁ : pathCoverMiddleBetween a b hab i ≠
      pathCoverMiddleBetween c d hcd r)
    (h₂ : pathCoverMiddleBetween a b hab i ≠
      pathCoverMiddleBetween c e hce s) :
    Disjoint (pathTriangleMiddles a b hab i)
      (augmentedEdgeC5Middles c d e hcd hce r s) := by
  rw [Finset.disjoint_left]
  simp only [pathTriangleMiddles, augmentedEdgeC5Middles,
    mem_singleton, mem_insert]
  intro z hz hz'
  subst z
  exact hz'.elim h₁ h₂

lemma augmentedEdgeC5Middles_disjoint_of_ne
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c d e f : X)
    (hab : a ≠ b) (hac : a ≠ c) (hde : d ≠ e) (hdf : d ≠ f)
    (i j r s : Fin k)
    (h₁₁ : pathCoverMiddleBetween a b hab i ≠
      pathCoverMiddleBetween d e hde r)
    (h₁₂ : pathCoverMiddleBetween a b hab i ≠
      pathCoverMiddleBetween d f hdf s)
    (h₂₁ : pathCoverMiddleBetween a c hac j ≠
      pathCoverMiddleBetween d e hde r)
    (h₂₂ : pathCoverMiddleBetween a c hac j ≠
      pathCoverMiddleBetween d f hdf s) :
    Disjoint (augmentedEdgeC5Middles a b c hab hac i j)
      (augmentedEdgeC5Middles d e f hde hdf r s) := by
  rw [Finset.disjoint_left]
  simp only [augmentedEdgeC5Middles, mem_insert, mem_singleton]
  intro z hz hz'
  rcases hz with rfl | rfl <;> rcases hz' with h | h
  · exact h₁₁ h
  · exact h₁₂ h
  · exact h₂₁ h
  · exact h₂₂ h

def augmentedEdgeC5Roots
    {X : Type*} [DecidableEq X] {k : ℕ} (a b c : X) :
    Finset (PathCoverVertex X k) :=
  {.root a, .root b, .root c}

lemma augmentedEdgeC5_map_edge_structure
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j : Fin k) {u v : PathCoverVertex X k}
    (huv : ((SimpleGraph.cycleGraph 5).map
      (augmentedEdgeC5Embedding a b c hab hac hbc i j)).Adj u v) :
      (u ∈ augmentedEdgeC5Roots (k := k) a b c ∧
        v ∈ augmentedEdgeC5Middles a b c hab hac i j) ∨
      (v ∈ augmentedEdgeC5Roots (k := k) a b c ∧
        u ∈ augmentedEdgeC5Middles a b c hab hac i j) ∨
      (pathCoverRootEdgeGraph (k := k) b c).Adj u v := by
  rw [augmentedEdgeC5_map_adj_iff] at huv
  simp only [augmentedEdgeC5Roots, augmentedEdgeC5Middles,
    mem_insert, mem_singleton, pathCoverRootEdgeGraph,
    SimpleGraph.edge_adj]
  aesop

lemma augmentedEdgeC5_map_eq
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j : Fin k) :
    (SimpleGraph.cycleGraph 5).map
        (augmentedEdgeC5Embedding a b c hab hac hbc i j) =
      (pathCoverTwoEdgePath a b hab i ⊔
        pathCoverRootEdgeGraph (k := k) b c) ⊔
        pathCoverTwoEdgePath a c hac j := by
  ext u v
  rw [augmentedEdgeC5_map_adj_iff, SimpleGraph.sup_adj,
    SimpleGraph.sup_adj, pathCoverTwoEdgePath_adj_iff,
    pathCoverTwoEdgePath_adj_iff]
  simp only [pathCoverRootEdgeGraph, SimpleGraph.edge_adj]
  constructor <;> aesop

lemma pairedPathC4_map_eq
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b : X) (hab : a ≠ b) (i j : Fin k) (hij : i ≠ j) :
    (SimpleGraph.cycleGraph 4).map
        (pairedPathC4Embedding a b hab i j hij) =
      pathCoverTwoEdgePath a b hab i ⊔
        pathCoverTwoEdgePath a b hab j := by
  ext u v
  rw [pairedPathC4_map_adj_iff, SimpleGraph.sup_adj,
    pathCoverTwoEdgePath_adj_iff, pathCoverTwoEdgePath_adj_iff]
  constructor <;> aesop

lemma pathTriangle_disjoint_pathTriangle_of_parts_disjoint
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c d : X) (hab : a ≠ b) (hcd : c ≠ d)
    (i j : Fin k)
    (hmiddle : Disjoint (pathTriangleMiddles a b hab i)
      (pathTriangleMiddles c d hcd j))
    (hroot : Disjoint (pathCoverRootEdgeGraph (k := k) a b)
      (pathCoverRootEdgeGraph (k := k) c d)) :
    Disjoint
      ((SimpleGraph.cycleGraph 3).map (pathTriangleEmbedding a b hab i))
      ((SimpleGraph.cycleGraph 3).map (pathTriangleEmbedding c d hcd j)) := by
  rw [SimpleGraph.disjoint_left]
  intro u v huv hw
  rw [pathTriangle_map_adj_iff_mem] at huv hw
  rcases huv with huv | huv | huv <;> rcases hw with hw | hw | hw
  all_goals
    first
    | exact Finset.disjoint_left.mp hmiddle huv.2 hw.2
    | exact SimpleGraph.disjoint_left.mp hroot u v huv hw
    | (simp_all [pathTriangleRoots, pathTriangleMiddles,
        pathCoverRootEdgeGraph, SimpleGraph.edge_adj,
        pathCoverMiddleBetween] <;> aesop)

lemma pathTriangle_disjoint_augmentedEdgeC5_of_parts_disjoint
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c d e : X) (hab : a ≠ b)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (i r s : Fin k)
    (hmiddle : Disjoint (pathTriangleMiddles a b hab i)
      (augmentedEdgeC5Middles c d e hcd hce r s))
    (hroot : Disjoint (pathCoverRootEdgeGraph (k := k) a b)
      (pathCoverRootEdgeGraph (k := k) d e)) :
    Disjoint
      ((SimpleGraph.cycleGraph 3).map (pathTriangleEmbedding a b hab i))
      ((SimpleGraph.cycleGraph 5).map
        (augmentedEdgeC5Embedding c d e hcd hce hde r s)) := by
  rw [SimpleGraph.disjoint_left]
  intro u v huv hw
  rw [pathTriangle_map_adj_iff_mem] at huv
  have hw' := augmentedEdgeC5_map_edge_structure c d e hcd hce hde r s hw
  rcases huv with huv | huv | huv <;> rcases hw' with hw | hw | hw
  all_goals
    first
    | exact Finset.disjoint_left.mp hmiddle huv.2 hw.2
    | exact SimpleGraph.disjoint_left.mp hroot u v huv hw
    | (simp_all [pathTriangleRoots, pathTriangleMiddles,
        augmentedEdgeC5Roots, augmentedEdgeC5Middles,
        pathCoverRootEdgeGraph, SimpleGraph.edge_adj,
        pathCoverMiddleBetween] <;> aesop)

lemma augmentedEdgeC5_disjoint_augmentedEdgeC5_of_parts_disjoint
    {X : Type*} [DecidableEq X] {k : ℕ}
    (a b c d e f : X)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (i j r s : Fin k)
    (hmiddle : Disjoint (augmentedEdgeC5Middles a b c hab hac i j)
      (augmentedEdgeC5Middles d e f hde hdf r s))
    (hroot : Disjoint (pathCoverRootEdgeGraph (k := k) b c)
      (pathCoverRootEdgeGraph (k := k) e f)) :
    Disjoint
      ((SimpleGraph.cycleGraph 5).map
        (augmentedEdgeC5Embedding a b c hab hac hbc i j))
      ((SimpleGraph.cycleGraph 5).map
        (augmentedEdgeC5Embedding d e f hde hdf hef r s)) := by
  rw [SimpleGraph.disjoint_left]
  intro u v huv hw
  have huv' := augmentedEdgeC5_map_edge_structure a b c hab hac hbc i j huv
  have hw' := augmentedEdgeC5_map_edge_structure d e f hde hdf hef r s hw
  rcases huv' with huv | huv | huv <;> rcases hw' with hw | hw | hw
  all_goals
    first
    | exact Finset.disjoint_left.mp hmiddle huv.2 hw.2
    | exact SimpleGraph.disjoint_left.mp hroot u v huv hw
    | (simp_all [augmentedEdgeC5Roots, augmentedEdgeC5Middles,
        pathCoverRootEdgeGraph, SimpleGraph.edge_adj,
        pathCoverMiddleBetween] <;> aesop)

lemma pairedPathC4Middles_disjoint_augmentedEdgeC5Middles_of_slot_ne
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y a b c : X) (hxy : x ≠ y) (hab : a ≠ b) (hac : a ≠ c)
    (i j r s : Fin k)
    (hri : r ≠ i) (hrj : r ≠ j) (hsi : s ≠ i) (hsj : s ≠ j) :
    Disjoint (pairedPathC4Middles x y hxy i j)
      (augmentedEdgeC5Middles a b c hab hac r s) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  simp only [augmentedEdgeC5Middles, mem_insert, mem_singleton] at hz'
  rcases hz' with rfl | rfl
  · simp only [pairedPathC4Middles, mem_insert, mem_singleton] at hz
    rcases hz with hz | hz
    · have := congrArg (fun v : PathCoverVertex X k ↦
          match v with
          | .root _ => none
          | .middle _ t => some t) hz
      simp only [pathCoverMiddleBetween] at this
      exact hri (Option.some.inj this)
    · have := congrArg (fun v : PathCoverVertex X k ↦
          match v with
          | .root _ => none
          | .middle _ t => some t) hz
      simp only [pathCoverMiddleBetween] at this
      exact hrj (Option.some.inj this)
  · simp only [pairedPathC4Middles, mem_insert, mem_singleton] at hz
    rcases hz with hz | hz
    · have := congrArg (fun v : PathCoverVertex X k ↦
          match v with
          | .root _ => none
          | .middle _ t => some t) hz
      simp only [pathCoverMiddleBetween] at this
      exact hsi (Option.some.inj this)
    · have := congrArg (fun v : PathCoverVertex X k ↦
          match v with
          | .root _ => none
          | .middle _ t => some t) hz
      simp only [pathCoverMiddleBetween] at this
      exact hsj (Option.some.inj this)

lemma pairedPathC4Middles_disjoint_augmentedEdgeC5Middles_of_ne
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y a b c : X) (hxy : x ≠ y) (hab : a ≠ b) (hac : a ≠ c)
    (i j r s : Fin k)
    (h₁₁ : pathCoverMiddleBetween x y hxy i ≠
      pathCoverMiddleBetween a b hab r)
    (h₁₂ : pathCoverMiddleBetween x y hxy i ≠
      pathCoverMiddleBetween a c hac s)
    (h₂₁ : pathCoverMiddleBetween x y hxy j ≠
      pathCoverMiddleBetween a b hab r)
    (h₂₂ : pathCoverMiddleBetween x y hxy j ≠
      pathCoverMiddleBetween a c hac s) :
    Disjoint (pairedPathC4Middles x y hxy i j)
      (augmentedEdgeC5Middles a b c hab hac r s) := by
  rw [Finset.disjoint_left]
  simp only [pairedPathC4Middles, augmentedEdgeC5Middles,
    mem_insert, mem_singleton]
  intro z hz hz'
  rcases hz with rfl | rfl <;> rcases hz' with h | h
  · exact h₁₁ h
  · exact h₁₂ h
  · exact h₂₁ h
  · exact h₂₂ h

lemma pairedPathC4_disjoint_augmentedEdgeC5_of_middles_disjoint
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y a b c : X) (hxy : x ≠ y)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j : Fin k) (hij : i ≠ j) (r s : Fin k)
    (hmiddle : Disjoint (pairedPathC4Middles x y hxy i j)
      (augmentedEdgeC5Middles a b c hab hac r s)) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map
        (pairedPathC4Embedding x y hxy i j hij))
      ((SimpleGraph.cycleGraph 5).map
        (augmentedEdgeC5Embedding a b c hab hac hbc r s)) := by
  rw [SimpleGraph.disjoint_left]
  intro u v huv4 huv5
  rw [pairedPathC4_map_adj_iff_mem] at huv4
  rw [SimpleGraph.map_adj] at huv5
  obtain ⟨t, w, htw, rfl, rfl⟩ := huv5
  rw [cycleGraph_five_adj_iff] at htw
  have hnotLeft : pathCoverMiddleBetween a b hab r ∉
      pairedPathC4Middles x y hxy i j := by
    intro hmem
    exact Finset.disjoint_left.mp hmiddle hmem (by
      simp [augmentedEdgeC5Middles])
  have hnotRight : pathCoverMiddleBetween a c hac s ∉
      pairedPathC4Middles x y hxy i j := by
    intro hmem
    exact Finset.disjoint_left.mp hmiddle hmem (by
      simp [augmentedEdgeC5Middles])
  rcases htw with h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩
  all_goals rcases huv4 with huv4 | huv4
  all_goals
    first
    | exact hnotLeft huv4.2
    | exact hnotRight huv4.2
    | simpa [pairedPathC4Roots, pairedPathC4Middles,
        pathCoverMiddleBetween] using huv4.1
    | simpa [pairedPathC4Roots, pairedPathC4Middles,
        pathCoverMiddleBetween] using huv4.2

/-- Every edge of the realized five-cycle is either a path-cover edge or the
single old edge `bc`. -/
lemma augmentedEdgeC5_map_le
    {X : Type*} [DecidableEq X] {k : ℕ}
    (G : SimpleGraph X)
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j : Fin k) (hbcG : G.Adj b c) :
    (SimpleGraph.cycleGraph 5).map
        (augmentedEdgeC5Embedding a b c hab hac hbc i j) ≤
      pathCoverGraph X k ⊔
        G.map (pathCoverRootEmbedding (X := X) (k := k)) := by
  rw [SimpleGraph.map_le_iff_le_comap]
  intro x y hxy
  rw [cycleGraph_five_adj_iff] at hxy
  rcases hxy with h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inl (pathCoverGraph_adj_left_middleBetween a b hab i)
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inl (pathCoverGraph_adj_left_middleBetween a b hab i).symm
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inl (pathCoverGraph_adj_right_middleBetween a b hab i).symm
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inl (pathCoverGraph_adj_right_middleBetween a b hab i)
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inr (SimpleGraph.map_adj_apply.mpr hbcG)
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inr (SimpleGraph.map_adj_apply.mpr hbcG.symm)
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inl (pathCoverGraph_adj_right_middleBetween a c hac j)
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inl (pathCoverGraph_adj_right_middleBetween a c hac j).symm
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inl (pathCoverGraph_adj_left_middleBetween a c hac j).symm
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inl (pathCoverGraph_adj_left_middleBetween a c hac j)

/-! ## Combining a four-cycle and a five-cycle -/

def c4InC4C5 : Fin 4 ↪ Fin 9 where
  toFun i := ⟨i.1, by omega⟩
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun z : Fin 9 => z.val) h)

def c5InC4C5 : Fin 5 ↪ Fin 9 where
  toFun i := ⟨i.1 + 4, by omega⟩
  inj' := by
    intro i j h
    exact Fin.ext (by
      simpa using congrArg (fun z : Fin 9 => z.val) h)

def c4C5FirstComponent : SimpleGraph (Fin 9) :=
  (SimpleGraph.cycleGraph 4).map c4InC4C5

def c4C5SecondComponent : SimpleGraph (Fin 9) :=
  (SimpleGraph.cycleGraph 5).map c5InC4C5

instance : DecidableRel c4C5FirstComponent.Adj := by
  unfold c4C5FirstComponent
  infer_instance

instance : DecidableRel c4C5SecondComponent.Adj := by
  unfold c4C5SecondComponent
  infer_instance

lemma c4c5TemplateGraph_eq_components :
    c4c5TemplateGraph = c4C5FirstComponent ⊔ c4C5SecondComponent := by
  ext x y
  fin_cases x <;> fin_cases y <;> decide

def combineC4C5Maps {Y : Type*} (f₄ : Fin 4 → Y) (f₅ : Fin 5 → Y) :
    Fin 9 → Y :=
  ![f₄ 0, f₄ 1, f₄ 2, f₄ 3,
    f₅ 0, f₅ 1, f₅ 2, f₅ 3, f₅ 4]

@[simp] lemma combineC4C5Maps_c4 {Y : Type*}
    (f₄ : Fin 4 → Y) (f₅ : Fin 5 → Y) (i : Fin 4) :
    combineC4C5Maps f₄ f₅ (c4InC4C5 i) = f₄ i := by
  fin_cases i <;> rfl

@[simp] lemma combineC4C5Maps_c5 {Y : Type*}
    (f₄ : Fin 4 → Y) (f₅ : Fin 5 → Y) (i : Fin 5) :
    combineC4C5Maps f₄ f₅ (c5InC4C5 i) = f₅ i := by
  fin_cases i <;> rfl

lemma map_c4C5FirstComponent_combine {Y : Type*}
    (f₄ : Fin 4 → Y) (f₅ : Fin 5 → Y) :
    c4C5FirstComponent.map (combineC4C5Maps f₄ f₅) =
      (SimpleGraph.cycleGraph 4).map f₄ := by
  rw [c4C5FirstComponent, SimpleGraph.map_map]
  congr 1
  funext i
  exact combineC4C5Maps_c4 f₄ f₅ i

lemma map_c4C5SecondComponent_combine {Y : Type*}
    (f₄ : Fin 4 → Y) (f₅ : Fin 5 → Y) :
    c4C5SecondComponent.map (combineC4C5Maps f₄ f₅) =
      (SimpleGraph.cycleGraph 5).map f₅ := by
  rw [c4C5SecondComponent, SimpleGraph.map_map]
  congr 1
  funext i
  exact combineC4C5Maps_c5 f₄ f₅ i

/-- Edge-disjoint realized `C4` and `C5` components give exactly one allowed
quotient root for the full KSSS cycle-cover bank. -/
lemma combineC4C5Maps_edgeFaithful
    {Y : Type*} (f₄ : Fin 4 → Y) (f₅ : Fin 5 → Y)
    (hf₄ : EdgeFaithfulMap (SimpleGraph.cycleGraph 4) f₄)
    (hf₅ : EdgeFaithfulMap (SimpleGraph.cycleGraph 5) f₅)
    (hdisjoint : Disjoint ((SimpleGraph.cycleGraph 4).map f₄)
      ((SimpleGraph.cycleGraph 5).map f₅)) :
    EdgeFaithfulMap c4c5TemplateGraph (combineC4C5Maps f₄ f₅) := by
  rw [c4c5TemplateGraph_eq_components]
  apply edgeFaithfulMap_sup
  · exact edgeFaithfulMap_map_embedding (SimpleGraph.cycleGraph 4)
      c4InC4C5 _ f₄ (combineC4C5Maps_c4 f₄ f₅) hf₄
  · exact edgeFaithfulMap_map_embedding (SimpleGraph.cycleGraph 5)
      c5InC4C5 _ f₅ (combineC4C5Maps_c5 f₄ f₅) hf₅
  · rw [map_c4C5FirstComponent_combine,
      map_c4C5SecondComponent_combine]
    exact hdisjoint

def c4c5QuotientMapOfEmbedded
    {Y : Type*} (f₄ : Fin 4 → Y) (f₅ : Fin 5 → Y)
    (hf₄ : EdgeFaithfulMap (SimpleGraph.cycleGraph 4) f₄)
    (hf₅ : EdgeFaithfulMap (SimpleGraph.cycleGraph 5) f₅)
    (hdisjoint : Disjoint ((SimpleGraph.cycleGraph 4).map f₄)
      ((SimpleGraph.cycleGraph 5).map f₅)) : C4C5QuotientMap Y :=
  ⟨combineC4C5Maps f₄ f₅,
    combineC4C5Maps_edgeFaithful f₄ f₅ hf₄ hf₅ hdisjoint⟩

end

end Erdos207
