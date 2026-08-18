/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.PathRamsey
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # A square-root coloring bound in terms of the number of edges -/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- The minimum degree of a nonempty finite graph is at most the square root
of twice any upper bound for its number of edges. -/
theorem minDegree_le_sqrt_twice_edge_bound
    {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {m : ℕ} (hm : G.edgeFinset.card ≤ m) :
    G.minDegree ≤ Nat.sqrt (2 * m) := by
  apply Nat.le_sqrt.mpr
  calc
    G.minDegree * G.minDegree ≤ Fintype.card V * G.minDegree :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt G.minDegree_lt_card)
    _ = ∑ _v : V, G.minDegree := by simp
    _ ≤ ∑ v : V, G.degree v := by
      exact Finset.sum_le_sum fun _ _ ↦ G.minDegree_le_degree _
    _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
    _ ≤ 2 * m := Nat.mul_le_mul_left 2 hm

/-- An induced subgraph has no more edges than the ambient finite graph. -/
theorem card_edgeFinset_induce_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)] [DecidableEq V] :
    (G.induce s).edgeFinset.card ≤ G.edgeFinset.card := by
  have hmap := congrArg Finset.card (G.map_edgeFinset_induce (s := s))
  rw [Finset.card_map] at hmap
  rw [hmap]
  exact Finset.card_le_card Finset.inter_subset_left

/-- Every finite graph with at most `m` edges admits a proper coloring with
`sqrt (2m) + 1` colors.  The proof repeatedly removes a minimum-degree
vertex and colors it after the remaining induced graph. -/
theorem colorable_sqrt_twice_edge_bound
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {m : ℕ} (hm : G.edgeFinset.card ≤ m) :
    G.Colorable (Nat.sqrt (2 * m) + 1) := by
  classical
  let q := Nat.sqrt (2 * m)
  cases isEmpty_or_nonempty V with
  | inl hV =>
      letI := hV
      exact SimpleGraph.Colorable.of_isEmpty _
  | inr hV =>
      letI := hV
      obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
      let U : Set V := {v}ᶜ
      let R : SimpleGraph U := G.induce U
      have hRedges : R.edgeFinset.card ≤ m :=
        (card_edgeFinset_induce_le G U).trans hm
      have hcardU : Fintype.card U < Fintype.card V := by
        rw [show Fintype.card U = Fintype.card V - 1 by
          change Fintype.card {x : V // ¬x = v} = Fintype.card V - 1
          rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]]
        exact Nat.sub_lt (Fintype.card_pos_iff.mpr hV) zero_lt_one
      obtain ⟨cR⟩ := colorable_sqrt_twice_edge_bound R hRedges
      have hdeg : G.degree v ≤ q := by
        rw [← hv]
        exact minDegree_le_sqrt_twice_edge_bound G hm
      let neighborColor : G.neighborFinset v → Fin (q + 1) := fun w ↦
        cR ⟨w.1, by
          change w.1 ∈ ({v} : Set V)ᶜ
          rw [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact (G.ne_of_adj ((G.mem_neighborFinset v w.1).mp w.2)).symm⟩
      let used : Finset (Fin (q + 1)) := Finset.univ.image neighborColor
      have husedCard : used.card ≤ q := by
        calc
          used.card ≤ (Finset.univ : Finset (↑(G.neighborFinset v))).card :=
            Finset.card_image_le
          _ = G.degree v := by simp
          _ ≤ q := hdeg
      obtain ⟨free, _hfreeUniv, hfree⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card
          (s := used) (t := (Finset.univ : Finset (Fin (q + 1)))) (by
            simpa using Nat.lt_succ_of_le husedCard)
      let color : V → Fin (q + 1) := fun w ↦
        if hw : w = v then free else cR ⟨w, by
          change w ∈ ({v} : Set V)ᶜ
          simpa [Set.mem_compl_iff, Set.mem_singleton_iff]⟩
      refine ⟨SimpleGraph.Coloring.mk color ?_⟩
      intro x y hxy heq
      by_cases hx : x = v <;> by_cases hy : y = v
      · subst x
        subst y
        exact hxy.ne rfl
      · subst x
        have hyMem : y ∈ G.neighborFinset v := (G.mem_neighborFinset v y).mpr hxy
        have hcolorUsed : cR ⟨y, by
            change y ∈ ({v} : Set V)ᶜ
            simpa [Set.mem_compl_iff, Set.mem_singleton_iff]⟩ ∈ used := by
          refine Finset.mem_image.mpr ⟨⟨y, hyMem⟩, Finset.mem_univ _, ?_⟩
          rfl
        have hfreeEq : free = cR ⟨y, by
            change y ∈ ({v} : Set V)ᶜ
            simpa [Set.mem_compl_iff, Set.mem_singleton_iff]⟩ := by
          simpa [color, hy] using heq
        rw [← hfreeEq] at hcolorUsed
        exact hfree hcolorUsed
      · subst y
        have hxMem : x ∈ G.neighborFinset v := (G.mem_neighborFinset v x).mpr hxy.symm
        have hcolorUsed : cR ⟨x, by
            change x ∈ ({v} : Set V)ᶜ
            simpa [Set.mem_compl_iff, Set.mem_singleton_iff]⟩ ∈ used := by
          refine Finset.mem_image.mpr ⟨⟨x, hxMem⟩, Finset.mem_univ _, ?_⟩
          rfl
        have hfreeEq : free = cR ⟨x, by
            change x ∈ ({v} : Set V)ᶜ
            simpa [Set.mem_compl_iff, Set.mem_singleton_iff]⟩ := by
          simpa [color, hx] using heq.symm
        rw [← hfreeEq] at hcolorUsed
        exact hfree hcolorUsed
      · let xU : U := ⟨x, by
            change x ∈ ({v} : Set V)ᶜ
            simpa [Set.mem_compl_iff, Set.mem_singleton_iff]⟩
        let yU : U := ⟨y, by
            change y ∈ ({v} : Set V)ᶜ
            simpa [Set.mem_compl_iff, Set.mem_singleton_iff]⟩
        exact cR.valid (v := xU) (w := yU) hxy
          (by simpa [color, hx, hy, xU, yU] using heq)
termination_by Fintype.card V
decreasing_by exact hcardU

/-- The path Ramsey estimate in the form used in the odd-cycle proof, with
the color count eliminated in favor of the target edge count. -/
theorem pathGraph_isContained_or_compl_sqrt_edges
    {W V : Type*} [Fintype W] [Fintype V]
    {k m : ℕ} (hk : 2 ≤ k) (H : SimpleGraph W) [DecidableRel H.Adj]
    (hm : H.edgeFinset.card ≤ m) (C : SimpleGraph V)
    (hcard : Fintype.card W + k * Nat.sqrt (2 * m) ≤ Fintype.card V) :
    SimpleGraph.pathGraph k ⊑ C ∨ H ⊑ Cᶜ := by
  obtain ⟨c⟩ := colorable_sqrt_twice_edge_bound H hm
  apply pathGraph_isContained_or_compl_of_coloring hk H c C
  simpa using hcard

/-- Coded exact-order version of the square-root path Ramsey estimate. -/
theorem ramseyAt_path_sqrt_edges {k : ℕ} (hk : 2 ≤ k) (H : GraphCode) :
    RamseyAt (pathCode k) H
      (H.vertexCount + k * Nat.sqrt (2 * H.edgeCount)) := by
  classical
  intro C
  letI : DecidableRel H.graph.Adj := Classical.decRel H.graph.Adj
  simpa [pathCode] using
    (pathGraph_isContained_or_compl_sqrt_edges hk H.graph
      (m := H.edgeCount) (by
        rw [← H.edgeCount_eq_card_edgeFinset]) C (by simp))

theorem graphRamseyNumber_path_le_sqrt_edges {k : ℕ} (hk : 2 ≤ k)
    (H : GraphCode) :
    graphRamseyNumber (pathCode k) H ≤
      H.vertexCount + k * Nat.sqrt (2 * H.edgeCount) :=
  graphRamseyNumber_le_of_ramseyAt (ramseyAt_path_sqrt_edges hk H)

end Erdos570
