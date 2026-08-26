/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.Coloring

/-!
# An edge-count coloring bound

For at least four edges, a graph is `(m / 2 + 1)`-colorable. This elementary
bound suffices for the counting argument of Erdős 569 and avoids a separate
chromatic-critical-subgraph construction.
-/

open scoped SimpleGraph

namespace Erdos569

open Erdos570

/-- A vertex of degree at most half the edge budget exists. -/
theorem minDegree_le_half_edge_bound
    {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {m : ℕ} (hm4 : 4 ≤ m) (hm : G.edgeFinset.card ≤ m) :
    G.minDegree ≤ m / 2 := by
  have hsum : (G.minDegree + 1) * G.minDegree ≤ 2 * m := by
    calc
      (G.minDegree + 1) * G.minDegree ≤ Fintype.card V * G.minDegree :=
        Nat.mul_le_mul_right _ G.minDegree_lt_card
      _ = ∑ _ : V, G.minDegree := by simp
      _ ≤ ∑ v : V, G.degree v :=
        Finset.sum_le_sum fun _ _ ↦ G.minDegree_le_degree _
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      _ ≤ 2 * m := Nat.mul_le_mul_left 2 hm
  have hq : 2 ≤ m / 2 := by omega
  have hm' : m ≤ 2 * (m / 2) + 1 := by omega
  by_contra h
  have hd : m / 2 + 1 ≤ G.minDegree := by omega
  nlinarith

/-- The coloring is constructed by minimum-degree deletion and extension. -/
theorem colorable_half_edge_bound
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {m : ℕ} (hm4 : 4 ≤ m) (hm : G.edgeFinset.card ≤ m) :
    G.Colorable (m / 2 + 1) := by
  classical
  let q := m / 2
  cases isEmpty_or_nonempty V with
  | inl hV =>
      let := hV
      exact SimpleGraph.Colorable.of_isEmpty _
  | inr hV =>
      let := hV
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
      obtain ⟨cR⟩ := colorable_half_edge_bound R hm4 hRedges
      have hdeg : G.degree v ≤ q := by
        rw [← hv]
        exact minDegree_le_half_edge_bound G hm4 hm
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
      obtain ⟨free, -, hfree⟩ :=
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


end Erdos569
