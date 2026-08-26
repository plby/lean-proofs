/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos569.TriangleIndependent
import ErdosProblems.Erdos569.TriangleIndependentTwo
import ErdosProblems.Erdos570.TriangleLeaf
import ErdosProblems.Erdos570.TriangleContraction
import ErdosProblems.Erdos569.Sharpness
import ErdosProblems.Erdos570.Components
import ErdosProblems.Erdos570.EmbeddingNeighborhood

/-! # The Goddard–Kleitman triangle bound for every edge count -/

open scoped SimpleGraph

namespace Erdos569

open Erdos79 Erdos570

theorem ramseyAt_triangle :
    ∀ H : GraphCode, NoIsolated H →
      RamseyAt (cycleCode 3) H (2 * H.edgeCount + 1) := by
  intro H hH
  suffices hmain : ∀ m : ℕ, ∀ Q : GraphCode, Q.edgeCount = m → NoIsolated Q →
      RamseyAt (cycleCode 3) Q (2 * m + 1) by
    exact hmain H.edgeCount H rfl hH
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro H hm hH
    subst m
    classical
    let : DecidableRel H.graph.Adj := Classical.decRel _
    have hIH (Q : GraphCode) (hQ : NoIsolated Q) (hlt : Q.edgeCount < H.edgeCount) :
        RamseyAt (cycleCode 3) Q (2 * Q.edgeCount + 1) :=
      ih Q.edgeCount hlt Q rfl hQ
    by_cases hm0 : H.edgeCount = 0
    · intro C
      right
      have hn0 : H.vertexCount = 0 := by
        have := hH.vertexCount_le_twice_edgeCount
        omega
      let : IsEmpty (Fin H.vertexCount) := by rw [hn0]; infer_instance
      exact SimpleGraph.IsContained.of_isEmpty
    have hmpos : 0 < H.edgeCount := by omega
    have hNk : 3 ≤ 2 * H.edgeCount + 1 := by
      omega
    by_cases hn2 : H.vertexCount ≤ 2
    · apply RamseyAt.mono_right (isContained_completeCode_of_vertexCount_le hn2)
      apply ramseyAt_of_graphRamseyNumber_le
      rw [cycle_completeTwo]
      exact hNk
    have hn3 : 3 ≤ H.vertexCount := by omega
    let : Nonempty (Fin H.vertexCount) := Fin.pos_iff_nonempty.mp (by omega)
    by_cases hconn : H.graph.Connected
    · obtain ⟨v, hvmin'⟩ := H.graph.exists_minimal_degree_vertex
      have hvmin : H.graph.degree v = H.graph.minDegree := hvmin'.symm
      have hδpos : 0 < H.graph.degree v := (H.graph.degree_pos v).mpr (hH v)
      let R := supportCode (deleteVertexCode H v)
      have hRedge : R.edgeCount = H.edgeCount - H.graph.degree v := by
        simp [R, deleteVertexCode_edgeCount]
      have hRlt : R.edgeCount < H.edgeCount := by rw [hRedge]; omega
      have hdelete : RamseyAt (cycleCode 3) R (2 * H.edgeCount + 1) :=
        (hIH R (supportCode_noIsolated _) hRlt).mono_vertices (by omega)
      intro C
      let : DecidableRel C.Adj := Classical.decRel _
      by_cases hred : (cycleCode 3).graph ⊑ C
      · exact Or.inl hred
      by_cases hblue : H.graph ⊑ Cᶜ
      · exact Or.inr hblue
      by_cases hδ1 : H.graph.degree v = 1
      · exact (triangle_degree_one_contradiction C hH hconn le_rfl v hδ1
          hdelete hred hblue).elim
      have hδ2 : 2 ≤ H.graph.degree v := by omega
      let S := minimumDegreeVertices H.graph v
      by_cases hSind : H.graph.IsIndepSet (S : Set (Fin H.vertexCount))
      · by_cases hδeq : H.graph.degree v = 2
        · exact (triangle_independent_degree_two_contradiction
            C hH le_rfl v hvmin hδeq hSind hdelete hred hblue).elim
        · exact (triangle_independent_minimum_contradiction
            C hH le_rfl v hvmin (by omega) hSind hdelete hred hblue).elim
      · rw [SimpleGraph.isIndepSet_iff, Set.Pairwise] at hSind
        push Not at hSind
        obtain ⟨u, huS, w, hwS, -, huwAdj⟩ := hSind
        have humin : H.graph.degree u = H.graph.minDegree := by
          calc
            H.graph.degree u = H.graph.degree v :=
              (mem_minimumDegreeVertices H.graph v u).mp huS
            _ = H.graph.minDegree := hvmin
        have hwdeg : H.graph.degree w = H.graph.degree u := by
          calc
            H.graph.degree w = H.graph.degree v :=
              (mem_minimumDegreeVertices H.graph v w).mp hwS
            _ = H.graph.degree u := by rw [humin, hvmin]
        let K := contractionCode H.graph u w
        have hKno : NoIsolated K :=
          contractionCode_noIsolated H.graph huwAdj hH
            (by rw [humin, ← hvmin]; exact hδ2)
        have hKlt : K.edgeCount < H.edgeCount := by
          dsimp only [K]
          simpa [GraphCode.edgeCount_eq_card_edgeFinset] using
            contractionCode_edgeCount_lt H.graph huwAdj
        have hKblue : K.graph ⊑ Cᶜ :=
          ((hIH K hKno hKlt).mono_vertices (by omega) C).resolve_left hred
        have hcopy : contractionGraph H.graph u w ⊑ Cᶜ := by
          apply (recodeGraph_isContained_iff (contractionGraph H.graph u w) Cᶜ).mp
          exact hKblue
        exact (triangle_adjacent_contraction_contradiction
          C hH le_rfl u w huwAdj humin hwdeg
          (by rw [humin, ← hvmin]; exact hδ2) hcopy hred hblue).elim
    · let v : Fin H.vertexCount := ⟨0, by omega⟩
      let c := H.graph.connectedComponentMk v
      let H₁ := componentCode H c
      let H₂ := componentRemainderCode H c
      have hsum : H₁.edgeCount + H₂.edgeCount = H.edgeCount :=
        componentCode_edgeCount_add_remainder H c
      have hpos : 0 < H₁.edgeCount := componentCode_edgeCount_pos_of_noIsolated hH c
      have hlt₁ : H₁.edgeCount < H.edgeCount := by
        by_contra h
        have he : H₁.edgeCount = H.edgeCount := by omega
        exact hconn (connected_of_component_edgeCount_eq hH c he)
      have hlt₂ : H₂.edgeCount < H.edgeCount := by omega
      have hno₁ : NoIsolated H₁ := componentCode_noIsolated c hpos
      have hno₂ : NoIsolated H₂ := componentRemainderCode_noIsolated hH c
      have h₁ := hIH H₁ hno₁ hlt₁
      have h₂ := hIH H₂ hno₂ hlt₂
      apply RamseyAt.mono_right (isContained_component_partition H c)
      apply ramseyAt_disjointUnion_remove_first
      · exact h₁.mono_vertices (by omega)
      · apply h₂.mono_vertices
        apply Nat.le_sub_of_add_le
        have hv := hno₁.vertexCount_le_twice_edgeCount
        change 2 * H₂.edgeCount + 1 + H₁.vertexCount ≤ 2 * H.edgeCount + 1
        omega

end Erdos569
