/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos569.ExactNeighborhood
import ErdosProblems.Erdos569.ExactArithmetic
import ErdosProblems.Erdos569.ExactColoring
import ErdosProblems.Erdos569.TriangleTargets
import ErdosProblems.Erdos569.Sharpness
import ErdosProblems.Erdos570.Components
import ErdosProblems.Erdos570.EmbeddingNeighborhood

/-! # The unconditional Ramsey bound for cycle lengths at least five -/

open scoped SimpleGraph

namespace Erdos569

open Erdos79 Erdos570

theorem ramseyAt_cycle_ge_five {k : ℕ} (hk : 5 ≤ k) :
    ∀ H : GraphCode, NoIsolated H →
      RamseyAt (cycleCode k) H ((k - 1) * H.edgeCount + 1) := by
  intro H hH
  suffices hmain : ∀ m : ℕ, ∀ Q : GraphCode, Q.edgeCount = m → NoIsolated Q →
      RamseyAt (cycleCode k) Q ((k - 1) * m + 1) by
    exact hmain H.edgeCount H rfl hH
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro H hm hH
    subst m
    classical
    let : DecidableRel H.graph.Adj := Classical.decRel _
    have hIH (Q : GraphCode) (hQ : NoIsolated Q) (hlt : Q.edgeCount < H.edgeCount) :
        RamseyAt (cycleCode k) Q ((k - 1) * Q.edgeCount + 1) :=
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
    have hNk : k ≤ (k - 1) * H.edgeCount + 1 := by
      have h := Nat.mul_le_mul_left (k - 1) hmpos
      omega
    by_cases hn2 : H.vertexCount ≤ 2
    · apply RamseyAt.mono_right (isContained_completeCode_of_vertexCount_le hn2)
      apply ramseyAt_of_graphRamseyNumber_le
      rw [cycle_completeTwo]
      exact hNk
    have hn3 : 3 ≤ H.vertexCount := by omega
    let : Nonempty (Fin H.vertexCount) := Fin.pos_iff_nonempty.mp (by omega)
    by_cases hconn : H.graph.Connected
    · have hnm1 : H.vertexCount ≤ H.edgeCount + 1 := by
        simpa [GraphCode.edgeCount] using hconn.card_vert_le_card_edgeSet_add_one
      obtain ⟨w, hwmin⟩ := H.graph.exists_minimal_degree_vertex
      let d := H.graph.degree w
      have hd : 0 < d := (H.graph.degree_pos w).mpr (hH w)
      let Q := supportCode (deleteVertexCode H w)
      have hQedge : Q.edgeCount = H.edgeCount - d := by
        simp [Q, d, deleteVertexCode_edgeCount]
      have hQlt : Q.edgeCount < H.edgeCount := by rw [hQedge]; omega
      have hQram := hIH Q (supportCode_noIsolated _) hQlt
      have hQroom : (k - 1) * Q.edgeCount + 1 ≤ (k - 1) * H.edgeCount + 1 := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hQlt.le) _
      intro C
      let : DecidableRel C.Adj := Classical.decRel _
      by_cases hcycle : (cycleCode k).graph ⊑ C
      · exact Or.inl hcycle
      by_cases hblue : H.graph ⊑ Cᶜ
      · exact Or.inr hblue
      have hnroom : H.vertexCount - 1 ≤ (k - 1) * H.edgeCount + 1 := by
        have h : H.edgeCount ≤ (k - 1) * H.edgeCount := by
          simpa only [one_mul] using
            Nat.mul_le_mul_right H.edgeCount (show 1 ≤ k - 1 by omega)
        omega
      obtain ⟨v, hstar⟩ := exists_large_degree_of_ramseyAt_supported_delete
        C w hd hnroom (hQram.mono_vertices hQroom) hcycle hblue
      have hpath : ¬ SimpleGraph.pathGraph (k - 1) ⊑ C.induce (C.neighborSet v) := by
        apply pathGraph_not_isContained_neighbor_of_cycleGraph_not_isContained (by omega) v
        rw [show k - 1 + 1 = k by omega]
        exact hcycle
      by_cases hd1 : d = 1
      · have hstar' : (k - 1) * H.edgeCount + 1 - (H.vertexCount - 1) ≤ C.degree v := by
          simpa only [show H.graph.degree w = 1 from hd1, one_mul] using hstar
        have hmul := Nat.mul_le_mul_left (k - 1) (show H.vertexCount - 1 ≤ H.edgeCount by omega)
        have heq : (k - 1) * (H.vertexCount - 1) =
            (k - 2) * (H.vertexCount - 1) + (H.vertexCount - 1) := by
          rw [show k - 1 = k - 2 + 1 by omega, Nat.add_mul, one_mul]
        have hroom : ((k - 1) - 1) * (H.vertexCount - 1) + 1 ≤
            (C.neighborFinset v).card := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          have hk' : k - 1 - 1 = k - 2 := by omega
          rw [hk']
          omega
        rcases Erdos570.RamseyAt.on_finset (ramseyAt_path_order H (by omega))
            C (C.neighborFinset v) hroom with hr | hb
        · have hset : (C.neighborFinset v : Set _) = C.neighborSet v := by ext x; simp
          exact (hpath (hset ▸ hr)).elim
        · exact (hblue (hb.trans (SimpleGraph.Embedding.induce _).isContained)).elim
      have hd2 : 2 ≤ d := by omega
      have hdegree : H.vertexCount * d ≤ 2 * H.edgeCount := by
        calc
          H.vertexCount * d = ∑ _ : Fin H.vertexCount, d := by simp
          _ ≤ ∑ x : Fin H.vertexCount, H.graph.degree x := by
            apply Finset.sum_le_sum
            intro x _
            change H.graph.degree w ≤ H.graph.degree x
            rw [← hwmin]
            exact H.graph.minDegree_le_degree x
          _ = 2 * H.edgeCount := by
            rw [H.graph.sum_degrees_eq_twice_card_edges, ← GraphCode.edgeCount_eq_card_edgeFinset]
      have hnm : H.vertexCount ≤ H.edgeCount := by nlinarith
      have hvroom : (k - 2) * (H.vertexCount / 2) + 1 ≤ C.degree v :=
        first_neighborhood_room (by omega) (by omega) hnm hdegree hstar
      obtain ⟨U₁, ha, hU₁, hclique⟩ := exists_blue_clique_in_neighborhood
        (a := H.vertexCount / 2 + 1) (by omega) C v hcycle (by simpa using hvroom)
      right
      by_cases hn_eq : H.vertexCount = 3
      · have hsmall := ramseyAt_cycle_three_vertices (by omega : 3 ≤ k) H hn_eq.le
        have hmul := Nat.mul_le_mul_left (k - 1)
          (show 3 ≤ H.edgeCount by omega)
        exact (hsmall.mono_vertices (by omega) C).resolve_left hcycle
      · obtain ⟨q, hqhalf, hqsq, ⟨c⟩⟩ := exists_colorable_half_square H (by omega)
        apply blue_of_clique_region_exact (budget := fun m ↦ (k - 1) * m + 1)
          hk hn3 hmpos C rfl c hcycle hIH v U₁ ha hU₁ hclique
        intro b g e hg hcounts _ havg
        apply remaining_region_exact_room hk (by omega) hnm ha hqhalf hqsq _ hcounts havg
        simpa only [Nat.add_sub_cancel] using hg
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
      · exact h₁.mono_vertices (Nat.add_le_add_right (Nat.mul_le_mul_left _ hlt₁.le) _)
      · apply h₂.mono_vertices
        apply Nat.le_sub_of_add_le
        have hv := hno₁.vertexCount_le_twice_edgeCount
        have hmul := Nat.mul_le_mul_right H₁.edgeCount (show 2 ≤ k - 1 by omega)
        nlinarith

end Erdos569
