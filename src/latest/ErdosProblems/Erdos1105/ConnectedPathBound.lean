import ErdosProblems.Erdos1105.Cone
import ErdosProblems.Erdos1105.PathExtremalArithmetic

namespace Erdos1105

open SimpleGraph Finset

/-- The connected path Turán bound (Faudree--Schelp and Kopylov), obtained
by adding a universal vertex and applying cone disintegration. -/
theorem connected_path_edges_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hk : 4 ≤ k) (hn : k ≤ Fintype.card V) (hconn : G.Preconnected)
    (hfree : ¬pathGraph k ⊑ G) :
    G.edgeFinset.card ≤ max (pathExtremalEdges (Fintype.card V) (k - 1) 1)
      (pathExtremalEdges (Fintype.card V) (k - 1) ((k - 2) / 2)) := by
  classical
  let n := Fintype.card V
  let d := (k - 2) / 2
  have hd₁ : 1 ≤ d := by dsimp [d]; omega
  have hkd₁ : 2 * d + 2 ≤ k := by dsimp [d]; omega
  have hkd₂ : k ≤ 2 * d + 3 := by dsimp [d]; omega
  obtain ⟨H, hGH, hH, hmax⟩ := exists_cycle_saturated_extension (graphCone G) (k + 1)
    (no_long_cycle_cone_of_path_free G (by omega) hfree)
  have hu : H.IsUniversal none := fun v hv ↦ hGH (graphCone_universal G hv)
  have hconnH : (H.induce {v | v ≠ none}).Preconnected :=
    (graphCone_delete_preconnected G hconn).mono (fun _ _ h ↦ hGH h)
  have hcount : G.edgeFinset.card + n ≤ H.edgeFinset.card := by
    rw [← graphCone_card_edges G]
    exact card_le_card (edgeFinset_mono hGH)
  have hb := saturated_cone_edge_bound H hH (by omega)
    (by simpa only [Fintype.card_option] using Nat.add_le_add_right hn 1)
    hu hconnH hmax (d := d + 1) (by omega) (by omega)
  simp only [Fintype.card_option] at hb
  rcases hb with hempty | ⟨r, hrlo, hrhi, hrbound⟩
  · have hc := cone_empty_count_le n k d hkd₁ hkd₂ hn
    have hle : G.edgeFinset.card ≤ pathExtremalEdges n (k - 1) d := by
      dsimp only [n] at *
      omega
    exact hle.trans (le_max_right _ _)
  · have ha₁ : 1 ≤ k - r := by omega
    have ha₂ : k - r ≤ d := by omega
    have hrk : r ≤ k := by omega
    have hc := cone_nonempty_count n k r (by omega) hrk hn
    have hle : G.edgeFinset.card ≤ pathExtremalEdges n (k - 1) (k - r) := by
      dsimp only [n] at *
      omega
    exact hle.trans (pathExtremalEdges_le_max n (k - 1) 1 (k - r) d
      ha₁ ha₂ (by omega) (by omega))

end Erdos1105

#print axioms Erdos1105.connected_path_edges_le
