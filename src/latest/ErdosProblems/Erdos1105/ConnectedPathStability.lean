import ErdosProblems.Erdos1105.ConnectedPathBound
import ErdosProblems.Erdos1105.CliquePendant

namespace Erdos1105

open SimpleGraph Finset

/-- Containment in the endpoint extremal graph `H(n,k-1,1)`, expressed
without choosing a labeling: outside a set of `k-2` vertices, every edge
is incident to one fixed vertex of that set. -/
def PendantCliqueShape {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Finset V, S.card = k - 2 ∧ ∃ u ∈ S,
    ∀ x ∉ S, ∀ y, G.Adj x y → y = u

/-- Above both non-endpoint Kopylov bounds, a connected path-free graph
has the pendant-clique shape. For odd `k`, this is the stability input
used in Yuan's path anti-Ramsey argument. -/
theorem connected_path_high_edges_pendant {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hk : 6 ≤ k) (hn : k ≤ Fintype.card V) (hconn : G.Preconnected)
    (hfree : ¬pathGraph k ⊑ G)
    (hedges : max (pathExtremalEdges (Fintype.card V) (k - 1) 2)
      (pathExtremalEdges (Fintype.card V) (k - 1) ((k - 2) / 2)) < G.edgeFinset.card) :
    PendantCliqueShape G k := by
  classical
  let n := Fintype.card V
  let d := (k - 2) / 2
  have hd₁ : 2 ≤ d := by dsimp [d]; omega
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
  have hb := saturated_cone_core_dichotomy H hH (by omega)
    (by simpa only [Fintype.card_option] using Nat.add_le_add_right hn 1)
    hu hconnH hmax (d := d + 1) (by omega) (by omega)
  rcases hb with hempty | ⟨hrlo, hrhi, hclique, hstable⟩
  · have he := edges_le_of_core_empty H (d + 1) hempty
    have hc := cone_empty_count_le n k d hkd₁ hkd₂ hn
    have hmaxd := le_max_right (pathExtremalEdges n (k - 1) 2)
      (pathExtremalEdges n (k - 1) d)
    simp only [Fintype.card_option] at he
    dsimp only [n, d] at *
    omega
  · let r := (vertexCore H (d + 1)).card
    have hrk : r = k - 1 := by
      by_contra hrne
      have ha₁ : 2 ≤ k - r := by dsimp [r]; omega
      have ha₂ : k - r ≤ d := by dsimp [r]; omega
      have he := edges_le_core_bound H (k + 1 - r)
      rw [hstable] at he
      simp only [Fintype.card_option] at he
      have hc := cone_nonempty_count n k r (by dsimp [r]; omega)
        (by dsimp [r]; omega) hn
      have hle : G.edgeFinset.card ≤ pathExtremalEdges n (k - 1) (k - r) := by
        dsimp only [n, r] at *
        omega
      have hconv := pathExtremalEdges_le_max n (k - 1) 2 (k - r) d
        ha₁ ha₂ (by omega) (by omega)
      exact (not_lt_of_ge (hle.trans hconv)) hedges
    have hcore : (vertexCore H (d + 1)).Nonempty := card_pos.mp (by dsimp [r] at hrk; omega)
    have hNone := universal_mem_vertexCore H (d + 1) hcore hu
    obtain ⟨S, hS, hScard⟩ := cone_clique_remove_none H hclique hNone
    let J := H.comap some
    have hGJ : G ≤ J := fun _ _ hadj ↦ hGH hadj
    have hJ : ¬pathGraph k ⊑ J := by
      apply path_free_of_no_long_cycle_cone J (by omega)
      rw [graphCone_comap_some H hu]
      exact hH
    have hSk : S.card + 2 = k := by dsimp only [r] at hrk; omega
    obtain ⟨u, huS, hpend⟩ := large_clique_pendant_structure J (hconn.mono hGJ)
      hS (by omega) (by omega) (by rw [hSk]; exact hJ)
    exact ⟨S, by omega, u, huS, fun x hx y hxy ↦ hpend x hx y (hGJ hxy)⟩

end Erdos1105

#print axioms Erdos1105.connected_path_high_edges_pendant
