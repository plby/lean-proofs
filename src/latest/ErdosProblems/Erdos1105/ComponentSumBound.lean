import ErdosProblems.Erdos1105.ComponentEndpointBound
import ErdosProblems.Erdos1105.SmallerPathArithmetic
import ErdosProblems.Erdos1105.PathDegeneracy

namespace Erdos1105

open SimpleGraph Finset

def connectedPathCount (n k : ℕ) : ℕ :=
  if n < k then n.choose 2 else
    max (pathExtremalEdges n (k - 1) 1) (pathExtremalEdges n (k - 1) ((k - 2) / 2))

theorem connected_path_count_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hconn : G.Preconnected) (hfree : ¬pathGraph k ⊑ G) :
    G.edgeFinset.card ≤ connectedPathCount (Fintype.card V) k := by
  by_cases hsmall : Fintype.card V < k
  · simpa only [connectedPathCount, if_pos hsmall] using G.card_edgeFinset_le_card_choose_two
  · rw [connectedPathCount, if_neg hsmall]
    by_cases hk₄ : 4 ≤ k
    · exact connected_path_edges_le G hk₄ (by omega) hconn hfree
    · have hk₃ : k = 3 := by omega
      subst k
      have h := path_free_edges_le_capped G (by omega) hfree
      rw [cappedEdgeBound_eq_linear (by omega)] at h
      norm_num [pathExtremalEdges, Nat.choose] at h ⊢
      omega

/-- A stronger numerical form of Yuan's component-counting lemma: the
secondary components need only satisfy the elementary degeneracy bound. -/
theorem connected_count_add_capped_le_formula {n n₀ k₁ k₂ : ℕ}
    (hk₂ : 3 ≤ k₂) (hkk : k₂ ≤ k₁) (hn₀ : k₁ - 1 ≤ n₀) (hn₀n : n₀ < n)
    (hn : k₁ + k₂ - 1 ≤ n) :
    connectedPathCount n₀ k₁ + cappedEdgeBound (n - n₀) (k₂ - 2) ≤
      pathFormula n (k₁ + k₂ - 1) := by
  have hclique : (k₁ - 1).choose 2 + cappedEdgeBound (n - k₁ + 1) (k₂ - 2) ≤
      pathFormula n (k₁ + k₂ - 1) := by
    rw [clique_plus_capped_eq_componentTerm hk₂ hn (by omega)]
    exact componentCliqueTerm_le_pathFormula (by omega) hn (by omega) (by omega)
  by_cases hsmall : n₀ < k₁
  · have heq : n₀ = k₁ - 1 := by omega
    have hsub : n - n₀ = n - k₁ + 1 := by omega
    rw [connectedPathCount, if_pos hsmall, hsub, heq]
    exact hclique
  · have hkn₀ : k₁ ≤ n₀ := by omega
    by_cases hk₄ : 4 ≤ k₁
    · have ha (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : 2 * a ≤ k₁ - 2) :
          pathExtremalEdges n₀ (k₁ - 1) a + cappedEdgeBound (n - n₀) (k₂ - 2) ≤
            pathFormula n (k₁ + k₂ - 1) := by
        apply (path_component_endpoint_bound hk₄ ha₂ hkn₀ hn₀n).trans
        apply max_le hclique
        exact smaller_pathExtremal_le_pathFormula hk₄ (by omega) hn ha₁ ha₂
      have h₁ := ha 1 le_rfl (by omega)
      have hs := ha ((k₁ - 2) / 2) (by omega) (by omega)
      simp only [connectedPathCount, if_neg hsmall]
      omega
    · have hk₁ : k₁ = 3 := by omega
      have hk₂' : k₂ = 3 := by omega
      subst k₁ k₂
      rw [connectedPathCount, if_neg hsmall, cappedEdgeBound_eq_linear (by omega)]
      norm_num [pathFormula, pathExtremalEdges, Nat.choose]
      omega

/-- Yuan's Lemma 4 for a family of actual path-free graphs. The
distinguished graph is connected; the other graphs need only be
nonempty. -/
theorem path_component_sum_le_formula {I V : Type*} [Fintype I] [Nonempty I]
    [Fintype V] [DecidableEq V] (W : I → Type*) [∀ i, Fintype (W i)] [∀ i, Nonempty (W i)]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : ∀ i, SimpleGraph (W i))
    [∀ i, DecidableRel (H i).Adj] {k₁ k₂ : ℕ}
    (hk₂ : 3 ≤ k₂) (hkk : k₂ ≤ k₁) (hn₀ : k₁ - 1 ≤ Fintype.card V)
    (hn : k₁ + k₂ - 1 ≤ Fintype.card V + ∑ i, Fintype.card (W i))
    (hconn : G.Preconnected) (hG : ¬pathGraph k₁ ⊑ G)
    (hH : ∀ i, ¬pathGraph k₂ ⊑ H i) :
    G.edgeFinset.card + (∑ i, (H i).edgeFinset.card) + (Fintype.card I - 1) ≤
      pathFormula (Fintype.card V + ∑ i, Fintype.card (W i)) (k₁ + k₂ - 1) := by
  classical
  let m := ∑ i, Fintype.card (W i)
  have hm : 0 < m := by
    obtain ⟨i⟩ := ‹Nonempty I›
    have hi : Fintype.card (W i) ≤ ∑ j, Fintype.card (W j) :=
      single_le_sum (fun j _ ↦ Nat.zero_le (Fintype.card (W j))) (mem_univ i)
    exact (Fintype.card_pos (α := W i)).trans_le hi
  have hprimary := connected_path_count_bound G (by omega) hconn hG
  have hsecondary : (∑ i, (H i).edgeFinset.card) ≤ ∑ i, cappedEdgeBound (Fintype.card (W i)) (k₂ - 2) :=
    sum_le_sum fun i _ ↦ path_free_edges_le_capped (H i) (by omega) (hH i)
  have hsum := cappedEdgeBound_sum univ (fun i ↦ Fintype.card (W i))
    (show 0 < k₂ - 2 by omega) (fun i _ ↦ Fintype.card_pos)
  simp only [card_univ] at hsum
  have hbound := connected_count_add_capped_le_formula hk₂ hkk hn₀
    (show Fintype.card V < Fintype.card V + m by omega) hn
  rw [Nat.add_sub_cancel_left] at hbound
  have hI : 0 < Fintype.card I := Fintype.card_pos
  dsimp only [m] at *
  omega

end Erdos1105

#print axioms Erdos1105.path_component_sum_le_formula
