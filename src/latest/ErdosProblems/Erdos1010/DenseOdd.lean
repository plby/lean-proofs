import ErdosProblems.Erdos1010.SparseAntineighborhood

/-! # A useful vertex in a dense odd-order graph -/

open Finset

namespace Erdos1010

theorem dense_odd_vertex {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r t : ℕ}
    (hn : Fintype.card V = 2 * r + 1) (ht : t < r)
    (hm : G.edgeFinset.card = r * (r + 1) + t) (hmin : ∀ v, r + 1 ≤ G.degree v) :
    ∃ u, G.degree u = r + 1 ∧ r ≤ (trianglesAt G u).card := by
  classical
  have hr : 1 ≤ r := by omega
  let F := Gᶜ
  have hFcap : ∀ v, F.degree v ≤ r - 1 := by
    intro v
    dsimp [F]
    rw [SimpleGraph.degree_compl, hn]
    have := hmin v
    omega
  have hFedges : (F.edgeFinset.card : ℤ) = (r : ℤ) ^ 2 - t := by
    have hc := edges_add_compl_edges G
    rw [hn, hm] at hc
    have hcZ : ((r : ℤ) * (r + 1) + t) + F.edgeFinset.card = ((2 * r + 1).choose 2 : ℤ) := by
      exact_mod_cast hc
    have hchoose : 2 * ((2 * r + 1).choose 2 : ℤ) = (2 * (r : ℤ)) * (2 * r + 1) := by
      exact_mod_cast twice_choose_succ_two (2 * r)
    nlinarith only [hcZ, hchoose]
  have hex : ∃ v, F.degree v = r - 1 := by
    by_contra! hnone
    have hlow : ∀ v, (F.degree v : ℤ) ≤ (r : ℤ) - 2 := by
      intro v
      have := hFcap v
      have := hnone v
      omega
    have hsum : (∑ v, (F.degree v : ℤ)) = 2 * ((r : ℤ) ^ 2 - t) := by
      have h : (∑ v, (F.degree v : ℤ)) = 2 * F.edgeFinset.card := by
        exact_mod_cast F.sum_degrees_eq_twice_card_edges
      rwa [hFedges] at h
    have hbound : (∑ v, (F.degree v : ℤ)) ≤ (2 * (r : ℤ) + 1) * (r - 2) := by
      calc
        _ ≤ ∑ _v : V, ((r : ℤ) - 2) := sum_le_sum fun v _ ↦ hlow v
        _ = _ := by simp [hn]; ring
    have htZ : (t : ℤ) < r := by exact_mod_cast ht
    nlinarith
  obtain ⟨v, hv⟩ := hex
  obtain ⟨u, huF, huE⟩ := exists_sparse_antineighborhood F (r - 1) (by omega) hFcap v hv
  have huG : G.degree u = r + 1 := by
    have hd := SimpleGraph.degree_compl (G := G) (v := u)
    have hlt := G.degree_lt_card_verts u
    rw [hn] at hd hlt
    change Gᶜ.degree u = r - 1 at huF
    omega
  refine ⟨u, huG, ?_⟩
  have hanti : antiNeighbors F u = G.neighborFinset u := by
    ext x
    rw [mem_antiNeighbors, SimpleGraph.mem_neighborFinset]
    change (x ≠ u ∧ ¬(u ≠ x ∧ ¬G.Adj u x)) ↔ G.Adj u x
    constructor
    · intro h
      by_contra hg
      exact h.2 ⟨h.1.symm, hg⟩
    · intro hg
      exact ⟨hg.ne.symm, fun h ↦ h.2 hg⟩
  have hpred : r - 1 + 1 = r := by omega
  rw [hanti, hpred] at huE
  have hcomp := internalPairs_add_compl G (G.neighborFinset u)
  rw [SimpleGraph.card_neighborFinset_eq_degree, huG] at hcomp
  have hchoose : (r + 1).choose 2 = r + r.choose 2 := by
    rw [Nat.choose_succ_succ]
    simp
  rw [hchoose] at hcomp
  rw [← card_internalPairs_neighbors]
  change (internalPairs Gᶜ (G.neighborFinset u)).card ≤ r.choose 2 at huE
  omega

end Erdos1010
