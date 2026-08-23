import ErdosProblems.Erdos1105.BipartiteClosure

/-!
# Yuan's dense balanced bipartite lemma

Lemma 7 of https://arxiv.org/html/2102.00807: a balanced bipartite graph
with parts of size `ℓ` and at least `(ℓ - 1) * ℓ + 2` edges is Hamiltonian.
-/

namespace Erdos1105

open SimpleGraph Finset

theorem bipartite_edges_le_remove_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {A B : Finset V}
    (hAB : G.IsBipartiteWith (A : Set V) (B : Set V))
    {x y : V} (hx : x ∈ A) (hy : y ∈ B) (hxy : ¬G.Adj x y) :
    G.edgeFinset.card ≤ (A.card - 1) * (B.card - 1) + G.degree x + G.degree y := by
  classical
  have hBpos : 1 ≤ B.card := card_pos.mpr ⟨y, hy⟩
  have hbound : ∀ a ∈ A.erase x,
      G.degree a ≤ (B.card - 1) + if G.Adj a y then 1 else 0 := by
    intro a ha
    have haA := (mem_erase.mp ha).2
    by_cases hay : G.Adj a y
    · simpa [hay, Nat.sub_add_cancel hBpos] using
        isBipartiteWith_degree_le hAB haA
    · simp only [hay, ↓reduceIte, add_zero]
      rw [← card_erase_of_mem hy, ← G.card_neighborFinset_eq_degree]
      apply card_le_card
      intro z hz
      apply mem_erase.mpr
      refine ⟨?_, isBipartiteWith_neighborFinset_subset hAB haA hz⟩
      intro hzy
      subst z
      exact hay (by simpa using hz)
  have hcount : ∑ a ∈ A.erase x, (if G.Adj a y then 1 else 0 : ℕ) = G.degree y := by
    simp only [sum_boole, Nat.cast_id]
    rw [← G.card_neighborFinset_eq_degree]
    apply congrArg Finset.card
    ext a
    simp only [mem_filter, mem_erase, mem_neighborFinset]
    constructor
    · exact fun h ↦ h.2.symm
    · intro hay
      refine ⟨⟨?_, hAB.mem_of_mem_adj' hy hay.symm⟩, hay.symm⟩
      intro hax
      subst a
      exact hxy hay.symm
  have hsum := sum_le_sum hbound
  rw [sum_add_distrib, sum_const, card_erase_of_mem hx, smul_eq_mul, hcount] at hsum
  have hsplit := sum_erase_add A (fun a ↦ G.degree a) hx
  rw [isBipartiteWith_sum_degrees_eq_card_edges hAB] at hsplit
  omega

/-- The dense balanced bipartite lemma used in the even-path case. -/
theorem hamiltonian_of_dense_balanced_bipartite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {A B : Finset V}
    (hAB : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcover : A ∪ B = univ) (hcard : A.card = B.card)
    (hedges : (A.card - 1) * A.card + 2 ≤ G.edgeFinset.card) :
    G.IsHamiltonian := by
  classical
  have hmax : G.edgeFinset.card ≤ A.card * B.card := by
    rw [← isBipartiteWith_sum_degrees_eq_card_edges hAB]
    exact (sum_le_sum fun a ha ↦ isBipartiteWith_degree_le hAB ha).trans_eq
      (by simp)
  have hpart : 2 ≤ A.card := by
    rw [← hcard] at hmax
    by_contra h
    have hA : A.card ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hA with h0 | h1
    · simp only [h0, Nat.zero_mul] at hmax
      omega
    · simp only [h1, Nat.one_mul] at hmax
      simp only [h1, Nat.sub_self, Nat.zero_mul] at hedges
      omega
  apply BipartiteClosure.Closure.isHamiltonian_of_degree_sum hAB hcover hcard hpart
  intro x hx y hy hxy
  have hbound := bipartite_edges_le_remove_two G hAB hx hy hxy
  rw [← hcard] at hbound
  have hA : A.card = (A.card - 1) + 1 := by omega
  nlinarith

end Erdos1105

#print axioms Erdos1105.hamiltonian_of_dense_balanced_bipartite
