import ErdosProblems.Erdos1105.DegreeObstruction

namespace Erdos1105

open SimpleGraph Finset

/-- The near-Dirac degree sequence with fewer than `l-1` exceptional
vertices is Hamiltonian on `2*l` vertices. -/
theorem hamiltonian_of_few_low_degrees {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {l : ℕ} (hl : 2 ≤ l)
    (hn : Fintype.card V = 2 * l) (B : Finset V) (hB : B.card < l - 1)
    (hmin : ∀ x, l - 1 ≤ G.degree x)
    (hhigh : ∀ x ∉ B, l ≤ G.degree x) : G.IsHamiltonian := by
  classical
  by_contra hnot
  obtain ⟨i, hi, hni, hlow, _⟩ :=
    nonhamiltonian_degree_obstruction G (by omega) hnot hmin
  have heq : i = l - 1 := by omega
  have hsub : (univ.filter fun x ↦ G.degree x ≤ i) ⊆ B := by
    intro x hx
    by_contra hxB
    have := hhigh x hxB
    have := (mem_filter.mp hx).2
    omega
  have := card_le_card hsub
  omega

end Erdos1105

#print axioms Erdos1105.hamiltonian_of_few_low_degrees
