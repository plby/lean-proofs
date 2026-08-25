/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos88.FiniteES

namespace Erdos799

/-- If `G` has no clique of order `h`, every vertex set of size at least
`R(h, q)` contains an independent set of order `q`. -/
theorem exists_independent_subset_of_ramsey_le
    {n h q : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n))
    (hclique : G.cliqueNum < h)
    (hcard : Ramsey.ramseyNumber h q ≤ B.card) :
    ∃ I : Finset (Fin n), I ⊆ B ∧ I.card = q ∧ G.IsIndepSet I := by
  rcases Erdos88.FiniteES.clique_or_independent_subset_of_ramseyNumber_le
      G B hcard with ⟨K, -, hK⟩ | ⟨I, hIB, hI⟩
  · exact False.elim (Nat.not_le_of_gt hclique
      (hK.card_eq ▸ hK.isClique.card_le_cliqueNum))
  · exact ⟨I, hIB, hI.card_eq, hI.isIndepSet⟩

end Erdos799
