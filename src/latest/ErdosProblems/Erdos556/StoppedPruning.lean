import ErdosProblems.Erdos556.Pruning

/-!
# Low-degree pruning with a cardinality floor

Stopping at a prescribed order retains the quadratic edge saving which
would be lost if an empty core were used in the two-colour counting step.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_induced_core_of_card_floor {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (a : ℕ) (ha : a ≤ Fintype.card V) :
    ∃ S : Finset V, a ≤ S.card ∧
      (G.edgeFinset.card : ℝ) - d * Fintype.card V ≤
        ((G.induce (S : Set V)).edgeFinset.card : ℝ) - d * S.card ∧
      (S.card = a ∨ ∀ v : S, d < (G.induce (S : Set V)).degree v) := by
  classical
  let excess (S : Finset V) : ℝ :=
    ((G.induce (S : Set V)).edgeFinset.card : ℝ) - d * S.card
  let baseline : ℝ := (G.edgeFinset.card : ℝ) - d * Fintype.card V
  let good : Finset (Finset V) := univ.filter fun S => a ≤ S.card ∧ baseline ≤ excess S
  have huniv : (univ : Finset V) ∈ good := by
    have he : (G.induce (↑(univ : Finset V) : Set V)).edgeFinset.card = G.edgeFinset.card := by
      rw [← G.card_filter_edgeFinset_toFinset_subset univ]
      simp
    simp [good, excess, baseline, he, ha]
  obtain ⟨S, hS, hminimal⟩ := good.exists_min_image Finset.card ⟨_, huniv⟩
  obtain ⟨hSa, hgood⟩ := (mem_filter.mp hS).2
  refine ⟨S, hSa, hgood, ?_⟩
  by_cases hcardeq : S.card = a
  · exact Or.inl hcardeq
  right
  intro v
  by_contra hdegree
  have hdegree' : ((G.induce (S : Set V)).degree v : ℝ) ≤ d := le_of_not_gt hdegree
  let T := S.erase v.val
  have hcard : T.card + 1 = S.card := card_erase_add_one v.property
  have hedge := induced_edges_erase_add_degree G S v
  have hedgeR : ((G.induce (T : Set V)).edgeFinset.card : ℝ) +
      (G.induce (S : Set V)).degree v = (G.induce (S : Set V)).edgeFinset.card := by exact_mod_cast hedge
  have hcardR : (T.card : ℝ) + 1 = S.card := by exact_mod_cast hcard
  have hT : T ∈ good := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, by omega, ?_⟩
    dsimp [excess] at hgood ⊢
    nlinarith
  have hle := hminimal T hT
  omega

#print axioms exists_induced_core_of_card_floor

end Erdos556
