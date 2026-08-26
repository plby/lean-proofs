import ErdosProblems.Erdos556.ProfileDeletedPairs
import ErdosProblems.Erdos556.NearCliqueCycleBound

/-! The weight cap on a profile with exactly one free colour. -/

namespace Erdos556

open SimpleGraph Finset

theorem ThreeColourDecomposition.edge_profile_size_bound {V : Type*} [Fintype V] [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D)
    (n : ℕ) (hn : 8 ≤ n) (hno : ∀ i, ¬ cycleGraph n ⊑ c.graph i)
    (p : CubeProfile) (hp : profileDimension p = 1) :
    (n : ℝ) * (h.profileClass p).card ≤ (n : ℝ) ^ 2 + 48 * E := by
  classical
  obtain ⟨i, hi, huniq⟩ := profileDimension_one_unique_free p hp
  let S := h.profileClass p
  have hsub : (c.graph i)ᶜ.induce (S : Set V) ≤ h.missing.induce (S : Set V) := by
    intro u v huv
    exact h.wrong_colour_in_edge_profile_missing p i huniq u.val v.val u.property v.property huv
  have hwrong : Nat.card ((c.graph i)ᶜ.induce (S : Set V)).edgeSet ≤ Nat.card h.missing.edgeSet :=
    (natCard_edges_mono _ _ hsub).trans (natCard_edges_induce_le h.missing S)
  have hbound := near_clique_order_bound_of_forbidden_cycle (c.graph i) S n hn (hno i)
  have hboundR : (n : ℝ) * S.card ≤ (n : ℝ) ^ 2 +
      16 * (Nat.card ((c.graph i)ᶜ.induce (S : Set V)).edgeSet : ℝ) := by
    rw [pow_two]
    exact_mod_cast hbound
  have hwrongR : (Nat.card ((c.graph i)ᶜ.induce (S : Set V)).edgeSet : ℝ) ≤
      Nat.card h.missing.edgeSet := by exact_mod_cast hwrong
  have hmissing := h.missing_edge_count_le
  change (n : ℝ) * S.card ≤ (n : ℝ) ^ 2 + 48 * E
  linarith

#print axioms ThreeColourDecomposition.edge_profile_size_bound

end Erdos556
