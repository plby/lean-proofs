import ErdosProblems.Erdos556.ProfileNormalization

/-! Near equality in the profile energy forces the bipartite pairs to be nearly full. -/

namespace Erdos556

open SimpleGraph Finset

theorem natCard_edges_split_of_le {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    Nat.card H.edgeSet = Nat.card G.edgeSet + Nat.card (H ⊓ Gᶜ).edgeSet := by
  have heq : G ⊔ (H ⊓ Gᶜ) = H := by
    ext u v
    constructor
    · rintro (hg | ⟨hh, _⟩)
      · exact hGH hg
      · exact hh
    · intro hh
      by_cases hg : G.Adj u v
      · exact Or.inl hg
      · exact Or.inr ⟨hh, hh.ne, hg⟩
  have hd : Disjoint G (H ⊓ Gᶜ) := by
    apply SimpleGraph.disjoint_left.mpr
    intro u v hg hh
    exact hh.2.2 hg
  have hh := natCard_edges_sup _ _ hd
  rwa [heq] at hh

def ThreeColourDecomposition.potentialMissing {V : Type*} [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) : SimpleGraph V :=
  profilePotentialGraph h.profile ⊓ h.bipartiteUnionᶜ

theorem ThreeColourDecomposition.potentialMissing_edge_count {V : Type*}
    [Fintype V] [DecidableEq V] {c : ThreeColouring V} {E D : ℝ}
    (h : ThreeColourDecomposition c E D) :
    (Nat.card (profilePotentialGraph h.profile).edgeSet : ℝ) =
      Nat.card h.bipartiteUnion.edgeSet + Nat.card h.potentialMissing.edgeSet := by
  exact_mod_cast natCard_edges_split_of_le _ _ h.bipartiteUnion_le_potential

theorem ThreeColourDecomposition.potentialMissing_bound {V : Type*}
    [Fintype V] [DecidableEq V] {c : ThreeColouring V} {E D : ℝ}
    (h : ThreeColourDecomposition c E D) (n : ℝ) (hn : n ≠ 0) :
    2 * (Nat.card h.potentialMissing.edgeSet : ℝ) ≤
      Fintype.card V + (2 * D - n) *
        (∑ p, (profileDimension p : ℝ) * (h.profileClass p).card) +
      6 * E - cubeEnergy (h.profileWeight n) * n ^ 2 := by
  have he := h.profileWeight_energy_identity n hn
  have hpot := profilePotentialGraph_edge_count h.profile
  have hsplit := h.potentialMissing_edge_count
  have hb := h.total_edge_budget
  change 2 * (Nat.card (profilePotentialGraph h.profile).edgeSet : ℝ) =
    cubeDisjointMass (fun p => ((h.profileClass p).card : ℝ)) at hpot
  nlinarith

theorem ThreeColourDecomposition.wrong_colour_unique_separator_missing {V : Type*}
    [Fintype V] [DecidableEq V] {c : ThreeColouring V} {E D : ℝ}
    (h : ThreeColourDecomposition c E D) (p q : CubeProfile) (i : Fin 3)
    (hsep : uniqueProfileSeparator p q i)
    (u v : V) (hu : u ∈ h.profileClass p) (hv : v ∈ h.profileClass q)
    (hwrong : ¬ (c.graph i).Adj u v) : h.potentialMissing.Adj u v := by
  have hup := (h.mem_profileClass_iff p u).mp hu
  have hvp := (h.mem_profileClass_iff q v).mp hv
  have hpot : (profilePotentialGraph h.profile).Adj u v := by
    change Disjoint (profileVertices (h.profile u)) (profileVertices (h.profile v))
    rw [hup, hvp]
    exact profileOppositeAt_disjoint _ _ i hsep.1
  refine ⟨hpot, hpot.ne, ?_⟩
  intro hb
  obtain ⟨j, hj⟩ := iSup_adj.mp hb
  have hopp := h.bipartite_profiles_opposite j u v hj
  rw [hup, hvp] at hopp
  have hji : j = i := by
    by_contra hji
    exact hsep.2 j hji hopp
  subst j
  exact hwrong (h.bipartite_le i hj)

#print axioms ThreeColourDecomposition.potentialMissing_bound
#print axioms ThreeColourDecomposition.wrong_colour_unique_separator_missing

end Erdos556
