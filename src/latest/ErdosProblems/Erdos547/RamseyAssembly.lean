import ErdosProblems.Erdos547.PositiveProportionEmbedding
import ErdosProblems.Erdos547.DegreeDichotomy
import ErdosProblems.Erdos547.NearCore

/-!
# Combining the two alternatives of the degree dichotomy
-/

namespace Erdos547

open Finset SimpleGraph

theorem eventually_ramsey_at_twice_edges :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ T : SimpleGraph (Fin (m + 1)),
      T.IsTree → RamseyAt T (2 * m) := by
  classical
  let ε : ℝ := 1 / coreDeficitDivisor
  have hε : 0 < ε := by norm_num [ε, coreDeficitDivisor]
  have hεone : ε ≤ 1 := by norm_num [ε, coreDeficitDivisor]
  obtain ⟨a, ha, habound, mD, hD⟩ := eventually_colour_degree_dichotomy ε hε hεone
  have haone : a ≤ 1 := habound.trans (by norm_num [ε, coreDeficitDivisor])
  obtain ⟨mNear, hNear⟩ := eventually_ramsey_of_near_core
  obtain ⟨nEmbed, hEmbed⟩ := eventually_positive_proportion_tree_embedding.{0, 0} a ha haone
  let m₀ := max 1 (max mD (max mNear nEmbed))
  refine ⟨m₀, ?_⟩
  intro m hm T hT R
  have hmone : 1 ≤ m := (le_max_left _ _).trans hm
  have hmD : mD ≤ m := ((le_max_left _ _).trans (le_max_right _ _)).trans hm
  have hmNear : mNear ≤ m :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hm
  have hmEmbed : nEmbed ≤ m :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hm
  obtain ⟨G, hG, hcase⟩ := hD m hmD R
  have hmono : T ⊑ G ∨ T ⊑ Gᶜ := by
    rcases hcase with ⟨Q, hQ, hdegree⟩ | ⟨S, hS, hminimum, hhigh⟩
    · exact hNear m hmNear T G Q hT hQ hdegree
    · have horder : (Fintype.card (Fin (m + 1)) : ℝ) - 1 = (m : ℝ) := by simp
      have hScard : Fintype.card ↥S = S.card := Fintype.card_coe S
      have hdegree (v : ↥S) : (G.induce (S : Set (Fin (2 * m)))).degree v =
          degreeIn G S v.val := (degreeIn_eq_induce_degree G S v).symm
      let H : Finset ↥S := Finset.univ.filter
        (fun v ↦ (1 + a) * m ≤ (degreeIn G S v.val : ℝ))
      have hH : H.card = (S.filter (fun v ↦ (1 + a) * m ≤ (degreeIn G S v : ℝ))).card := by
        exact card_coe_filter_univ S (fun v ↦ (1 + a) * m ≤ (degreeIn G S v : ℝ))
      have hhostLower : (Fintype.card (Fin (m + 1)) : ℝ) / 4 ≤ Fintype.card ↥S := by
        rw [hScard, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
        have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hmone
        linarith only [hS, hmR]
      have hhostUpper : (Fintype.card ↥S : ℝ) ≤ 2 * Fintype.card (Fin (m + 1)) := by
        have hh : S.card ≤ 2 * m := by simpa only [Fintype.card_fin] using S.card_le_univ
        have hhR : (S.card : ℝ) ≤ 2 * m := by exact_mod_cast hh
        rw [hScard, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
        linarith only [hhR]
      have hembedding : T ⊑ G.induce (S : Set (Fin (2 * m))) := by
        refine hEmbed (Fin (m + 1)) ↥S T (G.induce (S : Set (Fin (2 * m)))) hT
          (by simpa only [Fintype.card_fin] using hmEmbed.trans (Nat.le_succ m))
          hhostLower hhostUpper ?_ H ?_ ?_
        · intro v
          rw [horder, hdegree]
          exact (hminimum v.val v.property).le
        · intro v hv
          rw [horder, hdegree]
          exact (Finset.mem_filter.mp hv).2
        · rw [hScard, hH]
          exact hhigh
      exact Or.inl (hembedding.trans ⟨SimpleGraph.Copy.induce G (S : Set (Fin (2 * m)))⟩)
  rcases hG with rfl | rfl
  · exact hmono
  · simpa only [compl_compl, or_comm] using hmono

end Erdos547

#print axioms Erdos547.eventually_ramsey_at_twice_edges
