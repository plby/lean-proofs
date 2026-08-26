import ErdosProblems.Erdos547.FiniteTreeBoundary

/-!
# Degree mass of an induced forest
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {U : Type*} (T : SimpleGraph U) [DecidableRel T.Adj]

theorem degreeMass_forest_le (hT : T.IsAcyclic) (S : Finset U) :
    degreeMass T S ≤ 2 * S.card := by
  classical
  by_cases hS : S.Nonempty
  · letI : Nonempty ↥(S : Set U) := hS.to_set.to_subtype
    let G := T.induce (S : Set U)
    have htop := SimpleGraph.connected_top (V := ↥(S : Set U))
    obtain ⟨F, hGF, _, hF⟩ := htop.exists_isTree_le_of_le_of_isAcyclic
      (H := G) le_top (hT.induce _)
    have hs : (∑ u ∈ S, degreeIn T S u) ≤ ∑ u : (S : Set U), F.degree u := by
      rw [← Finset.sum_finset_coe]
      apply Finset.sum_le_sum
      intro u _
      rw [degreeIn_eq_induce_degree]
      exact G.degree_le_of_le hGF
    rw [F.sum_degrees_eq_twice_card_edges] at hs
    have he := hF.card_edgeFinset
    have hc : Fintype.card ↥(S : Set U) = S.card := by simp
    rw [hc] at he
    have hh : (∑ u ∈ S, degreeIn T S u) ≤ 2 * S.card := by omega
    unfold degreeMass
    exact_mod_cast hh
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [degreeMass]

end Erdos547

#print axioms Erdos547.degreeMass_forest_le
