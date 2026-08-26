import ErdosProblems.Erdos19.MissingPairs
import ErdosProblems.Erdos19.ColorIncidence

/-! # Consequences of a uniformly dense graph part -/

namespace Erdos19.SetHypergraph

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem missingOrderedPairs_le_of_dense_twoGraph (n : ℕ) (H : SetHypergraph (Fin n))
    (delta : ℝ) (hG : ∀ v, (1 - delta) * n ≤ (H.twoGraph.degree v : ℝ)) :
    (H.missingOrderedPairs.card : ℝ) ≤ delta * (n : ℝ) ^ 2 := by
  classical
  let F (v : Fin n) := univ.filter fun w ↦ ¬H.twoGraph.Adj v w
  have hcard : H.missingOrderedPairs.card ≤ ∑ v : Fin n, (F v).card := by
    calc
      H.missingOrderedPairs.card = ∑ p : Fin n × Fin n,
          if p.1 ≠ p.2 ∧ ¬H.twoGraph.Adj p.1 p.2 then 1 else 0 := by
        simp [missingOrderedPairs]
      _ ≤ ∑ p : Fin n × Fin n, if ¬H.twoGraph.Adj p.1 p.2 then 1 else 0 := by
        apply sum_le_sum
        intro p _
        split_ifs <;> tauto
      _ = ∑ v : Fin n, (F v).card := by
        rw [Fintype.sum_prod_type]
        simp only [sum_boole]
        rfl
  have hper : ∀ v : Fin n, ((F v).card : ℝ) ≤ delta * n := by
    intro v
    have heq : H.twoGraph.degree v + (F v).card = n := by
      have h := @card_filter_add_card_filter_not (Fin n) univ (H.twoGraph.Adj v) _ _
      simpa only [← H.twoGraph.neighborFinset_eq_filter, card_neighborFinset_eq_degree,
        card_univ, Fintype.card_fin] using h
    have heqR : (H.twoGraph.degree v : ℝ) + (F v).card = n := by exact_mod_cast heq
    nlinarith only [heqR, hG v]
  have hcardR : (H.missingOrderedPairs.card : ℝ) ≤ ∑ v : Fin n, ((F v).card : ℝ) := by
    exact_mod_cast hcard
  calc
    (H.missingOrderedPairs.card : ℝ) ≤ ∑ v : Fin n, ((F v).card : ℝ) := hcardR
    _ ≤ ∑ _v : Fin n, delta * n := sum_le_sum (fun v _ ↦ hper v)
    _ = delta * (n : ℝ) ^ 2 := by simp; ring

theorem largeDegree_le_of_dense_twoGraph (n : ℕ) (H : SetHypergraph (Fin n))
    (hlinear : H.IsLinear) (hcomplete : H.IsPairComplete)
    (hsize : ∀ e : H, 2 ≤ e.1.ncard) (delta : ℝ)
    (hG : ∀ v, (1 - delta) * n ≤ (H.twoGraph.degree v : ℝ)) :
    ∀ v, (H.largeDegree v : ℝ) ≤ delta * n := by
  intro v
  have hsplit := H.twoGraph_degree_add_largeDegree hsize v
  have hbudget := H.incident_degree_add_excess hlinear hcomplete hsize v
  have hexcess := H.largeDegree_le_incidentExcess v
  have hb : (H.twoGraph.neighborSet v).ncard + H.largeDegree v ≤ n := by
    simp only [Fintype.card_fin] at hbudget
    omega
  have hb' : H.twoGraph.degree v + H.largeDegree v ≤ n := by
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hb
  have hbR : (H.twoGraph.degree v : ℝ) + H.largeDegree v ≤ n := by exact_mod_cast hb'
  nlinarith only [hbR, hG v]

#print axioms missingOrderedPairs_le_of_dense_twoGraph
#print axioms largeDegree_le_of_dense_twoGraph

end Erdos19.SetHypergraph
