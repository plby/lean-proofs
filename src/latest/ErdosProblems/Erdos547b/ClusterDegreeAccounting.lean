/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Section6Dichotomy

/-! # Exact degree accounting over disjoint physical clusters -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoClusterDegreeAccounting

open Finset SimpleGraph Erdos547EC2 Erdos547b.ZhaoStability
open Erdos547b.ZhaoSection6Dichotomy

variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
variable (P : ClusterAssignment V I) (H : SimpleGraph V) [DecidableRel H.Adj]

theorem degreeInto_clusterUnion (J : Finset I) (z : V) :
    degreeInto H z (clusterUnion P J) = ∑ j ∈ J, degreeInto H z (clusterVertices P j) := by
  have hdis : (J : Set I).PairwiseDisjoint
      (fun j => (clusterVertices P j).filter (H.Adj z)) := by
    intro i _ j _ hij
    exact (clusterVertices_disjoint P hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  unfold degreeInto clusterUnion
  rw [Finset.filter_biUnion, Finset.card_biUnion hdis]

theorem sum_degreeInto_le_degree (J : Finset I) (z : V) :
    (∑ j ∈ J, degreeInto H z (clusterVertices P j)) ≤ H.degree z := by
  rw [← degreeInto_clusterUnion]
  change ((clusterUnion P J).filter (H.Adj z)).card ≤ (H.neighborFinset z).card
  apply Finset.card_le_card
  intro y hy
  exact (H.mem_neighborFinset z y).mpr (Finset.mem_filter.mp hy).2

variable [Fintype I]

theorem degree_le_exceptional_add_sum (z : V) :
    H.degree z ≤ (exceptionalVertices P).card +
      ∑ j : I, degreeInto H z (clusterVertices P j) := by
  let ordinary := (clusterUnion P Finset.univ).filter (H.Adj z)
  have hsub : H.neighborFinset z ⊆ exceptionalVertices P ∪ ordinary := by
    intro y hy
    cases hp : P y with
    | none => exact Finset.mem_union_left _ ((mem_exceptionalVertices P y).mpr hp)
    | some j =>
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨(mem_clusterUnion P Finset.univ y).mpr ⟨j, Finset.mem_univ _, hp⟩,
          (H.mem_neighborFinset z y).mp hy⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have heq : ordinary.card = ∑ j : I, degreeInto H z (clusterVertices P j) :=
    degreeInto_clusterUnion P H Finset.univ z
  simpa only [H.card_neighborFinset_eq_degree, heq] using hcard

theorem clusterVolume_le_card (N : ℕ) (hN : ∀ j, (clusterVertices P j).card = N) :
    Fintype.card I * N ≤ Fintype.card V := by
  have hdis : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint (clusterVertices P) := by
    intro i _ j _ hij
    exact clusterVertices_disjoint P hij
  have heq : (clusterUnion P Finset.univ).card = Fintype.card I * N := by
    unfold clusterUnion
    rw [Finset.card_biUnion hdis]
    simp only [hN, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← heq]
  exact Finset.card_le_univ _

end Erdos547b.ZhaoClusterDegreeAccounting

#print axioms Erdos547b.ZhaoClusterDegreeAccounting.degreeInto_clusterUnion
#print axioms Erdos547b.ZhaoClusterDegreeAccounting.degree_le_exceptional_add_sum
#print axioms Erdos547b.ZhaoClusterDegreeAccounting.clusterVolume_le_card
