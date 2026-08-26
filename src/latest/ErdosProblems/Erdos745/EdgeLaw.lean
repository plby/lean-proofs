import ErdosProblems.Erdos745.Moments
import ErdosProblems.Erdos746.Model
import ErdosProblems.Erdos746.BernoulliFinset

/-!
# Finite edge coordinates for the exact random-graph measure

This adapter reuses the finite Bernoulli calculations from Erdős 746 and
proves that they compute the same probabilities as Mathlib's graph measure.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal unitInterval

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The possible edges on the labelled vertex set. -/
abbrev Edge (n : ℕ) : Type := Erdos746.Edge n

/-- A graph's edge set in the finite coordinate type of possible edges. -/
def edgeCoordinates {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Edge n) :=
  Finset.univ.filter fun e ↦ e.val ∈ G.edgeSet

@[simp] theorem mem_edgeCoordinates {n : ℕ} (G : SimpleGraph (Fin n))
    (e : Edge n) : e ∈ edgeCoordinates G ↔ e.val ∈ G.edgeSet := by
  simp [edgeCoordinates]

theorem graphOfEdges_injective {n : ℕ} :
    Function.Injective (Erdos746.graphOfEdges : Finset (Edge n) → SimpleGraph (Fin n)) := by
  intro A B hAB
  have h := congrArg SimpleGraph.edgeSet hAB
  simpa only [Erdos746.edgeSet_graphOfEdges, Finset.coe_inj, Finset.map_inj] using h

@[simp] theorem graphOfEdges_edgeCoordinates {n : ℕ} (G : SimpleGraph (Fin n)) :
    Erdos746.graphOfEdges (edgeCoordinates G) = G := by
  apply SimpleGraph.edgeSet_injective
  rw [Erdos746.edgeSet_graphOfEdges]
  ext e
  simp only [Finset.mem_coe, Finset.mem_map, mem_edgeCoordinates]
  constructor
  · rintro ⟨e', he', rfl⟩
    exact he'
  · intro he
    have heTop : e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset := by
      apply SimpleGraph.mem_edgeFinset.mpr
      exact SimpleGraph.edgeSet_mono le_top he
    exact ⟨⟨e, heTop⟩, he, rfl⟩

@[simp] theorem edgeCoordinates_graphOfEdges {n : ℕ} (A : Finset (Edge n)) :
    edgeCoordinates (Erdos746.graphOfEdges A) = A := by
  apply graphOfEdges_injective
  exact graphOfEdges_edgeCoordinates _

/-- The finite edge-coordinate presentation is a bijection, not a change of model. -/
def graphEdgeEquiv (n : ℕ) : Finset (Edge n) ≃ SimpleGraph (Fin n) where
  toFun := Erdos746.graphOfEdges
  invFun := edgeCoordinates
  left_inv := edgeCoordinates_graphOfEdges
  right_inv := graphOfEdges_edgeCoordinates

theorem atomWeight_graphOfEdges (lam : ℝ) (n : ℕ) (A : Finset (Edge n)) :
    atomWeight lam n (Erdos746.graphOfEdges A) =
      Erdos746.BernoulliFinset.weight Finset.univ (edgeProbability lam n : ℝ) A := by
  rw [atomWeight, measureReal_def, randomGraph, SimpleGraph.binomialRandom_singleton,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow]
  have hcard : (Finset.univ : Finset (Edge n)).card = n.choose 2 := by
    rw [Finset.card_univ]
    exact Erdos746.card_edge n
  rw [Erdos746.BernoulliFinset.weight, hcard]
  simp

/-- Equality of all event probabilities in the measure and finite-sum presentations. -/
theorem probability_eq_edgeEventMass (lam : ℝ) (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) :
    probability lam n P =
      Erdos746.BernoulliFinset.eventMass Finset.univ (edgeProbability lam n : ℝ)
        (fun A ↦ P (Erdos746.graphOfEdges A)) := by
  rw [probability_eq_sum]
  have hsum := (graphEdgeEquiv n).sum_comp
    (fun G ↦ if P G then atomWeight lam n G else 0)
  rw [← hsum]
  unfold Erdos746.BernoulliFinset.eventMass
  rw [Finset.sum_filter]
  have hpowerset : (Finset.univ : Finset (Edge n)).powerset = Finset.univ := by
    ext A
    simp only [Finset.mem_powerset, Finset.mem_univ, iff_true]
    exact Finset.subset_univ A
  rw [hpowerset]
  apply Finset.sum_congr rfl
  intro A _
  change (if P (Erdos746.graphOfEdges A) then
      atomWeight lam n (Erdos746.graphOfEdges A) else 0) = _
  rw [atomWeight_graphOfEdges]

/-- Exact probability of prescribing arbitrary disjoint present and absent
edge sets.  Every unprescribed edge remains free. -/
theorem probability_edge_cylinder (lam : ℝ) (n : ℕ)
    (S T : Finset (Edge n)) (hST : Disjoint S T) :
    probability lam n (fun G ↦ S ⊆ edgeCoordinates G ∧
      Disjoint T (edgeCoordinates G)) =
        (edgeProbability lam n : ℝ) ^ S.card *
          (1 - (edgeProbability lam n : ℝ)) ^ T.card := by
  rw [probability_eq_edgeEventMass]
  simp only [edgeCoordinates_graphOfEdges]
  exact Erdos746.BernoulliFinset.eventMass_contains_disjoint
    (Finset.subset_univ S) (Finset.subset_univ T) hST _

/-- The common absent edges are the exact correction to multiplication of
two compatible edge-cylinder probabilities. -/
theorem probability_edge_cylinder_pair (lam : ℝ) (n : ℕ)
    (A B C D : Finset (Edge n)) (hAC : Disjoint A C)
    (hAB : Disjoint A B) (hAD : Disjoint A D)
    (hCB : Disjoint C B) (hCD : Disjoint C D) :
    probability lam n (fun G ↦
      (A ⊆ edgeCoordinates G ∧ Disjoint B (edgeCoordinates G)) ∧
      (C ⊆ edgeCoordinates G ∧ Disjoint D (edgeCoordinates G))) *
        (1 - (edgeProbability lam n : ℝ)) ^ (B ∩ D).card =
      probability lam n (fun G ↦ A ⊆ edgeCoordinates G ∧ Disjoint B (edgeCoordinates G)) *
        probability lam n (fun G ↦ C ⊆ edgeCoordinates G ∧ Disjoint D (edgeCoordinates G)) := by
  have hevent : (fun G ↦
      (A ⊆ edgeCoordinates G ∧ Disjoint B (edgeCoordinates G)) ∧
      (C ⊆ edgeCoordinates G ∧ Disjoint D (edgeCoordinates G))) =
      (fun G ↦ A ∪ C ⊆ edgeCoordinates G ∧ Disjoint (B ∪ D) (edgeCoordinates G)) := by
    funext G
    apply propext
    simp only [Finset.union_subset_iff, Finset.disjoint_union_left]
    tauto
  have hdis : Disjoint (A ∪ C) (B ∪ D) := by
    simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
    exact ⟨⟨hAB, hCB⟩, ⟨hAD, hCD⟩⟩
  rw [hevent, probability_edge_cylinder _ _ _ _ hdis,
    probability_edge_cylinder _ _ _ _ hAB, probability_edge_cylinder _ _ _ _ hCD,
    Finset.card_union_of_disjoint hAC, mul_assoc, ← pow_add,
    Finset.card_union_add_card_inter, pow_add, pow_add]
  ring

end

end Erdos745
