import ErdosProblems.Erdos745.JointMoments
import ErdosProblems.Erdos745.SmallComponentVertices

/-! # Exact graph marginals and small-vertex loss under sprinkling -/

open scoped BigOperators

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

open BernoulliUnion

def sprinkleRate (lam0 lam : ℝ) (n : ℕ) : ℝ := (lam - lam0) / ((n : ℝ) - lam0)

theorem sprinkleRate_pos {lam0 lam : ℝ} {n : ℕ} (h01 : lam0 < lam) (hln : lam < n) :
    0 < sprinkleRate lam0 lam n := by
  unfold sprinkleRate
  exact div_pos (sub_pos.mpr h01) (sub_pos.mpr (h01.trans hln))

theorem sprinkleRate_lt_one {lam0 lam : ℝ} {n : ℕ} (h01 : lam0 < lam) (hln : lam < n) :
    sprinkleRate lam0 lam n < 1 := by
  unfold sprinkleRate
  rw [div_lt_one (sub_pos.mpr (h01.trans hln))]
  linarith

theorem sprinkleRate_ge_div {lam0 lam : ℝ} {n : ℕ}
    (hlam0 : 0 ≤ lam0) (h01 : lam0 < lam) (hln : lam < n) :
    (lam - lam0) / n ≤ sprinkleRate lam0 lam n := by
  unfold sprinkleRate
  exact div_le_div_of_nonneg_left (sub_nonneg.mpr h01.le)
    (sub_pos.mpr (h01.trans hln)) (by linarith)

theorem sprinkleRate_superposition {lam0 lam : ℝ} {n : ℕ}
    (hlam0 : 0 ≤ lam0) (h01 : lam0 < lam) (hln : lam < n) :
    (edgeProbability lam0 n : ℝ) + (1 - (edgeProbability lam0 n : ℝ)) * sprinkleRate lam0 lam n =
      (edgeProbability lam n : ℝ) := by
  have hnR : (0 : ℝ) < n := lt_of_le_of_lt hlam0 (h01.trans hln)
  have hn : 0 < n := by exact_mod_cast hnR
  rw [coe_edgeProbability hlam0 hn (h01.trans hln).le,
    coe_edgeProbability (hlam0.trans h01.le) hn hln.le, sprinkleRate]
  have hd : (n : ℝ) - lam0 ≠ 0 := (sub_pos.mpr (h01.trans hln)).ne'
  field_simp
  ring

theorem expectation_eq_subsetExpectation (lam : ℝ) (n : ℕ) (X : SimpleGraph (Fin n) → ℝ) :
    expectation lam n X = subsetExpectation Finset.univ (edgeProbability lam n : ℝ)
      (fun A ↦ X (Erdos746.graphOfEdges A)) := by
  unfold expectation subsetExpectation
  rw [FiniteHarris.powerset_univ]
  have h := (graphEdgeEquiv n).sum_comp (fun G ↦ atomWeight lam n G * X G)
  rw [← h]
  apply Finset.sum_congr rfl
  intro A _
  change atomWeight lam n (Erdos746.graphOfEdges A) * X (Erdos746.graphOfEdges A) = _
  rw [atomWeight_graphOfEdges]

/-- The finite two-stage law, with the final graph represented by the union. -/
def sprinklingMass (lam0 lam : ℝ) (n : ℕ)
    (P : SimpleGraph (Fin n) → SimpleGraph (Fin n) → Prop) : ℝ :=
  jointMass Finset.univ (edgeProbability lam0 n : ℝ) (sprinkleRate lam0 lam n)
    (fun A B ↦ P (Erdos746.graphOfEdges A) (Erdos746.graphOfEdges (A ∪ B)))

theorem sprinklingMass_first (lam0 lam : ℝ) (n : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    sprinklingMass lam0 lam n (fun G _H ↦ P G) = probability lam0 n P := by
  rw [sprinklingMass, jointMass_first, probability_eq_edgeEventMass]

theorem sprinklingMass_final {lam0 lam : ℝ} {n : ℕ}
    (hlam0 : 0 ≤ lam0) (h01 : lam0 < lam) (hln : lam < n)
    (P : SimpleGraph (Fin n) → Prop) :
    sprinklingMass lam0 lam n (fun _G H ↦ P H) = probability lam n P := by
  rw [sprinklingMass, jointMass_union_event _ _ _ (fun A ↦ P (Erdos746.graphOfEdges A)),
    sprinkleRate_superposition hlam0 h01 hln,
    probability_eq_edgeEventMass]

theorem smallComponent_loss_card {n : ℕ} (A B : Finset (Edge n)) (K : ℕ) :
    ((smallComponentVertices (Erdos746.graphOfEdges A) K \
      smallComponentVertices (Erdos746.graphOfEdges (A ∪ B)) K).card : ℝ) =
      ((smallComponentVertices (Erdos746.graphOfEdges A) K).card : ℝ) -
        ((smallComponentVertices (Erdos746.graphOfEdges (A ∪ B)) K).card : ℝ) := by
  have hsub := smallComponentVertices_antitone
    (Erdos746.graphOfEdges_mono (Finset.subset_union_left : A ⊆ A ∪ B)) K
  rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]

theorem sprinkling_loss_expectation {lam0 lam : ℝ} {n : ℕ}
    (hlam0 : 0 ≤ lam0) (h01 : lam0 < lam) (hln : lam < n) (K : ℕ) :
    jointExpectation (Finset.univ : Finset (Edge n))
      (edgeProbability lam0 n : ℝ) (sprinkleRate lam0 lam n)
      (fun A B ↦ ((smallComponentVertices (Erdos746.graphOfEdges A) K \
        smallComponentVertices (Erdos746.graphOfEdges (A ∪ B)) K).card : ℝ)) =
      expectation lam0 n (fun G ↦ ((smallComponentVertices G K).card : ℝ)) -
        expectation lam n (fun G ↦ ((smallComponentVertices G K).card : ℝ)) := by
  simp_rw [smallComponent_loss_card]
  rw [jointExpectation_sub, jointExpectation_first,
    jointExpectation_union _ _ _
      (fun A : Finset (Edge n) ↦ ((smallComponentVertices (Erdos746.graphOfEdges A) K).card : ℝ)),
    sprinkleRate_superposition hlam0 h01 hln,
    ← expectation_eq_subsetExpectation lam0 n (fun G ↦ ((smallComponentVertices G K).card : ℝ)),
    ← expectation_eq_subsetExpectation lam n (fun G ↦ ((smallComponentVertices G K).card : ℝ))]

theorem sprinkling_loss_markov {lam0 lam t : ℝ} {n : ℕ}
    (hlam0 : 0 ≤ lam0) (h01 : lam0 < lam) (hln : lam < n) (ht : 0 < t) (K : ℕ) :
    sprinklingMass lam0 lam n (fun G H ↦
      t ≤ ((smallComponentVertices G K \ smallComponentVertices H K).card : ℝ)) ≤
      (expectation lam0 n (fun G ↦ ((smallComponentVertices G K).card : ℝ)) -
        expectation lam n (fun G ↦ ((smallComponentVertices G K).card : ℝ))) / t := by
  unfold sprinklingMass
  have hm := jointMass_markov (U := (Finset.univ : Finset (Edge n)))
    (edgeProbability lam0 n).property.1
    (edgeProbability lam0 n).property.2 (sprinkleRate_pos h01 hln).le
    (sprinkleRate_lt_one h01 hln).le ht
    (fun A B : Finset (Edge n) ↦ ((smallComponentVertices (Erdos746.graphOfEdges A) K \
      smallComponentVertices (Erdos746.graphOfEdges (A ∪ B)) K).card : ℝ))
    (fun _ _ _ _ ↦ Nat.cast_nonneg _)
  rw [sprinkling_loss_expectation hlam0 h01 hln K] at hm
  exact hm

end

end Erdos745
