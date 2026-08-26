import ErdosProblems.Erdos547.ForestDegreeMass
import ErdosProblems.Erdos547.DegreeMassSupermodular

/-!
# A potential for absorbing short paths between cut vertices
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {U : Type*} (T : SimpleGraph U) [DecidableRel T.Adj]

noncomputable def shortBridgePotential (S : Finset U) : ℝ :=
  5 * S.card - 2 * degreeMass T S

theorem shortBridgePotential_lower (hT : T.IsAcyclic) (S : Finset U) :
    (S.card : ℝ) ≤ shortBridgePotential T S := by
  have hh := degreeMass_forest_le T hT S
  unfold shortBridgePotential
  linarith

theorem shortBridgePotential_upper (S : Finset U) :
    shortBridgePotential T S ≤ 5 * S.card := by
  have hh : 0 ≤ degreeMass T S := Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
  unfold shortBridgePotential
  linarith

theorem shortBridgePotential_union_le [DecidableEq U] (hT : T.IsAcyclic)
    (S P : Finset U) (hP : (T.induce (P : Set U)).Connected) (hsmall : P.card ≤ 6)
    (hinter : (S ∩ P).card = 2) (hzero : degreeMass T (S ∩ P) = 0) :
    shortBridgePotential T (S ∪ P) ≤ shortBridgePotential T S := by
  classical
  have htree := sum_degreeIn_tree T (show (T.induce (P : Set U)).IsTree from
    ⟨hP, hT.induce _⟩)
  have hmass : degreeMass T P + 2 = 2 * P.card := by
    unfold degreeMass
    exact_mod_cast htree
  have hsuper := degreeMass_supermodular T S P
  rw [hzero] at hsuper
  have hcards : ((S ∪ P).card : ℝ) + 2 = S.card + P.card := by
    have hc := Finset.card_union_add_card_inter S P
    rw [hinter] at hc
    exact_mod_cast hc
  have hsmall' : (P.card : ℝ) ≤ 6 := by exact_mod_cast hsmall
  unfold shortBridgePotential
  linarith

end Erdos547

#print axioms Erdos547.shortBridgePotential_union_le
