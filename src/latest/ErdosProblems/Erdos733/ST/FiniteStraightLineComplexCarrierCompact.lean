import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: FiniteStraightLineComplexCarrierCompact]
lemma FiniteStraightLineComplexCarrierCompact
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (hA :
      A =
        (V : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ e : {e // e ∈ E}, segment ℝ e.1.1 e.1.2) :
    IsCompact A := by
-- BODY
  rw [hA]
  refine (V.finite_toSet.isCompact).union ?_
  apply isCompact_iUnion
  intro e
  rw [segment_eq_image_lineMap]
  exact (isCompact_Icc.image AffineMap.lineMap_continuous)
