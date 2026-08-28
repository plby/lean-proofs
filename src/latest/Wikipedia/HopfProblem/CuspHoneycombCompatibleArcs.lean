import Wikipedia.HopfProblem.CuspHoneycombHexagonArcs
import Wikipedia.HopfProblem.CuspHoneycombOpposite

/-!
# Choosing actual boundary arcs compatible with opposite gluing

The first three sides use the previously constructed actual boundary arcs.
Each opposite side uses the reversed parameter followed by the genuine
positive-twist identification. The resulting six homeomorphisms retain
the original toric endpoints and satisfy exact opposite-side compatibility.
-/

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

open ToricCharts ToricFan ToricSpace ToricComponent CuspPositive

/-- Reverse an actual side arc and transport it to its opposite side. -/
noncomputable def reversedOppositeBoundaryArc
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    unitInterval ≃ₜ positiveBoundary (k + 3) :=
  unitInterval.symmHomeomorph.trans
    ((positiveBoundaryArc k).trans (oppositePositiveBoundaryHomeomorph C₀ k))

theorem reversedOppositeBoundaryArc_zero
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    reversedOppositeBoundaryArc C₀ k 0 = positiveBoundaryArc (k + 3) 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change ((oppositePositiveBoundaryHomeomorph C₀ k
    (positiveBoundaryArc k (unitInterval.symm 0))).1.1 : Space) =
      ((positiveBoundaryArc (k + 3) 0).1.1 : Space)
  rw [unitInterval.symm_zero, oppositePositiveBoundaryHomeomorph_coe,
    positiveBoundaryArc_one_coe, opposite_twistedTranslate_origin_current,
    positiveBoundaryArc_zero_coe]
  have hi : (k + 3) - 1 = k + 2 := by fin_cases k <;> decide
  rw [hi]

theorem reversedOppositeBoundaryArc_one
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    reversedOppositeBoundaryArc C₀ k 1 = positiveBoundaryArc (k + 3) 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change ((oppositePositiveBoundaryHomeomorph C₀ k
    (positiveBoundaryArc k (unitInterval.symm 1))).1.1 : Space) =
      ((positiveBoundaryArc (k + 3) 1).1.1 : Space)
  rw [unitInterval.symm_one, oppositePositiveBoundaryHomeomorph_coe,
    positiveBoundaryArc_zero_coe, opposite_twistedTranslate_origin_previous,
    positiveBoundaryArc_one_coe]

/-- The constructed six compatible arcs on the literal positive component. -/
noncomputable def compatibleBoundaryArc
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    (k : Fin 6) → unitInterval ≃ₜ positiveBoundary k :=
  Fin.cases (positiveBoundaryArc 0)
    (Fin.cases (positiveBoundaryArc 1)
      (Fin.cases (positiveBoundaryArc 2)
        (Fin.cases (reversedOppositeBoundaryArc C₀ 0)
          (Fin.cases (reversedOppositeBoundaryArc C₀ 1)
            (Fin.cases (reversedOppositeBoundaryArc C₀ 2) (fun i => Fin.elim0 i))))))

theorem compatibleBoundaryArc_first
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (hk : k.1 < 3) :
    compatibleBoundaryArc C₀ k = positiveBoundaryArc k := by
  fin_cases k
  · rfl
  · rfl
  · rfl
  · norm_num at hk
  · norm_num at hk
  · norm_num at hk

/-- Every initial endpoint is unchanged from the original toric arc. -/
theorem compatibleBoundaryArc_zero
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    compatibleBoundaryArc C₀ k 0 = positiveBoundaryArc k 0 := by
  fin_cases k
  · rfl
  · rfl
  · rfl
  · exact reversedOppositeBoundaryArc_zero C₀ 0
  · exact reversedOppositeBoundaryArc_zero C₀ 1
  · exact reversedOppositeBoundaryArc_zero C₀ 2

/-- Every final endpoint is unchanged from the original toric arc. -/
theorem compatibleBoundaryArc_one
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    compatibleBoundaryArc C₀ k 1 = positiveBoundaryArc k 1 := by
  fin_cases k
  · rfl
  · rfl
  · rfl
  · exact reversedOppositeBoundaryArc_one C₀ 0
  · exact reversedOppositeBoundaryArc_one C₀ 1
  · exact reversedOppositeBoundaryArc_one C₀ 2

theorem compatibleBoundaryArc_zero_point
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    (compatibleBoundaryArc C₀ k 0).1 = squarePoint (k - 1) cornerZero := by
  rw [compatibleBoundaryArc_zero, positiveBoundaryArc_zero]

theorem compatibleBoundaryArc_one_point
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    (compatibleBoundaryArc C₀ k 1).1 = squarePoint k cornerZero := by
  rw [compatibleBoundaryArc_one, positiveBoundaryArc_one]

theorem compatibleBoundaryArc_next_endpoint
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    (compatibleBoundaryArc C₀ k 1).1 = (compatibleBoundaryArc C₀ (k + 1) 0).1 := by
  rw [compatibleBoundaryArc_one, compatibleBoundaryArc_zero]
  exact positiveBoundaryArc_next_endpoint k

/-- The two opposite translations cancel on actual toric points. -/
theorem oppositePositiveBoundaryHomeomorph_twice_coe
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (x : positiveBoundary k) :
    ((oppositePositiveBoundaryHomeomorph C₀ (k + 3)
      (oppositePositiveBoundaryHomeomorph C₀ k x)).1.1 : Space) = (x.1.1 : Space) := by
  rw [oppositePositiveBoundaryHomeomorph_coe, oppositePositiveBoundaryHomeomorph_coe,
    hexagonRay_opposite, cuspVector_neg, twistedTranslate_add,
    neg_add_cancel, twistedTranslate_zero]

/-- All six actual side parametrizations obey the genuine opposite-side
gluing, with parameter reversal. -/
theorem compatibleBoundaryArc_opposite
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (t : unitInterval) :
    compatibleBoundaryArc C₀ (k + 3) (unitInterval.symm t) =
      oppositePositiveBoundaryHomeomorph C₀ k (compatibleBoundaryArc C₀ k t) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  fin_cases k
  · change ((oppositePositiveBoundaryHomeomorph C₀ 0
      (positiveBoundaryArc 0 (unitInterval.symm (unitInterval.symm t)))).1.1 : Space) =
        ((oppositePositiveBoundaryHomeomorph C₀ 0 (positiveBoundaryArc 0 t)).1.1 : Space)
    rw [unitInterval.symm_symm]
  · change ((oppositePositiveBoundaryHomeomorph C₀ 1
      (positiveBoundaryArc 1 (unitInterval.symm (unitInterval.symm t)))).1.1 : Space) =
        ((oppositePositiveBoundaryHomeomorph C₀ 1 (positiveBoundaryArc 1 t)).1.1 : Space)
    rw [unitInterval.symm_symm]
  · change ((oppositePositiveBoundaryHomeomorph C₀ 2
      (positiveBoundaryArc 2 (unitInterval.symm (unitInterval.symm t)))).1.1 : Space) =
        ((oppositePositiveBoundaryHomeomorph C₀ 2 (positiveBoundaryArc 2 t)).1.1 : Space)
    rw [unitInterval.symm_symm]
  · exact (oppositePositiveBoundaryHomeomorph_twice_coe C₀ 0
      (positiveBoundaryArc 0 (unitInterval.symm t))).symm
  · exact (oppositePositiveBoundaryHomeomorph_twice_coe C₀ 1
      (positiveBoundaryArc 1 (unitInterval.symm t))).symm
  · exact (oppositePositiveBoundaryHomeomorph_twice_coe C₀ 2
      (positiveBoundaryArc 2 (unitInterval.symm t))).symm

theorem compatibleBoundaryArc_opposite_coe
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (t : unitInterval) :
    ((compatibleBoundaryArc C₀ (k + 3) (unitInterval.symm t)).1.1 : Space) =
      twistedTranslate (positiveTwist C₀) (cuspVector (hexagonRay k))
        ((compatibleBoundaryArc C₀ k t).1.1 : Space) := by
  rw [compatibleBoundaryArc_opposite, oppositePositiveBoundaryHomeomorph_coe]

end Wikipedia.HopfProblem.CuspHoneycombHexagon
