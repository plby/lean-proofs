import StackExchange.Puzzling139335.LoopVariation.Finiteness
import Wikipedia.SchoenfliesTheorem.Curve

/-!
# Set-level names for finite-resolution variation

For an arc or Jordan curve, choose one of its actual parametrizations and take
the concrete finite-chain supremum defined earlier. The value on a set which is
not respectively an arc or a Jordan curve is zero. Parametrization-independence
is proved in the accompanying modules; it is not an assumption of these
definitions.
-/

open Set

namespace Puzzling139335.LoopVariation

open ArcVariation

noncomputable section

/-- The concrete truncated variation of one chosen parametrization of an arc. -/
def arcVariation (ε : ℝ) (A : Set Schoenflies.Plane) : ℝ := by
  classical
  exact if h : Schoenflies.IsArc A then
    variationOn ε (Classical.choose h) (Icc (0 : ℝ) 1)
  else 0

/-- The concrete cyclic truncated variation of one chosen Jordan parametrization. -/
def loopVariation (ε : ℝ) (C : Set Schoenflies.Plane) : ℝ := by
  classical
  exact if h : Schoenflies.IsJordanCurve C then
    loopVariationOn ε (Classical.choose h) (Icc (0 : ℝ) 1)
  else 0

/-- A set-level Jordan variation is nonnegative, by the concrete finiteness proof. -/
theorem loopVariation_nonneg {ε : ℝ} {C : Set Schoenflies.Plane}
    (hC : Schoenflies.IsJordanCurve C) (hε : 0 < ε) :
    0 ≤ loopVariation ε C := by
  rw [loopVariation, dif_pos hC]
  obtain ⟨hf, _⟩ := Classical.choose_spec hC
  exact loopVariationOn_nonneg
    (bddAbove_cycleScoresOn_Icc zero_le_one hf.continuousOn hf.closes hε)

/-- A nondegenerate Jordan curve has a fixed positive lower bound at every
sufficiently small positive resolution. -/
theorem loopVariation_exists_positive_lower_bound {C : Set Schoenflies.Plane}
    (hC : Schoenflies.IsJordanCurve C) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η → η ≤ loopVariation ε C := by
  obtain ⟨hf, _⟩ := Classical.choose_spec hC
  obtain ⟨η, hη, hbound⟩ := exists_positive_lower_bound_of_injOn_Ico
    (by norm_num : (0 : ℝ) < 1) hf.continuousOn hf.closes hf.injOn
  refine ⟨η, hη, ?_⟩
  intro ε hε hsmall
  rw [loopVariation, dif_pos hC]
  exact hbound ε hε hsmall

end

end Puzzling139335.LoopVariation
