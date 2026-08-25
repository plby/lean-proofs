import StackExchange.Puzzling139335.LoopVariation
import StackExchange.Puzzling139335.AntipodalEndpoints
import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Kernel and Euclidean-interface checks for cyclic variation

This module records kernel dependencies of the substantive public theorems and
checks their direct application to Euclidean Jordan curves and ambient affine
isometry equivalences. It is built separately from the public aggregate.
-/

open Set
open Puzzling139335.LoopVariation

#print axioms Puzzling139335.LoopVariation.bddAbove_cycleScoresOn_Icc
#print axioms Puzzling139335.LoopVariation.loop_partition_estimates_of_continuousOn
#print axioms Puzzling139335.LoopVariation.loopVariation_partition_bounds
#print axioms Puzzling139335.LoopVariation.loopVariationOn_eq_of_isometry_image_eq
#print axioms Puzzling139335.LoopVariation.loopVariation_image_isometry
#print axioms Puzzling139335.LoopVariation.loopVariation_cutPair_bounds
#print axioms Puzzling139335.LoopVariation.abs_arcVariation_sub_le_of_common_arc_isometry
#print axioms Puzzling139335.LoopVariation.common_cut_excludes_three_arc_extension
#print axioms Puzzling139335.common_cut_endpoints_antipodal
#print axioms Puzzling139335.JordanCrosscut.endpoints_antipodal_of_congruent_sides

example {C A B : Set (EuclideanSpace ℝ (Fin 2))} {p q : EuclideanSpace ℝ (Fin 2)}
    {ε : ℝ} (hcut : Schoenflies.IsCutPair C p q A B) (hε : 0 < ε) :
    |loopVariation ε C - (arcVariation ε A + arcVariation ε B)| ≤ 2 * ε := by
  have h := loopVariation_cutPair_bounds hcut hε
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

example {C : Set (EuclideanSpace ℝ (Fin 2))} (hC : Schoenflies.IsJordanCurve C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2)) (ε : ℝ) :
    loopVariation ε (e '' C) = loopVariation ε C :=
  loopVariation_image_isometry ε hC e.isometry
