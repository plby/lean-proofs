import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Straight boundary arcs with their actual subspace topology

A nondegenerate closed line segment is parametrized homeomorphically by
the unit interval. This will identify each of the six actual positive
component intersections with an arc after the hexagon charts are glued.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E] [T2Space E]

/-- The affine interval parametrization, with the inherited topology on
the literal closed segment. -/
def segmentIntervalHomeomorph (a b : E) (hab : a ≠ b) :
    unitInterval ≃ₜ segment ℝ a b :=
  ((Path.segment a b).continuous.isClosedEmbedding
    (Path.segment_injective_of_ne hab)).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (Path.range_segment a b))

@[simp] theorem segmentIntervalHomeomorph_apply (a b : E) (hab : a ≠ b)
    (t : unitInterval) :
    (segmentIntervalHomeomorph a b hab t : E) =
      (1 - (t : ℝ)) • a + (t : ℝ) • b := by
  change AffineMap.lineMap a b (t : ℝ) = _
  exact AffineMap.lineMap_apply_module _ _ _

@[simp] theorem segmentIntervalHomeomorph_zero (a b : E) (hab : a ≠ b) :
    (segmentIntervalHomeomorph a b hab 0 : E) = a := by
  simp

@[simp] theorem segmentIntervalHomeomorph_one (a b : E) (hab : a ≠ b) :
    (segmentIntervalHomeomorph a b hab 1 : E) = b := by
  simp

end Wikipedia.HopfProblem.CuspHoneycombHexagon
