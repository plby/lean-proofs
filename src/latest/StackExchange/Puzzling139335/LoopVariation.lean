import StackExchange.Puzzling139335.LoopVariation.Finiteness
import StackExchange.Puzzling139335.LoopVariation.Cuts
import StackExchange.Puzzling139335.LoopVariation.Cuts.GeometricPartition
import StackExchange.Puzzling139335.LoopVariation.Invariance
import StackExchange.Puzzling139335.LoopVariation.Geometric.ArcCuts
import StackExchange.Puzzling139335.LoopVariation.Geometric.CutPairs
import StackExchange.Puzzling139335.LoopVariation.Geometric.ExtensionContradiction

/-!
# Finite-resolution variation of arbitrary Jordan curves

This module defines cyclic variation by an actual supremum of finite cyclic
chord scores and proves its finiteness at every positive resolution. Exact
parametrization independence follows by rotating a simple loop to a common
base point, using a circle chart to identify the two orientations, and mapping
the concrete finite lists. No variation property is postulated.

A continuous closed curve cut into `m` parameter arcs satisfies
`sum arcVariations ≤ loopVariation ≤ sum arcVariations + m * ε`.
The geometric wrappers express the two-arc case using `Schoenflies.IsCutPair`
and prove exact invariance under ambient isometries. Consequently, congruent
Jordan curves with one common interface have remaining-arc variations within
`2 * ε` of each other, which excludes an isometric copy with nondegenerate arcs
left over on both sides. This is the metric part of the antipodal-endpoint
argument; the separate cyclic-order containment theorem supplies the topology.

All finiteness statements use only compact-interval continuity and `ε > 0`.
They require no rectifiability, finite ordinary perimeter, or boundary measure
assumption.
-/

open Set

namespace Puzzling139335.LoopVariation

noncomputable section

/-- Congruent Jordan-loop images have equal cyclic variation in arbitrary
metric codomains and under independently chosen parametrizations. -/
theorem loopVariationOn_eq_of_isometry_image_eq
    {E F : Type*} [MetricSpace E] [MetricSpace F]
    {f : ℝ → E} {g : ℝ → F} {a b c d : ℝ} (ε : ℝ)
    {e : E → F} (he : Isometry e) (hab : a < b) (hcd : c < d)
    (hfcont : ContinuousOn f (Icc a b)) (hfclose : f a = f b)
    (hfi : InjOn f (Ico a b))
    (hgcont : ContinuousOn g (Icc c d)) (hgclose : g c = g d)
    (hgi : InjOn g (Ico c d))
    (himage : e '' (f '' Icc a b) = g '' Icc c d) :
    loopVariationOn ε f (Icc a b) = loopVariationOn ε g (Icc c d) := by
  have hecont : ContinuousOn (e ∘ f) (Icc a b) :=
    he.continuous.comp_continuousOn hfcont
  have heinj : InjOn (e ∘ f) (Ico a b) := by
    intro x hx y hy hxy
    exact hfi hx hy (he.injective hxy)
  have heimage : (e ∘ f) '' Icc a b = g '' Icc c d := by
    simpa only [Set.image_image, Function.comp_def] using himage
  rw [← loopVariationOn_comp_isometry he ε f (Icc a b)]
  exact loopVariationOn_eq_of_loop_image_eq ε hab hcd hecont
    (congrArg e hfclose) heinj hgcont hgclose hgi heimage

end

end Puzzling139335.LoopVariation
