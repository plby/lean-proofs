import Wikipedia.HopfProblem.CuspCoinvariantExtensionPhaseSmooth
import Wikipedia.HopfProblem.CuspCoinvariantExtensionPhaseCollarBasic

/-!
# Original-atlas smoothness on the actual outer cusp collar

The collar-adjusted unit phase equals the original punctured phase on an
actual open annulus.  The original open-submanifold inclusion transfers
the proved punctured smoothness to ambient smoothness on that annulus.
The outer closed collar is invariant under the native flow and has this
open annulus as a neighborhood, supplying exact relative-smoothing data.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase

open CuspUniformization SpecialPeriods.CuspFamily ThreefoldHomologyFinitenessCusp

local notation "I₃" => modelWithCornersSelf ℝ (ToricCharts.CoordinateSpace 3)
local notation "I₁" => modelWithCornersSelf ℝ ℂ

/-- The unit phase is smooth on this open subset in the existing native
complex-derived real atlas, without asserting smoothness across the core. -/
theorem capPhase_contMDiffOn_outer (D : Data) (bound : ℝ) (E : CollarExtension D bound) :
    letI := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift
    ContMDiffOn I₃ I₁ ∞ (capPhase D bound E) (outerCollar D bound E) := by
  let := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos
    D.radius_lt_one D.holomorphic D.smallDrift
  have hincl : ContMDiff I₃ I₃ ∞
      (TopologicalSpace.Opens.inclusion (outerCollar_le_punctured D bound E)) :=
    contMDiff_inclusion (outerCollar_le_punctured D bound E)
  have hp : ContMDiff I₃ I₁ ∞
      (fun q : outerCollar D bound E => capPhase D bound E q.val) :=
    ((puncturedPhase_contMDiff D).comp hincl).congr fun q =>
      capPhase_outer D bound E
        (TopologicalSpace.Opens.inclusion (outerCollar_le_punctured D bound E) q)
        q.property.le
  intro q hq
  exact (contMDiffAt_subtype_iff.mp
    (hp.contMDiffAt (x := ⟨q, hq⟩))).contMDiffWithinAt

end Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase
