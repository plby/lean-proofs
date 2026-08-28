import Wikipedia.HopfProblem.PeriodFamily
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Topology of the original period-family total space and its opens

For a holomorphic period map over an open subset of `ℂ`, the actual total
space has the existing topology on `U × RealTorus₄`.  The compactness and
separation properties below use this topology and the inherited topology on
every actual open subset.  No choice or replacement of manifold atlas is made.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Geometry

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The original period-family total space is Hausdorff. -/
theorem totalSpace_t2 : T2Space P.TotalSpace := inferInstance

/-- The original total space has its inherited second-countable topology. -/
theorem totalSpace_secondCountable : SecondCountableTopology P.TotalSpace := inferInstance

/-- Local compactness of the original total space follows from the open
complex base and the actual compact real torus. -/
theorem totalSpace_locallyCompact : LocallyCompactSpace P.TotalSpace := by
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  infer_instance

/-- The original total space is sigma-compact, with no compactness
assumption on the base open. -/
theorem totalSpace_sigmaCompact : SigmaCompactSpace P.TotalSpace := by
  let := totalSpace_locallyCompact P
  infer_instance

variable (Ω : Opens P.TotalSpace)

/-- Every actual total-space open is Hausdorff in the inherited topology. -/
theorem open_t2 : T2Space Ω := inferInstance

/-- Every actual total-space open is second countable in the inherited topology. -/
theorem open_secondCountable : SecondCountableTopology Ω := inferInstance

/-- Local compactness holds for every actual open subset of the total space. -/
theorem open_locallyCompact : LocallyCompactSpace Ω := by
  let := totalSpace_locallyCompact P
  exact Ω.isOpen.locallyCompactSpace

/-- Every actual total-space open, including a full inverse image of a base
open, is sigma-compact in its original inherited topology. -/
theorem open_sigmaCompact : SigmaCompactSpace Ω := by
  let := open_locallyCompact P Ω
  infer_instance

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Geometry
