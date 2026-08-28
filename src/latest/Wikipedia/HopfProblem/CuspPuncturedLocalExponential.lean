import Wikipedia.HopfProblem.CuspPuncturedBasic
import Wikipedia.HopfProblem.CuspPuncturedExponentialCharts
import Wikipedia.HopfProblem.CuspPuncturedCovering
import Wikipedia.HopfProblem.ToricTorusChart

/-!
# Local biholomorphisms into the punctured cusp

The logarithmic exponential maps into the genuine toric manifold. Its local
analytic inverses are obtained by composing the dense-torus chart with the
local inverses of the three coordinate exponentials.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricSpace CuspQuotient

theorem torusPoint_isLocalDiffeomorphAt {z : CoordinateSpace 3} (hz : z ∈ torus) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω torusPoint z := by
  refine ⟨{
    toPartialEquiv := torusChart.symm.toPartialEquiv
    open_source := torusChart.open_target
    open_target := torusChart.open_source
    contMDiffOn_toFun := torusPoint_holomorphic
    contMDiffOn_invFun := torusCoordinates_holomorphic }, hz, ?_⟩
  intro w _
  rfl

theorem totalExponentialPoint_isLocalDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω totalExponentialPoint := by
  intro p
  change IsLocalDiffeomorphAt (modelWithCornersSelf ℂ LogModel)
    (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (torusPoint ∘ totalExponentialCoordinates) p
  exact (totalExponentialCoordinates_isLocalDiffeomorph p).comp
    (K := modelWithCornersSelf ℂ (CoordinateSpace 3)) (P := Space)
    (torusPoint_isLocalDiffeomorphAt (totalExponentialCoordinates_mem_torus p))

theorem totalExponentialLift_isLocalDiffeomorph (ε : ℝ) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (totalExponentialLift ε) := by
  exact isLocalDiffeomorph_restrictOpens (modelWithCornersSelf ℂ LogModel)
    (modelWithCornersSelf ℂ (CoordinateSpace 3)) totalExponentialPoint_isLocalDiffeomorph
    (logDomain ε) (tubeOpen (disc ε))
    (fun p hp => (totalExponentialLift ε ⟨p, hp⟩).prop)

theorem puncturedExponential_isLocalDiffeomorph (ε : ℝ) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (puncturedExponential ε) := by
  exact isLocalDiffeomorph_codRestrictOpens (modelWithCornersSelf ℂ LogModel)
    (modelWithCornersSelf ℂ (CoordinateSpace 3)) (totalExponentialLift_isLocalDiffeomorph ε)
    (puncturedTubeOpen ε) (fun p => (puncturedExponential ε p).prop)

end Wikipedia.HopfProblem.CuspUniformization
