import Wikipedia.SmoothSixDPoincare.MorseCellHomologySequence
import Wikipedia.SmoothSixDPoincare.SphereLinearDiffeomorph
import Wikipedia.HopfProblem.SphereHomologyVanishing

/-!
# Downward homology propagation through a nonmatching handle index

The actual attaching sphere has no homology outside its own dimension.
The native Morse exact sequence therefore transports vanishing downward
through a handle whose index is not one more than the homology degree.
-/

noncomputable section

open Set Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology Wikipedia.HopfProblem.SphereHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

omit [T2Space M] in
theorem attachingHomology_subsingleton_of_index (k : ℕ) (hk : k ≠ 0)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    (hne : Module.finrank ℝ d.chart.NegativeCoordinates ≠ k + 1) :
    Subsingleton (SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) k) := by
  let n := Module.finrank ℝ d.chart.NegativeCoordinates - 2
  have hn : Module.finrank ℝ d.chart.NegativeCoordinates = (n + 1) + 1 := by
    dsimp [n]
    omega
  let : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = (n + 1) + 1) := ⟨hn⟩
  let : Subsingleton (SingularHomology (UnitSphere (n + 1)) k) :=
    unitSphere_homology_subsingleton n k hk (by omega)
  exact (homeomorphHomologyEquiv
    (SphereCoordinates.standardParametrization
      d.chart.NegativeCoordinates (n + 1)).symm.toHomeomorph k).injective.subsingleton

theorem lowerHomology_subsingleton_of_upper_and_index (hf : Continuous f) (k : ℕ) (hk : k ≠ 0)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    (hne : Module.finrank ℝ d.chart.NegativeCoordinates ≠ k + 1)
    [Subsingleton (SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} k)] :
    Subsingleton (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} k) := by
  let := d.attachingHomology_subsingleton_of_index k hk hindex hne
  exact d.lowerHomology_subsingleton_of_upper_and_sphere hf k hk

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
