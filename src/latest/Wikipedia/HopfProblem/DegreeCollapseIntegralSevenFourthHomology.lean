import Wikipedia.HopfProblem.DegreeCollapseIntegralManifoldDuality
import Wikipedia.HopfProblem.DegreeCollapseRelativeIntegralCohomology

/-!
# Fourth homology vanishing for the required closed seven-manifold data

The original integer universal-coefficient evaluation gives zero third
cohomology when second homology vanishes and third homology is finite.
The now proved original integral cap duality then gives zero fourth
homology for a compact simply connected smooth seven-manifold. This
does not apply a closed-manifold theorem to a filling with boundary.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralSevenDuality

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree

variable (X : Type) [TopologicalSpace X]

/-- The actual absolute integral cohomology vanishes under the stated adjacent homology data. -/
theorem cohomology_succ_subsingleton (k : ℕ)
    [Subsingleton (SingularHomology X k)] [Finite (SingularHomology X (k + 1))] :
    Subsingleton (SingularCohomology X (k + 1)) := by
  let (j : ℕ) : Module.Free ℤ ((singularComplex X).X j) :=
    Module.Free.of_basis (chainBasis X j)
  let : Subsingleton ((singularComplex X).homology k) :=
    inferInstanceAs (Subsingleton (SingularHomology X k))
  let : Finite ((singularComplex X).homology (k + 1)) :=
    inferInstanceAs (Finite (SingularHomology X (k + 1)))
  exact RelativeIntegralCohomology.cohomology_succ_subsingleton (singularComplex X) k

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 7)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]

include E in
/-- Finite third homology may have torsion; no freeness premise is needed here. -/
theorem fourth_homology_subsingleton
    [Subsingleton (SingularHomology M 2)] [Finite (SingularHomology M 3)] :
    Subsingleton (SingularHomology M 4) := by
  let : Subsingleton (SingularCohomology M 3) := cohomology_succ_subsingleton M 2
  exact (IntegralCompactSupportCap.absoluteDualityMap_bijective (E := E) 4 M 3 4 rfl).2.subsingleton

end Wikipedia.HopfProblem.DegreeCollapse.IntegralSevenDuality
