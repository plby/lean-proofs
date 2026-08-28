import Wikipedia.NoExoticSixSphere.NativeEquivalenceDiskLifting
import Wikipedia.NoExoticSixSphere.JamesSphereHomotopyComparison
import Wikipedia.HopfProblem.DegreeCollapseMorseFiniteCells

/-!
# Exact disk and finite-domain lifts for the original James comparison

All native homotopy maps of the original comparison are already proved
bijective, including degree zero and every source basepoint. The new
relative lifting theorem therefore supplies full prescribed disk-side
homotopies in every finite dimension. Existing finite-cell assembly and
the actual Morse cell construction give lifts of maps from compact smooth
manifolds. Homotopy reflection on those domains is not asserted here.
-/

noncomputable section

open scoped Topology ContDiff Manifold
open Wikipedia.HopfProblem

namespace NoExoticSixSphere.JamesSphere.HomotopyComparison

open DegreeCollapse

theorem comparison_relativeDiskLifting (n : ℕ) (hn : 2 ≤ n) (d : ℕ) :
    FiniteCells.RelativeDiskLifting (loopComparison n) d := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  let := JamesSphere.simplyConnectedSpace k
  exact RelativeDiskLifting.relativeDiskLifting_of_native_bijective (loopComparison (k + 2))
    (fun m x ↦ comparison_pi_bijective k m x) d

theorem comparison_finiteCell_mapsLift (n : ℕ) (hn : 2 ≤ n)
    {Z : Type} [TopologicalSpace Z] {d : ℕ} (hZ : FiniteCells.Built d Z) :
    FiniteCells.MapsLift (loopComparison n) Z :=
  FiniteCells.mapsLift_of_built (loopComparison n) (comparison_relativeDiskLifting n hn d) hZ

theorem comparison_compactManifold_mapsLift (n : ℕ) (hn : 2 ≤ n)
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] : FiniteCells.MapsLift (loopComparison n) M :=
  comparison_finiteCell_mapsLift n hn (MorseCells.built_of_compact_smooth_manifold (E := E))

theorem comparison_threeSphereProduct_mapsLift (n : ℕ) (hn : 2 ≤ n) :
    FiniteCells.MapsLift (loopComparison n) (Sphere 3 × Sphere 3) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Sphere 3) := inferInstance
  let : IsManifold (𝓡 3) ∞ (Sphere 3) := inferInstance
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
      (Sphere 3 × Sphere 3) := prodChartedSpace _ _ _ _
  let : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) ∞
      (Sphere 3 × Sphere 3) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓡 3) (I' := 𝓡 3) (Sphere 3) (Sphere 3)
  exact comparison_compactManifold_mapsLift n hn
    (E := EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))

end NoExoticSixSphere.JamesSphere.HomotopyComparison
