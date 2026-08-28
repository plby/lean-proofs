import Wikipedia.NoExoticSixSphere.JamesComparisonDiskLifting
import Wikipedia.NoExoticSixSphere.HomotopyPullbackNativeComparison
import Wikipedia.NoExoticSixSphere.JamesSphereOrderedLoopComparison

/-!
# Finite-domain homotopy reflection for the original James comparison

The native isomorphisms of the original comparison now reflect actual
homotopies from finite-cell domains. The original Morse construction
applies this to compact smooth manifolds and, in particular, the literal
product of three-spheres. The coordinate-ordered comparison has the same
reflection property by canceling its actual loop-space homeomorphism.
-/

noncomputable section

open scoped Topology ContDiff Manifold
open Wikipedia.HopfProblem

namespace NoExoticSixSphere.JamesSphere.HomotopyComparison

open DegreeCollapse AttachingSquare

theorem comparison_finiteCell_homotopic_reflect (n : ℕ) (hn : 2 ≤ n)
    {Z : Type} [TopologicalSpace Z] {d : ℕ} (hZ : FiniteCells.Built d Z)
    (u v : C(Z, WordHomology.Words n))
    (H : ((loopComparison n).comp u).Homotopic ((loopComparison n).comp v)) :
    u.Homotopic v := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  let := JamesSphere.simplyConnectedSpace k
  exact HomotopyPullbackDiagonal.finiteCell_homotopic_reflect_of_native_bijective
    (loopComparison (k + 2)) (fun m x ↦ comparison_pi_bijective k m x) hZ u v H

theorem comparison_compactManifold_homotopic_reflect (n : ℕ) (hn : 2 ≤ n)
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] (u v : C(M, WordHomology.Words n))
    (H : ((loopComparison n).comp u).Homotopic ((loopComparison n).comp v)) :
    u.Homotopic v :=
  comparison_finiteCell_homotopic_reflect n hn
    (MorseCells.built_of_compact_smooth_manifold (E := E)) u v H

theorem comparison_threeSphereProduct_homotopic_reflect (n : ℕ) (hn : 2 ≤ n)
    (u v : C(Sphere 3 × Sphere 3, WordHomology.Words n))
    (H : ((loopComparison n).comp u).Homotopic ((loopComparison n).comp v)) :
    u.Homotopic v := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Sphere 3) := inferInstance
  let : IsManifold (𝓡 3) ∞ (Sphere 3) := inferInstance
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
      (Sphere 3 × Sphere 3) := prodChartedSpace _ _ _ _
  let : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) ∞
      (Sphere 3 × Sphere 3) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓡 3) (I' := 𝓡 3) (Sphere 3) (Sphere 3)
  exact comparison_compactManifold_homotopic_reflect n hn
    (E := EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) u v H

theorem comparison_homotopic_of_orderedComparison (n : ℕ)
    {Z : Type} [TopologicalSpace Z] (u v : C(Z, WordHomology.Words n))
    (H : ((orderedLoopComparison n).comp u).Homotopic
      ((orderedLoopComparison n).comp v)) :
    ((loopComparison n).comp u).Homotopic ((loopComparison n).comp v) := by
  let e := reorderPathsHomeomorph n
  let back : C(Path (spherePole (n + 1)) (spherePole (n + 1)),
      Path (spherePole (n + 1)) (spherePole (n + 1))) := e.symm
  have hcancel (w : C(Z, WordHomology.Words n)) :
      back.comp ((orderedLoopComparison n).comp w) =
        (loopComparison n).comp w := by
    apply ContinuousMap.ext
    intro z
    exact e.symm_apply_apply (loopComparison n (w z))
  have h := (ContinuousMap.Homotopic.refl back).comp H
  rw [hcancel u, hcancel v] at h
  exact h

theorem orderedComparison_threeSphereProduct_homotopic_reflect (n : ℕ) (hn : 2 ≤ n)
    (u v : C(Sphere 3 × Sphere 3, WordHomology.Words n))
    (H : ((orderedLoopComparison n).comp u).Homotopic
      ((orderedLoopComparison n).comp v)) : u.Homotopic v :=
  comparison_threeSphereProduct_homotopic_reflect n hn u v
    (comparison_homotopic_of_orderedComparison n u v H)

end NoExoticSixSphere.JamesSphere.HomotopyComparison
