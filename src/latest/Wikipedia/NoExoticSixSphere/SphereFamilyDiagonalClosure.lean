import Wikipedia.NoExoticSixSphere.SphereFamilyCoordinateSmoothness
import Wikipedia.NoExoticSixSphere.GenericFamilyLocalCurve
import Wikipedia.NoExoticSixSphere.LocalInverse

/-!
# Intrinsic immersions exclude diagonal accumulation of sphere-family double points

Genuine local coordinates and a smooth representative reduce to the checked
Euclidean track argument. This applies at arbitrary times, including endpoints.
It does not assume that neighboring slices are globally injective.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization ManifoldAffineSphereFamily FamilyEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M]

theorem diagonal_not_mem_closure (g : ℝ → Sphere 3 → M)
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))
    (q : ℝ × Sphere 3) (hi : Injective (mfderiv (𝓡 3) (𝓡 n) (g q.1) q.2)) :
    (q.1, (q.2, q.2)) ∉ closure (doublePoints g) := by
  let s : SourceChart := modelChartPartialDiffeomorph (I := 𝓡 3) q.2
  let c : TargetChart n M := modelChartPartialDiffeomorph (I := 𝓡 n) (g q.1 q.2)
  have hs : q.2 ∈ s.source := mem_extChartAt_source q.2
  have hc : g q.1 q.2 ∈ c.source := mem_extChartAt_source (g q.1 q.2)
  have hqi := (injective_coordinate_spatial_iff g hg s c q hs hc).mpr hi
  have hqU := mem_coordinateRegion_at_source g hg s c q hs hc
  have hnot := diagonal_not_mem_closure_doublePoints_of_local
    (coordinateFamily g s c) (coordinateRegion g hg s c).isOpen
      (contDiffOn_coordinateFamily g hg s c) (q.1, s q.2) hqU hqi
  have hqT : (q.1, (q.2, q.2)) ∈ (pairCoordinates g hg.continuous s c).source :=
    (mem_pairCoordinates_source g hg.continuous s c _).mpr ⟨hs, hs, hc, hc⟩
  intro hcl
  exact hnot ((isImage_closedDoublePoints g hg.continuous s c hqT).mpr hcl)

theorem singular_of_diagonal_mem_closure (g : ℝ → Sphere 3 → M)
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))
    (q : ℝ × Sphere 3) (hq : (q.1, (q.2, q.2)) ∈ closure (doublePoints g)) :
    ¬ Injective (mfderiv (𝓡 3) (𝓡 n) (g q.1) q.2) :=
  fun hi ↦ diagonal_not_mem_closure g hg q hi hq

end NoExoticSixSphere.SphereFamily
