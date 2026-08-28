import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumPathHomotopyComparison
import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumPathFamily
import Wikipedia.NoExoticSixSphere.PathFamilyCurrying

/-!
# Relative representatives and homotopy reflection for the actual balanced path map

Currying transfers the proved path-family deformation and comparison to
Mathlib's native compact-open path space, using the original rotation map.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open QuaternionicSymmetricMatrices NoExoticSixSphere QuaternionicSymmetricMatrices.Polygon

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem uncurry_pathMap_comp (n : ℕ) (P : C(X, Space n)) :
    PathFamilies.uncurry ((pathMap n).comp P) = rotationPathFamily P := by
  apply ContinuousMap.ext
  intro z
  rfl

theorem mem_pathMap_range_iff (n : ℕ)
    (p : Path specialIdentity (antipode n)) :
    p ∈ range (pathMap n) ↔
      ∃ P : Space n, ∀ u : unitInterval, p u = rotation P ((u : ℝ) * Real.pi) := by
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P, fun _ ↦ rfl⟩
  · rintro ⟨P, hP⟩
    refine ⟨P, Path.ext ?_⟩
    funext u
    exact (hP u).symm

theorem minimumPathParameters_eq_preimage (n : ℕ)
    (p : C(X, Path specialIdentity (antipode n))) :
    minimumPathParameters (PathFamilies.uncurry p) = p ⁻¹' range (pathMap n) := by
  ext x
  exact (mem_pathMap_range_iff n (p x)).symm

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

include I

theorem exists_pathMap_representative (n : ℕ) (hd : finrank ℝ B < n)
    (p : C(M, Path specialIdentity (antipode n))) :
    ∃ P : C(M, Space n), Nonempty (p.HomotopyRel ((pathMap n).comp P)
      (p ⁻¹' range (pathMap n))) := by
  obtain ⟨P, ⟨G⟩⟩ := exists_homotopy_to_minimum_path_family (I := I)
    n hd
    (PathFamilies.uncurry p) (PathFamilies.uncurry_zero p) (PathFamilies.uncurry_one p)
  rw [minimumPathParameters_eq_preimage n p] at G
  exact ⟨P, ⟨PathFamilies.curryHomotopy (G.cast rfl (uncurry_pathMap_comp n P).symm)⟩⟩

theorem pathMap_homotopicRel_iff (n : ℕ) (hd : finrank ℝ B + 1 < n)
    (f g : C(M, Space n)) (S : Set M) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty (((pathMap n).comp f).HomotopyRel ((pathMap n).comp g) S) := by
  have h := rotationHomotopicRel_iff_paths (I := I) n hd f g S
  rw [← uncurry_pathMap_comp n f, ← uncurry_pathMap_comp n g] at h
  exact h.trans (PathFamilies.homotopicRel_iff_uncurry
    ((pathMap n).comp f) ((pathMap n).comp g) S).symm

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
