import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondMinimumPathHomotopyComparison
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondPathFamily
import Wikipedia.NoExoticSixSphere.PathFamilyCurrying

/-!
# Relative representatives and homotopy reflection for the actual second path map

Currying transfers the proved path-family deformation and comparison to
Mathlib's native compact-open path space, using the original rotation map.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.SecondPaths

open AnticommutingStructures NoExoticSixSphere ComplexStructurePolygon

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem uncurry_pathMap_comp (a : ComplexStructures.Space n) (P : C(X, Space a)) :
    PathFamilies.uncurry ((pathMap a).comp P) = rotationPathFamily P := by
  apply ContinuousMap.ext
  intro z
  rfl

theorem mem_pathMap_range_iff (a : ComplexStructures.Space n)
    (p : Path a (ComplexStructures.negative a)) :
    p ∈ range (pathMap a) ↔
      ∃ P : Space a, ∀ u : unitInterval, p u = rotation P ((u : ℝ) * Real.pi) := by
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P, fun _ ↦ rfl⟩
  · rintro ⟨P, hP⟩
    refine ⟨P, Path.ext ?_⟩
    funext u
    exact (hP u).symm

theorem minimumPathParameters_eq_preimage (a : ComplexStructures.Space n)
    (p : C(X, Path a (ComplexStructures.negative a))) :
    minimumPathParameters (PathFamilies.uncurry p) a = p ⁻¹' range (pathMap a) := by
  ext x
  exact (mem_pathMap_range_iff a (p x)).symm

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

include I

theorem exists_pathMap_representative (a : ComplexStructures.Space n) (hd : finrank ℝ B < n)
    (p : C(M, Path a (ComplexStructures.negative a))) :
    ∃ P : C(M, Space a), Nonempty (p.HomotopyRel ((pathMap a).comp P)
      (p ⁻¹' range (pathMap a))) := by
  obtain ⟨P, ⟨G⟩⟩ := exists_homotopy_to_minimum_path_family (I := I)
    a (ComplexStructures.negative a) (negative_antipodal a) hd
    (PathFamilies.uncurry p) (PathFamilies.uncurry_zero p) (PathFamilies.uncurry_one p)
  rw [minimumPathParameters_eq_preimage a p] at G
  exact ⟨P, ⟨PathFamilies.curryHomotopy (G.cast rfl (uncurry_pathMap_comp a P).symm)⟩⟩

theorem pathMap_homotopicRel_iff (a : ComplexStructures.Space n) (hd : finrank ℝ B + 1 < n)
    (f g : C(M, Space a)) (S : Set M) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty (((pathMap a).comp f).HomotopyRel ((pathMap a).comp g) S) := by
  have h := rotationHomotopicRel_iff_paths (I := I) a hd f g S
  rw [← uncurry_pathMap_comp a f, ← uncurry_pathMap_comp a g] at h
  exact h.trans (PathFamilies.homotopicRel_iff_uncurry
    ((pathMap a).comp f) ((pathMap a).comp g) S).symm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.SecondPaths
