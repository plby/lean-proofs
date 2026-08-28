import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondPathComparison
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondHomotopyMap

/-!
# Relative representatives and homotopy reflection for the second loop map

The original conjugation homeomorphism transfers the antipodal path comparison
to based loops. This uses the already defined rotation-loop map exactly.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.SecondPaths

open AnticommutingStructures NoExoticSixSphere

variable {n : ℕ} {a : ComplexStructures.Space n}
variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

include I

theorem exists_loopMap_representative (J : Space a) (hd : finrank ℝ B < n)
    (p : C(M, Path a a)) :
    ∃ P : C(M, Space a), Nonempty (p.HomotopyRel ((loopMap J).comp P)
      (p ⁻¹' range (loopMap J))) := by
  let e := loopHomeomorph J
  let q := (toContinuousMap e.symm).comp p
  obtain ⟨P, ⟨G⟩⟩ := exists_pathMap_representative (I := I) a hd q
  have hleft : (toContinuousMap e).comp q = p := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (p x)
  have hright : (toContinuousMap e).comp ((pathMap a).comp P) = (loopMap J).comp P := rfl
  have hsets : q ⁻¹' range (pathMap a) = p ⁻¹' range (loopMap J) := by
    ext x
    constructor
    · rintro ⟨K, hK⟩
      refine ⟨K, ?_⟩
      exact (congrArg e hK).trans (e.apply_symm_apply (p x))
    · rintro ⟨K, hK⟩
      refine ⟨K, ?_⟩
      exact (e.symm_apply_apply (pathMap a K)).symm.trans (congrArg e.symm hK)
  have G' := (G.compContinuousMap (toContinuousMap e)).cast hleft hright
  rw [hsets] at G'
  exact ⟨P, ⟨G'⟩⟩

theorem loopMap_homotopicRel_iff (J : Space a) (hd : finrank ℝ B + 1 < n)
    (f g : C(M, Space a)) (S : Set M) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty (((loopMap J).comp f).HomotopyRel ((loopMap J).comp g) S) :=
  (pathMap_homotopicRel_iff (I := I) a hd f g S).trans
    (pathMap_homotopicRel_iff_loopMap J f g S)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.SecondPaths
