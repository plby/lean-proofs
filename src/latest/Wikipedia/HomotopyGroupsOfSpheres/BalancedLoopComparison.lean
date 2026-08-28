import Wikipedia.HomotopyGroupsOfSpheres.BalancedPathComparison
import Wikipedia.HomotopyGroupsOfSpheres.BalancedHomotopyMap

/-!
# Relative representatives and homotopy reflection for the balanced loop map

The original reference congruence homeomorphism transfers the antipodal path comparison
to based loops. This uses the already defined rotation-loop map exactly.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open QuaternionicSymmetricMatrices NoExoticSixSphere

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

include I

theorem exists_loopMap_representative (n : ℕ) (hd : finrank ℝ B < n)
    (p : C(M, Path (specialIdentity : SpecialSpace (Index n)) specialIdentity)) :
    ∃ P : C(M, Space n), Nonempty (p.HomotopyRel ((loopMap n).comp P)
      (p ⁻¹' range (loopMap n))) := by
  let e := loopHomeomorph n
  let q := (toContinuousMap e.symm).comp p
  obtain ⟨P, ⟨G⟩⟩ := exists_pathMap_representative (I := I) n hd q
  have hleft : (toContinuousMap e).comp q = p := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (p x)
  have hright : (toContinuousMap e).comp ((pathMap n).comp P) = (loopMap n).comp P := rfl
  have hsets : q ⁻¹' range (pathMap n) = p ⁻¹' range (loopMap n) := by
    ext x
    constructor
    · rintro ⟨K, hK⟩
      refine ⟨K, ?_⟩
      exact (congrArg e hK).trans (e.apply_symm_apply (p x))
    · rintro ⟨K, hK⟩
      refine ⟨K, ?_⟩
      exact (e.symm_apply_apply (pathMap n K)).symm.trans (congrArg e.symm hK)
  have G' := (G.compContinuousMap (toContinuousMap e)).cast hleft hright
  rw [hsets] at G'
  exact ⟨P, ⟨G'⟩⟩

theorem loopMap_homotopicRel_iff (n : ℕ) (hd : finrank ℝ B + 1 < n)
    (f g : C(M, Space n)) (S : Set M) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty (((loopMap n).comp f).HomotopyRel ((loopMap n).comp g) S) :=
  (pathMap_homotopicRel_iff (I := I) n hd f g S).trans
    (pathMap_homotopicRel_iff_loopMap n f g S)

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
