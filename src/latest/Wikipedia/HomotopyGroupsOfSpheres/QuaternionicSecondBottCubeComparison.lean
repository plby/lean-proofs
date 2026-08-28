import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondLoopComparison
import Wikipedia.NoExoticSixSphere.CubeSphereRetract
import Wikipedia.NoExoticSixSphere.RetractionHomotopyTransfer

/-!
# The second Bott comparison for native cube-parameter families

Transfer relative representatives and homotopy reflection from spheres to
their cube retracts, preserving the parameter-dimension bounds.
-/

open Set
open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.SecondPaths

open AnticommutingStructures NoExoticSixSphere

variable {n : ℕ} {a : ComplexStructures.Space n}

theorem exists_cube_loopMap_representative (d : ℕ) (J : Space a) (hd : d < n)
    (p : C((Fin d → unitInterval), Path a a)) :
    ∃ P : C((Fin d → unitInterval), Space a),
      Nonempty (p.HomotopyRel ((loopMap J).comp P) (p ⁻¹' range (loopMap J))) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = d + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  obtain ⟨e, r, hre⟩ := CubeSphereRetract.exists_retract d
  apply RetractionHomotopyTransfer.representatives e r hre (loopMap J) _ p
  intro P
  exact exists_loopMap_representative (I := 𝓡 d) J
    (by simpa only [finrank_euclideanSpace_fin] using hd) P

theorem cube_loopMap_homotopicRel_iff (d : ℕ) (J : Space a) (hd : d + 1 < n)
    (f g : C((Fin d → unitInterval), Space a)) (S : Set (Fin d → unitInterval)) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty (((loopMap J).comp f).HomotopyRel ((loopMap J).comp g) S) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨F.compContinuousMap (loopMap J)⟩
  · rintro ⟨F⟩
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = d + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    obtain ⟨e, r, hre⟩ := CubeSphereRetract.exists_retract d
    apply RetractionHomotopyTransfer.reflection e r hre (loopMap J) _ f g S F
    intro f' g' S' hF
    exact (loopMap_homotopicRel_iff (I := 𝓡 d) J
      (by simpa only [finrank_euclideanSpace_fin] using hd) f' g' S').mpr hF

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.SecondPaths
