import Wikipedia.HomotopyGroupsOfSpheres.BalancedLoopComparison
import Wikipedia.NoExoticSixSphere.CubeSphereRetract
import Wikipedia.NoExoticSixSphere.RetractionHomotopyTransfer

/-!
# The balanced Bott comparison for native cube-parameter families

Transfer relative representatives and homotopy reflection from spheres to
their cube retracts, preserving the parameter-dimension bounds.
-/

open Set
open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open QuaternionicSymmetricMatrices NoExoticSixSphere


theorem exists_cube_loopMap_representative (d : ℕ) (n : ℕ) (hd : d < n)
    (p : C((Fin d → unitInterval),
      Path (specialIdentity : SpecialSpace (Index n)) specialIdentity)) :
    ∃ P : C((Fin d → unitInterval), Space n),
      Nonempty (p.HomotopyRel ((loopMap n).comp P) (p ⁻¹' range (loopMap n))) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = d + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  obtain ⟨e, r, hre⟩ := CubeSphereRetract.exists_retract d
  apply RetractionHomotopyTransfer.representatives e r hre (loopMap n) _ p
  intro P
  exact exists_loopMap_representative (I := 𝓡 d) n
    (by simpa only [finrank_euclideanSpace_fin] using hd) P

theorem cube_loopMap_homotopicRel_iff (d : ℕ) (n : ℕ) (hd : d + 1 < n)
    (f g : C((Fin d → unitInterval), Space n)) (S : Set (Fin d → unitInterval)) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty (((loopMap n).comp f).HomotopyRel ((loopMap n).comp g) S) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨F.compContinuousMap (loopMap n)⟩
  · rintro ⟨F⟩
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = d + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    obtain ⟨e, r, hre⟩ := CubeSphereRetract.exists_retract d
    apply RetractionHomotopyTransfer.reflection e r hre (loopMap n) _ f g S F
    intro f' g' S' hF
    exact (loopMap_homotopicRel_iff (I := 𝓡 d) n
      (by simpa only [finrank_euclideanSpace_fin] using hd) f' g' S').mpr hF

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
