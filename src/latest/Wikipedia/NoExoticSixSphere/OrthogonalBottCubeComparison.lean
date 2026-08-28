import Wikipedia.NoExoticSixSphere.OrthogonalBottLoopMap
import Wikipedia.NoExoticSixSphere.CubeSphereRetract
import Wikipedia.NoExoticSixSphere.RetractionHomotopyTransfer

/-!
# The first Bott comparison for actual cube-parameter families

The cube is a retract of a same-dimensional sphere. Relative representatives
and homotopy reflection therefore extend from compact boundaryless parameter
manifolds to the cubes used in the native higher homotopy groups.
-/

open Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization

variable {n : ℕ}

theorem exists_cube_bottLoopMap_representative (d : ℕ) (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) (hd : d + 2 < n)
    (p : C((Fin d → unitInterval), Path a a)) :
    ∃ J : C((Fin d → unitInterval), OrthogonalComplexStructures.Space n),
      Nonempty (p.HomotopyRel ((bottLoopMap a b hanti J₀).comp J)
        (p ⁻¹' range (bottLoopMap a b hanti J₀))) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = d + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  obtain ⟨e, r, hre⟩ := CubeSphereRetract.exists_retract d
  apply RetractionHomotopyTransfer.representatives e r hre (bottLoopMap a b hanti J₀) _ p
  intro P
  exact exists_bottLoopMap_representative (I := 𝓡 d) a b hanti J₀
    (by simpa only [finrank_euclideanSpace_fin] using hd) P

theorem cube_bottLoopMap_homotopicRel_iff (d : ℕ) (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) (hd : d + 3 < n)
    (f g : C((Fin d → unitInterval), OrthogonalComplexStructures.Space n))
    (S : Set (Fin d → unitInterval)) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty (((bottLoopMap a b hanti J₀).comp f).HomotopyRel
        ((bottLoopMap a b hanti J₀).comp g) S) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨F.compContinuousMap (bottLoopMap a b hanti J₀)⟩
  · rintro ⟨F⟩
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = d + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    obtain ⟨e, r, hre⟩ := CubeSphereRetract.exists_retract d
    apply RetractionHomotopyTransfer.reflection e r hre (bottLoopMap a b hanti J₀) _ f g S F
    intro f' g' S' hF
    exact (bottLoopMap_homotopicRel_iff (I := 𝓡 d) a b hanti J₀
      (by simpa only [finrank_euclideanSpace_fin] using hd) f' g' S').mpr hF

end NoExoticSixSphere.OrthogonalPolygon
