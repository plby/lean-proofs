import Wikipedia.NoExoticSixSphere.FramedSlabBoundaryComponents
import Wikipedia.HopfProblem.SphereHomologyCoefficientsNaturality

/-!
# Every native mod-two boundary class is a sum of original endpoint images

The actual integral disjoint-union coordinates and coefficient reduction
give surjectivity of the sum of the two original mod-two inclusion maps.
This concerns the whole boundary group, not the kernel of its map to
the filling. No integral lift of a mod-two kernel class is asserted.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData

variable {m n : ℕ} {z : Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) z s t}
  {hd : m = n + 6} {a : Sphere m} (A : d.FramedSlabData 6 hd a)

def modTwoBoundarySum :
    (ModHomology 2 {x : Sphere m // d.leftMap x = z} 3 ×
      ModHomology 2 {x : Sphere m // d.rightMap x = z} 3) →ₗ[ℤ]
      ModHomology 2 A.nativeBoundary 3 :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    ((modHomologyMap 2 A.nativeBoundaryInl 3).toAddMonoidHom.coprod
      (modHomologyMap 2 A.nativeBoundaryInr 3).toAddMonoidHom)

theorem modTwoBoundarySum_apply
    (u : ModHomology 2 {x : Sphere m // d.leftMap x = z} 3 ×
      ModHomology 2 {x : Sphere m // d.rightMap x = z} 3) :
    A.modTwoBoundarySum u = modHomologyMap 2 A.nativeBoundaryInl 3 u.1 +
      modHomologyMap 2 A.nativeBoundaryInr 3 u.2 := rfl

theorem modTwoBoundarySum_reduction
    (u : SingularHomology {x : Sphere m // d.leftMap x = z} 3 ×
      SingularHomology {x : Sphere m // d.rightMap x = z} 3) :
    A.modTwoBoundarySum
        (reductionHomologyMap 2 {x : Sphere m // d.leftMap x = z} 3 u.1,
          reductionHomologyMap 2 {x : Sphere m // d.rightMap x = z} 3 u.2) =
      reductionHomologyMap 2 A.nativeBoundary 3 (A.integralBoundarySumEquiv 3 u) := by
  rw [modTwoBoundarySum_apply, integralBoundarySumEquiv_apply, map_add,
    modHomologyMap_reduction, modHomologyMap_reduction]

theorem modTwoBoundarySum_inclusion
    (u : ModHomology 2 {x : Sphere m // d.leftMap x = z} 3 ×
      ModHomology 2 {x : Sphere m // d.rightMap x = z} 3) :
    modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3 (A.modTwoBoundarySum u) =
      modHomologyMap 2 ((subtypeInclusion A.nativeBoundary).comp A.nativeBoundaryInl) 3 u.1 +
        modHomologyMap 2 ((subtypeInclusion A.nativeBoundary).comp A.nativeBoundaryInr) 3 u.2 := by
  rw [modTwoBoundarySum_apply, map_add, modHomologyMap_comp, modHomologyMap_comp]
  rfl

variable [SimplyConnectedSpace {x : Sphere m // d.leftMap x = z}]
  [SimplyConnectedSpace {x : Sphere m // d.rightMap x = z}]
  (l₀ : {x : Sphere m // d.leftMap x = z}) (r₀ : {x : Sphere m // d.rightMap x = z})
  [hL₂ : Subsingleton (π_ 2 {x : Sphere m // d.leftMap x = z} l₀)]
  [hR₂ : Subsingleton (π_ 2 {x : Sphere m // d.rightMap x = z} r₀)]

include l₀ r₀ hL₂ hR₂ in
theorem modTwoBoundarySum_surjective : Function.Surjective A.modTwoBoundarySum := by
  let := A.nativeBoundary_secondHomology_subsingleton l₀ r₀
  intro b
  obtain ⟨c, rfl⟩ := ZeroSecondHomologyEvaluation.reduction_surjective A.nativeBoundary b
  obtain ⟨u, hu⟩ := (A.integralBoundarySumEquiv 3).surjective c
  refine ⟨(reductionHomologyMap 2 {x : Sphere m // d.leftMap x = z} 3 u.1,
    reductionHomologyMap 2 {x : Sphere m // d.rightMap x = z} 3 u.2), ?_⟩
  rw [modTwoBoundarySum_reduction, hu]

end NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData
