import Wikipedia.NoExoticSixSphere.FramedSlabModTwoBoundaryEquiv
import Wikipedia.NoExoticSixSphere.MiddleHomologyKernelObstruction

/-!
# The exact coefficient obstruction on the full original boundary kernel

The obstruction uses the actual native boundary inclusion. Its kernel
consists exactly of reductions of actual integral kernel classes. The
equivalent endpoint formulation retains both original components and
allows integral images to cancel in the filling.

The quotient includes target two-torsion. Neither its vanishing nor
quadratic vanishing on classes with nonzero obstruction is asserted.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData

open CylinderFiberSlab

attribute [local instance] Submodule.Quotient.module

variable {m n : ℕ} {z : Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) z s t}
  {hd : m = n + 6} {a : Sphere m} (A : d.FramedSlabData 6 hd a)
  [SimplyConnectedSpace {x : Sphere m // d.leftMap x = z}]
  [SimplyConnectedSpace {x : Sphere m // d.rightMap x = z}]
  (l₀ : {x : Sphere m // d.leftMap x = z}) (r₀ : {x : Sphere m // d.rightMap x = z})
  [Subsingleton (π_ 2 {x : Sphere m // d.leftMap x = z} l₀)]
  [Subsingleton (π_ 2 {x : Sphere m // d.rightMap x = z} r₀)]

def boundaryKernelObstruction :
    LinearMap.ker (modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3) →ₗ[ℤ]
      SingularHomology (slab d.map z s t) 3 ⧸
        MiddleKernelCoefficients.Indeterminacy (subtypeInclusion A.nativeBoundary) := by
  let := A.nativeBoundary_secondHomology_subsingleton l₀ r₀
  exact MiddleKernelCoefficients.obstruction (subtypeInclusion A.nativeBoundary)

theorem boundaryKernelObstruction_zero_iff
    (v : LinearMap.ker (modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3)) :
    A.boundaryKernelObstruction l₀ r₀ v = 0 ↔
      ∃ x : SingularHomology A.nativeBoundary 3,
        singularHomologyMap (subtypeInclusion A.nativeBoundary) 3 x = 0 ∧
          reductionHomologyMap 2 A.nativeBoundary 3 x = v.val := by
  let := A.nativeBoundary_secondHomology_subsingleton l₀ r₀
  exact MiddleKernelCoefficients.obstruction_zero_iff (subtypeInclusion A.nativeBoundary) v

theorem boundaryKernelObstruction_eq
    (v : LinearMap.ker (modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3))
    (x : SingularHomology A.nativeBoundary 3) (b : SingularHomology (slab d.map z s t) 3)
    (hx : reductionHomologyMap 2 A.nativeBoundary 3 x = v.val)
    (hb : singularHomologyMap (subtypeInclusion A.nativeBoundary) 3 x = (2 : ℤ) • b) :
    A.boundaryKernelObstruction l₀ r₀ v = Submodule.Quotient.mk b := by
  let := A.nativeBoundary_secondHomology_subsingleton l₀ r₀
  exact MiddleKernelCoefficients.obstruction_eq (subtypeInclusion A.nativeBoundary) v x b hx hb

theorem boundaryKernelObstruction_twice
    (v : LinearMap.ker (modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3)) :
    (2 : ℤ) • A.boundaryKernelObstruction l₀ r₀ v = 0 := by
  let := A.nativeBoundary_secondHomology_subsingleton l₀ r₀
  exact MiddleKernelCoefficients.obstruction_twice (subtypeInclusion A.nativeBoundary) v

theorem boundaryKernelObstruction_zero_iff_endpoint_lift
    (u : ModHomology 2 {x : Sphere m // d.leftMap x = z} 3 ×
      ModHomology 2 {x : Sphere m // d.rightMap x = z} 3)
    (hu : modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3 (A.modTwoBoundarySum u) = 0) :
    A.boundaryKernelObstruction l₀ r₀ ⟨A.modTwoBoundarySum u, hu⟩ = 0 ↔
      ∃ x : SingularHomology {x : Sphere m // d.leftMap x = z} 3 ×
          SingularHomology {x : Sphere m // d.rightMap x = z} 3,
        singularHomologyMap (subtypeInclusion A.nativeBoundary) 3
            (A.integralBoundarySumEquiv 3 x) = 0 ∧
          (reductionHomologyMap 2 {x : Sphere m // d.leftMap x = z} 3 x.1,
            reductionHomologyMap 2 {x : Sphere m // d.rightMap x = z} 3 x.2) = u := by
  rw [boundaryKernelObstruction_zero_iff]
  constructor
  · rintro ⟨x, hx, hred⟩
    obtain ⟨y, rfl⟩ := (A.integralBoundarySumEquiv 3).surjective x
    refine ⟨y, hx, A.modTwoBoundarySum_injective l₀ r₀ ?_⟩
    exact (A.modTwoBoundarySum_reduction y).trans hred
  · rintro ⟨x, hx, hred⟩
    refine ⟨A.integralBoundarySumEquiv 3 x, hx, ?_⟩
    exact (A.modTwoBoundarySum_reduction x).symm.trans (congrArg A.modTwoBoundarySum hred)

end NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData
