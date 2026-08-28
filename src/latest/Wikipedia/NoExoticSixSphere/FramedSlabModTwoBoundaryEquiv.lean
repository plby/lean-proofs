import Wikipedia.NoExoticSixSphere.FramedSlabModTwoBoundarySum
import Wikipedia.NoExoticSixSphere.CoefficientKernelLifting

/-!
# Exact mod-two endpoint coordinates on the native boundary

The original inclusion-sum map is injective as well as surjective.
Integral endpoint coordinates and the exact coefficient kernel prove this
without replacing any map by an abstract isomorphism. These are coordinates
on the whole boundary, not an assertion that its kernel lifts integrally.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData

variable {m n : ℕ} {z : Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) z s t}
  {hd : m = n + 6} {a : Sphere m} (A : d.FramedSlabData 6 hd a)
  [SimplyConnectedSpace {x : Sphere m // d.leftMap x = z}]
  [SimplyConnectedSpace {x : Sphere m // d.rightMap x = z}]
  (l₀ : {x : Sphere m // d.leftMap x = z}) (r₀ : {x : Sphere m // d.rightMap x = z})
  [hL₂ : Subsingleton (π_ 2 {x : Sphere m // d.leftMap x = z} l₀)]
  [hR₂ : Subsingleton (π_ 2 {x : Sphere m // d.rightMap x = z} r₀)]

include l₀ r₀ hL₂ hR₂ in
theorem modTwoBoundarySum_injective : Function.Injective A.modTwoBoundarySum := by
  apply (injective_iff_map_eq_zero A.modTwoBoundarySum).mpr
  rintro ⟨u, v⟩ huv
  obtain ⟨x, rfl⟩ := TwoConnectedCoefficients.middleReduction_surjective l₀ u
  obtain ⟨y, rfl⟩ := TwoConnectedCoefficients.middleReduction_surjective r₀ v
  have hred : reductionHomologyMap 2 A.nativeBoundary 3
      (A.integralBoundarySumEquiv 3 (x, y)) = 0 :=
    (A.modTwoBoundarySum_reduction (x, y)).symm.trans huv
  have hmem : A.integralBoundarySumEquiv 3 (x, y) ∈
      scalarImage 2 (SingularHomology A.nativeBoundary 3) := by
    rw [scalarImage_eq_reduction_ker 2 (by decide) A.nativeBoundary 3]
    exact hred
  obtain ⟨b, hb⟩ := (CoefficientKernelLifting.mem_twice_iff _).mp hmem
  obtain ⟨w, rfl⟩ := (A.integralBoundarySumEquiv 3).surjective b
  have hw : (2 : ℤ) • w = (x, y) :=
    (A.integralBoundarySumEquiv 3).injective ((map_zsmul _ _ _).trans hb)
  apply Prod.ext
  · change reductionHomologyMap 2 {x : Sphere m // d.leftMap x = z} 3 x = 0
    have hwl : (2 : ℤ) • w.1 = x := congrArg Prod.fst hw
    rw [← hwl]
    exact CoefficientKernelLifting.reduction_twice _
      (scalarImage_eq_reduction_ker 2 (by decide) _ 3).symm w.1
  · change reductionHomologyMap 2 {x : Sphere m // d.rightMap x = z} 3 y = 0
    have hwr : (2 : ℤ) • w.2 = y := congrArg Prod.snd hw
    rw [← hwr]
    exact CoefficientKernelLifting.reduction_twice _
      (scalarImage_eq_reduction_ker 2 (by decide) _ 3).symm w.2

def modTwoBoundaryEquiv :
    (ModHomology 2 {x : Sphere m // d.leftMap x = z} 3 ×
      ModHomology 2 {x : Sphere m // d.rightMap x = z} 3) ≃ₗ[ℤ]
        ModHomology 2 A.nativeBoundary 3 :=
  LinearEquiv.ofBijective A.modTwoBoundarySum
    ⟨A.modTwoBoundarySum_injective l₀ r₀, A.modTwoBoundarySum_surjective l₀ r₀⟩

theorem modTwoBoundaryEquiv_apply
    (u : ModHomology 2 {x : Sphere m // d.leftMap x = z} 3 ×
      ModHomology 2 {x : Sphere m // d.rightMap x = z} 3) :
    A.modTwoBoundaryEquiv l₀ r₀ u = A.modTwoBoundarySum u := rfl

end NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData
