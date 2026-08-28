import Wikipedia.HopfProblem.DegreeCollapseNinthSphereStableVanishing
import Wikipedia.HopfProblem.DegreeCollapseHopfClutching

/-!
# Every original pi10(S4) class stabilizes to one of two values

Surjectivity of the actual Hopf connecting map on suspended classes
allows subtraction of a suspension from pi9(S3). That suspension has
zero stable image by the proved finite vanishing theorem. The remainder
lies in the actual Hopf kernel, whose two possible stable values were
already computed.

This proves the whole image from S4, not surjectivity of this image onto
the stable sixth stem. The remaining desuspension and Arf arguments are
not assumed here.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SixthSphereFourImage

open NoExoticSixSphere CubicalSphereSuspension QuaternionicHopf

theorem stable_eq_one_or_square (x : π_ 10 (Sphere 4) (spherePole 4)) :
    CubicalStableSix.ofNative (k := 2) x = 1 ∨
      CubicalStableSix.ofNative (k := 2) x = StableThirdComposition.stableSquare := by
  obtain ⟨c, hc⟩ := HopfClutching.connecting_suspension_surjective 9 (connecting 9 x)
  change connecting 9 (hom 9 3 c) = connecting 9 x at hc
  have hk : connecting 9 (x / hom 9 3 c) = 1 := by
    change connectingHom 9 (x / hom 9 3 c) = 1
    rw [map_div]
    change connecting 9 x / connecting 9 (hom 9 3 c) = 1
    rw [hc, div_self']
  have hE : CubicalStableSix.ofNative (k := 2) (hom 9 3 c) = 1 :=
    (CubicalStableSix.ofNative_stepHom 1 c).trans
      (NinthSphereStableVanishing.stable_eq_one c)
  have hstable : CubicalStableSix.ofNative (k := 2) (x / hom 9 3 c) =
      CubicalStableSix.ofNative (k := 2) x := by
    change CubicalStableSix.ofNativeHom 2 (x / hom 9 3 c) = _
    rw [map_div]
    change CubicalStableSix.ofNative (k := 2) x /
      CubicalStableSix.ofNative (k := 2) (hom 9 3 c) = _
    rw [hE, div_one]
  have h := SixthHopfKernel.stable_hopf_kernel_eq_one_or_square (x / hom 9 3 c) hk
  rwa [hstable] at h

theorem stable_pow_two (x : π_ 10 (Sphere 4) (spherePole 4)) :
    CubicalStableSix.ofNative (k := 2) x ^ 2 = 1 := by
  rcases stable_eq_one_or_square x with h | h
  · rw [h, one_pow]
  · rw [h, StableThirdComposition.stableSquare_pow_two]

theorem transition_eq_one_or_square (x : π_ 10 (Sphere 4) (spherePole 4)) :
    CubicalStableSix.transition 2 8 (by decide) x = 1 ∨
      CubicalStableSix.transition 2 8 (by decide) x = StableThirdComposition.squareClass 2 := by
  have he := CubicalStableSix.ofNative_transition (by decide : 2 ≤ 8) x
  rcases stable_eq_one_or_square x with h | h
  · exact Or.inl ((CubicalStableSix.ofNative_eq_one_iff_native (by decide : 6 ≤ 8) _).mp
      (he.trans h))
  · apply Or.inr
    apply CubicalStableSix.ofNative_injective (by decide : 6 ≤ 8)
    exact he.trans (h.trans (StableThirdComposition.stableSquare_eq_stage 2).symm)

end Wikipedia.HopfProblem.DegreeCollapse.SixthSphereFourImage
