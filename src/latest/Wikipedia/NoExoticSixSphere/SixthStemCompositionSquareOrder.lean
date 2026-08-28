import Wikipedia.NoExoticSixSphere.SixthStemSquareComparisonCoordinates

/-!
# The original stable composition square has order at most two

The actual smash square is the inverse of the actual composition
square in native pi16(S10). The middle permutation disappears by a
based homotopy, and the final target permutation acts by inversion.
Thus the checked smash-square order bound applies to the original
composition square and every one of its stable-range representatives.

Nontriviality, generation of the sixth stem, and Arf detection remain
separate proof obligations.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.SixthStemSquareComparison

open SmoothCube SphereComposition IteratedProductSphere

theorem middleBased_native (g : Based 16 13) :
    mapHom middleBased 16 (sphereClass g) = sphereClass g := by
  have h := HigherHomotopy.map_eq_of_homotopicRel
    (permutation 13 (by decide) middleBlock) (ContinuousMap.id _)
    (permutation_pole 13 (by decide) middleBlock) rfl
    (permutation_homotopic_id (by decide) middleBlock middleBlock_sign) (sphereClass g)
  exact h

theorem twisted_native (f : Based 8 5) :
    sphereClass (twisted f) = sphereClass (comp (iterate f 5) (iterate f 8)) := by
  change sphereClass (comp (iterate f 5) (comp middleBased (iterate f 8))) = _
  rw [← mapHom_sphereClass, ← mapHom_sphereClass, middleBased_native, mapHom_sphereClass]

theorem smash_native_eq_inverse (f : Based 8 5) :
    sphereClass (SphereSmash.basedSquare f) =
      (sphereClass (comp (iterate f 5) (iterate f 8)))⁻¹ := by
  have hm : sphereClass (SphereSmash.basedSquare f) =
      HigherHomotopy.map (N := Fin 16)
        (permutation 10 (by decide) SixthStemSmashSquare.blockFive)
        (permutation_pole 10 (by decide) SixthStemSmashSquare.blockFive)
        (sphereClass (twisted f)) := by
    apply congrArg (fun p : GenLoop (Fin 16) (Sphere 10) (spherePole 10) ↦
      (Quotient.mk' p : π_ 16 (Sphere 10) (spherePole 10)))
    apply GenLoop.ext
    intro u
    exact smash_factorization f (quotient 16 u)
  rw [hm, CubicalSphereSuspension.permutation_native_negative (d := 15) (n := 9)
    (by decide) SixthStemSmashSquare.blockFive SixthStemSmashSquare.blockFive_sign,
    twisted_native]

theorem nativeClass_eq_inverse : SixthStemSmashSquare.nativeClass =
    (StableThirdComposition.squareClass 2)⁻¹ :=
  smash_native_eq_inverse (StableThirdComposition.representative 0)

theorem stableClass_eq_inverse : SixthStemSmashSquare.stableClass =
    StableThirdComposition.stableSquare⁻¹ := by
  change CubicalStableSix.ofNativeHom 8 SixthStemSmashSquare.nativeClass = _
  rw [nativeClass_eq_inverse, map_inv]
  change (CubicalStableSix.ofNative (StableThirdComposition.squareClass 2))⁻¹ = _
  rw [StableThirdComposition.stableSquare_eq_stage]

end NoExoticSixSphere.SixthStemSquareComparison

namespace NoExoticSixSphere.StableThirdComposition

theorem stableSquare_pow_two : stableSquare ^ 2 = 1 := by
  have h := SixthStemSmashSquare.stableClass_pow_two
  rw [SixthStemSquareComparison.stableClass_eq_inverse, inv_pow, inv_eq_one] at h
  exact h

theorem squareClass_pow_two (k : ℕ) : squareClass k ^ 2 = 1 := by
  apply (CubicalStableSix.ofNative_eq_one_iff_native (by omega) (squareClass k ^ 2)).mp
  change CubicalStableSix.ofNativeHom (k + 6) (squareClass k ^ 2) = 1
  rw [map_pow]
  change (CubicalStableSix.ofNative (squareClass k)) ^ 2 = 1
  rw [stableSquare_eq_stage]
  exact stableSquare_pow_two

end NoExoticSixSphere.StableThirdComposition
