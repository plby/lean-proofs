import Wikipedia.NoExoticSixSphere.ThirdStemSmashParity

/-!
# Mixed third-stem compositions in the actual sixth stem

The native smash pairing of two independent S8-to-S5 maps equals the
inverse of their fifth/eighth suspended composition. The coordinate
permutations and collapsed cube faces are the original ones. Bilinearity
and the proved cyclic third-stem calculation therefore show that every
such mixed composition is either the identity or the native square.

This does not assert generation of the entire sixth stem or Arf detection.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.MixedSixthComposition

open NoExoticSixSphere SmoothCube SphereComposition IteratedProductSphere
open SixthStemSquareComparison

def twisted (f g : Based 8 5) : Based 16 10 :=
  comp (iterate f 5) (comp middleBased (iterate g 8))

theorem factorization_of_prefix (f g : Based 8 5) (f₅ : Based 13 10) (g₈ : Based 16 13)
    (h₅ : ∀ u x, f₅.val (prefixSphere 8 5 u x) = prefixSphere 5 5 u (f.val x))
    (h₈ : ∀ u x, g₈.val (prefixSphere 8 8 u x) = prefixSphere 5 8 u (g.val x))
    (u v : Fin 8 → I) :
    JamesSphere.pairing 5 (f.val (quotient 8 u), g.val (quotient 8 v)) =
      permutation 10 (by decide) SixthStemSmashSquare.blockFive
        (f₅.val (permutation 13 (by decide) middleBlock
          (g₈.val (JamesSphere.pairing 8 (quotient 8 u, quotient 8 v))))) := by
  obtain ⟨w, hw⟩ := quotient_surjective (by decide : 0 < 5) (g.val (quotient 8 v))
  rw [← prefix_pairing_eight, h₈, ← hw, middleBlock_prefix, h₅, prefix_pairing_five]
  exact JamesSphere.PairingCoordinates.pairing_swap_of_coordinates 5 (by decide)
    SixthStemSmashSquare.blockFive SixthStemSmashSquare.blockFive_coordinates
    (quotient 5 w) (f.val (quotient 8 u))

theorem pairing_factorization (f g : Based 8 5) (u v : Fin 8 → I) :
    JamesSphere.pairing 5 (f.val (quotient 8 u), g.val (quotient 8 v)) =
      permutation 10 (by decide) SixthStemSmashSquare.blockFive
        ((twisted f g).val (JamesSphere.pairing 8 (quotient 8 u, quotient 8 v))) :=
  factorization_of_prefix f g (iterate f 5) (iterate g 8)
    (iterate_prefix f 5) (iterate_prefix g 8) u v

theorem paired_cube_factorization (f g : Based 8 5) (u : Fin 16 → I) :
    SphereSmashNative.loop (toGenLoop f) (toGenLoop g) u =
      permutation 10 (by decide) SixthStemSmashSquare.blockFive
        ((twisted f g).val (quotient 16 u)) := by
  change JamesSphere.pairing 5
    (f.val (quotient 8 (SphereSmashNative.left u)),
      g.val (quotient 8 (SphereSmashNative.right u))) = _
  rw [pairing_factorization, JamesSphere.PairingCoordinates.pairing_cubes,
    SphereSmashNative.append_left_right]

theorem twisted_native (f g : Based 8 5) :
    sphereClass (twisted f g) =
      sphereClass (comp (iterate f 5) (iterate g 8)) := by
  change sphereClass (comp (iterate f 5) (comp middleBased (iterate g 8))) = _
  rw [← mapHom_sphereClass, ← mapHom_sphereClass,
    SixthStemSquareComparison.middleBased_native, mapHom_sphereClass]

theorem product_eq_inverse_composition (f g : Based 8 5) :
    SphereSmashNative.product (sphereClass f) (sphereClass g) =
      (sphereClass (comp (iterate f 5) (iterate g 8)))⁻¹ := by
  have h : SphereSmashNative.product (sphereClass f) (sphereClass g) =
      HigherHomotopy.map (N := Fin 16)
        (permutation 10 (by decide) SixthStemSmashSquare.blockFive)
        (permutation_pole 10 (by decide) SixthStemSmashSquare.blockFive)
        (sphereClass (twisted f g)) := by
    apply congrArg (fun p : GenLoop (Fin 16) (Sphere 10) (spherePole 10) ↦
      (Quotient.mk' p : π_ 16 (Sphere 10) (spherePole 10)))
    apply GenLoop.ext
    exact paired_cube_factorization f g
  rw [h, CubicalSphereSuspension.permutation_native_negative (d := 15) (n := 9)
    (by decide) SixthStemSmashSquare.blockFive SixthStemSmashSquare.blockFive_sign,
    twisted_native]

theorem composition_coordinates (f g : Based 8 5) :
    sphereClass (comp (iterate f 5) (iterate g 8)) =
      StableThirdComposition.squareClass 2 ^
        ((SphereSmashNative.coordinate (sphereClass f)).val *
          (SphereSmashNative.coordinate (sphereClass g)).val) := by
  have h := product_eq_inverse_composition f g
  rw [SphereSmashNative.product_coordinates,
    SixthStemSquareComparison.nativeClass_eq_inverse, inv_pow] at h
  exact inv_injective h.symm

theorem composition_eq_one_or_square (f g : Based 8 5) :
    sphereClass (comp (iterate f 5) (iterate g 8)) = 1 ∨
      sphereClass (comp (iterate f 5) (iterate g 8)) =
        StableThirdComposition.squareClass 2 := by
  rw [composition_coordinates, SphereSmashNative.pow_eq_mod_two _
    (StableThirdComposition.squareClass_pow_two 2)]
  rcases Nat.mod_two_eq_zero_or_one
      ((SphereSmashNative.coordinate (sphereClass f)).val *
        (SphereSmashNative.coordinate (sphereClass g)).val) with h | h
  · exact Or.inl (by rw [h, pow_zero])
  · exact Or.inr (by rw [h, pow_one])

theorem stable_composition_eq_one_or_square (f g : Based 8 5) :
    CubicalStableSix.ofNative (k := 8)
        (sphereClass (comp (iterate f 5) (iterate g 8))) = 1 ∨
      CubicalStableSix.ofNative (k := 8)
        (sphereClass (comp (iterate f 5) (iterate g 8))) =
        StableThirdComposition.stableSquare := by
  rcases composition_eq_one_or_square f g with h | h
  · exact Or.inl (by rw [h, CubicalStableSix.ofNative_one])
  · exact Or.inr (by rw [h, StableThirdComposition.stableSquare_eq_stage])

end Wikipedia.HopfProblem.DegreeCollapse.MixedSixthComposition
