import Wikipedia.NoExoticSixSphere.QuaternionicHopfStableNontriviality
import Wikipedia.NoExoticSixSphere.SixthStemCompositionSquareOrder

/-!
# The original stable composition square is nonzero and has exact order two

The already proved comparison identifies the original Hopf smash square
with the inverse of the original composition square. Nontriviality
therefore transfers to that composition square and every retained native
stable-range stage. The entire sixth-stem generation theorem is not
assumed or concluded here.
-/

noncomputable section

namespace NoExoticSixSphere.StableThirdComposition

theorem stableSquare_ne_one : stableSquare ≠ 1 := by
  intro h
  apply SixthStemSmashSquare.stableClass_ne_one
  rw [SixthStemSquareComparison.stableClass_eq_inverse, h, inv_one]

theorem squareClass_ne_one (k : ℕ) : squareClass k ≠ 1 := by
  intro h
  apply stableSquare_ne_one
  rw [← stableSquare_eq_stage k, h]
  exact map_one (CubicalStableSix.ofNativeHom (k + 6))

theorem orderOf_stableSquare : orderOf stableSquare = 2 :=
  orderOf_eq_prime stableSquare_pow_two stableSquare_ne_one

theorem orderOf_squareClass (k : ℕ) : orderOf (squareClass k) = 2 :=
  orderOf_eq_prime (squareClass_pow_two k) (squareClass_ne_one k)

end NoExoticSixSphere.StableThirdComposition
