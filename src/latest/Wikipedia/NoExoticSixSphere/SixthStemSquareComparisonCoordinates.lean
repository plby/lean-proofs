import Wikipedia.NoExoticSixSphere.IteratedProductSphereCoordinates
import Wikipedia.NoExoticSixSphere.SixthStemSmashSquareOrder
import Mathlib.GroupTheory.Perm.Fin

/-!
# Actual coordinates comparing the two sixth-stem square maps

The smash square of an S8-to-S5 map factors through its eighth and
fifth ORIGINAL product suspensions. The middle coordinate permutation
has positive sign, and the final five-block exchange has negative sign.
All formulas retain the original quotient maps and collapsed faces.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.SixthStemSquareComparison

open SmoothCube SphereComposition IteratedProductSphere

def middleBlock : Equiv.Perm (Fin 13) := finRotate 13 ^ 8

theorem middleBlock_sign : ((Equiv.Perm.sign middleBlock : ℤˣ) : ℤ) = 1 := by
  norm_num [middleBlock, map_pow, sign_finRotate]

theorem middleBlock_coordinates (u : Fin 8 → I) (v : Fin 5 → I) :
    Fin.append v u = fun j : Fin 13 ↦ Fin.append u v (middleBlock j) := by
  funext j
  fin_cases j <;> rfl

theorem prefixCube_eight_eight (u v : Fin 8 → I) :
    prefixCube 8 8 u v = Fin.append u v := by
  funext j
  fin_cases j <;> rfl

theorem prefixCube_five_eight (u : Fin 8 → I) (v : Fin 5 → I) :
    prefixCube 5 8 u v = Fin.append u v := by
  funext j
  fin_cases j <;> rfl

theorem prefixCube_eight_five (u : Fin 5 → I) (v : Fin 8 → I) :
    prefixCube 8 5 u v = Fin.append u v := by
  funext j
  fin_cases j <;> rfl

theorem prefixCube_five_five (u v : Fin 5 → I) :
    prefixCube 5 5 u v = Fin.append u v := by
  funext j
  fin_cases j <;> rfl

theorem middleBlock_prefix (u : Fin 8 → I) (v : Fin 5 → I) :
    permutation 13 (by decide) middleBlock (prefixSphere 5 8 u (quotient 5 v)) =
      prefixSphere 8 5 v (quotient 8 u) := by
  rw [prefixSphere_quotient, prefixSphere_quotient,
    prefixCube_five_eight, prefixCube_eight_five, permutation_quotient,
    middleBlock_coordinates]

theorem prefix_pairing_eight (u : Fin 8 → I) (x : Sphere 8) :
    prefixSphere 8 8 u x = JamesSphere.pairing 8 (quotient 8 u, x) := by
  obtain ⟨v, rfl⟩ := quotient_surjective (by decide : 0 < 8) x
  rw [prefixSphere_quotient, prefixCube_eight_eight,
    JamesSphere.PairingCoordinates.pairing_cubes]

theorem prefix_pairing_five (u : Fin 5 → I) (x : Sphere 5) :
    prefixSphere 5 5 u x = JamesSphere.pairing 5 (quotient 5 u, x) := by
  obtain ⟨v, rfl⟩ := quotient_surjective (by decide : 0 < 5) x
  rw [prefixSphere_quotient, prefixCube_five_five,
    JamesSphere.PairingCoordinates.pairing_cubes]

def middleBased : Based 13 13 :=
  ⟨permutation 13 (by decide) middleBlock, permutation_pole 13 (by decide) middleBlock⟩

def twisted (f : Based 8 5) : Based 16 10 :=
  comp (iterate f 5) (comp middleBased (iterate f 8))

theorem factorization_of_prefix (f : Based 8 5) (f₅ : Based 13 10) (f₈ : Based 16 13)
    (h₅ : ∀ u x, f₅.val (prefixSphere 8 5 u x) = prefixSphere 5 5 u (f.val x))
    (h₈ : ∀ u x, f₈.val (prefixSphere 8 8 u x) = prefixSphere 5 8 u (f.val x))
    (z : Sphere 16) :
    SphereSmash.squareMap f z =
      permutation 10 (by decide) SixthStemSmashSquare.blockFive
        (f₅.val (permutation 13 (by decide) middleBlock (f₈.val z))) := by
  obtain ⟨⟨x, y⟩, rfl⟩ := JamesSphere.pairing_surjective 8 z
  obtain ⟨u, rfl⟩ := quotient_surjective (by decide : 0 < 8) x
  obtain ⟨v, rfl⟩ := quotient_surjective (by decide : 0 < 8) y
  obtain ⟨w, hw⟩ := quotient_surjective (by decide : 0 < 5) (f.val (quotient 8 v))
  rw [SphereSmash.squareMap_pairing]
  change JamesSphere.pairing 5 (f.val (quotient 8 u), f.val (quotient 8 v)) =
    permutation 10 (by decide) SixthStemSmashSquare.blockFive
      (f₅.val (permutation 13 (by decide) middleBlock
        (f₈.val (JamesSphere.pairing 8 (quotient 8 u, quotient 8 v)))))
  rw [← prefix_pairing_eight, h₈, ← hw, middleBlock_prefix, h₅, prefix_pairing_five]
  exact JamesSphere.PairingCoordinates.pairing_swap_of_coordinates 5 (by decide)
    SixthStemSmashSquare.blockFive SixthStemSmashSquare.blockFive_coordinates
    (quotient 5 w) (f.val (quotient 8 u))

theorem smash_factorization (f : Based 8 5) (z : Sphere 16) :
    SphereSmash.squareMap f z =
      permutation 10 (by decide) SixthStemSmashSquare.blockFive ((twisted f).val z) :=
  factorization_of_prefix f (iterate f 5) (iterate f 8)
    (iterate_prefix f 5) (iterate_prefix f 8) z

end NoExoticSixSphere.SixthStemSquareComparison
