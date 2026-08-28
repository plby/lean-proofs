import Wikipedia.NoExoticSixSphere.ProductSphereSuspensionComparison
import Wikipedia.NoExoticSixSphere.OnePointProductCoordinates
import Wikipedia.NoExoticSixSphere.JamesSpherePairingQuotient

/-!
# Actual compactification coordinates for a pair of stabilized tubes

Use the same finite coordinate ordering as the original product suspension
and the original equal-factor sphere pairing. All maps here are specified
homeomorphisms, not degree or stable-class identifications.
-/

noncomputable section

open scoped OnePoint

namespace NoExoticSixSphere.SuspensionProductComparison

open Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct

local notation "V" n => EuclideanSpace ℝ (Fin n)

def productFiniteCoordinates (n : ℕ) : (V n) × ℝ ≃ₜ V (n + 1) :=
  (Homeomorph.prodComm (V n) ℝ).trans (coordinates n).toHomeomorph

theorem productSphereHomeomorph_coordinates (n : ℕ) (z : OnePoint ((V n) × ℝ)) :
    productSphereHomeomorph n z =
      euclideanOnePointSphere (n + 1) ((productFiniteCoordinates n).onePointCongr z) := rfl

def productPairSphereHomeomorph (n : ℕ) :
    OnePoint (((V n) × ℝ) × ((V n) × ℝ)) ≃ₜ Sphere ((n + 1) + (n + 1)) :=
  ((productFiniteCoordinates n).prodCongr (productFiniteCoordinates n)).onePointCongr.trans
    (JamesSphere.pairingHomeomorph (n + 1))

theorem productPairSphereHomeomorph_map (n : ℕ) (x y : OnePoint ((V n) × ℝ)) :
    productPairSphereHomeomorph n (OnePointProduct.map (x, y)) =
      JamesSphere.pairing (n + 1) (productSphereHomeomorph n x, productSphereHomeomorph n y) := by
  change JamesSphere.pairingHomeomorph (n + 1)
    (((productFiniteCoordinates n).prodCongr (productFiniteCoordinates n)).onePointCongr
      (OnePointProduct.map (x, y))) = _
  rw [OnePointProduct.map_prodCongr, productSphereHomeomorph_coordinates,
    productSphereHomeomorph_coordinates]
  change JamesSphere.pairingHomeomorph (n + 1)
    (OnePointProduct.map ((productFiniteCoordinates n).onePointCongr x,
      (productFiniteCoordinates n).onePointCongr y)) =
    JamesSphere.pairingHomeomorph (n + 1)
      (OnePointProduct.map
        ((euclideanOnePointSphere (n + 1)).symm
          (euclideanOnePointSphere (n + 1) ((productFiniteCoordinates n).onePointCongr x)),
        (euclideanOnePointSphere (n + 1)).symm
          (euclideanOnePointSphere (n + 1) ((productFiniteCoordinates n).onePointCongr y))))
  rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]

theorem productPairSphereHomeomorph_infty (n : ℕ) :
    productPairSphereHomeomorph n ∞ = spherePole ((n + 1) + (n + 1)) := by
  change JamesSphere.pairingHomeomorph (n + 1) ∞ = _
  exact JamesSphere.pairingHomeomorph_infty (n + 1)

end NoExoticSixSphere.SuspensionProductComparison
