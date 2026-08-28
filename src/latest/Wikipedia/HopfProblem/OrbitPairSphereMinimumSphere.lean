import Wikipedia.HopfProblem.OrbitPairSphereMinimumRetraction
import Wikipedia.NoExoticSixSphere.EquatorDimension

/-!
# The minimum semicircle locus is the actual sphere of one lower dimension

The unit tangent directions are the equator perpendicular to the initial
endpoint. The checked orthonormal coordinates on that actual hyperplane
identify them with the standard Euclidean sphere. Composing with the explicit
minimum parametrization gives a homeomorphism onto the literal minimum set.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.SphereSemicircle

open NoExoticSixSphere

def directionEquatorHomeomorph {n : ℕ} (a : Sphere n) : Direction a ≃ₜ Equator a where
  toFun y := ⟨⟨y.val, by
    simpa only [Metric.mem_sphere, dist_zero_right] using y.2.1⟩, y.2.2⟩
  invFun y := ⟨y.val.val, ClosedHemisphere.unit_norm y.val, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def directionSphereHomeomorph {n : ℕ} (a : Sphere (n + 1)) : Direction a ≃ₜ Sphere n :=
  (directionEquatorHomeomorph a).trans
    (equatorEuclideanHomeomorph a (n := n + 1) finrank_euclideanSpace_fin)

end Wikipedia.HopfProblem.OrbitPair.SphereSemicircle

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereSemicircle

def sphereMinimumHomeomorph {n m : ℕ} (a b : Sphere (n + 1))
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val)
    (hmesh : ∀ i : Fin (m + 1), Real.pi ^ 2 * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)
    (j : Fin m) : Sphere n ≃ₜ minimumSet a b τ :=
  (directionSphereHomeomorph a).symm.trans
    (directionMinimumHomeomorph a b τ hτ hzero hone hanti hmesh j)

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
