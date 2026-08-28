import Wikipedia.NoExoticSixSphere.SuspensionProductNullhomotopy
import Wikipedia.NoExoticSixSphere.IteratedSphereHomotopyEquivalence
import Wikipedia.HopfProblem.DegreeCollapseEuclideanProductCoordinates

/-!
# Finite-suspension comparison after literal Euclidean product coordinates

An explicit coordinate homeomorphism identifies the product compactification
with the standard sphere. The meridian quotient becomes an actual sphere
homotopy equivalence, and its commuting square persists under every specified
finite number of suspensions. No vanishing theorem is used or asserted.
-/

noncomputable section

open scoped ContinuousMap OnePoint

namespace NoExoticSixSphere.SuspensionProductComparison

open Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct

def productSphereHomeomorph (n : ℕ) :
    OnePoint (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₜ Sphere (n + 1) :=
  ((Homeomorph.prodComm (EuclideanSpace ℝ (Fin n)) ℝ).trans
    (coordinates n).toHomeomorph).onePointCongr.trans (euclideanOnePointSphere (n + 1))

def sphereQuotientEquiv (n : ℕ) : Sphere (n + 1) ≃ₕ Sphere (n + 1) :=
  (rightQuotientEquiv n).trans (productSphereHomeomorph n).toHomotopyEquiv

theorem sphereQuotientEquiv_apply (n : ℕ) (y : Sphere (n + 1)) :
    (sphereQuotientEquiv n).toFun y = productSphereHomeomorph n (rightQuotient n y) := by
  change productSphereHomeomorph n ((rightQuotientEquiv n).toFun y) = _
  rw [rightQuotientEquiv_toFun]

variable {m n : ℕ}

def productSphereMap
    (f : C(OnePoint (EuclideanSpace ℝ (Fin m)), OnePoint (EuclideanSpace ℝ (Fin n))))
    (hf : f ∞ = ∞) : C(Sphere (m + 1), Sphere (n + 1)) :=
  (productSphereHomeomorph n).toHomotopyEquiv.toFun.comp
    ((OnePointProduct.productMap f (ContinuousMap.id (OnePoint ℝ)) hf
      (ContinuousMap.id_apply ∞)).comp
        (productSphereHomeomorph m).symm.toHomotopyEquiv.toFun)

theorem sphereQuotient_suspension
    (f : C(OnePoint (EuclideanSpace ℝ (Fin m)), OnePoint (EuclideanSpace ℝ (Fin n))))
    (hf : f ∞ = ∞) :
    (sphereQuotientEquiv n).toFun.comp (SphereMapSuspension.map (sphereMap f)) =
      (productSphereMap f hf).comp (sphereQuotientEquiv m).toFun := by
  apply ContinuousMap.ext
  intro y
  change (sphereQuotientEquiv n).toFun (SphereMapSuspension.map (sphereMap f) y) =
    productSphereHomeomorph n
      (OnePointProduct.productMap f (ContinuousMap.id (OnePoint ℝ)) hf
        (ContinuousMap.id_apply ∞)
        ((productSphereHomeomorph m).symm ((sphereQuotientEquiv m).toFun y)))
  rw [sphereQuotientEquiv_apply, sphereQuotientEquiv_apply, Homeomorph.symm_apply_apply,
    rightQuotient_suspension]

theorem iterate_suspension_nullhomotopic_iff_product
    (f : C(OnePoint (EuclideanSpace ℝ (Fin m)), OnePoint (EuclideanSpace ℝ (Fin n))))
    (hf : f ∞ = ∞) (r : ℕ) :
    (SphereMapSuspension.iterate (SphereMapSuspension.map (sphereMap f)) r).Nullhomotopic ↔
      (SphereMapSuspension.iterate (productSphereMap f hf) r).Nullhomotopic := by
  apply SphereMapSuspension.iterate_nullhomotopic_iff_of_equiv_square
    (sphereQuotientEquiv m) (sphereQuotientEquiv n)
  rw [sphereQuotient_suspension f hf]

end NoExoticSixSphere.SuspensionProductComparison
