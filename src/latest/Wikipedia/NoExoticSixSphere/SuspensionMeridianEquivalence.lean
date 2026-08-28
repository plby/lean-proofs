import Wikipedia.NoExoticSixSphere.ContractedQuotientEquivalence
import Wikipedia.NoExoticSixSphere.SuspensionMeridianContraction

/-!
# The actual meridian quotient is a homotopy equivalence

The whole-sphere contraction and the computed fibers construct an inverse
to the original quotient. The coordinate-swapped quotient used for the
product tube has an inverse as well. Both forward maps are identified
exactly, rather than only up to an unspecified homeomorphism.
-/

noncomputable section

open scoped ContinuousMap

namespace NoExoticSixSphere.SuspensionProductComparison

theorem exists_quotientEquiv (n : ℕ) :
    ∃ e : Sphere (n + 1) ≃ₕ OnePoint (ℝ × EuclideanSpace ℝ (Fin n)),
      e.toFun = quotient n := by
  obtain ⟨g, H, hpres, hend⟩ := exists_meridian_contracting_homotopy n
  exact ⟨ContractedQuotient.homotopyEquiv (quotient n) (isQuotientMap_quotient n)
    (meridian n) (quotient_eq_iff n) (meridianCenter n) hend H hpres, rfl⟩

def quotientEquiv (n : ℕ) :
    Sphere (n + 1) ≃ₕ OnePoint (ℝ × EuclideanSpace ℝ (Fin n)) :=
  (exists_quotientEquiv n).choose

theorem quotientEquiv_toFun (n : ℕ) : (quotientEquiv n).toFun = quotient n :=
  (exists_quotientEquiv n).choose_spec

def rightQuotientEquiv (n : ℕ) :
    Sphere (n + 1) ≃ₕ OnePoint (EuclideanSpace ℝ (Fin n) × ℝ) :=
  (quotientEquiv n).trans
    (Homeomorph.prodComm ℝ (EuclideanSpace ℝ (Fin n))).onePointCongr.toHomotopyEquiv

theorem rightQuotientEquiv_toFun (n : ℕ) :
    (rightQuotientEquiv n).toFun = rightQuotient n := by
  change (Homeomorph.prodComm ℝ (EuclideanSpace ℝ (Fin n))).onePointCongr.toHomotopyEquiv.toFun.comp
    (quotientEquiv n).toFun = _
  rw [quotientEquiv_toFun]
  rfl

end NoExoticSixSphere.SuspensionProductComparison
