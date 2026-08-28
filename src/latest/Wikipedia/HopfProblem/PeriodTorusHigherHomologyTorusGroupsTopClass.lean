import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroups
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePointClass
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsCoordinateAlgebra

/-!
# A genuine top-degree generator of each product torus

The top class is an element of actual integral singular homology. Its
normalization is specified by the proved recursive Mayer--Vietoris
equivalence. Degree zero is the actual point class, and splitting off a
circle sends each successive top class to `(0, previous top class)`.

This normalization does not assume a comparison with a cross product.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris

/-- The genuine top-degree singular homology class normalized to one in
the proved recursive homology coordinates. -/
def productTorusTopClass (n : ℕ) : SingularHomology (ProductTorus n) n :=
  (productTorusHomologyEquiv n n).symm (fun _ => (1 : ℤ))

@[simp] theorem productTorusHomologyEquiv_topClass (n : ℕ) :
    productTorusHomologyEquiv n n (productTorusTopClass n) = fun _ => (1 : ℤ) :=
  (productTorusHomologyEquiv n n).apply_symm_apply _

/-- The degree-zero normalization is the genuine singular class of the
unique point of the empty product. -/
@[simp] theorem productTorusTopClass_zero :
    productTorusTopClass 0 = pointClass (0 : ProductTorus 0) := by
  apply (productTorusHomologyEquiv 0 0).injective
  rw [productTorusHomologyEquiv_topClass, productTorusHomologyEquiv_zero]
  simp only [LinearEquiv.trans_apply, connectedHomologyZeroEquiv_pointClass]
  rfl

/-- The actual circle-product splitting sends the normalized top class
to zero in the projection coordinate and the previous top class in the
signed connecting coordinate. -/
theorem productTorusTopClass_succ_coordinates (n : ℕ) :
    circleProductHomologyEquiv (ProductTorus n) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)
          (productTorusTopClass (n + 1))) =
      (0, productTorusTopClass n) := by
  apply Prod.ext
  · exact @Subsingleton.elim (SingularHomology (ProductTorus n) (n + 1))
      (productTorus_homology_subsingleton_of_lt (Nat.lt_succ_self n)) _ _
  · apply (productTorusHomologyEquiv n n).injective
    have h := congrArg Prod.snd
      (productTorusHomologyEquiv_succ_apply n n (productTorusTopClass (n + 1)))
    rw [productTorusHomologyEquiv_topClass, binomialModuleSuccEquiv_top] at h
    exact h.symm.trans (productTorusHomologyEquiv_topClass n).symm

@[simp] theorem productTorusTopClass_succ_projection (n : ℕ) :
    circleProjectionHomology (ProductTorus n) (n + 1)
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)
          (productTorusTopClass (n + 1))) = 0 :=
  congrArg Prod.fst (productTorusTopClass_succ_coordinates n)

@[simp] theorem productTorusTopClass_succ_boundary (n : ℕ) :
    circleBoundary (ProductTorus n) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)
          (productTorusTopClass (n + 1))) = productTorusTopClass n :=
  congrArg Prod.snd (productTorusTopClass_succ_coordinates n)

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
