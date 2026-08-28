import Wikipedia.HopfProblem.CuspNormalizationGermsClosure
import Wikipedia.HopfProblem.CuspNormalizationGermsClosureTotal
import Wikipedia.HopfProblem.CuspNormalizationGermsBirational
import Wikipedia.HopfProblem.CuspNormalizationGermsNormal

/-!
# Integral closure of actual singular analytic function germs

The branch rings are the actual analytic germ rings in two complex
variables, whose integral closedness has been proved analytically. The
coordinate-cofactor construction supplies the actual total-fraction
comparison. Consequently the product of these branch rings is the
literal integral closure of the singular function-germ ring inside its
genuine total fraction ring. No normality or birationality premise remains.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

attribute [local instance] GermsFractions.productFractionAlgebra

/-- The actual branch product is the integral closure of the actual
restriction image in the product of its branch fraction fields. -/
theorem branchImage_product_isIntegralClosure (s : Finset (Fin 3)) :
    IsIntegralClosure (s → BranchGerm) (BranchImage s) (s → FractionRing BranchGerm) :=
  GermsClosure.product_isIntegralClosure (fun _ : s => BranchGerm) (BranchImage s)
    (branchImage_coordinate_surjective s)

def branchImageIntegralClosureEquiv (s : Finset (Fin 3)) :
    (s → BranchGerm) ≃ₐ[BranchImage s]
      integralClosure (BranchImage s) (s → FractionRing BranchGerm) :=
  GermsClosure.productIntegralClosureEquiv (fun _ : s => BranchGerm) (BranchImage s)
    (branchImage_coordinate_surjective s)

@[simp] theorem branchImageIntegralClosureEquiv_coe (s : Finset (Fin 3)) (f : s → BranchGerm) :
    (branchImageIntegralClosureEquiv s f : s → FractionRing BranchGerm) =
      GermsFractions.productFractionMap (fun _ : s => BranchGerm) f :=
  GermsClosure.productIntegralClosureEquiv_coe (fun _ : s => BranchGerm) (BranchImage s)
    (branchImage_coordinate_surjective s) f

/-- The proved total-fraction comparison extends the actual restriction
of singular function germs to their branches. -/
theorem restrictedTotalFractionEquiv_restriction_diagram
    (s : Finset (Fin 3)) (φ : RestrictedAnalyticGerm s) :
    restrictedTotalFractionEquiv s
      (algebraMap (RestrictedAnalyticGerm s) (FractionRing (RestrictedAnalyticGerm s)) φ) =
        GermsFractions.productFractionMap (fun _ : s => BranchGerm)
          (restrictionToBranches s φ) := by
  funext j
  exact restrictedTotalFractionEquiv_algebraMap_apply s φ j

/-- The actual branch product mapped into the genuine total fraction
ring of the singular analytic function-germ ring. -/
def restrictedProductToTotalFraction (s : Finset (Fin 3)) :
    (s → BranchGerm) →+* FractionRing (RestrictedAnalyticGerm s) :=
  GermsClosure.totalProductMap (fun _ : s => BranchGerm) (restrictedTotalFractionEquiv s)

@[simp] theorem restrictedProductToTotalFraction_diagram
    (s : Finset (Fin 3)) (f : s → BranchGerm) :
    restrictedTotalFractionEquiv s (restrictedProductToTotalFraction s f) =
      GermsFractions.productFractionMap (fun _ : s => BranchGerm) f :=
  (restrictedTotalFractionEquiv s).apply_symm_apply _

/-- Integral closure is taken in the genuine total fraction ring, with
the explicitly defined actual branch-product inclusion. -/
theorem restrictedProduct_isIntegralClosure (s : Finset (Fin 3)) :
    letI := (restrictedProductToTotalFraction s).toAlgebra
    IsIntegralClosure (s → BranchGerm) (RestrictedAnalyticGerm s)
      (FractionRing (RestrictedAnalyticGerm s)) :=
  GermsClosure.totalProduct_isIntegralClosure (fun _ : s => BranchGerm)
    (restrictionToBranches s) (restrictionToBranches_finite s) (restrictedTotalFractionEquiv s)
    (restrictedTotalFractionEquiv_restriction_diagram s)

/-- Actual branch germs are the literal integral closure of the actual
singular function-germ ring in its total fraction ring. -/
def restrictedBranchIntegralClosureEquiv (s : Finset (Fin 3)) :
    (s → BranchGerm) ≃+*
      integralClosure (RestrictedAnalyticGerm s) (FractionRing (RestrictedAnalyticGerm s)) :=
  GermsClosure.totalProductIntegralClosureEquiv (fun _ : s => BranchGerm)
    (restrictionToBranches s) (restrictionToBranches_finite s) (restrictedTotalFractionEquiv s)
    (restrictedTotalFractionEquiv_restriction_diagram s)

@[simp] theorem restrictedBranchIntegralClosureEquiv_coe
    (s : Finset (Fin 3)) (f : s → BranchGerm) :
    (restrictedBranchIntegralClosureEquiv s f : FractionRing (RestrictedAnalyticGerm s)) =
      restrictedProductToTotalFraction s f :=
  GermsClosure.totalProductIntegralClosureEquiv_coe (fun _ : s => BranchGerm)
    (restrictionToBranches s) (restrictionToBranches_finite s) (restrictedTotalFractionEquiv s)
    (restrictedTotalFractionEquiv_restriction_diagram s) f

/-- The integral-closure equivalence carries actual branch restriction
to the canonical inclusion of the singular ring into its integral closure. -/
@[simp] theorem restrictedBranchIntegralClosureEquiv_restriction
    (s : Finset (Fin 3)) (φ : RestrictedAnalyticGerm s) :
    restrictedBranchIntegralClosureEquiv s (restrictionToBranches s φ) =
      algebraMap (RestrictedAnalyticGerm s)
        (integralClosure (RestrictedAnalyticGerm s) (FractionRing (RestrictedAnalyticGerm s))) φ :=
  GermsClosure.totalProductIntegralClosureEquiv_restriction (fun _ : s => BranchGerm)
    (restrictionToBranches s) (restrictionToBranches_finite s) (restrictedTotalFractionEquiv s)
    (restrictedTotalFractionEquiv_restriction_diagram s) φ

theorem restrictedBranchIntegralClosureEquiv_ambient
    (s : Finset (Fin 3)) (φ : AmbientGerm) :
    restrictedBranchIntegralClosureEquiv s (toBranches s φ) =
      algebraMap (RestrictedAnalyticGerm s)
        (integralClosure (RestrictedAnalyticGerm s) (FractionRing (RestrictedAnalyticGerm s)))
          ((toPlaneUnion s).rangeRestrict φ) := by
  rw [← restrictionToBranches_rangeRestrict, restrictedBranchIntegralClosureEquiv_restriction]

end Wikipedia.HopfProblem.CuspNormalization.Germs
