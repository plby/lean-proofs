import Wikipedia.HopfProblem.DegreeCollapseCommonSmallIntegralCapCohomology
import Wikipedia.HopfProblem.DegreeCollapseIntegralConnectingUnionCocycles
import Wikipedia.NoExoticSixSphere.CommonSmallUnionCap

/-!
# Original integral union cap agrees with overlap-localized cap

The original common-small simplex inclusion into the overlap/union
small complex preserves the ambient chain. Both caps therefore have
the same image under the actual injective overlap inclusion.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralCap

open NoExoticSixSphere SingularCohomologyFree
open IntegralCap (Coefficient)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

/-- Pulling back an original union cochain gives the actual overlap-localized cap. -/
theorem capInDegree_union {p q n : ℕ} (h : p + q = n)
    (θ : RelativeIntegralCap.Cochain (A ∪ B) p) (c : (complex U A V B).X n) :
    capInDegree U A V B h
        (((dualMap (RelativeCoefficients.smallToUnionQuotient Coefficient A B)).f p).hom θ) c =
      SmallIntegralCap.capInDegree (U ∩ V) (A ∪ B) h θ
        ((((SimplicialCoefficients.chains Coefficient).map
          (SingularSubcomplex.commonToOverlapSmall U A V B)).f n).hom c) := by
  apply SmallIntegralCap.inclusion_injective (U ∩ V) q
  have he := congrArg (fun m => (m.f n).hom c)
    (SingularSubcomplex.commonToOverlapSmall_chain_inclusion U A V B Coefficient)
  apply (inclusion_capInDegree U A V B h _ c).trans
  apply Eq.trans _ (SmallIntegralCap.inclusion_capInDegree (U ∩ V) (A ∪ B) h θ _).symm
  exact congrArg₂ (fun α t => IntegralCap.capInDegree h α t)
    (SmallRelativeIntegralCochains.toAbsolute_union A B p θ) he.symm

end Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralCap
