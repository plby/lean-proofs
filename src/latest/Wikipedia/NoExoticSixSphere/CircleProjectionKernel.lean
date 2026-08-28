import Wikipedia.NoExoticSixSphere.ProductProjectionHomology
import Wikipedia.NoExoticSixSphere.SplitProjectionKernel
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProductNaturality

/-!
# The circle-product projection kernel is naturally one degree lower

Restrict the actual circle-product homology splitting to the kernel of
second projection. Its second coordinate is the proved circle boundary
map, whose naturality retains the original map on the second factor.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.CircleProjectionKernel

variable (X : Type) [TopologicalSpace X]

def equiv (d : ℕ) : ProductProjectionHomology.Kernel CircleTopology.Circle X (d + 1) ≃ₗ[ℤ]
    SingularHomology X d :=
  SplitProjectionKernel.equiv (circleProductHomologyEquiv X d).toAddEquiv
    (ProductProjectionHomology.projection CircleTopology.Circle X (d + 1)) (fun _ ↦ rfl)

theorem equiv_apply (d : ℕ) (a : ProductProjectionHomology.Kernel CircleTopology.Circle X (d + 1)) :
    equiv X d a = (circleProductHomologyEquiv X d a.val).2 := rfl

variable {X} {Z : Type} [TopologicalSpace Z]

theorem equiv_naturality (f : C(X, Z)) (d : ℕ)
    (a : ProductProjectionHomology.Kernel CircleTopology.Circle X (d + 1)) :
    equiv Z d (ProductProjectionHomology.map CircleTopology.Circle f (d + 1) a) =
      singularHomologyMap f d (equiv X d a) :=
  congrArg Prod.snd (circleProductHomologyEquiv_naturality f d a.val)

end NoExoticSixSphere.CircleProjectionKernel
