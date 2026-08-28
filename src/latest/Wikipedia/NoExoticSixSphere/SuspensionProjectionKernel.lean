import Wikipedia.NoExoticSixSphere.ProductCoverKernelTransport
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionTopology

/-!
# Natural degree reduction for suspension-product projection kernels

The actual suspension cone cover and its actual middle-band equivalence
give a degree-lowering equivalence on kernels of second projection.
The construction commutes with every continuous map of the second factor.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem CuspCentralHomology

namespace NoExoticSixSphere.SuspensionProjectionKernel

variable (P : Type) [TopologicalSpace P] [Nonempty P]

def overlapPoint : (Suspension.northOpen ∩ Suspension.southOpen : Set (Suspension P)) :=
  ⟨Classical.choose (Suspension.middleBand_nonempty (X := P)),
    Classical.choose_spec (Suspension.middleBand_nonempty (X := P))⟩

variable (X : Type) [TopologicalSpace X]

def equiv (d : ℕ) : ProductProjectionHomology.Kernel (Suspension P) X (d + 1) ≃ₗ[ℤ]
    ProductProjectionHomology.Kernel P X d :=
  (ProductCoverKernel.productConnectingEquiv X Suspension.northOpen Suspension.southOpen
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover
    (overlapPoint P) d).trans
      (ProductProjectionHomology.firstEquiv X (Suspension.middleBandHomotopyEquiv (X := P)) d)

variable {X} {Z : Type} [TopologicalSpace Z]

theorem equiv_naturality (f : C(X, Z)) (d : ℕ)
    (a : ProductProjectionHomology.Kernel (Suspension P) X (d + 1)) :
    equiv P Z d (ProductProjectionHomology.map (Suspension P) f (d + 1) a) =
      ProductProjectionHomology.map P f d (equiv P X d a) := by
  change ProductProjectionHomology.firstEquiv Z (Suspension.middleBandHomotopyEquiv (X := P)) d
    (ProductCoverKernel.productConnectingEquiv Z Suspension.northOpen Suspension.southOpen
      Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover
      (overlapPoint P) d (ProductProjectionHomology.map (Suspension P) f (d + 1) a)) = _
  rw [ProductCoverKernel.productConnectingEquiv_naturality,
    ProductProjectionHomology.firstEquiv_naturality]
  rfl

theorem map_bijective_iff (f : C(X, Z)) (d : ℕ) :
    Function.Bijective (ProductProjectionHomology.map (Suspension P) f (d + 1)) ↔
      Function.Bijective (ProductProjectionHomology.map P f d) := by
  have h : equiv P Z d ∘ ProductProjectionHomology.map (Suspension P) f (d + 1) =
      ProductProjectionHomology.map P f d ∘ equiv P X d := funext (equiv_naturality P f d)
  have h₁ := Function.Bijective.of_comp_iff' (equiv P Z d).bijective
    (ProductProjectionHomology.map (Suspension P) f (d + 1))
  have h₂ := Function.Bijective.of_comp_iff (ProductProjectionHomology.map P f d)
    (equiv P X d).bijective
  rw [← h₁, h, h₂]

end NoExoticSixSphere.SuspensionProjectionKernel
