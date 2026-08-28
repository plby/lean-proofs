import Wikipedia.NoExoticSixSphere.ProductCoverKernelNaturality

/-!
# Transporting the kernel connecting equivalence to the literal overlap product

The actual overlap is homeomorphic to the product of the first-factor
overlap and the second factor. Its homology equivalence preserves second
projection and commutes with maps of the second factor. Transport gives
a natural degree-lowering equivalence between product projection kernels.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology
open Wikipedia.HopfProblem.OrbitPair.ProductCover

namespace NoExoticSixSphere.ProductCoverKernel

variable {Y : Type} [TopologicalSpace Y] (X : Type) [TopologicalSpace X] (U V : Set Y)

theorem overlapHomeomorph_projection (d : ℕ) (a : SingularHomology (Overlap X U V) d) :
    ProductProjectionHomology.projection (U ∩ V : Set Y) X d
      (homeomorphHomologyEquiv (overlapHomeomorph (X := X) U V) d a) =
        singularHomologyMap (overlapProjection U V) d a :=
  (LinearMap.congr_fun (singularHomologyMap_comp
    (overlapHomeomorph (X := X) U V).toHomotopyEquiv.toFun
      (ContinuousMap.snd : C((U ∩ V : Set Y) × X, X)) d) a).symm

def overlapEquiv (d : ℕ) : Kernel X U V d ≃ₗ[ℤ]
    ProductProjectionHomology.Kernel (U ∩ V : Set Y) X d := by
  let E := homeomorphHomologyEquiv (overlapHomeomorph (X := X) U V) d
  refine
    { toLinearMap := (E.toLinearMap.comp (Kernel X U V d).subtype).codRestrict _ ?_
      invFun := fun a ↦ ⟨E.symm a.val, ?_⟩
      left_inv := fun a ↦ Subtype.ext (E.symm_apply_apply a.val)
      right_inv := fun a ↦ Subtype.ext (E.apply_symm_apply a.val) }
  · intro a
    exact (overlapHomeomorph_projection X U V d a.val).trans a.property
  · have h := overlapHomeomorph_projection X U V d (E.symm a.val)
    change ProductProjectionHomology.projection (U ∩ V : Set Y) X d
      (E (E.symm a.val)) = singularHomologyMap (overlapProjection U V) d (E.symm a.val) at h
    rw [E.apply_symm_apply] at h
    exact h.symm.trans a.property

theorem overlapEquiv_apply (d : ℕ) (a : Kernel X U V d) :
    (overlapEquiv X U V d a).val =
      homeomorphHomologyEquiv (overlapHomeomorph (X := X) U V) d a.val := rfl

variable {X} {Z : Type} [TopologicalSpace Z]

theorem overlapEquiv_naturality (f : C(X, Z)) (d : ℕ) (a : Kernel X U V d) :
    overlapEquiv Z U V d (mapOverlapKernel U V f d a) =
      ProductProjectionHomology.map (U ∩ V : Set Y) f d (overlapEquiv X U V d a) := by
  apply Subtype.ext
  have h : (overlapHomeomorph (X := Z) U V).toHomotopyEquiv.toFun.comp (overlapMap U V f) =
      (ProductProjectionHomology.secondMap (U ∩ V : Set Y) f).comp
        (overlapHomeomorph (X := X) U V).toHomotopyEquiv.toFun := rfl
  have hh := congrArg (fun q ↦ singularHomologyMap q d) h
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at hh
  exact LinearMap.congr_fun hh a.val

variable (X) [ContractibleSpace U] [ContractibleSpace V]
    (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ) (u : (U ∩ V : Set Y))

def productConnectingEquiv (d : ℕ) : ProductProjectionHomology.Kernel Y X (d + 1) ≃ₗ[ℤ]
    ProductProjectionHomology.Kernel (U ∩ V : Set Y) X d :=
  (connectingEquiv X U V hU hV hc u d).trans (overlapEquiv X U V d)

theorem productConnectingEquiv_apply (d : ℕ)
    (a : ProductProjectionHomology.Kernel Y X (d + 1)) :
    (productConnectingEquiv X U V hU hV hc u d a).val =
      homeomorphHomologyEquiv (overlapHomeomorph (X := X) U V) d
        (connecting X U V hU hV hc d a.val) := rfl

variable {X}

theorem productConnectingEquiv_naturality (f : C(X, Z)) (d : ℕ)
    (a : ProductProjectionHomology.Kernel Y X (d + 1)) :
    productConnectingEquiv Z U V hU hV hc u d (ProductProjectionHomology.map Y f (d + 1) a) =
      ProductProjectionHomology.map (U ∩ V : Set Y) f d
        (productConnectingEquiv X U V hU hV hc u d a) := by
  change overlapEquiv Z U V d
    (connectingEquiv Z U V hU hV hc u d (ProductProjectionHomology.map Y f (d + 1) a)) = _
  rw [← connectingEquiv_naturality U V hU hV hc u f d a, overlapEquiv_naturality]
  rfl

end NoExoticSixSphere.ProductCoverKernel
