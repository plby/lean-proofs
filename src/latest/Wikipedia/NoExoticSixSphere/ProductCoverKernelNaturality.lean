import Wikipedia.NoExoticSixSphere.ProductCoverKernelEquivalence
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleMayerVietorisNaturality

/-!
# Naturality of the product-cover equivalence on projection kernels

Changing the second factor preserves both actual cover pieces. The
proved Mayer--Vietoris naturality theorem therefore applies to the
restricted connecting maps and their kernel equivalences.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology
open Wikipedia.HopfProblem.OrbitPair.ProductCover

namespace NoExoticSixSphere.ProductCoverKernel

variable {Y X Z : Type} [TopologicalSpace Y] [TopologicalSpace X] [TopologicalSpace Z]
    (U V : Set Y)

def overlapMap (f : C(X, Z)) : C(Overlap X U V, Overlap Z U V) :=
  ⟨fun p ↦ ⟨(p.val.1, f p.val.2), p.property⟩,
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (f.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _⟩

theorem overlapProjection_map (f : C(X, Z)) (d : ℕ)
    (a : SingularHomology (Overlap X U V) d) :
    singularHomologyMap (overlapProjection U V) d (singularHomologyMap (overlapMap U V f) d a) =
      singularHomologyMap f d (singularHomologyMap (overlapProjection U V) d a) := by
  have h : (overlapProjection (X := Z) U V).comp (overlapMap U V f) =
      f.comp (overlapProjection (X := X) U V) := rfl
  have hh := congrArg (fun q ↦ singularHomologyMap q d) h
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at hh
  exact LinearMap.congr_fun hh a

def mapOverlapKernel (f : C(X, Z)) (d : ℕ) : Kernel X U V d →ₗ[ℤ] Kernel Z U V d :=
  ((singularHomologyMap (overlapMap U V f) d).comp (Kernel X U V d).subtype).codRestrict _ (by
    intro a
    change singularHomologyMap (overlapProjection U V) d
      (singularHomologyMap (overlapMap U V f) d a.val) = 0
    rw [overlapProjection_map, a.property, map_zero])

theorem mapOverlapKernel_val (f : C(X, Z)) (d : ℕ) (a : Kernel X U V d) :
    (mapOverlapKernel U V f d a).val = singularHomologyMap (overlapMap U V f) d a.val := rfl

variable [ContractibleSpace U] [ContractibleSpace V]
    (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ)

omit [ContractibleSpace U] [ContractibleSpace V] in
theorem connecting_naturality (f : C(X, Z)) (d : ℕ) (a : SingularHomology (Y × X) (d + 1)) :
    singularHomologyMap (overlapMap U V f) d (connecting X U V hU hV hc d a) =
      connecting Z U V hU hV hc d
        (singularHomologyMap (ProductProjectionHomology.secondMap Y f) (d + 1) a) :=
  connectingHomomorphism_naturality_apply (ProductProjectionHomology.secondMap Y f)
    (piece (X := X) U) (piece (X := X) V) (piece (X := Z) U) (piece (X := Z) V)
    (fun _ h ↦ h) (fun _ h ↦ h)
    (piece_open U hU) (piece_open V hV) (piece_cover U V hc)
    (piece_open U hU) (piece_open V hV) (piece_cover U V hc) d a

theorem kernelConnecting_naturality (f : C(X, Z)) (d : ℕ)
    (a : ProductProjectionHomology.Kernel Y X (d + 1)) :
    mapOverlapKernel U V f d (kernelConnecting X U V hU hV hc d a) =
      kernelConnecting Z U V hU hV hc d (ProductProjectionHomology.map Y f (d + 1) a) := by
  apply Subtype.ext
  exact connecting_naturality U V hU hV hc f d a.val

theorem connectingEquiv_naturality (u : (U ∩ V : Set Y)) (f : C(X, Z)) (d : ℕ)
    (a : ProductProjectionHomology.Kernel Y X (d + 1)) :
    mapOverlapKernel U V f d (connectingEquiv X U V hU hV hc u d a) =
      connectingEquiv Z U V hU hV hc u d (ProductProjectionHomology.map Y f (d + 1) a) :=
  kernelConnecting_naturality U V hU hV hc f d a

end NoExoticSixSphere.ProductCoverKernel
