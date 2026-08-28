import Wikipedia.NoExoticSixSphere.ProductProjectionHomology
import Wikipedia.HopfProblem.OrbitPairProductCoverVanishing

/-!
# Projection kernels in the actual product-cover sequence

After identifying the two contractible cover pieces with the second
factor, the signed intersection map has coordinates projection and minus
projection. Thus the actual connecting map lands in the overlap's
projection kernel. A fixed section has zero connecting image.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology
open Wikipedia.HopfProblem.OrbitPair.ProductCover

namespace NoExoticSixSphere.ProductCoverKernel

variable {Y : Type} [TopologicalSpace Y] (X : Type) [TopologicalSpace X] (U V : Set Y)

abbrev Overlap : Type := (piece (X := X) U ∩ piece V : Set (Y × X))

abbrev Kernel (d : ℕ) := LinearMap.ker (singularHomologyMap (overlapProjection (X := X) U V) d)

instance kernelModule (d : ℕ) : Module ℤ (Kernel X U V d) := (Kernel X U V d).module

variable [ContractibleSpace U] [ContractibleSpace V]

omit [ContractibleSpace V] in
theorem left_fst (d : ℕ) (a : SingularHomology (Overlap X U V) d) :
    pieceHomologyEquiv U d (leftHomologyMap (piece U) (piece V) d a).1 =
      singularHomologyMap (overlapProjection U V) d a := by
  rw [leftHomologyMap_apply]
  exact (LinearMap.congr_fun (singularHomologyMap_comp
    (ContinuousMap.inclusion (Set.inter_subset_left : piece U ∩ piece V ⊆ piece U))
      (projection U) d) a).symm

omit [ContractibleSpace U] in
theorem left_snd (d : ℕ) (a : SingularHomology (Overlap X U V) d) :
    pieceHomologyEquiv V d (leftHomologyMap (piece U) (piece V) d a).2 =
      -singularHomologyMap (overlapProjection U V) d a := by
  rw [leftHomologyMap_apply, map_neg]
  exact congrArg Neg.neg (LinearMap.congr_fun (singularHomologyMap_comp
    (ContinuousMap.inclusion (Set.inter_subset_right : piece U ∩ piece V ⊆ piece V))
      (projection V) d) a).symm

theorem left_eq_zero_iff (d : ℕ) (a : SingularHomology (Overlap X U V) d) :
    leftHomologyMap (piece U) (piece V) d a = 0 ↔
      singularHomologyMap (overlapProjection U V) d a = 0 := by
  constructor
  · intro h
    have he := left_fst X U V d a
    rw [h] at he
    exact he.symm.trans (pieceHomologyEquiv U d).map_zero
  · intro h
    apply Prod.ext
    · apply (pieceHomologyEquiv U d).injective
      rw [left_fst, h]
      exact (pieceHomologyEquiv U d).map_zero.symm
    · apply (pieceHomologyEquiv V d).injective
      rw [left_snd, h, neg_zero]
      exact (pieceHomologyEquiv V d).map_zero.symm

variable (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ)

def connecting (d : ℕ) : SingularHomology (Y × X) (d + 1) →ₗ[ℤ]
    SingularHomology (Overlap X U V) d :=
  connectingHomomorphism (piece U) (piece V) (piece_open U hU) (piece_open V hV)
    (piece_cover U V hc) d

theorem connecting_mem (d : ℕ) (a : SingularHomology (Y × X) (d + 1)) :
    connecting X U V hU hV hc d a ∈ Kernel X U V d := by
  apply (left_eq_zero_iff X U V d _).mp
  exact LinearMap.congr_fun (connectingHomomorphism_comp_left (piece U) (piece V)
    (piece_open U hU) (piece_open V hV) (piece_cover U V hc) d) a

def kernelConnecting (d : ℕ) :
    ProductProjectionHomology.Kernel Y X (d + 1) →ₗ[ℤ] Kernel X U V d :=
  ((connecting X U V hU hV hc d).comp
    (ProductProjectionHomology.Kernel Y X (d + 1)).subtype).codRestrict _
      (fun a ↦ connecting_mem X U V hU hV hc d a.val)

theorem kernelConnecting_val (d : ℕ) (a : ProductProjectionHomology.Kernel Y X (d + 1)) :
    (kernelConnecting X U V hU hV hc d a).val = connecting X U V hU hV hc d a.val := rfl

omit [ContractibleSpace U] [ContractibleSpace V] in
theorem section_right (u : U) (d : ℕ) (a : SingularHomology X d) :
    rightHomologyMap (piece U) (piece V) d
      (singularHomologyMap (fixedSection U u) d a, 0) =
        singularHomologyMap (ProductProjectionHomology.sectionMap Y X u.val) d a := by
  rw [rightHomologyMap_apply, map_zero, add_zero]
  exact (LinearMap.congr_fun (singularHomologyMap_comp (fixedSection U u)
    (subtypeInclusion (piece U)) d) a).symm

omit [ContractibleSpace U] [ContractibleSpace V] in
theorem connecting_section (u : U) (d : ℕ) (a : SingularHomology X (d + 1)) :
    connecting X U V hU hV hc d
      (singularHomologyMap (ProductProjectionHomology.sectionMap Y X u.val) (d + 1) a) = 0 := by
  rw [← section_right X U V u (d + 1) a]
  exact LinearMap.congr_fun (rightHomologyMap_comp_connecting (piece U) (piece V)
    (piece_open U hU) (piece_open V hV) (piece_cover U V hc) d) _

theorem kernelConnecting_surjective (u : U) (d : ℕ) :
    Function.Surjective (kernelConnecting X U V hU hV hc d) := by
  intro b
  have hb : b.val ∈ LinearMap.ker (leftHomologyMap (piece U) (piece V) d) :=
    (left_eq_zero_iff X U V d b.val).mpr b.property
  rw [← exact_at_intersection (piece U) (piece V)
    (piece_open U hU) (piece_open V hV) (piece_cover U V hc) d] at hb
  obtain ⟨a, ha⟩ := hb
  let s := singularHomologyMap (ProductProjectionHomology.sectionMap Y X u.val) (d + 1)
    (ProductProjectionHomology.projection Y X (d + 1) a)
  have hp : a - s ∈ ProductProjectionHomology.Kernel Y X (d + 1) := by
    change ProductProjectionHomology.projection Y X (d + 1) (a - s) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (ProductProjectionHomology.projection_section Y X u.val _ _).symm
  refine ⟨⟨a - s, hp⟩, ?_⟩
  apply Subtype.ext
  change connecting X U V hU hV hc d (a - s) = b.val
  rw [map_sub, connecting_section X U V hU hV hc u d, sub_zero]
  exact ha

end NoExoticSixSphere.ProductCoverKernel
