import Wikipedia.NoExoticSixSphere.ProductCoverProjectionKernel

/-!
# The product-cover connecting map is an equivalence on projection kernels

The fixed section corrects any connecting lift to have zero second
projection. Conversely, a class killed by both projection and connecting
is zero: exactness writes it as a pair of cover-piece classes, and a
section of the overlap realizes that pair as an intersection boundary.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology
open Wikipedia.HopfProblem.OrbitPair.ProductCover

namespace NoExoticSixSphere.ProductCoverKernel

variable {Y : Type} [TopologicalSpace Y] (X : Type) [TopologicalSpace X] (U V : Set Y)
    [ContractibleSpace U] [ContractibleSpace V]
    (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ) (u : (U ∩ V : Set Y))

include u in
theorem joint_kernel_eq_zero (d : ℕ) (a : SingularHomology (Y × X) (d + 1))
    (hp : ProductProjectionHomology.projection Y X (d + 1) a = 0)
    (hd : connecting X U V hU hV hc d a = 0) : a = 0 := by
  have ha : a ∈ LinearMap.ker (connectingHomomorphism (piece U) (piece V)
      (piece_open U hU) (piece_open V hV) (piece_cover U V hc) d) := hd
  rw [← exact_at_ambient (piece U) (piece V)
    (piece_open U hU) (piece_open V hV) (piece_cover U V hc) d] at ha
  obtain ⟨p, rfl⟩ := ha
  change singularHomologyMap (ContinuousMap.snd : C(Y × X, X)) (d + 1)
    (rightHomologyMap (piece U) (piece V) (d + 1) p) = 0 at hp
  rw [projection_right] at hp
  let b := singularHomologyMap (overlapSection U V u) (d + 1)
    (pieceHomologyEquiv U (d + 1) p.1)
  have hb : leftHomologyMap (piece U) (piece V) (d + 1) b = p := by
    rw [leftHomologyMap_apply]
    apply Prod.ext
    · apply (pieceHomologyEquiv U (d + 1)).injective
      change singularHomologyMap (projection U) (d + 1)
        (singularHomologyMap (ContinuousMap.inclusion _) (d + 1)
          (singularHomologyMap (overlapSection U V u) (d + 1) _)) = _
      rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
        ← LinearMap.comp_apply, ← singularHomologyMap_comp]
      change singularHomologyMap (ContinuousMap.id X) (d + 1) _ = _
      rw [singularHomologyMap_id]
      rfl
    · apply (pieceHomologyEquiv V (d + 1)).injective
      rw [map_neg]
      change -(singularHomologyMap (projection V) (d + 1)
        (singularHomologyMap (ContinuousMap.inclusion _) (d + 1)
          (singularHomologyMap (overlapSection U V u) (d + 1) _))) = _
      rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
        ← LinearMap.comp_apply, ← singularHomologyMap_comp]
      change -(singularHomologyMap (ContinuousMap.id X) (d + 1) _) = _
      rw [singularHomologyMap_id]
      exact (neg_eq_iff_add_eq_zero).mpr hp
  rw [← hb]
  exact LinearMap.congr_fun (leftHomologyMap_comp_right (piece U) (piece V) (d + 1)) b

include u in
theorem kernelConnecting_eq_zero (d : ℕ) (a : ProductProjectionHomology.Kernel Y X (d + 1))
    (ha : kernelConnecting X U V hU hV hc d a = 0) : a = 0 := by
  apply Subtype.ext
  exact joint_kernel_eq_zero X U V hU hV hc u d a.val a.property (congrArg Subtype.val ha)

include u in
theorem kernelConnecting_injective (d : ℕ) :
    Function.Injective (kernelConnecting X U V hU hV hc d) :=
  LinearMap.ker_eq_bot.mp
    (LinearMap.ker_eq_bot'.mpr (kernelConnecting_eq_zero X U V hU hV hc u d))

def connectingEquiv (d : ℕ) :
    ProductProjectionHomology.Kernel Y X (d + 1) ≃ₗ[ℤ] Kernel X U V d :=
  LinearEquiv.ofBijective (kernelConnecting X U V hU hV hc d)
    ⟨kernelConnecting_injective X U V hU hV hc u d,
      kernelConnecting_surjective X U V hU hV hc ⟨u.val, u.property.1⟩ d⟩

theorem connectingEquiv_apply (d : ℕ) (a : ProductProjectionHomology.Kernel Y X (d + 1)) :
    (connectingEquiv X U V hU hV hc u d a).val = connecting X U V hU hV hc d a.val := rfl

end NoExoticSixSphere.ProductCoverKernel
