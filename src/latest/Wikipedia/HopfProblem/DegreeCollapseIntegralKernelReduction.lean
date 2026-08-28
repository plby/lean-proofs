import Wikipedia.HopfProblem.DegreeCollapsePrimitiveClassSplit
import Wikipedia.HopfProblem.SphereHomologyCoefficientsAlgebra

/-!
# Reducing an integral detector kernel to its actual residue kernel

Let R be an onto coefficient reduction with kernel twice the original
group. If a residue functional agrees with the integral detector modulo
two, a value-one detector class corrects every residue-kernel lift into
the exact integral kernel. The restricted reduction is onto and its
kernel is exactly twice that integral kernel. No torsion-freeness of
the original group is assumed.
-/

noncomputable section

open Function Set

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralKernelReduction

open SphereHomologyCoefficients

variable {H V : Type} [AddCommGroup H] [Module ℤ H] [AddCommGroup V] [Module ℤ V]
  (R : H →ₗ[ℤ] V) (p : H →ₗ[ℤ] ℤ) (b : V →ₗ[ℤ] ZMod 2)
  (hcomp : ∀ x, b (R x) = (p x : ZMod 2))

def reduction : LinearMap.ker p →ₗ[ℤ] LinearMap.ker b := by
  let F : LinearMap.ker p →+ LinearMap.ker b := {
    toFun x := ⟨R x, by
      change b (R x.val) = 0
      rw [hcomp, show p x.val = 0 from x.property, Int.cast_zero]⟩
    map_zero' := Subtype.ext (map_zero R)
    map_add' := fun x y ↦ Subtype.ext (map_add R x.val y.val) }
  exact F.toIntLinearMap

theorem reduction_val (x : LinearMap.ker p) : (reduction R p b hcomp x).val = R x := rfl

variable (hker : LinearMap.ker R = scalarImage 2 H)

include hker in
theorem twice_maps_zero (x : H) : R ((2 : ℤ) • x) = 0 := by
  have hx : (2 : ℤ) • x ∈ scalarImage 2 H := by
    refine ⟨x, ?_⟩
    change ((2 : ℤ) • (LinearMap.id : H →ₗ[ℤ] H)) x = (2 : ℤ) • x
    rw [two_zsmul, LinearMap.add_apply, LinearMap.id_apply, two_zsmul]
  rw [← hker] at hx
  exact hx

include hker in
theorem projection_same_reduction (d : H) (x : H) (hx : (p x : ZMod 2) = 0) :
    R (PrimitiveSplitting.projection p d x) = R x := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (p x) 2).mp hx
  have he : p x • d = (2 : ℤ) • (k • d) := by
    calc
      p x • d = (2 * k) • d := congrArg (fun z : ℤ ↦ z • d) hk
      _ = k • d + k • d := by rw [two_mul, add_zsmul]
      _ = (2 : ℤ) • (k • d) := (two_zsmul (k • d)).symm
  rw [PrimitiveSplitting.projection_apply, map_sub, he, twice_maps_zero R hker, sub_zero]

include hker in
theorem reduction_surjective (hR : Surjective R) (d : H) (hd : p d = 1) :
    Surjective (reduction R p b hcomp) := by
  intro y
  obtain ⟨x, hx⟩ := hR y.val
  have hz : (p x : ZMod 2) = 0 := (hcomp x).symm.trans ((congrArg b hx).trans y.property)
  refine ⟨⟨PrimitiveSplitting.projection p d x,
    PrimitiveSplitting.projection_coordinate p d hd x⟩, ?_⟩
  apply Subtype.ext
  exact (projection_same_reduction R p hker d x hz).trans hx

include hker in
theorem reduction_kernel : LinearMap.ker (reduction R p b hcomp) =
    scalarImage 2 (LinearMap.ker p) := by
  ext x
  constructor
  · intro hx
    have hRx : R x.val = 0 := congrArg Subtype.val hx
    have hm : x.val ∈ scalarImage 2 H := by rw [← hker]; exact hRx
    obtain ⟨y, hy⟩ := hm
    have hy' : (2 : ℤ) • y = x.val := by
      change ((2 : ℤ) • (LinearMap.id : H →ₗ[ℤ] H)) y = x.val at hy
      rw [two_zsmul, LinearMap.add_apply, LinearMap.id_apply] at hy
      rwa [two_zsmul]
    have hpy : p y = 0 := by
      have h : p ((2 : ℤ) • y) = 0 := (congrArg p hy').trans x.property
      rw [map_zsmul] at h
      change 2 * p y = 0 at h
      omega
    refine ⟨⟨y, hpy⟩, ?_⟩
    exact Subtype.ext hy'
  · rintro ⟨y, hy⟩
    change reduction R p b hcomp x = 0
    apply Subtype.ext
    have hy' : (2 : ℤ) • y.val = x.val := congrArg Subtype.val hy
    change R x.val = 0
    rw [← hy']
    exact twice_maps_zero R hker y.val

def quotientEquiv (hR : Surjective R) (d : H) (hd : p d = 1) :
    (LinearMap.ker p ⧸ scalarImage 2 (LinearMap.ker p)) ≃ₗ[ℤ] LinearMap.ker b := by
  let E := (Submodule.quotEquivOfEq _ _ (reduction_kernel R p b hcomp hker).symm).trans
    ((reduction R p b hcomp).quotKerEquivOfSurjective
      (reduction_surjective R p b hcomp hker hR d hd))
  let ea : (LinearMap.ker p ⧸ scalarImage 2 (LinearMap.ker p)) ≃+ LinearMap.ker b := {
    toEquiv := E.toEquiv
    map_add' := fun x y ↦ E.map_add' x y }
  exact ea.toIntLinearEquiv

theorem quotientEquiv_mk (hR : Surjective R) (d : H) (hd : p d = 1)
    (x : LinearMap.ker p) :
    quotientEquiv R p b hcomp hker hR d hd (Submodule.Quotient.mk x) = reduction R p b hcomp x := by
  change (reduction R p b hcomp).quotKerEquivOfSurjective
    (reduction_surjective R p b hcomp hker hR d hd)
    (Submodule.quotEquivOfEq _ _ (reduction_kernel R p b hcomp hker).symm
      (Submodule.Quotient.mk x)) = _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

end Wikipedia.HopfProblem.DegreeCollapse.IntegralKernelReduction
