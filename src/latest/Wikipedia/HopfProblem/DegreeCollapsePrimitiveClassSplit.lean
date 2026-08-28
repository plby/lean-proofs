import Wikipedia.HopfProblem.DegreeCollapseIntegerSplit
import Wikipedia.NoExoticSixSphere.IntegralSplitting
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Split off an actual primitive integral class

For an integral functional taking value one on `a`, the projection
`x ↦ x - l(x) • a` has kernel exactly the span of `a` and image exactly
the kernel of `l`. The quotient therefore identifies with that kernel.
The resulting product splitting retains the supplied class itself as
the integer summand, rather than choosing a different preimage of one.
-/

noncomputable section

open Function NoExoticSixSphere

namespace Wikipedia.HopfProblem.DegreeCollapse.PrimitiveSplitting

variable {H : Type*} [AddCommGroup H] [Module ℤ H]
  (l : H →ₗ[ℤ] ℤ) (a : H) (ha : l a = 1)

def projection : H →ₗ[ℤ] H := by
  let r : H →+ H := {
    toFun x := x - l x • a
    map_zero' := by simp only [map_zero, zero_zsmul, sub_zero]
    map_add' := by
      intro x y
      change (x + y) - l (x + y) • a = (x - l x • a) + (y - l y • a)
      rw [map_add, add_zsmul, add_sub_add_comm] }
  exact {
    toFun := r
    map_add' := r.map_add
    map_smul' := by
      intro k x
      exact (congrArg r (int_smul_eq_zsmul (inferInstance : Module ℤ H) k x)).trans
        ((r.map_zsmul k x).trans
          (int_smul_eq_zsmul (inferInstance : Module ℤ H) k (r x)).symm) }

theorem projection_apply (x : H) : projection l a x = x - l x • a := rfl

include ha in
theorem projection_coordinate (x : H) : l (projection l a x) = 0 := by
  rw [projection_apply, map_sub, map_zsmul, ha]
  simp only [smul_eq_mul, mul_one, sub_self]

theorem projection_fixed (x : H) (hx : l x = 0) : projection l a x = x := by
  rw [projection_apply, hx, zero_zsmul, sub_zero]

include ha in
theorem projection_ker : LinearMap.ker (projection l a) = Submodule.span ℤ {a} := by
  ext x
  change x - l x • a = 0 ↔ x ∈ Submodule.span ℤ {a}
  constructor
  · intro hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨l x, ?_⟩
    exact (int_smul_eq_zsmul (inferInstance : Module ℤ H) (l x) a).trans
      (sub_eq_zero.mp hx).symm
  · intro hx
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hx
    have hk' : k • a = x :=
      (int_smul_eq_zsmul (inferInstance : Module ℤ H) k a).symm.trans hk
    rw [← hk', map_zsmul, ha]
    simp only [smul_eq_mul, mul_one, sub_self]

include ha in
theorem projection_range : LinearMap.range (projection l a) = LinearMap.ker l := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact projection_coordinate l a ha y
  · intro hx
    exact ⟨x, projection_fixed l a x hx⟩

def quotientEquivKer : (H ⧸ Submodule.span ℤ {a}) ≃ₗ[ℤ] LinearMap.ker l := by
  let e₁ := Submodule.quotEquivOfEq _ _ (projection_ker l a ha).symm
  let e₂ := (projection l a).quotKerEquivRange
  let e₃ := LinearEquiv.ofEq _ _ (projection_range l a ha)
  let e := e₁.trans (e₂.trans e₃)
  let ea : (H ⧸ Submodule.span ℤ {a}) ≃+ LinearMap.ker l := {
    toEquiv := e.toEquiv
    map_add' := fun x y => e.map_add' x y }
  exact ea.toIntLinearEquiv

def kernelInclusion : LinearMap.ker l →ₗ[ℤ] H := by
  let j : LinearMap.ker l →+ H := {
    toFun := Subtype.val
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  exact {
    toFun := j
    map_add' := j.map_add
    map_smul' := by
      intro k x
      exact (j.map_zsmul k x).trans
        (int_smul_eq_zsmul (inferInstance : Module ℤ H) k (j x)).symm }

theorem kernelInclusion_range : LinearMap.range (kernelInclusion l) = LinearMap.ker l := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

def splitEquiv : H ≃ₗ[ℤ] (H ⧸ Submodule.span ℤ {a}) × ℤ := by
  let E := (LinearEquiv.ofBijective (IntegralSplitting.sumMap (kernelInclusion l) a)
    (IntegralSplitting.sumMap_bijective (kernelInclusion l) l Subtype.val_injective
      (kernelInclusion_range l) a ha)).symm
  let P := (quotientEquivKer l a ha).symm.toAddEquiv.prodCongr (AddEquiv.refl ℤ)
  let ea := E.toAddEquiv.trans P
  exact ea.toIntLinearEquiv

theorem splitEquiv_symm_zero (k : ℤ) : (splitEquiv l a ha).symm (0, k) = k • a := by
  change ((quotientEquivKer l a ha (0 : H ⧸ Submodule.span ℤ {a})) : H) + k • a = k • a
  rw [map_zero, Submodule.coe_zero, zero_add]

end Wikipedia.HopfProblem.DegreeCollapse.PrimitiveSplitting
