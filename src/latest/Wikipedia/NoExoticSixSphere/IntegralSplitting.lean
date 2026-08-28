import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Prod

/-!
# An exact integral sequence with quotient ℤ splits

For an injective integral map whose image is the kernel of a surjective
integer coordinate, a lift of one gives an explicit product decomposition.
Its first summand is the supplied inclusion, not a replacement embedding.
The marked variant uses a specified lift and is useful for primitive classes.
-/

noncomputable section

namespace NoExoticSixSphere.IntegralSplitting

variable {K H : Type*} [AddCommGroup K] [Module ℤ K]
  [AddCommGroup H] [Module ℤ H] (i : K →ₗ[ℤ] H) (l : H →ₗ[ℤ] ℤ)

def sumMap (a : H) : K × ℤ →ₗ[ℤ] H := by
  let f : K × ℤ →+ H := {
    toFun x := i x.1 + x.2 • a
    map_zero' := by
      change i 0 + (0 : ℤ) • a = 0
      rw [map_zero, zero_zsmul, add_zero]
    map_add' := by
      intro x y
      change i (x.1 + y.1) + (x.2 + y.2) • a = _
      rw [map_add, add_zsmul]
      exact add_add_add_comm _ _ _ _ }
  exact {
    toFun := f
    map_add' := f.map_add
    map_smul' := by
      intro k x
      exact (congrArg f (int_smul_eq_zsmul (inferInstance : Module ℤ (K × ℤ)) k x)).trans
        ((f.map_zsmul k x).trans
          (int_smul_eq_zsmul (inferInstance : Module ℤ H) k (f x)).symm) }

theorem sumMap_apply (a : H) (x : K × ℤ) : sumMap i a x = i x.1 + x.2 • a := rfl

variable (hi : Function.Injective i) (hexact : LinearMap.range i = LinearMap.ker l)

include hexact in
theorem coordinate_inclusion (x : K) : l (i x) = 0 := by
  have hx : i x ∈ LinearMap.range i := ⟨x, rfl⟩
  rw [hexact] at hx
  exact hx

include hexact in
theorem sumMap_coordinate (a : H) (ha : l a = 1) (x : K × ℤ) :
    l (sumMap i a x) = x.2 := by
  rw [sumMap_apply, map_add, coordinate_inclusion i l hexact, map_zsmul, ha]
  simp only [zero_add, zsmul_eq_mul, Int.cast_id, mul_one]

include hi hexact in
theorem sumMap_bijective (a : H) (ha : l a = 1) :
    Function.Bijective (sumMap i a) := by
  constructor
  · intro x y hxy
    have hs : x.2 = y.2 := (sumMap_coordinate i l hexact a ha x).symm.trans
      ((congrArg l hxy).trans (sumMap_coordinate i l hexact a ha y))
    apply Prod.ext ?_ hs
    apply hi
    rw [sumMap_apply, sumMap_apply, hs] at hxy
    exact add_right_cancel hxy
  · intro x
    have hx : x - l x • a ∈ LinearMap.ker l := by
      change l (x - l x • a) = 0
      rw [map_sub, map_zsmul, ha]
      simp only [zsmul_eq_mul, Int.cast_id, mul_one, sub_self]
    rw [← hexact] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨(y, l x), ?_⟩
    rw [sumMap_apply, hy, sub_add_cancel]

variable (hl : Function.Surjective l)

def splitEquiv : H ≃ₗ[ℤ] K × ℤ :=
  (LinearEquiv.ofBijective (sumMap i (hl 1).choose)
    (sumMap_bijective i l hi hexact (hl 1).choose (hl 1).choose_spec)).symm

theorem splitEquiv_symm_inl (x : K) : (splitEquiv i l hi hexact hl).symm (x, 0) = i x := by
  change i x + (0 : ℤ) • (hl 1).choose = i x
  rw [zero_zsmul, add_zero]

theorem splitEquiv_snd (x : H) : (splitEquiv i l hi hexact hl x).2 = l x := by
  have he := sumMap_coordinate i l hexact (hl 1).choose (hl 1).choose_spec
    (splitEquiv i l hi hexact hl x)
  change l ((splitEquiv i l hi hexact hl).symm (splitEquiv i l hi hexact hl x)) = _ at he
  rw [LinearEquiv.symm_apply_apply] at he
  exact he.symm

end NoExoticSixSphere.IntegralSplitting
