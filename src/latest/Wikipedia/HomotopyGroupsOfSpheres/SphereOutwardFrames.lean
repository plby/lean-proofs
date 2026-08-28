import Wikipedia.HomotopyGroupsOfSpheres.SphereCoordinateIsometries
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Orientation

/-!
# Outward frames for the actual centered sphere charts

An ordered tangent basis is oriented by placing the outward unit normal first.
An ambient linear isometry of positive determinant preserves this orientation.
The tangent vectors in this construction are the derivatives of the actual
inverse stereographic charts, rather than unrelated abstract tangent models.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem inner_self_unit (z : UnitSphere E) : inner ℝ z.val z.val = 1 := by
  rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp z.property, one_pow]

theorem inner_normal_tangent (z : UnitSphere E) (v : Tangent z) :
    inner ℝ z.val v.val = 0 := by
  have hv := Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property
  simpa only [inner_neg_left, neg_eq_zero] using hv

def tangentRemainder (z : UnitSphere E) (w : E) : Tangent z :=
  ⟨w - inner ℝ z.val w • z.val, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp [inner_sub_right, inner_smul_right]⟩

/-- Resolve an ambient vector into its outward normal and tangent components. -/
def normalTangentEquiv (z : UnitSphere E) : (ℝ × Tangent z) ≃ₗ[ℝ] E where
  toFun p := p.1 • z.val + p.2.val
  invFun w := (inner ℝ z.val w, tangentRemainder z w)
  left_inv p := by
    apply Prod.ext
    · simp [inner_add_right, inner_smul_right, inner_normal_tangent]
    · apply Subtype.ext
      simp [tangentRemainder, inner_add_right, inner_smul_right,
        inner_normal_tangent]
  right_inv w := by simp [tangentRemainder]
  map_add' p q := by
    change (p.1 + q.1) • z.val + (p.2.val + q.2.val) =
      (p.1 • z.val + p.2.val) + (q.1 • z.val + q.2.val)
    rw [add_smul]
    abel
  map_smul' a p := by
    change (a * p.1) • z.val + a • p.2.val = a • (p.1 • z.val + p.2.val)
    rw [smul_add, smul_smul]

/-- A tangent basis with the outward normal adjoined as the first vector. -/
def outwardFrame {ι : Type*} (z : UnitSphere E) (b : Module.Basis ι ℝ (Tangent z)) :
    Module.Basis (Unit ⊕ ι) ℝ E :=
  ((Module.Basis.singleton Unit ℝ).prod b).map (normalTangentEquiv z)

@[simp] theorem outwardFrame_normal {ι : Type*} (z : UnitSphere E)
    (b : Module.Basis ι ℝ (Tangent z)) (u : Unit) :
    outwardFrame z b (Sum.inl u) = z.val := by
  simp [outwardFrame, normalTangentEquiv]

@[simp] theorem outwardFrame_tangent {ι : Type*} (z : UnitSphere E)
    (b : Module.Basis ι ℝ (Tangent z)) (i : ι) :
    outwardFrame z b (Sum.inr i) = (b i).val := by
  simp [outwardFrame, normalTangentEquiv]

theorem outwardFrame_map {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) (z : UnitSphere E)
    (b : Module.Basis ι ℝ (Tangent z)) :
    outwardFrame (sphereIsometry e z) (b.map (tangentIsometry e z).toLinearEquiv) =
      (outwardFrame z b).map e.toLinearEquiv := by
  apply DFunLike.ext
  intro i
  cases i with
  | inl u =>
      simp only [Module.Basis.map_apply, outwardFrame_normal]
      rfl
  | inr i => simp [tangentIsometry]

/-- Positive ambient determinant preserves the orientation of outward frames. -/
theorem outwardFrame_orientation_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : E ≃ₗᵢ[ℝ] E) (he : 0 < e.toLinearEquiv.toLinearMap.det)
    (z : UnitSphere E) (b : Module.Basis ι ℝ (Tangent z)) :
    (outwardFrame (sphereIsometry e z)
      (b.map (tangentIsometry e z).toLinearEquiv)).orientation =
        (outwardFrame z b).orientation := by
  rw [outwardFrame_map]
  exact ((outwardFrame z b).orientation_comp_linearEquiv_eq_iff_det_pos
    e.toLinearEquiv).mpr he

/-- The tangent part of an outward frame is the actual inverse-chart differential. -/
theorem outwardFrame_inverse_fderiv {ι : Type*} (z : UnitSphere E)
    (b : Module.Basis ι ℝ (Tangent z)) (i : ι) :
    outwardFrame z b (Sum.inr i) =
      fderiv ℝ (fun v : Tangent z ↦ (inverse z v).val) 0 (b i) := by
  rw [(hasFDerivAt_inverse_val z).fderiv]
  exact outwardFrame_tangent z b i

end Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates
