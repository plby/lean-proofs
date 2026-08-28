import Wikipedia.HopfProblem.ConifoldPolarNativeFramingDefs
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The literal orthogonal correction to the native real-sphere frame

The map uses the native fixed north vector and the native chosen isometry of
the complex plane with its orthogonal complement.  Its isometry property is
proved by this orthogonal decomposition, without choosing new coordinate axes.
-/

noncomputable section

open scoped InnerProductSpace

namespace Wikipedia.HopfProblem.ConifoldPolar.NativeFraming

open CuspCircleNormalTrivialization

theorem north_inner_equator (z : ℂ) :
    ⟪RealSphere.northVector, (RealSphere.equatorEquiv z : Base)⟫_ℝ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp (RealSphere.equatorEquiv z).property

theorem orthogonalMap_add (x y : Base) :
    orthogonalMap (x + y) = orthogonalMap x + orthogonalMap y := by
  have h : (⟨(x + y) 1, -((x + y) 2)⟩ : ℂ) =
      (⟨x 1, -(x 2)⟩ : ℂ) + (⟨y 1, -(y 2)⟩ : ℂ) := by
    apply Complex.ext <;> simp [add_comm]
  rw [orthogonalMap, h, map_add, Submodule.coe_add]
  simp only [orthogonalMap, PiLp.add_apply, neg_add, add_smul]
  abel

theorem orthogonalMap_smul (a : ℝ) (x : Base) :
    orthogonalMap (a • x) = a • orthogonalMap x := by
  have h : (⟨(a • x) 1, -((a • x) 2)⟩ : ℂ) =
      a • (⟨x 1, -(x 2)⟩ : ℂ) := by
    apply Complex.ext <;> simp
  rw [orthogonalMap, h, map_smul, Submodule.coe_smul]
  simp only [orthogonalMap, PiLp.smul_apply, smul_eq_mul, smul_add, smul_smul, mul_neg]

theorem orthogonalMap_norm_sq (x : Base) : ‖orthogonalMap x‖ ^ 2 = ‖x‖ ^ 2 := by
  have horth :
      ⟪-(x 0) • RealSphere.northVector,
        (RealSphere.equatorEquiv (⟨x 1, -(x 2)⟩ : ℂ) : Base)⟫_ℝ = 0 := by
    rw [real_inner_smul_left, north_inner_equator, mul_zero]
  have hpy :
      ‖-(x 0) • RealSphere.northVector +
        (RealSphere.equatorEquiv (⟨x 1, -(x 2)⟩ : ℂ) : Base)‖ ^ 2 =
      ‖-(x 0) • RealSphere.northVector‖ ^ 2 +
        ‖(RealSphere.equatorEquiv (⟨x 1, -(x 2)⟩ : ℂ) : Base)‖ ^ 2 := by
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  have hnorth : ‖-(x 0) • RealSphere.northVector‖ ^ 2 = (x 0) ^ 2 := by
    simp [norm_smul, RealSphere.norm_northVector, Real.norm_eq_abs]
  have hequator :
      ‖(RealSphere.equatorEquiv (⟨x 1, -(x 2)⟩ : ℂ) : Base)‖ ^ 2 =
        (x 1) ^ 2 + (x 2) ^ 2 := by
    change ‖RealSphere.equatorEquiv (⟨x 1, -(x 2)⟩ : ℂ)‖ ^ 2 = _
    rw [LinearIsometryEquiv.norm_map, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, pow_two]
  rw [orthogonalMap, hpy, hnorth, hequator, base_norm_sq]
  ring

theorem orthogonalMap_norm (x : Base) : ‖orthogonalMap x‖ = ‖x‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (orthogonalMap_norm_sq x)

/-- The specified formula, bundled as a real linear isometry. -/
def orthogonalIsometry : Base →ₗᵢ[ℝ] Base where
  toFun := orthogonalMap
  map_add' := orthogonalMap_add
  map_smul' := orthogonalMap_smul
  norm_map' := orthogonalMap_norm

/-- The same literal isometry, surjective by equality of the finite dimensions. -/
def orthogonalEquiv : Base ≃ₗᵢ[ℝ] Base :=
  orthogonalIsometry.toLinearIsometryEquiv rfl

@[simp] theorem orthogonalEquiv_apply (x : Base) :
    orthogonalEquiv x = orthogonalMap x := rfl

theorem orthogonalMap_injective : Function.Injective orthogonalMap :=
  orthogonalEquiv.injective

theorem orthogonalMap_surjective : Function.Surjective orthogonalMap :=
  orthogonalEquiv.surjective

theorem orthogonalMap_continuous : Continuous orthogonalMap :=
  orthogonalEquiv.continuous

theorem orthogonalMap_north_inner (x : Base) :
    ⟪RealSphere.northVector, orthogonalMap x⟫_ℝ = -(x 0) := by
  rw [orthogonalMap, inner_add_right, real_inner_smul_right, north_inner_equator,
    real_inner_self_eq_norm_sq, RealSphere.norm_northVector]
  simp

theorem orthogonalMap_equator_part (x : Base) :
    orthogonalMap x + (x 0) • RealSphere.northVector =
      (RealSphere.equatorEquiv (⟨x 1, -(x 2)⟩ : ℂ) : Base) := by
  simp only [orthogonalMap, neg_smul]
  abel

theorem orthogonalMap_zero_coordinate (x : Base) : orthogonalMap x 0 = -(x 0) := by
  simpa [RealSphere.northVector, EuclideanSpace.inner_single_left] using
    orthogonalMap_north_inner x

end Wikipedia.HopfProblem.ConifoldPolar.NativeFraming
