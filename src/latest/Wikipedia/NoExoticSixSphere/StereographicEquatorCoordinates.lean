import Wikipedia.NoExoticSixSphere.SpherePoleCompactification
import Wikipedia.NoExoticSixSphere.SphereEquatorRetraction

/-!
# Equators and antipodal axes in the actual stereographic coordinates

The chart uses Mathlib's orthonormal basis of the pole's orthogonal
complement. Its scale is two: finite coordinates twice a unit vector map
to the corresponding orthogonal unit vector on the sphere. Coordinate
hyperplanes map exactly to the corresponding equators.
-/

noncomputable section

open scoped InnerProductSpace OnePoint

namespace NoExoticSixSphere.StereographicEquator

abbrev V (n : ℕ) := EuclideanSpace ℝ (Fin n)

local instance (n : ℕ) : Fact (Module.finrank ℝ (V (n + 1)) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def coordinates (n : ℕ) :
    (ℝ ∙ ((spherePole n) : V (n + 1)))ᗮ ≃ₗᵢ[ℝ] V n :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (spherePole n))).repr

def lift (n : ℕ) (x : V n) : V (n + 1) := (coordinates n).symm x

theorem norm_lift (n : ℕ) (x : V n) : ‖lift n x‖ = ‖x‖ :=
  (coordinates n).symm.norm_map x

theorem inner_lift (n : ℕ) (x y : V n) :
    inner ℝ (lift n x) (lift n y) = inner ℝ x y :=
  (coordinates n).symm.inner_map_map x y

theorem lift_smul (n : ℕ) (a : ℝ) (x : V n) : lift n (a • x) = a • lift n x := by
  exact congrArg Subtype.val ((coordinates n).symm.map_smul a x)

theorem inner_lift_pole (n : ℕ) (x : V n) : inner ℝ (lift n x) (spherePole n).val = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_left.mp ((coordinates n).symm x).property

def axis (n : ℕ) (v : UnitSphere (V n)) : Sphere n :=
  ⟨lift n v.val, by
    simpa only [Metric.mem_sphere, dist_zero_right, norm_lift] using
      ClosedHemisphere.unit_norm v⟩

theorem finite_apply (n : ℕ) (x : V n) :
    (euclideanOnePointSphere n (x : OnePoint _) : V (n + 1)) =
      (‖x‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • lift n x +
        (‖x‖ ^ 2 + 4)⁻¹ • (‖x‖ ^ 2 - 4) • (spherePole n).val := by
  rw [euclideanOnePointSphere_coe]
  have he := stereographic'_symm_apply (spherePole n) x
  change ((sphereProjection n).symm x : V (n + 1)) =
    (‖lift n x‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • lift n x +
      (‖lift n x‖ ^ 2 + 4)⁻¹ • (‖lift n x‖ ^ 2 - 4) • (spherePole n).val at he
  simpa only [norm_lift] using he

theorem inner_axis_finite (n : ℕ) (v : UnitSphere (V n)) (x : V n) :
    inner ℝ (axis n v).val (euclideanOnePointSphere n (x : OnePoint _)).val =
      (‖x‖ ^ 2 + 4)⁻¹ * 4 * inner ℝ v.val x := by
  rw [finite_apply]
  change inner ℝ (lift n v.val) _ = _
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, inner_lift,
    real_inner_smul_right, real_inner_smul_right, inner_lift_pole]
  ring

theorem inner_axis_pole (n : ℕ) (v : UnitSphere (V n)) :
    inner ℝ (axis n v).val (spherePole n).val = 0 := inner_lift_pole n v.val

theorem finite_mem_equator_iff (n : ℕ) (v : UnitSphere (V n)) (x : V n) :
    euclideanOnePointSphere n (x : OnePoint _) ∈ equator (axis n v) ↔ inner ℝ v.val x = 0 := by
  change inner ℝ (axis n v).val (euclideanOnePointSphere n (x : OnePoint _)).val = 0 ↔ _
  rw [inner_axis_finite]
  have h : (‖x‖ ^ 2 + 4)⁻¹ * 4 ≠ 0 :=
    mul_ne_zero (inv_ne_zero (by positivity)) (by norm_num)
  exact mul_eq_zero.trans (or_iff_right h)

theorem compactification_double_axis (n : ℕ) (v : UnitSphere (V n)) :
    euclideanOnePointSphere n (((2 : ℝ) • v.val : V n) : OnePoint _) = axis n v := by
  apply Subtype.ext
  rw [finite_apply, norm_smul, Real.norm_eq_abs, ClosedHemisphere.unit_norm, lift_smul]
  change ((|2| * 1) ^ 2 + 4)⁻¹ • (4 : ℝ) • ((2 : ℝ) • lift n v.val) +
    ((|2| * 1) ^ 2 + 4)⁻¹ • ((|2| * 1) ^ 2 - 4) • (spherePole n).val = lift n v.val
  norm_num [smul_smul]

theorem axis_antipode (n : ℕ) (v : UnitSphere (V n)) :
    axis n (antipode v) = antipode (axis n v) := by
  apply Subtype.ext
  change (lift n (-v.val) : V (n + 1)) = -lift n v.val
  exact congrArg Subtype.val ((coordinates n).symm.map_neg v.val)

theorem compactification_neg_double_axis (n : ℕ) (v : UnitSphere (V n)) :
    euclideanOnePointSphere n (((-2 : ℝ) • v.val : V n) : OnePoint _) =
      antipode (axis n v) := by
  have he : (-2 : ℝ) • v.val = (2 : ℝ) • (antipode v).val := by
    change (-2 : ℝ) • v.val = (2 : ℝ) • (-v.val)
    rw [neg_smul, smul_neg]
  rw [he, compactification_double_axis, axis_antipode]

end NoExoticSixSphere.StereographicEquator
