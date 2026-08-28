import Wikipedia.NoExoticSixSphere.Equator
import Mathlib.Topology.Separation.Hausdorff

/-!
# A closed hemisphere as a cone on its equator

The explicit parametrization has height `t` and equatorial radius
`sqrt (1 - t²)`. Its only identifications collapse the top to the pole. This
will allow a genuine nullhomotopy to descend to a hemisphere extension.
-/

open Set unitInterval

namespace NoExoticSixSphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace HemisphereCone

/-- The square of the equatorial radius is nonnegative throughout the interval. -/
theorem radicand_nonneg (t : I) : 0 ≤ 1 - (t : ℝ) ^ 2 := by
  nlinarith [t.2.1, t.2.2]

/-- The ambient vector at latitude `t` over an equatorial point. -/
noncomputable def vector (v : UnitSphere E) (t : I) (x : Equator v) : E :=
  Real.sqrt (1 - (t : ℝ) ^ 2) • (x.1 : E) + (t : ℝ) • (v : E)

/-- The latitude formula lies on the actual unit sphere. -/
theorem norm_vector (v : UnitSphere E) (t : I) (x : Equator v) : ‖vector v t x‖ = 1 := by
  have hvx : inner ℝ (x.1 : E) (v : E) = 0 := by
    rw [real_inner_comm]
    exact x.2
  have hs : ‖vector v t x‖ ^ 2 = 1 := by
    rw [vector, norm_add_sq_real, norm_smul, norm_smul,
      ClosedHemisphere.unit_norm, ClosedHemisphere.unit_norm,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg t.2.1, mul_one, mul_one,
      real_inner_smul_left, real_inner_smul_right, hvx]
    nlinarith [Real.sq_sqrt (radicand_nonneg t)]
  nlinarith [norm_nonneg (vector v t x)]

/-- The height of a cone point is exactly its interval parameter. -/
theorem inner_vector (v : UnitSphere E) (t : I) (x : Equator v) :
    inner ℝ (v : E) (vector v t x) = (t : ℝ) := by
  rw [vector, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    x.2, real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm]
  ring

/-- The latitude parametrization as a map to the actual closed hemisphere. -/
noncomputable def point (v : UnitSphere E) (p : I × Equator v) : ClosedHemisphere v :=
  ⟨⟨vector v p.1 p.2, by
    simpa only [Metric.mem_sphere, dist_zero_right] using norm_vector v p.1 p.2⟩,
    by change 0 ≤ inner ℝ (v : E) (vector v p.1 p.2); rw [inner_vector]; exact p.1.2.1⟩

/-- The cone parametrization is jointly continuous, including at the collapsed top. -/
theorem continuous_point (v : UnitSphere E) : Continuous (point v) := by
  have ht : Continuous (fun p : I × Equator v ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : I × Equator v ↦ (p.2.1 : E)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact (((continuous_const.sub (ht.pow 2)).sqrt.smul hx).add
    (ht.smul continuous_const)).subtype_mk _ |>.subtype_mk _

/-- The base of the cone is the actual equator inclusion. -/
theorem point_zero (v : UnitSphere E) (x : Equator v) :
    point v (0, x) = equatorNorth v x := by
  apply Subtype.ext
  apply Subtype.ext
  change vector v 0 x = (x.1 : E)
  simp [vector]

/-- The top of the cone is the pole, independently of the equatorial coordinate. -/
theorem point_one (v : UnitSphere E) (x : Equator v) :
    point v (1, x) = ClosedHemisphere.center v := by
  apply Subtype.ext
  apply Subtype.ext
  change vector v 1 x = (v : E)
  simp [vector]

/-- A hemisphere point's height belongs to the unit interval. -/
noncomputable def height (v : UnitSphere E) (x : ClosedHemisphere v) : I :=
  ⟨inner ℝ (v : E) (x.1 : E), x.2, by
    calc
      inner ℝ (v : E) (x.1 : E) ≤ ‖(v : E)‖ * ‖(x.1 : E)‖ := real_inner_le_norm _ _
      _ = 1 := by rw [ClosedHemisphere.unit_norm, ClosedHemisphere.unit_norm, one_mul]⟩

/-- The equatorial component of a hemisphere point. -/
noncomputable def radial (v : UnitSphere E) (x : ClosedHemisphere v) : E :=
  (x.1 : E) - (height v x : ℝ) • (v : E)

/-- The radial component is perpendicular to the pole. -/
theorem inner_radial (v : UnitSphere E) (x : ClosedHemisphere v) :
    inner ℝ (v : E) (radial v x) = 0 := by
  rw [radial, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    ClosedHemisphere.unit_norm, one_pow, mul_one]
  exact sub_self _

/-- The radius is determined by the height through the unit-sphere equation. -/
theorem norm_radial_sq (v : UnitSphere E) (x : ClosedHemisphere v) :
    ‖radial v x‖ ^ 2 = 1 - (height v x : ℝ) ^ 2 := by
  rw [radial, norm_sub_sq_real, ClosedHemisphere.unit_norm, norm_smul,
    ClosedHemisphere.unit_norm, Real.norm_eq_abs, abs_of_nonneg (height v x).2.1,
    mul_one, real_inner_smul_right, real_inner_comm]
  change 1 ^ 2 - 2 * ((height v x : ℝ) * (height v x : ℝ)) + (height v x : ℝ) ^ 2 = _
  ring

/-- The nonnegative radius agrees with the square-root radius in the cone formula. -/
theorem norm_radial (v : UnitSphere E) (x : ClosedHemisphere v) :
    ‖radial v x‖ = Real.sqrt (1 - (height v x : ℝ) ^ 2) := by
  rw [← norm_radial_sq, Real.sqrt_sq (norm_nonneg _)]

/-- If the radial component vanishes, the height must be one. -/
theorem height_eq_one_of_radial_eq_zero (v : UnitSphere E) (x : ClosedHemisphere v)
    (hx : radial v x = 0) : (height v x : ℝ) = 1 := by
  have h := norm_radial_sq v x
  rw [hx, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  nlinarith [(height v x).2.1]

/-- Away from the pole, normalize the actual radial component to obtain an equatorial direction. -/
noncomputable def direction (v : UnitSphere E) (x : ClosedHemisphere v)
    (hx : radial v x ≠ 0) : Equator v :=
  ⟨⟨NormedSpace.normalize (radial v x), by
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hx⟩, by
    change inner ℝ (v : E) (‖radial v x‖⁻¹ • radial v x) = 0
    rw [real_inner_smul_right, inner_radial, mul_zero]⟩

/-- Height and direction reconstruct every point away from the pole. -/
theorem point_height_direction (v : UnitSphere E) (x : ClosedHemisphere v)
    (hx : radial v x ≠ 0) : point v (height v x, direction v x hx) = x := by
  apply Subtype.ext
  apply Subtype.ext
  change Real.sqrt (1 - (height v x : ℝ) ^ 2) •
    (‖radial v x‖⁻¹ • radial v x) + (height v x : ℝ) • (v : E) = (x.1 : E)
  rw [← norm_radial, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  exact sub_add_cancel _ _

/-- The latitude parametrization covers the closed hemisphere when its equator is nonempty. -/
theorem surjective_point (v : UnitSphere E) [Nonempty (Equator v)] :
    Function.Surjective (point v) := by
  intro x
  by_cases hx : radial v x = 0
  · refine ⟨(1, Classical.choice inferInstance), ?_⟩
    rw [point_one]
    apply Subtype.ext
    apply Subtype.ext
    change (v : E) = (x.1 : E)
    have hvec : (x.1 : E) = (height v x : ℝ) • (v : E) := sub_eq_zero.mp hx
    simpa only [height_eq_one_of_radial_eq_zero v x hx, one_smul] using hvec.symm
  · exact ⟨(height v x, direction v x hx), point_height_direction v x hx⟩

/-- Two cone coordinates represent the same point only when equal or both at the collapsed top. -/
theorem point_fibers (v : UnitSphere E) (p q : I × Equator v)
    (hpq : point v p = point v q) : p = q ∨ (p.1 = 1 ∧ q.1 = 1) := by
  have hvec : vector v p.1 p.2 = vector v q.1 q.2 :=
    congrArg (fun y : ClosedHemisphere v ↦ (y.1 : E)) hpq
  have ht : p.1 = q.1 := by
    apply Subtype.ext
    have h := congrArg (fun y : E ↦ inner ℝ (v : E) y) hvec
    simpa only [inner_vector] using h
  rcases p with ⟨t, x⟩
  rcases q with ⟨s, y⟩
  dsimp only at ht
  subst s
  by_cases htop : t = 1
  · exact Or.inr ⟨htop, htop⟩
  · left
    have hlt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (by
      intro heq
      exact htop (Subtype.ext heq))
    have hr : Real.sqrt (1 - (t : ℝ) ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by nlinarith [t.2.1]))
    change Real.sqrt (1 - (t : ℝ) ^ 2) • (x.1 : E) + (t : ℝ) • (v : E) =
      Real.sqrt (1 - (t : ℝ) ^ 2) • (y.1 : E) + (t : ℝ) • (v : E) at hvec
    have hxy : (x.1 : E) = (y.1 : E) := (smul_right_injective E hr) (add_right_cancel hvec)
    exact congrArg (fun z : Equator v ↦ (t, z)) (Subtype.ext (Subtype.ext hxy))

/-- The finite-dimensional cone parametrization is a quotient map. -/
theorem isQuotientMap_point [FiniteDimensional ℝ E] (v : UnitSphere E)
    [Nonempty (Equator v)] : Topology.IsQuotientMap (point v) :=
  .of_surjective_continuous (surjective_point v) (continuous_point v)

end HemisphereCone

end NoExoticSixSphere
