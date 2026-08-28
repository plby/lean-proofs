import Wikipedia.HopfProblem.OrbitPairSphereAngleFirstVariation

/-!
# Length and endpoint recovery for the nonantipodal sphere logarithm

The explicit tangent logarithm has norm equal to the endpoint angle. Its
actual skew exponential reaches the requested endpoint. The proof treats
the zero logarithm separately, and uses the sine-cosine rotation formula
on the two-dimensional plane for distinct endpoints.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.OrbitPair.SphereAngle

open NoExoticSixSphere GLOrthonormalization SphereTangentExponential

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_tangentComponent_sq {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖y - inner ℝ x y • x‖ ^ 2 = 1 - inner ℝ x y ^ 2 := by
  have hcomm : inner ℝ y x = inner ℝ x y := real_inner_comm _ _
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hx, hy, mul_one, one_pow,
    sq_abs, real_inner_smul_right, hcomm]
  ring

theorem norm_tangentComponent {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖y - inner ℝ x y • x‖ = Real.sqrt (1 - inner ℝ x y ^ 2) := by
  rw [← norm_tangentComponent_sq hx hy, Real.sqrt_sq (norm_nonneg _)]

theorem sqrt_one_sub_inner_sq_pos {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hlo : -1 < inner ℝ x y) (hne : x ≠ y) :
    0 < Real.sqrt (1 - inner ℝ x y ^ 2) := by
  have hhi := (inner_lt_one_iff_real_of_norm_eq_one hx hy).mpr hne
  apply Real.sqrt_pos.mpr
  nlinarith

theorem factor_nonneg (c : ℝ) : 0 ≤ factor c :=
  div_nonneg (Real.arccos_nonneg c) (Real.sqrt_nonneg _)

theorem norm_logVector {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hlo : -1 < inner ℝ x y) : ‖logVector x y‖ = Real.arccos (inner ℝ x y) := by
  by_cases he : x = y
  · subst y
    rw [logVector_diagonal hx, norm_zero, real_inner_self_eq_norm_sq, hx, one_pow,
      Real.arccos_one]
  · have hs := ne_of_gt (sqrt_one_sub_inner_sq_pos hx hy hlo he)
    rw [logVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg (factor_nonneg _),
      norm_tangentComponent hx hy, factor, div_mul_cancel₀ _ hs]

theorem logVector_eq_zero_iff {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hlo : -1 < inner ℝ x y) : logVector x y = 0 ↔ x = y := by
  constructor
  · intro he
    have ha := norm_logVector hx hy hlo
    rw [he, norm_zero] at ha
    have hc : inner ℝ x y = 1 := le_antisymm
      (real_inner_le_one_of_norm_eq_one hx hy) (Real.arccos_eq_zero.mp ha.symm)
    exact (inner_eq_one_iff_of_norm_eq_one hx hy).mp hc
  · intro he
    subst y
    exact logVector_diagonal hx

end InnerProduct

variable {n : ℕ}

def tangentLog (x y : Vector n) (hx : ‖x‖ = 1) : Tangent x :=
  ⟨logVector x y, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (inner_logVector hx y)⟩

theorem curve_formula_of_ne_zero {x : Vector n} (hx : ‖x‖ = 1)
    (v : Tangent x) (hv : v ≠ 0) (t : ℝ) :
    curve x v t = Real.cos (‖v‖ * t) • x +
      Real.sin (‖v‖ * t) • (‖v‖⁻¹ • (v : Vector n)) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hKx : (generator x v : Vector n →L[ℝ] Vector n) x =
      ‖v‖ • (‖v‖⁻¹ • (v : Vector n)) := by
    rw [generator_base hx, smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hKy : (generator x v : Vector n →L[ℝ] Vector n) (‖v‖⁻¹ • (v : Vector n)) =
      (-‖v‖) • x := by
    rw [map_smul, generator_velocity, smul_smul]
    congr 1
    field_simp
  exact SkewRotationExponential.exp_apply_rotation (generator x v) hKx hKy t

theorem curve_tangentLog_one {x y : Vector n} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hlo : -1 < inner ℝ x y) : curve x (tangentLog x y hx) 1 = y := by
  by_cases he : x = y
  · subst y
    have hz : tangentLog x x hx = 0 := Subtype.ext (logVector_diagonal hx)
    rw [hz, curve_zero_velocity]
  · have hs : Real.sqrt (1 - inner ℝ x y ^ 2) ≠ 0 :=
      ne_of_gt (sqrt_one_sub_inner_sq_pos hx hy hlo he)
    have hangle : Real.arccos (inner ℝ x y) ≠ 0 :=
      ne_of_gt (Real.arccos_pos.mpr ((inner_lt_one_iff_real_of_norm_eq_one hx hy).mpr he))
    have hv : tangentLog x y hx ≠ 0 := by
      intro h
      exact he ((logVector_eq_zero_iff hx hy hlo).mp (congrArg Subtype.val h))
    have hn : ‖tangentLog x y hx‖ = Real.arccos (inner ℝ x y) := by
      change ‖logVector x y‖ = Real.arccos (inner ℝ x y)
      exact norm_logVector (x := x) (y := y) hx hy hlo
    rw [curve_formula_of_ne_zero hx _ hv, hn, mul_one,
      Real.cos_arccos hlo.le (real_inner_le_one_of_norm_eq_one hx hy), Real.sin_arccos]
    change inner ℝ x y • x + Real.sqrt (1 - inner ℝ x y ^ 2) •
      ((Real.arccos (inner ℝ x y))⁻¹ •
        (factor (inner ℝ x y) • (y - inner ℝ x y • x))) = y
    rw [smul_smul, smul_smul]
    have hc : Real.sqrt (1 - inner ℝ x y ^ 2) * (Real.arccos (inner ℝ x y))⁻¹ *
        factor (inner ℝ x y) = 1 := by
      unfold factor
      field_simp
    rw [hc, one_smul]
    module

end Wikipedia.HopfProblem.OrbitPair.SphereAngle
