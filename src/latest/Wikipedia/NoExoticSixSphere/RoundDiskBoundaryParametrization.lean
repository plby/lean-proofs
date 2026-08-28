import Wikipedia.NoExoticSixSphere.RoundDiskBoundarySegments

/-!
# Every round-disk interior point has boundary-segment coordinates

The endpoint is found by extending the ray from the selected boundary
point. Its scale and time are given by the actual inner-product formula.
Together with uniqueness, this identifies the noncollapsed part of the
disk-boundary suspension without assuming a sphere-quotient comparison.
-/

noncomputable section

open Set Metric
open scoped unitInterval InnerProductSpace

namespace NoExoticSixSphere.RoundDiskBoundarySegments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem sub_base_ne_zero (b : Boundary (E := E)) {x : E}
    (hx : x ∈ ball (0 : E) 1) : x - b.val ≠ 0 := by
  intro he
  have hxb : x = b.val := sub_eq_zero.mp he
  have hn := mem_ball_zero_iff.mp hx
  rw [hxb, norm_boundary] at hn
  exact (lt_irrefl 1) hn

def rayScale (b : Boundary (E := E)) (x : E) : ℝ :=
  2 * (1 - ⟪x, b.val⟫_ℝ) / ‖x - b.val‖ ^ 2

theorem rayScale_gt_one (b : Boundary (E := E)) {x : E}
    (hx : x ∈ ball (0 : E) 1) : 1 < rayScale b x := by
  have hd : 0 < ‖x - b.val‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_base_ne_zero b hx))
  apply (lt_div_iff₀ hd).mpr
  have he := norm_sub_sq_real x b.val
  rw [norm_boundary] at he
  have hn := mem_ball_zero_iff.mp hx
  nlinarith [norm_nonneg x]

theorem rayScale_mul_chord (b : Boundary (E := E)) {x : E}
    (hx : x ∈ ball (0 : E) 1) :
    rayScale b x * ‖x - b.val‖ ^ 2 = 2 * (1 - ⟪x, b.val⟫_ℝ) := by
  exact div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_base_ne_zero b hx)))

def rayEndpoint (b : Boundary (E := E)) (x : E) : E :=
  b.val + rayScale b x • (x - b.val)

theorem rayEndpoint_norm_sq (b : Boundary (E := E)) {x : E}
    (hx : x ∈ ball (0 : E) 1) : ‖rayEndpoint b x‖ ^ 2 = 1 := by
  rw [rayEndpoint, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq,
    norm_boundary, real_inner_comm x b.val]
  have hm := congrArg (fun y : ℝ ↦ rayScale b x * y) (rayScale_mul_chord b hx)
  nlinarith [hm]

theorem rayEndpoint_mem_sphere (b : Boundary (E := E)) {x : E}
    (hx : x ∈ ball (0 : E) 1) : rayEndpoint b x ∈ sphere (0 : E) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have he := rayEndpoint_norm_sq b hx
  nlinarith [norm_nonneg (rayEndpoint b x)]

theorem exists_point_of_mem_ball (b : Boundary (E := E)) {x : E}
    (hx : x ∈ ball (0 : E) 1) :
    ∃ t : unitInterval, ∃ s : Boundary (E := E),
      0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ s ≠ b ∧ (point b (t, s)).val = x := by
  let a := rayScale b x
  have ha : 1 < a := rayScale_gt_one b hx
  have ha₀ : 0 < a := zero_lt_one.trans ha
  have hi₀ : 0 < a⁻¹ := inv_pos.mpr ha₀
  have hi₁ : a⁻¹ < 1 := (inv_lt_one₀ ha₀).mpr ha
  let t : unitInterval := ⟨1 - a⁻¹, by constructor <;> linarith⟩
  let s : Boundary (E := E) := ⟨rayEndpoint b x, rayEndpoint_mem_sphere b hx⟩
  have he : (point b (t, s)).val = x := by
    change (1 - (1 - a⁻¹)) • (b.val + a • (x - b.val)) + (1 - a⁻¹) • b.val = x
    rw [sub_sub_cancel, smul_add, smul_smul, inv_mul_cancel₀ ha₀.ne', one_smul]
    module
  refine ⟨t, s, ?_, ?_, ?_, he⟩
  · change 0 < 1 - a⁻¹
    linarith
  · change 1 - a⁻¹ < 1
    linarith
  · intro hs
    rw [hs, point_base] at he
    exact sub_base_ne_zero b hx (sub_eq_zero.mpr he.symm)

end NoExoticSixSphere.RoundDiskBoundarySegments
