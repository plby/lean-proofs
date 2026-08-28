import Wikipedia.NoExoticSixSphere.SphereHemisphereFold

/-!
# Normalized straight-line contraction inside a spherical cap

A cap of height greater than a positive constant is preserved by normalizing
the straight segment toward its pole. The vector being normalized never
vanishes. Arbitrarily small such caps form neighborhoods of the pole.
-/

noncomputable section

open Set Function Metric

namespace NoExoticSixSphere.SphereCap

open SphereFold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def blend (v x : UnitSphere E) (a : ℝ) : E := (1 - a) • (x : E) + a • (v : E)

theorem blend_zero (v x : UnitSphere E) : blend v x 0 = (x : E) := by
  simp only [blend, sub_zero, one_smul, zero_smul, add_zero]

theorem blend_one (v x : UnitSphere E) : blend v x 1 = (v : E) := by
  simp only [blend, sub_self, zero_smul, one_smul, zero_add]

theorem blend_pole (v : UnitSphere E) (a : ℝ) : blend v v a = (v : E) := by
  rw [blend, ← add_smul]
  simp only [sub_add_cancel, one_smul]

theorem inner_blend (v x : UnitSphere E) (a : ℝ) :
    inner ℝ (v : E) (blend v x a) = (1 - a) * height v x + a := by
  rw [blend, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm v]
  change (1 - a) * height v x + a * 1 ^ 2 = _
  ring

theorem height_le_inner_blend (v x : UnitSphere E) {a : ℝ} (ha : 0 ≤ a) :
    height v x ≤ inner ℝ (v : E) (blend v x a) := by
  have hx : height v x ≤ 1 := real_inner_le_one_of_norm_eq_one
    (ClosedHemisphere.unit_norm v) (ClosedHemisphere.unit_norm x)
  rw [inner_blend]
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hx)]

theorem blend_ne_zero (v x : UnitSphere E) {a : ℝ} (ha : 0 ≤ a)
    (hx : 0 < height v x) : blend v x a ≠ 0 := by
  intro he
  have hp := hx.trans_le (height_le_inner_blend v x ha)
  rw [he, inner_zero_right] at hp
  exact lt_irrefl 0 hp

theorem norm_blend_le_one (v x : UnitSphere E) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    ‖blend v x a‖ ≤ 1 := by
  calc
    ‖blend v x a‖ ≤ ‖(1 - a) • (x : E)‖ + ‖a • (v : E)‖ := norm_add_le _ _
    _ = 1 := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ha.2), abs_of_nonneg ha.1,
        ClosedHemisphere.unit_norm x, ClosedHemisphere.unit_norm v]
      ring

def contract (v x : UnitSphere E) (a : ℝ) : UnitSphere E :=
  SphereRadialRetraction.retract v (blend v x a)

theorem contract_zero (v x : UnitSphere E) : contract v x 0 = x := by
  rw [contract, blend_zero, SphereRadialRetraction.retract_coe]

theorem contract_one (v x : UnitSphere E) : contract v x 1 = v := by
  rw [contract, blend_one, SphereRadialRetraction.retract_coe]

theorem contract_pole (v : UnitSphere E) (a : ℝ) : contract v v a = v := by
  rw [contract, blend_pole, SphereRadialRetraction.retract_coe]

theorem contract_mem_cap (v x : UnitSphere E) {a c : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hc : 0 ≤ c) (hx : c < height v x) :
    c < height v (contract v x a) := by
  have hne := blend_ne_zero v x ha.1 (hc.trans_lt hx)
  have hn := norm_pos_iff.mpr hne
  have hn1 := norm_blend_le_one v x ha
  have hi := height_le_inner_blend v x ha.1
  have hval : (contract v x a : E) = ‖blend v x a‖⁻¹ • blend v x a := by
    simp only [contract, SphereRadialRetraction.retract, dif_neg hne, NormedSpace.normalize]
  change c < inner ℝ (v : E) (contract v x a : E)
  rw [hval, real_inner_smul_right, ← div_eq_inv_mul, lt_div_iff₀ hn]
  exact (mul_le_of_le_one_right hc hn1).trans_lt (hx.trans_le hi)

theorem dist_sq (v x : UnitSphere E) : dist x v ^ 2 = 2 * (1 - height v x) := by
  rw [Subtype.dist_eq, dist_eq_norm]
  rw [norm_sub_sq_real, ClosedHemisphere.unit_norm x, ClosedHemisphere.unit_norm v,
    real_inner_comm (v : E) (x : E)]
  change 1 ^ 2 - 2 * height v x + 1 ^ 2 = _
  ring

theorem exists_cap_subset (v : UnitSphere E) {U : Set (UnitSphere E)}
    (hU : IsOpen U) (hv : v ∈ U) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ {x | c < height v x} ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hv)
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  refine ⟨1 - δ ^ 2 / 2, ?_, ?_, ?_⟩
  · nlinarith [sq_nonneg (δ - 1)]
  · nlinarith [sq_pos_of_pos hδ]
  · intro x hx
    apply hεU
    have hsq := dist_sq v x
    have hd : dist x v < δ := by
      change 1 - δ ^ 2 / 2 < height v x at hx
      nlinarith [dist_nonneg (x := x) (y := v)]
    exact hd.trans_le (min_le_left ε 1)

end NoExoticSixSphere.SphereCap
