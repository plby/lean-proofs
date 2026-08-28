import Wikipedia.NoExoticSixSphere.SphereAnnulusFrontier

/-!
# Literal radial clamping onto the original closed annulus

On nonzero vectors the norm is clamped to the interval from one to two.
The map fixes the entire original annulus, sends the inner region to
the radius-one sphere and the outer region to the radius-two sphere,
and is continuous on the actual complement of the origin.
-/

noncomputable section

open Set Metric

namespace NoExoticSixSphere.SphereAnnulus

open GLOrthonormalization

def clamp {p : ℕ} (x : Vector (p + 1)) : Vector (p + 1) :=
  (max 1 (min 2 ‖x‖) / ‖x‖) • x

theorem clampedRadius_bounds {p : ℕ} (x : Vector (p + 1)) :
    1 ≤ max 1 (min 2 ‖x‖) ∧ max 1 (min 2 ‖x‖) ≤ 2 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem continuousOn_clamp (p : ℕ) :
    ContinuousOn (clamp (p := p)) {x | x ≠ 0} :=
  (((continuous_const.max (continuous_const.min continuous_norm)).continuousOn.div
    continuous_norm.continuousOn (fun _ hx ↦ norm_ne_zero_iff.mpr hx)).smul
      continuous_id.continuousOn)

theorem norm_clamp {p : ℕ} (x : Vector (p + 1)) (hx : x ≠ 0) :
    ‖clamp x‖ = max 1 (min 2 ‖x‖) := by
  rw [clamp, norm_smul, Real.norm_of_nonneg
    (div_nonneg (zero_le_one.trans (clampedRadius_bounds x).1) (norm_nonneg x))]
  exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)

theorem clamp_mem_domain {p : ℕ} (x : Vector (p + 1)) (hx : x ≠ 0) :
    clamp x ∈ domain p := by
  change 1 ≤ ‖clamp x‖ ∧ ‖clamp x‖ ≤ 2
  rw [norm_clamp x hx]
  exact clampedRadius_bounds x

theorem clamp_ne_zero {p : ℕ} (x : Vector (p + 1)) (hx : x ≠ 0) : clamp x ≠ 0 :=
  ne_zero ⟨clamp x, clamp_mem_domain x hx⟩

theorem clamp_of_mem_domain {p : ℕ} (x : Vector (p + 1)) (hx : x ∈ domain p) :
    clamp x = x := by
  rw [clamp, min_eq_right hx.2, max_eq_right hx.1,
    div_self (zero_lt_one.trans_le hx.1).ne', one_smul]

theorem norm_clamp_of_norm_le_one {p : ℕ} (x : Vector (p + 1)) (hx : x ≠ 0)
    (hn : ‖x‖ ≤ 1) : ‖clamp x‖ = 1 := by
  rw [norm_clamp x hx, min_eq_right (hn.trans (by norm_num)), max_eq_left hn]

theorem norm_clamp_of_two_le_norm {p : ℕ} (x : Vector (p + 1)) (hx : x ≠ 0)
    (hn : 2 ≤ ‖x‖) : ‖clamp x‖ = 2 := by
  rw [norm_clamp x hx, min_eq_left hn]
  norm_num

end NoExoticSixSphere.SphereAnnulus
