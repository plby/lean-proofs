import Wikipedia.NoExoticSixSphere.SphereCurveEnergy

/-!
# Endpoint angle bounds the energy of a unit-sphere curve

The regularized-angle argument applies to arbitrary endpoints and any
nondegenerate time interval. The square of their spherical angle is at
most interval length times energy.
-/

open scoped ContDiff
open Set

namespace NoExoticSixSphere.SphereCurveAngle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {γ : ℝ → E}

theorem endpoint_angle_pairing_le (hγ : ContDiff ℝ ∞ γ) (hn : ∀ t, ‖γ t‖ = 1)
    {l u : ℝ} (hlu : l ≤ u) (c : ℝ) :
    2 * c * Real.arccos (inner ℝ (γ l) (γ u)) ≤
      (∫ t : ℝ in l..u, ‖deriv γ t‖ ^ 2) + (u - l) * c ^ 2 := by
  let Eγ := ∫ t : ℝ in l..u, ‖deriv γ t‖ ^ 2
  let z := inner ℝ (γ l) (γ u)
  let f : ℝ → ℝ := fun r ↦ 2 * c * (Real.arccos (r * z) - Real.arccos r)
  have hf : Continuous f := continuous_const.mul
    ((Real.continuous_arccos.comp (continuous_id.mul continuous_const)).sub Real.continuous_arccos)
  have hc : IsClosed {r : ℝ | f r ≤ Eγ + (u - l) * c ^ 2} :=
    isClosed_le hf continuous_const
  have hsub : Ioo (0 : ℝ) 1 ⊆ {r : ℝ | f r ≤ Eγ + (u - l) * c ^ 2} := by
    intro r hr
    change f r ≤ Eγ + (u - l) * c ^ 2
    have h := regularized_energy_bound_on (hn l) hγ hn hr.1.le hr.2 hlu c
    simpa only [angle, real_inner_self_eq_norm_sq, hn l, one_pow, mul_one, f, z, Eγ] using h
  have hone : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨zero_le_one, le_rfl⟩
  have hlim := (closure_minimal hsub hc) hone
  change f 1 ≤ Eγ + (u - l) * c ^ 2 at hlim
  simpa only [f, one_mul, Real.arccos_one, sub_zero, z, Eγ] using hlim

theorem endpoint_angle_sq_le_energy (hγ : ContDiff ℝ ∞ γ) (hn : ∀ t, ‖γ t‖ = 1)
    {l u : ℝ} (hlu : l < u) :
    Real.arccos (inner ℝ (γ l) (γ u)) ^ 2 ≤
      (u - l) * ∫ t : ℝ in l..u, ‖deriv γ t‖ ^ 2 := by
  let θ := Real.arccos (inner ℝ (γ l) (γ u))
  let Eγ := ∫ t : ℝ in l..u, ‖deriv γ t‖ ^ 2
  have hlen : 0 < u - l := sub_pos.mpr hlu
  have h := endpoint_angle_pairing_le hγ hn hlu.le (θ / (u - l))
  change 2 * (θ / (u - l)) * θ ≤ Eγ + (u - l) * (θ / (u - l)) ^ 2 at h
  have hm := mul_le_mul_of_nonneg_left h hlen.le
  have hleft : (u - l) * (2 * (θ / (u - l)) * θ) = 2 * θ ^ 2 := by
    field_simp
  have hright : (u - l) * (Eγ + (u - l) * (θ / (u - l)) ^ 2) =
      (u - l) * Eγ + θ ^ 2 := by
    field_simp
  rw [hleft, hright] at hm
  change θ ^ 2 ≤ (u - l) * Eγ
  linarith

end NoExoticSixSphere.SphereCurveAngle
