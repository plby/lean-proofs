import StackExchange.Puzzling139335.N4Diagonal.SideBounds.Projection
import StackExchange.Puzzling139335.N4Diagonal.Defs

/-!
# Sharp support-length bounds from actual side coverage

The coordinate estimates use only supporting-line inequalities and actual
ray endpoints in the prototype.  No convex-hull boundary parametrization
or monotonicity theorem is needed.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ThreeCorners

/-- Both coordinate projections are positive at an interior first-quadrant
angle, and their sum is strictly greater than one. -/
theorem sin_cos_pos_and_sum_gt_one {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin t ∧ 0 < Real.cos t ∧ 1 < Real.cos t + Real.sin t := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  refine ⟨hs, hc, ?_⟩
  apply (sq_lt_sq₀ zero_le_one (add_nonneg hc.le hs.le)).mp
  nlinarith [Real.sin_sq_add_cos_sq t, mul_pos hc hs]

namespace Model

/-- Bottom contact plus an actual incoming endpoint bounds the first
support length by the remaining coordinate sum of the triangle. -/
theorem first_support_length_bound (m : Model) {x₀ t : ℝ} (hθ : 0 < m.θ)
    (hbottom : (!₂[x₀, 0] : Plane) ∈ m.P)
    (hend : m.p - t • ray m.θ ∈ m.P) :
    x₀ + t * (Real.cos m.θ + Real.sin m.θ) ≤ 1 := by
  have hs : 0 < Real.sin m.θ := Real.sin_pos_of_pos_of_lt_pi hθ
    (by linarith [m.theta_bounds.2, Real.pi_pos])
  have hc : 0 ≤ Real.cos m.θ := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [m.theta_bounds.1, Real.pi_pos], m.theta_bounds.2⟩
  have hbounds := bottom_support_coordinate_bounds
    (fun x hx => ⟨(m.triangle hx).1, (m.triangle hx).2.1⟩)
    hbottom hend (fun x hx => (m.first_support x hx).1) hs hc
  have hp := (m.triangle m.p_mem).2.2
  nlinarith [hbounds.1, hbounds.2]

/-- Left contact plus an actual last incoming endpoint gives the symmetric
support-length bound. -/
theorem last_support_length_bound (m : Model) {y₀ t : ℝ}
    (hβ : m.β < Real.pi / 2) (hleft : (!₂[0, y₀] : Plane) ∈ m.P)
    (hend : m.q - t • ray m.β ∈ m.P) :
    y₀ + t * (Real.cos m.β + Real.sin m.β) ≤ 1 := by
  have hc : 0 < Real.cos m.β := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [m.beta_nonneg, Real.pi_pos], hβ⟩
  have hs : 0 ≤ Real.sin m.β := Real.sin_nonneg_of_nonneg_of_le_pi m.beta_nonneg
    (by linarith [hβ, Real.pi_pos])
  have hbounds := left_support_coordinate_bounds
    (fun x hx => ⟨(m.triangle hx).1, (m.triangle hx).2.1⟩)
    hleft hend (fun x hx => (m.last_support x hx).2) hc hs
  have hq := (m.triangle m.q_mem).2.2
  nlinarith [hbounds.1, hbounds.2]

/-- Assignment I bottom coverage excludes every interior first angle. -/
theorem first_incoming_not_interior_angle (m : Model) {x₀ : ℝ} (hx₀ : x₀ < 1)
    (hbottom : (!₂[x₀, 0] : Plane) ∈ m.P)
    (hend : m.p - (1 - x₀) • ray m.θ ∈ m.P) :
    m.θ ∉ Ioo (0 : ℝ) (Real.pi / 2) := by
  intro hθ
  have hbound := m.first_support_length_bound hθ.1 hbottom hend
  have hsum := (sin_cos_pos_and_sum_gt_one hθ).2.2
  nlinarith [mul_pos (sub_pos.mpr hx₀) (sub_pos.mpr hsum)]

/-- Assignment I left or top coverage excludes every interior last angle. -/
theorem last_incoming_not_interior_angle (m : Model) {y₀ : ℝ} (hy₀ : y₀ < 1)
    (hleft : (!₂[0, y₀] : Plane) ∈ m.P)
    (hend : m.q - (1 - y₀) • ray m.β ∈ m.P) :
    m.β ∉ Ioo (0 : ℝ) (Real.pi / 2) := by
  intro hβ
  have hbound := m.last_support_length_bound hβ.2 hleft hend
  have hsum := (sin_cos_pos_and_sum_gt_one hβ).2.2
  nlinarith [mul_pos (sub_pos.mpr hy₀) (sub_pos.mpr hsum)]

/-- The two source endpoints forced in Assignment II are incompatible
with two interior angular directions. -/
theorem no_interior_angles_of_cross_endpoints (m : Model)
    (hθ : 0 < m.θ) (hβ : m.β < Real.pi / 2)
    {x₀ y₀ : ℝ} (hx₀ : x₀ < 1) (hy₀ : y₀ < 1)
    (hbottom : (!₂[x₀, 0] : Plane) ∈ m.P) (hleft : (!₂[0, y₀] : Plane) ∈ m.P)
    (hpEnd : m.p - (1 - y₀) • ray m.θ ∈ m.P)
    (hqEnd : m.q - (1 - x₀) • ray m.β ∈ m.P) : False := by
  have hpbound := m.first_support_length_bound hθ hbottom hpEnd
  have hqbound := m.last_support_length_bound hβ hleft hqEnd
  have hsumθ := (sin_cos_pos_and_sum_gt_one
    ⟨hθ, m.beta_bounds.1.trans_lt hβ⟩).2.2
  have hsumβ := (sin_cos_pos_and_sum_gt_one
    ⟨hθ.trans_le m.beta_bounds.1, hβ⟩).2.2
  nlinarith [mul_pos (sub_pos.mpr hy₀) (sub_pos.mpr hsumθ),
    mul_pos (sub_pos.mpr hx₀) (sub_pos.mpr hsumβ)]

/-- In the zero-first-angle case, left coverage gives `x₀ ≤ y₀`, whereas
the last incoming endpoint at an interior angle gives `y₀ < x₀`.
No side-interlacing equality is required. -/
theorem no_zero_first_angle_of_endpoints (m : Model) (hθ : m.θ = 0)
    (hβ : m.β ∈ Ioo (0 : ℝ) (Real.pi / 2))
    {x₀ y₀ : ℝ} (hx₀ : x₀ < 1)
    (hbottom : (!₂[x₀, 0] : Plane) ∈ m.P) (hleft : (!₂[0, y₀] : Plane) ∈ m.P)
    (hpEnd : m.p + (1 - y₀) • perpRay m.θ ∈ m.P)
    (hqEnd : m.q - (1 - x₀) • ray m.β ∈ m.P) : False := by
  have hsupport := (m.first_support (!₂[x₀, 0]) hbottom).2
  simp [hθ, Schoenflies.Plane.inner_eq, ray] at hsupport
  have hsumP := (m.triangle hpEnd).2.2
  simp [hθ, perpRay] at hsumP
  have hxy : x₀ ≤ y₀ := by linarith [(m.triangle m.p_mem).2.1]
  have hqbound := m.last_support_length_bound hβ.2 hleft hqEnd
  have hsumβ := (sin_cos_pos_and_sum_gt_one hβ).2.2
  nlinarith [mul_pos (sub_pos.mpr hx₀) (sub_pos.mpr hsumβ)]

end Model

end Puzzling139335.N4Diagonal
