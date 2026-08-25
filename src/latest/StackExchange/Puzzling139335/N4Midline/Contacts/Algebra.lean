import StackExchange.Puzzling139335.ThreeCorners.Rays

/-!
# Supporting cones and level-one contacts

These lemmas concern the actual set in a supporting cone. In particular,
no chord of its convex hull is inserted into the set.
-/

open Set

namespace Puzzling139335.N4Midline

open ThreeCorners

noncomputable section

/-- The contact with the opposite side of a unit square, expressed in
the inward coordinate at the source corner. -/
def levelOneContact (P : Set Plane) (V e : Plane) : Set Plane :=
  {x | x ∈ P ∧ inner ℝ e (x - V) = 1}

theorem ray_inner_ray (θ φ : ℝ) :
    inner ℝ (ray θ) (ray φ) = Real.cos (φ - θ) := by
  simp only [Schoenflies.Plane.inner_eq, ray_zero, ray_one, Real.cos_sub]
  ring

theorem ray_inner_perp (θ φ : ℝ) :
    inner ℝ (ray θ) (perpRay φ) = -Real.sin (φ - θ) := by
  simp only [Schoenflies.Plane.inner_eq, ray_zero, ray_one,
    perpRay_zero, perpRay_one, Real.sin_sub]
  ring

theorem perp_inner_perp (θ φ : ℝ) :
    inner ℝ (perpRay θ) (perpRay φ) = Real.cos (φ - θ) := by
  simp only [Schoenflies.Plane.inner_eq, perpRay_zero, perpRay_one, Real.cos_sub]
  ring

theorem ray_add_pi_div_two (θ : ℝ) :
    ray (θ + Real.pi / 2) = perpRay θ := by
  ext i
  fin_cases i <;> simp [ray, perpRay, Real.sin_add, Real.cos_add]

theorem perp_add_pi_div_two (θ : ℝ) :
    perpRay (θ + Real.pi / 2) = -ray θ := by
  ext i
  fin_cases i <;> simp [ray, perpRay, Real.sin_add, Real.cos_add]

theorem ray_inner_self (θ : ℝ) : inner ℝ (ray θ) (ray θ) = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_ray]
  norm_num

theorem perp_inner_self (θ : ℝ) : inner ℝ (perpRay θ) (perpRay θ) = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_perpRay]
  norm_num

/-- A direction strictly negative on both inward rays has a unique
maximizer at the supporting vertex. -/
theorem strict_cone_support {W e x : Plane} {θ : ℝ}
    (hx : x ∈ supportCone W θ)
    (hfirst : inner ℝ e (ray θ) < 0)
    (hsecond : inner ℝ e (perpRay θ) < 0) :
    inner ℝ e (x - W) ≤ 0 ∧
      (inner ℝ e (x - W) = 0 → x = W) := by
  obtain ⟨s, t, hs, ht, hrepr⟩ := (mem_supportCone_iff x W θ).mp hx
  have hsub : x - W = s • ray θ + t • perpRay θ := by
    rw [hrepr]
    abel
  have hsum : inner ℝ e (x - W) =
      s * inner ℝ e (ray θ) + t * inner ℝ e (perpRay θ) := by
    rw [hsub, inner_add_right, inner_smul_right, inner_smul_right]
  have hsprod : s * inner ℝ e (ray θ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs hfirst.le
  have htprod : t * inner ℝ e (perpRay θ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht hsecond.le
  refine ⟨by linarith, ?_⟩
  intro hzero
  have hsprod0 : s * inner ℝ e (ray θ) = 0 := by linarith
  have htprod0 : t * inner ℝ e (perpRay θ) = 0 := by linarith
  have hs0 : s = 0 := (mul_eq_zero.mp hsprod0).resolve_right hfirst.ne
  have ht0 : t = 0 := (mul_eq_zero.mp htprod0).resolve_right hsecond.ne
  simpa [hs0, ht0] using hrepr

/-- A direction with two strictly negative Cartesian components uniquely
maximizes at the origin in the nonnegative quadrant. -/
theorem negative_coordinate_support {e x : Plane}
    (hx0 : 0 ≤ x 0) (hx1 : 0 ≤ x 1)
    (he0 : e 0 < 0) (he1 : e 1 < 0) :
    inner ℝ e x ≤ 0 ∧ (inner ℝ e x = 0 → x = 0) := by
  have hsum : inner ℝ e x = e 0 * x 0 + e 1 * x 1 :=
    Schoenflies.Plane.inner_eq e x
  have hp0 : e 0 * x 0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg he0.le hx0
  have hp1 : e 1 * x 1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg he1.le hx1
  refine ⟨by linarith, ?_⟩
  intro hzero
  have hp0zero : e 0 * x 0 = 0 := by linarith
  have hp1zero : e 1 * x 1 = 0 := by linarith
  have hx0zero : x 0 = 0 := (mul_eq_zero.mp hp0zero).resolve_left he0.ne
  have hx1zero : x 1 = 0 := (mul_eq_zero.mp hp1zero).resolve_left he1.ne
  ext i
  fin_cases i <;> simp [hx0zero, hx1zero]

/-- If the inward coordinate is bounded by one at a unique maximizing
point, every level-one contact is that point. -/
theorem levelOneContact_subset_singleton_of_support
    {P : Set Plane} {V W e : Plane}
    (hbound : inner ℝ e (W - V) ≤ 1)
    (hsupport : ∀ x ∈ P, inner ℝ e (x - W) ≤ 0 ∧
      (inner ℝ e (x - W) = 0 → x = W)) :
    levelOneContact P V e ⊆ {W} := by
  rintro x ⟨hxP, hxlevel⟩
  obtain ⟨hxle, hxeq⟩ := hsupport x hxP
  have hsum : inner ℝ e (x - V) =
      inner ℝ e (x - W) + inner ℝ e (W - V) := by
    rw [← inner_add_right]
    congr 1
    abel
  have hxzero : inner ℝ e (x - W) = 0 := by linarith
  exact hxeq hxzero

/-- Consecutive perpendicular supporting frames force the segment
joining their vertices to run along their common boundary direction. -/
theorem adjacent_support_vertices {B C : Plane} {θ : ℝ}
    (hC : C ∈ supportCone B θ)
    (hB : B ∈ supportCone C (θ + Real.pi / 2)) :
    ∃ s : ℝ, 0 ≤ s ∧ C = B + s • ray θ := by
  obtain ⟨s, t, hs, ht, hrepr⟩ := (mem_supportCone_iff C B θ).mp hC
  have hreverse : inner ℝ (perpRay θ) (ray θ) = 0 := by
    rw [real_inner_comm]
    exact ray_inner_perpRay θ
  have hBC : B - C = -(s • ray θ + t • perpRay θ) := by
    rw [hrepr]
    abel
  have hinner : inner ℝ (perpRay θ) (B - C) = -t := by
    rw [hBC, inner_neg_right, inner_add_right, inner_smul_right,
      inner_smul_right, hreverse, perp_inner_self]
    ring
  have htneg : 0 ≤ -t := by
    have hb := hB.1
    rw [ray_add_pi_div_two, hinner] at hb
    exact hb
  have ht0 : t = 0 := by linarith
  refine ⟨s, hs, ?_⟩
  simpa [ht0] using hrepr

/-- In consecutive perpendicular frames, a full unit separation makes
the two frame centers equal. -/
theorem frame_centers_eq_of_unit_separation {B C : Plane} {θ : ℝ}
    (hC : C = B + ray θ) :
    C + (1 / 2 : ℝ) •
        (ray (θ + Real.pi / 2) + perpRay (θ + Real.pi / 2)) =
      B + (1 / 2 : ℝ) • (ray θ + perpRay θ) := by
  rw [hC, ray_add_pi_div_two, perp_add_pi_div_two]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
  ring

/-- If the two frame centers differ, consecutive perpendicular frames
cannot attain level one in either of the facing coordinates. -/
theorem adjacent_frames_strict_levels {B C x : Plane} {θ : ℝ}
    (hC : C ∈ supportCone B θ)
    (hB : B ∈ supportCone C (θ + Real.pi / 2))
    (hbound : inner ℝ (ray θ) (C - B) ≤ 1)
    (hcenters : C + (1 / 2 : ℝ) •
        (ray (θ + Real.pi / 2) + perpRay (θ + Real.pi / 2)) ≠
      B + (1 / 2 : ℝ) • (ray θ + perpRay θ))
    (hxB : x ∈ supportCone B θ)
    (hxC : x ∈ supportCone C (θ + Real.pi / 2)) :
    inner ℝ (ray θ) (x - B) < 1 ∧
      inner ℝ (perpRay (θ + Real.pi / 2)) (x - C) < 1 := by
  obtain ⟨s, hs, hrepr⟩ := adjacent_support_vertices hC hB
  have hCB : C - B = s • ray θ := by rw [hrepr]; abel
  have hsep : inner ℝ (ray θ) (C - B) = s := by
    rw [hCB, inner_smul_right, ray_inner_self, mul_one]
  have hsle : s ≤ 1 := by simpa only [hsep] using hbound
  have hsne : s ≠ 1 := by
    intro hs1
    apply hcenters
    apply frame_centers_eq_of_unit_separation
    simpa only [hs1, one_smul] using hrepr
  have hslt : s < 1 := lt_of_le_of_ne hsle hsne
  have hxCle : inner ℝ (ray θ) (x - C) ≤ 0 := by
    have h := hxC.2
    rw [perp_add_pi_div_two, inner_neg_left] at h
    linarith
  have hsum : inner ℝ (ray θ) (x - B) =
      inner ℝ (ray θ) (x - C) + s := by
    rw [← hsep, ← inner_add_right]
    congr 1
    abel
  have hneg : inner ℝ (perpRay (θ + Real.pi / 2)) (x - C) =
      s - inner ℝ (ray θ) (x - B) := by
    rw [perp_add_pi_div_two, inner_neg_left]
    linarith
  constructor
  · linarith
  · have hxBnonneg := hxB.1
    linarith

end

end Puzzling139335.N4Midline
