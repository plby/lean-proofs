import StackExchange.Puzzling139335.ThreeCorners.AngleParam
import StackExchange.Puzzling139335.CornerSupport.Equality.Coordinates

/-!
# Positively oriented frames for supporting right corners

The inward rays at angle `θ` are the unit vectors at angles `θ` and
`θ + π / 2`.  Their negative sum is the outward supporting bisector.
-/

open Set

namespace Puzzling139335.ThreeCorners

noncomputable section

/-- The first unit inward ray. -/
def ray (θ : ℝ) : Plane := !₂[Real.cos θ, Real.sin θ]

/-- The second inward ray, a counterclockwise quarter-turn from the first. -/
def perpRay (θ : ℝ) : Plane := !₂[-Real.sin θ, Real.cos θ]

/-- The outward bisector of the positively oriented inward frame. -/
def outwardBisector (θ : ℝ) : Plane := -(ray θ + perpRay θ)

@[simp] theorem ray_zero (θ : ℝ) : ray θ 0 = Real.cos θ := rfl
@[simp] theorem ray_one (θ : ℝ) : ray θ 1 = Real.sin θ := rfl
@[simp] theorem perpRay_zero (θ : ℝ) : perpRay θ 0 = -Real.sin θ := rfl
@[simp] theorem perpRay_one (θ : ℝ) : perpRay θ 1 = Real.cos θ := rfl

theorem norm_ray (θ : ℝ) : ‖ray θ‖ = 1 := by
  have hsq : ‖ray θ‖ ^ 2 = (1 : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two, ray_zero, ray_one]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (ray θ)]

theorem norm_perpRay (θ : ℝ) : ‖perpRay θ‖ = 1 := by
  have hsq : ‖perpRay θ‖ ^ 2 = (1 : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two, perpRay_zero, perpRay_one]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (perpRay θ)]

theorem ray_inner_perpRay (θ : ℝ) : inner ℝ (ray θ) (perpRay θ) = 0 := by
  simp only [Schoenflies.Plane.inner_eq, ray_zero, ray_one, perpRay_zero, perpRay_one]
  ring

theorem rays_orthonormal (θ : ℝ) :
    Orthonormal ℝ (![ray θ, perpRay θ] : Fin 2 → Plane) := by
  simp [orthonormal_vecCons_iff, norm_ray, norm_perpRay, ray_inner_perpRay]

/-- The angular inward frame as an orthonormal basis of the plane. -/
def rayBasis (θ : ℝ) : OrthonormalBasis (Fin 2) ℝ Plane :=
  OrthonormalBasis.mk (rays_orthonormal θ)
    ((rays_orthonormal θ).linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp [Plane])).ge

@[simp] theorem rayBasis_zero (θ : ℝ) : rayBasis θ 0 = ray θ := by
  simp [rayBasis, OrthonormalBasis.coe_mk]

@[simp] theorem rayBasis_one (θ : ℝ) : rayBasis θ 1 = perpRay θ := by
  simp [rayBasis, OrthonormalBasis.coe_mk]

theorem outwardBisector_norm_sq (θ : ℝ) : ‖outwardBisector θ‖ ^ 2 = (2 : ℝ) := by
  have hreverse : inner ℝ (perpRay θ) (ray θ) = 0 := by
    rw [real_inner_comm]
    exact ray_inner_perpRay θ
  norm_num [outwardBisector, norm_add_sq_real, norm_ray, norm_perpRay,
    ray_inner_perpRay, hreverse]

/-- Bisector inner products measure the cosine of the difference between
the corresponding first inward-ray angles. -/
theorem outwardBisector_inner (θ φ : ℝ) :
    inner ℝ (outwardBisector θ) (outwardBisector φ) =
      2 * Real.cos (φ - θ) := by
  simp [Schoenflies.Plane.inner_eq, outwardBisector, ray, perpRay, Real.cos_sub]
  ring

@[simp] theorem outwardBisector_zero : outwardBisector 0 = !₂[-1, -1] := by
  ext i
  fin_cases i <;> simp [outwardBisector, ray, perpRay]

/-- A bisector nonacute to the outward bisector at the origin has a
canonical inward-ray angle in the opposite closed semicircle. -/
theorem exists_angle_of_inner_origin_nonpos (b : Plane)
    (hb : ‖b‖ ^ 2 = (2 : ℝ))
    (hInner : inner ℝ (!₂[-1, -1] : Plane) b ≤ 0) :
    ∃ θ : ℝ, θ ∈ Icc (Real.pi / 2) (3 * Real.pi / 2) ∧
      b = outwardBisector θ := by
  have hb' : b 0 ^ 2 + b 1 ^ 2 = 2 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using hb
  have hunit : (-(b 0 + b 1) / 2) ^ 2 + ((b 0 - b 1) / 2) ^ 2 = (1 : ℝ) := by
    nlinarith
  have hleft : -(b 0 + b 1) / 2 ≤ 0 := by
    simp only [Schoenflies.Plane.inner_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at hInner
    nlinarith
  obtain ⟨θ, hθ, hcos, hsin⟩ := exists_angle_left_semicircle hunit hleft
  refine ⟨θ, hθ, ?_⟩
  ext i
  fin_cases i <;> simp [outwardBisector, ray, perpRay, hcos, hsin] <;> ring

/-- The right-angle supporting cone in its positively oriented inward
frame. -/
def supportCone (v : Plane) (θ : ℝ) : Set Plane :=
  {x | 0 ≤ inner ℝ (ray θ) (x - v) ∧ 0 ≤ inner ℝ (perpRay θ) (x - v)}

theorem mem_supportCone_iff (x v : Plane) (θ : ℝ) :
    x ∈ supportCone v θ ↔
      ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ x = v + s • ray θ + t • perpRay θ := by
  constructor
  · intro hx
    refine ⟨inner ℝ (ray θ) (x - v), inner ℝ (perpRay θ) (x - v),
      hx.1, hx.2, ?_⟩
    have hrepr := (rayBasis θ).sum_repr' (x - v)
    simp only [Fin.sum_univ_two, rayBasis_zero, rayBasis_one] at hrepr
    calc
      x = v + (x - v) := by abel
      _ = v + (inner ℝ (ray θ) (x - v) • ray θ +
          inner ℝ (perpRay θ) (x - v) • perpRay θ) :=
        congrArg (fun z : Plane => v + z) hrepr.symm
      _ = v + inner ℝ (ray θ) (x - v) • ray θ +
          inner ℝ (perpRay θ) (x - v) • perpRay θ := by
        abel
  · rintro ⟨s, t, hs, ht, rfl⟩
    have hfirst : inner ℝ (ray θ) (ray θ) = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_ray]
      norm_num
    have hsecond : inner ℝ (perpRay θ) (perpRay θ) = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_perpRay]
      norm_num
    have hreverse : inner ℝ (perpRay θ) (ray θ) = 0 := by
      rw [real_inner_comm]
      exact ray_inner_perpRay θ
    have hsub : v + s • ray θ + t • perpRay θ - v =
        s • ray θ + t • perpRay θ := by abel
    simp only [supportCone, mem_ofPred_eq, hsub, inner_add_right, inner_smul_right,
      hfirst, hsecond, ray_inner_perpRay, hreverse, mul_one, mul_zero, add_zero,
      zero_add]
    exact ⟨hs, ht⟩

/-- The whole set lies in the cone determined by its supporting bisector.
The chosen ordering of the two original normals is immaterial. -/
theorem subset_supportCone_of_bisector {P : Set Plane} {v : Plane}
    (h : SupportCorner P v) {θ : ℝ} (hθ : h.bisector = outwardBisector θ) :
    P ⊆ supportCone v θ := by
  intro x hx
  have hcoords := CornerSupport.Equality.coords_nonneg_of_bisector_eq_neg_sum
    h (rayBasis θ) (by simpa [outwardBisector] using hθ) hx
  change 0 ≤ inner ℝ (ray θ) (x - v) ∧ 0 ≤ inner ℝ (perpRay θ) (x - v)
  simpa only [rayBasis_zero, rayBasis_one] using hcoords

end

end Puzzling139335.ThreeCorners
