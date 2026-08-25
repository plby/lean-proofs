import StackExchange.Puzzling139335.N4Diagonal.Defs

/-!
# Angular coordinates for an actual diagonal pair

The ordered inward angles supplied by the three-corner theorem are shifted
by a quarter-turn and a half-turn to give the diagonal model's coordinates.
-/

open Set

namespace Puzzling139335.N4Diagonal.FromDissection

open ThreeCorners

theorem ray_sub_half_pi (θ : ℝ) :
    ray (θ - Real.pi / 2) = -perpRay θ := by
  ext i
  fin_cases i <;> simp [ray, perpRay, Real.cos_sub_pi_div_two,
    Real.sin_sub_pi_div_two]

theorem perpRay_sub_half_pi (θ : ℝ) :
    perpRay (θ - Real.pi / 2) = ray θ := by
  ext i
  fin_cases i <;> simp [ray, perpRay, Real.cos_sub_pi_div_two,
    Real.sin_sub_pi_div_two]

theorem ray_sub_pi (θ : ℝ) : ray (θ - Real.pi) = -ray θ := by
  ext i
  fin_cases i <;> simp [ray, Real.cos_sub_pi, Real.sin_sub_pi]

theorem perpRay_sub_pi (θ : ℝ) : perpRay (θ - Real.pi) = -perpRay θ := by
  ext i
  fin_cases i <;> simp [perpRay, Real.cos_sub_pi, Real.sin_sub_pi]

theorem shifted_angle_bounds {θ φ : ℝ}
    (hθ : θ ∈ Icc (Real.pi / 2) Real.pi)
    (hφ : φ ∈ Icc (θ + Real.pi / 2) (3 * Real.pi / 2)) :
    θ - Real.pi / 2 ∈ Icc (0 : ℝ) (Real.pi / 2) ∧
      φ - Real.pi ∈ Icc (θ - Real.pi / 2) (Real.pi / 2) := by
  constructor <;> constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2]

theorem first_support_of_supportCone {P : Set Plane} {p : Plane} {θ : ℝ}
    (hP : P ⊆ supportCone p θ) :
    ∀ x ∈ P,
      0 ≤ inner ℝ (perpRay (θ - Real.pi / 2)) (x - p) ∧
        inner ℝ (ray (θ - Real.pi / 2)) (x - p) ≤ 0 := by
  intro x hx
  simpa only [perpRay_sub_half_pi, ray_sub_half_pi, inner_neg_left, neg_nonpos,
    supportCone, mem_ofPred_eq]
    using hP hx

theorem last_support_of_supportCone {P : Set Plane} {q : Plane} {φ : ℝ}
    (hP : P ⊆ supportCone q φ) :
    ∀ x ∈ P,
      inner ℝ (ray (φ - Real.pi)) (x - q) ≤ 0 ∧
        inner ℝ (perpRay (φ - Real.pi)) (x - q) ≤ 0 := by
  intro x hx
  simpa only [ray_sub_pi, perpRay_sub_pi, inner_neg_left, neg_nonpos,
    supportCone, mem_ofPred_eq]
    using hP hx

end Puzzling139335.N4Diagonal.FromDissection
