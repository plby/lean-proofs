import StackExchange.Puzzling139335.N4TwoOneOne.TopFace

/-!
# The outgoing-direction version of the actual top-face pullback
-/

open Set

namespace Puzzling139335.N4TwoOneOne

open PlaneIsometries ThreeCorners

theorem eCoord_add_half_pi (φ : ℝ) (p : Plane) :
    eCoord (φ + Real.pi / 2) p = fCoord φ p := by
  simp [eCoord, fCoord, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]

theorem perpRay_add_half_pi (φ : ℝ) :
    perpRay (φ + Real.pi / 2) = -ray φ := by
  ext i
  fin_cases i <;> simp [perpRay, ray, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]

theorem exists_suffix_top_face_endpoints {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {φ T : ℝ}
    (hfit : e '' P ⊆ unitSquare)
    (h₀ : linearMatrix e 1 0 = -Real.sin φ)
    (h₁ : linearMatrix e 1 1 = Real.cos φ)
    (hleft : (!₂[T, 1] : Plane) ∈ e '' P)
    (hright : (!₂[1 - T, 1] : Plane) ∈ e '' P) :
    ∃ X Y : Plane, X ∈ P ∧ Y ∈ P ∧
      Y = X - (1 - 2 * T) • ray φ ∧
      (∀ p ∈ P, fCoord φ p ≤ fCoord φ X) ∧
      (∀ p ∈ P, fCoord φ X - 1 ≤ fCoord φ p) := by
  have he₀ : linearMatrix e 1 0 = Real.cos (φ + Real.pi / 2) := by
    simpa only [Real.cos_add_pi_div_two] using h₀
  have he₁ : linearMatrix e 1 1 = Real.sin (φ + Real.pi / 2) := by
    simpa only [Real.sin_add_pi_div_two] using h₁
  obtain ⟨X, Y, hX, hY, hstep, hsupport, hstrip⟩ :=
    exists_top_face_endpoints e hfit he₀ he₁ hleft hright
  refine ⟨X, Y, hX, hY, ?_, ?_, ?_⟩
  · simpa only [perpRay_add_half_pi, smul_neg, ← sub_eq_add_neg] using hstep
  · simpa only [eCoord_add_half_pi] using hsupport
  · simpa only [eCoord_add_half_pi] using hstrip

end Puzzling139335.N4TwoOneOne
