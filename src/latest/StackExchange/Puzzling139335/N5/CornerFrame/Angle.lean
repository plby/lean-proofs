import StackExchange.Puzzling139335.N5.CornerFrame
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The angle range of the actual five-incidence corner frame
-/

open Set

namespace Puzzling139335.N5

/-- Ordered nonnegative unit-circle parameters give an angle between zero
and one eighth of a turn. -/
theorem exists_angle_of_ordered_frame {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (hs : 0 ≤ s) (hsc : s ≤ c) :
    ∃ θ : ℝ, θ ∈ Icc (0 : ℝ) (Real.pi / 4) ∧
      Real.cos θ = c ∧ Real.sin θ = s := by
  have hc : 0 ≤ c := hs.trans hsc
  have hc₁ : c ≤ 1 := by nlinarith [sq_nonneg s]
  have hcneg : -1 ≤ c := by linarith
  have hdiff := mul_nonneg (sub_nonneg.mpr hsc) (add_nonneg hc hs)
  have hroot : Real.sqrt 2 ≤ 2 * c := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith⟩
  have hcos : Real.cos (Real.pi / 4) ≤ c := by
    rw [Real.cos_pi_div_four]
    linarith
  have hangle : Real.arccos c ≤ Real.pi / 4 := by
    calc
      Real.arccos c ≤ Real.arccos (Real.cos (Real.pi / 4)) :=
        Real.arccos_le_arccos hcos
      _ = Real.pi / 4 := Real.arccos_cos
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  refine ⟨Real.arccos c, ⟨Real.arccos_nonneg c, hangle⟩,
    Real.cos_arccos hcneg hc₁, ?_⟩
  rw [Real.sin_arccos, show 1 - c ^ 2 = s ^ 2 by linarith,
    Real.sqrt_sq_eq_abs, abs_of_nonneg hs]

/-- The actual placement therefore has the same coordinate alternatives
with cosine and sine of an angle in `[0, π/4]`. -/
theorem cornerAngle_of_placement {P : Set Plane} {C : Plane}
    (hP : P ⊆ unitSquare) (hbelow : P ⊆ {p | p 1 ≤ p 0})
    (hA : corner 0 ∈ P) (hB : corner 1 ∈ P)
    (hC : C ∈ P) (hCA : C ≠ corner 0) (hCB : C ≠ corner 1)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P ⊆ unitSquare)
    (heC : e C = corner 2) :
    0 < C 1 ∧ ∃ θ : ℝ,
      θ ∈ Icc (0 : ℝ) (Real.pi / 4) ∧ 0 < Real.cos θ ∧
      Real.sin θ * C 0 ≤ Real.cos θ * C 1 ∧
      Real.cos θ * (1 - C 0) ≤ Real.sin θ * C 1 ∧
      ((∀ p, e p =
          !₂[1 - Real.cos θ * C 0 - Real.sin θ * C 1 +
               Real.cos θ * p 0 + Real.sin θ * p 1,
             1 + Real.sin θ * C 0 - Real.cos θ * C 1 -
               Real.sin θ * p 0 + Real.cos θ * p 1]) ∨
       (∀ p, e p =
          !₂[1 + Real.sin θ * C 0 - Real.cos θ * C 1 -
               Real.sin θ * p 0 + Real.cos θ * p 1,
             1 - Real.cos θ * C 0 - Real.sin θ * C 1 +
               Real.cos θ * p 0 + Real.sin θ * p 1])) := by
  obtain ⟨hk, c, s, hcs, hs, hsc, hcpos, hleft, hright, hform⟩ :=
    cornerFrame_of_placement hP hbelow hA hB hC hCA hCB e he heC
  obtain ⟨θ, hθ, hcos, hsin⟩ := exists_angle_of_ordered_frame hcs hs hsc
  refine ⟨hk, θ, hθ, ?_, ?_, ?_, ?_⟩
  · simpa only [hcos] using hcpos
  · simpa only [hcos, hsin] using hleft
  · simpa only [hcos, hsin] using hright
  · simpa only [hcos, hsin] using hform

end Puzzling139335.N5
