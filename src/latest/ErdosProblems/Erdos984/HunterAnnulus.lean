/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Thin annuli and three-term progressions

This is the deterministic geometric core of the blue-progression argument:
three equally spaced points in one squared annulus force the squared norm of
the step to be no larger than the annulus width.
-/

namespace Erdos984

section RealInnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def squaredNorm (x : E) : ℝ := ‖x‖ ^ 2

def InSquaredAnnulus (radius width : ℝ) (x : E) : Prop :=
  radius ≤ squaredNorm x ∧ squaredNorm x ≤ radius + width

omit [InnerProductSpace ℝ E] in
lemma squaredNorm_nonneg (x : E) : 0 ≤ squaredNorm x := by
  simp [squaredNorm]

/-- The second-difference identity for squared norm along a three-term
progression. -/
lemma squaredNorm_second_difference (u v : E) :
    squaredNorm u + squaredNorm ((u + v) + v) =
      2 * squaredNorm (u + v) + 2 * squaredNorm v := by
  simp only [squaredNorm, norm_add_sq_real, inner_add_left,
    real_inner_self_eq_norm_sq]
  ring

lemma squaredNorm_step_le_width {radius width : ℝ} {u v : E}
    (h₀ : InSquaredAnnulus radius width u)
    (h₁ : InSquaredAnnulus radius width (u + v))
    (h₂ : InSquaredAnnulus radius width ((u + v) + v)) :
    squaredNorm v ≤ width := by
  have hid := squaredNorm_second_difference u v
  unfold InSquaredAnnulus at h₀ h₁ h₂
  nlinarith [squaredNorm_nonneg v]

/-- A thin squared annulus cannot contain a nontrivial three-term
progression whose step has squared norm larger than its width. -/
lemma not_three_mem_squaredAnnulus {radius width : ℝ} {u v : E}
    (hthin : width < squaredNorm v) :
    ¬(InSquaredAnnulus radius width u ∧
      InSquaredAnnulus radius width (u + v) ∧
      InSquaredAnnulus radius width ((u + v) + v)) := by
  rintro ⟨h₀, h₁, h₂⟩
  exact (not_le_of_gt hthin) (squaredNorm_step_le_width h₀ h₁ h₂)

/-- A coordinate lower bound supplies the step-size hypothesis needed by
the annulus lemma. -/
lemma squaredNorm_step_gt_of_coordinate {D : ℕ} {v : EuclideanSpace ℝ (Fin D)}
    {i : Fin D} {δ : ℝ} (hδ : 0 ≤ δ) (hi : √δ < |v i|) :
    δ < squaredNorm v := by
  have hcoord : |v i| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  have hsqrt : √δ < ‖v‖ := lt_of_lt_of_le hi hcoord
  have hsq : δ = (√δ) ^ 2 := (Real.sq_sqrt hδ).symm
  have hsquares : (√δ) ^ 2 < ‖v‖ ^ 2 := by
    simpa only [pow_two] using
      mul_self_lt_mul_self (Real.sqrt_nonneg δ) hsqrt
  rw [squaredNorm, hsq]
  exact hsquares

end RealInnerProduct

end Erdos984
