import Wikipedia.SmoothSixDPoincare.SmallPerturbationDiffeomorph
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Genuine compactly supported bump-translation diffeomorphisms

A compactly supported smooth scalar cutoff is globally Lipschitz. Multiplying
it by a sufficiently small vector gives a smooth perturbation of the identity
with a proved global smooth inverse. The map has the exact translation formula
on the cutoff's plateau and is exactly fixed on its zero set.
-/

noncomputable section

open Function Set
open scoped ContDiff Manifold NNReal

namespace Wikipedia.SmoothSixDPoincare.SmallPerturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The explicit Lipschitz estimate for a scalar-weighted vector displacement. -/
theorem lipschitzWith_smul_const {β : E → ℝ} {k : ℝ≥0}
    (hβ : LipschitzWith k β) (a : E) : LipschitzWith (k * ‖a‖₊) (fun x => β x • a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (β x • a) (β y • a) = ‖β x - β y‖ * ‖a‖ := by
      rw [dist_eq_norm, ← sub_smul, norm_smul]
    _ ≤ ((k : ℝ) * dist x y) * ‖a‖ :=
      mul_le_mul_of_nonneg_right (hβ.dist_le_mul x y) (norm_nonneg a)
    _ = (k * ‖a‖₊ : ℝ≥0) * dist x y := by
      simp only [NNReal.coe_mul, coe_nnnorm]
      ring

variable [FiniteDimensional ℝ E]

/-- The weighted translation, with its actual globally smooth inverse. -/
def bumpTranslation {β : E → ℝ} {k : ℝ≥0} (hs : ContDiff ℝ ∞ β)
    (hβ : LipschitzWith k β) (a : E) (ha : k * ‖a‖₊ < 1) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  diffeomorphIdAdd (hs.smul contDiff_const) (lipschitzWith_smul_const hβ a) ha

theorem bumpTranslation_apply {β : E → ℝ} {k : ℝ≥0} (hs : ContDiff ℝ ∞ β)
    (hβ : LipschitzWith k β) (a : E) (ha : k * ‖a‖₊ < 1) (x : E) :
    bumpTranslation hs hβ a ha x = x + β x • a := rfl

theorem bumpTranslation_eq_of_zero {β : E → ℝ} {k : ℝ≥0} (hs : ContDiff ℝ ∞ β)
    (hβ : LipschitzWith k β) (a : E) (ha : k * ‖a‖₊ < 1) {x : E} (hx : β x = 0) :
    bumpTranslation hs hβ a ha x = x := by
  rw [bumpTranslation_apply, hx, zero_smul, add_zero]

/-- Compact support gives a positive radius of actual diffeomorphism parameters. -/
theorem exists_radius_bumpTranslation {β : E → ℝ} (hs : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : E, ‖a‖ < ε →
      ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        (∀ x, d x = x + β x • a) ∧ ∀ x ∉ tsupport β, d x = x := by
  obtain ⟨k, hk⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hs (by simp)
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  refine ⟨((k : ℝ) + 1)⁻¹, inv_pos.mpr hkpos, ?_⟩
  intro a ha
  have hmul : ((k : ℝ) + 1) * ‖a‖ < 1 := by
    calc
      ((k : ℝ) + 1) * ‖a‖ < ((k : ℝ) + 1) * ((k : ℝ) + 1)⁻¹ :=
        mul_lt_mul_of_pos_left ha hkpos
      _ = 1 := mul_inv_cancel₀ hkpos.ne'
  have hsmall : k * ‖a‖₊ < 1 := by
    have hreal : (k : ℝ) * ‖a‖ < 1 := by nlinarith [norm_nonneg a]
    exact hreal
  refine ⟨bumpTranslation hs hk a hsmall, fun _ => rfl, ?_⟩
  intro x hx
  apply bumpTranslation_eq_of_zero
  by_contra hne
  exact hx (subset_tsupport β hne)

end Wikipedia.SmoothSixDPoincare.SmallPerturbation
