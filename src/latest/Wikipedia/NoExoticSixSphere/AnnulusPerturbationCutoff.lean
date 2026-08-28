import Wikipedia.NoExoticSixSphere.SphereAnnulusCoordinates
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A smooth nonnegative cutoff with exactly the desired active annulus

The cutoff is positive precisely between the two chosen radii and zero
on both protected collars. Squared norms make it globally smooth, including
at the origin. Its closed active core is compact and strictly inside the
original annulus when the chosen radii are strictly between one and two.
-/

noncomputable section

open Set Metric
open scoped ContDiff

namespace NoExoticSixSphere.SphereAnnulus

open GLOrthonormalization

def perturbationCutoff {p : ℕ} (r₀ r₁ : ℝ) (x : Vector (p + 1)) : ℝ :=
  Real.smoothTransition (‖x‖ ^ 2 - r₀ ^ 2) * Real.smoothTransition (r₁ ^ 2 - ‖x‖ ^ 2)

theorem contDiff_perturbationCutoff (p : ℕ) (r₀ r₁ : ℝ) :
    ContDiff ℝ ∞ (perturbationCutoff (p := p) r₀ r₁) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_norm_sq ℝ).sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ)))

theorem perturbationCutoff_nonneg {p : ℕ} (r₀ r₁ : ℝ) (x : Vector (p + 1)) :
    0 ≤ perturbationCutoff r₀ r₁ x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem perturbationCutoff_ne_zero_iff {p : ℕ} (r₀ r₁ : ℝ)
    (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁) (x : Vector (p + 1)) :
    perturbationCutoff r₀ r₁ x ≠ 0 ↔ r₀ < ‖x‖ ∧ ‖x‖ < r₁ := by
  simp only [perturbationCutoff, mul_ne_zero_iff, ne_eq,
    Real.smoothTransition.zero_iff_nonpos, not_le]
  have hn := norm_nonneg x
  constructor
  · rintro ⟨h₀, h₁⟩
    constructor <;> nlinarith
  · rintro ⟨h₀, h₁⟩
    constructor <;> nlinarith

theorem perturbationCutoff_zero_of_protected {p : ℕ} (r₀ r₁ : ℝ)
    (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁) (x : Vector (p + 1))
    (hx : ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖) : perturbationCutoff r₀ r₁ x = 0 := by
  by_contra hne
  obtain ⟨h₀, h₁⟩ := (perturbationCutoff_ne_zero_iff r₀ r₁ hr₀ hr₁ x).mp hne
  exact hx.elim (not_le_of_gt h₀) (not_le_of_gt h₁)

def closedCore (p : ℕ) (r₀ r₁ : ℝ) : Set (Vector (p + 1)) :=
  {x | r₀ ≤ ‖x‖ ∧ ‖x‖ ≤ r₁}

theorem isCompact_closedCore (p : ℕ) (r₀ r₁ : ℝ) : IsCompact (closedCore p r₀ r₁) :=
  (isCompact_closedBall (0 : Vector (p + 1)) r₁).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    (fun _ hx ↦ mem_closedBall_zero_iff.mpr hx.2)

theorem closedCore_subset_domain (p : ℕ) {r₀ r₁ : ℝ} (hr₀ : 1 ≤ r₀) (hr₁ : r₁ ≤ 2) :
    closedCore p r₀ r₁ ⊆ domain p :=
  fun _ hx ↦ ⟨hr₀.trans hx.1, hx.2.trans hr₁⟩

end NoExoticSixSphere.SphereAnnulus
