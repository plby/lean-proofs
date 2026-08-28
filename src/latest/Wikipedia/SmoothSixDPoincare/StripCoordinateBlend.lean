import Wikipedia.SmoothSixDPoincare.StripSliceDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Smooth blending of strip coordinate maps

The model strip has the exact straight center section and the specified
normal derivative. Time-dependent cutoffs blend in two corner maps without
changing those data wherever the corner jets agree with the model.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.StripCoordinates

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

abbrev Space (A B : Type*) := (ℝ × A) × B

def center (t : ℝ) : Space A B := ((t, 0), 0)

def model (v : ℝ → B) (p : ℝ × ℝ) : Space A B := ((p.1, 0), p.2 • v p.1)

def normalDerivative (F : (ℝ × ℝ) → Space A B) (t : ℝ) : B :=
  fderiv ℝ (fun p => (F p).2) (t, 0) (0, 1)

def blend (v : ℝ → B) (F₀ F₁ : (ℝ × ℝ) → Space A B) (β₀ β₁ : ℝ → ℝ)
    (p : ℝ × ℝ) : Space A B :=
  model v p + β₀ p.1 • (F₀ p - model v p) + β₁ p.1 • (F₁ p - model v p)

theorem contDiff_model {v : ℝ → B} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (model (A := A) v) :=
  (contDiff_fst.prodMk contDiff_const).prodMk (contDiff_snd.smul (hv.comp contDiff_fst))

theorem contDiff_blend {v : ℝ → B} {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hF₀ : ContDiff ℝ ∞ F₀) (hF₁ : ContDiff ℝ ∞ F₁)
    (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁) :
    ContDiff ℝ ∞ (blend v F₀ F₁ β₀ β₁) :=
  ((contDiff_model hv).add ((hβ₀.comp contDiff_fst).smul (hF₀.sub (contDiff_model hv)))).add
    ((hβ₁.comp contDiff_fst).smul (hF₁.sub (contDiff_model hv)))

omit [NormedSpace ℝ A] in
theorem model_zero (v : ℝ → B) (t : ℝ) : model (A := A) v (t, 0) = center t := by
  simp only [model, center, zero_smul]

theorem blend_zero {v : ℝ → B} {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ}
    (h₀ : ∀ t, β₀ t ≠ 0 → F₀ (t, 0) = center t)
    (h₁ : ∀ t, β₁ t ≠ 0 → F₁ (t, 0) = center t) (t : ℝ) :
    blend v F₀ F₁ β₀ β₁ (t, 0) = center t := by
  have hterm₀ : β₀ t • (F₀ (t, 0) - model v (t, 0)) = 0 := by
    by_cases h : β₀ t = 0
    · rw [h, zero_smul]
    · rw [h₀ t h, model_zero, sub_self, smul_zero]
  have hterm₁ : β₁ t • (F₁ (t, 0) - model v (t, 0)) = 0 := by
    by_cases h : β₁ t = 0
    · rw [h, zero_smul]
    · rw [h₁ t h, model_zero, sub_self, smul_zero]
  change model v (t, 0) + β₀ t • (F₀ (t, 0) - model v (t, 0)) +
    β₁ t • (F₁ (t, 0) - model v (t, 0)) = center t
  rw [hterm₀, hterm₁, add_zero, add_zero, model_zero]

theorem blend_eq_left {v : ℝ → B} {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ}
    {p : ℝ × ℝ} (h₀ : β₀ p.1 = 1) (h₁ : β₁ p.1 = 0) :
    blend v F₀ F₁ β₀ β₁ p = F₀ p := by
  simp only [blend, h₀, h₁, one_smul, zero_smul, add_zero]
  rw [← add_sub_assoc, add_sub_cancel_left]

theorem blend_eq_right {v : ℝ → B} {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ}
    {p : ℝ × ℝ} (h₀ : β₀ p.1 = 0) (h₁ : β₁ p.1 = 1) :
    blend v F₀ F₁ β₀ β₁ p = F₁ p := by
  simp only [blend, h₀, h₁, one_smul, zero_smul, add_zero]
  rw [← add_sub_assoc, add_sub_cancel_left]

theorem normalDerivative_blend {v : ℝ → B} {F₀ F₁ : (ℝ × ℝ) → Space A B}
    {β₀ β₁ : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hF₀ : ContDiff ℝ ∞ F₀) (hF₁ : ContDiff ℝ ∞ F₁)
    (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁)
    (h₀ : ∀ t, β₀ t ≠ 0 → normalDerivative F₀ t = v t)
    (h₁ : ∀ t, β₁ t ≠ 0 → normalDerivative F₁ t = v t) (t : ℝ) :
    normalDerivative (blend v F₀ F₁ β₀ β₁) t = v t := by
  have hm : HasDerivAt (fun s : ℝ => s • v t) (v t) 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const (v t)
  have hd₀ := hasDerivAt_verticalSlice (t := t) (s := 0)
    (hF₀.snd.contDiffAt.differentiableAt (by simp))
  have hd₁ := hasDerivAt_verticalSlice (t := t) (s := 0)
    (hF₁.snd.contDiffAt.differentiableAt (by simp))
  have hterm₀ : β₀ t • (normalDerivative F₀ t - v t) = 0 := by
    by_cases h : β₀ t = 0
    · rw [h, zero_smul]
    · rw [h₀ t h, sub_self, smul_zero]
  have hterm₁ : β₁ t • (normalDerivative F₁ t - v t) = 0 := by
    by_cases h : β₁ t = 0
    · rw [h, zero_smul]
    · rw [h₁ t h, sub_self, smul_zero]
  have hblend : HasDerivAt (fun s : ℝ => (blend v F₀ F₁ β₀ β₁ (t, s)).2)
      (v t + β₀ t • (normalDerivative F₀ t - v t) +
        β₁ t • (normalDerivative F₁ t - v t)) 0 :=
    HasDerivAt.add
      (HasDerivAt.add hm (HasDerivAt.const_smul (β₀ t) (HasDerivAt.sub hd₀ hm)))
      (HasDerivAt.const_smul (β₁ t) (HasDerivAt.sub hd₁ hm))
  have hblend' : HasDerivAt (fun s : ℝ => (blend v F₀ F₁ β₀ β₁ (t, s)).2) (v t) 0 := by
    simpa only [hterm₀, hterm₁, add_zero] using hblend
  exact (hasDerivAt_verticalSlice
    ((contDiff_blend hv hF₀ hF₁ hβ₀ hβ₁).snd.contDiffAt.differentiableAt (by simp))).unique hblend'

end Wikipedia.SmoothSixDPoincare.StripCoordinates
