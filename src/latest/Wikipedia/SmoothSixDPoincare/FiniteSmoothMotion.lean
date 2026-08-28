import Wikipedia.SmoothSixDPoincare.UniformSupportedBumpIsotopy

/-!
# Finite composition of smooth families of diffeomorphisms

All factors use the same control parameter. Joint smoothness, the initial
identity, a common fixed complement, and preserved coordinate functions pass
to the finite composition. Every parameter value remains a diffeomorphism.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmallPerturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Apply the first `n` spatial motions in their given order. -/
def composeFamily (B : ℕ → ℝ × E → E) : ℕ → ℝ × E → E
  | 0, p => p.2
  | n + 1, p => B n (p.1, composeFamily B n p)

theorem contDiff_composeFamily {B : ℕ → ℝ × E → E}
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (n : ℕ) :
    ContDiff ℝ ∞ (composeFamily B n) := by
  induction n with
  | zero => exact contDiff_snd
  | succ n ih => exact (hB n).comp (contDiff_fst.prodMk ih)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem composeFamily_zero {B : ℕ → ℝ × E → E}
    (hB : ∀ i x, B i (0, x) = x) (n : ℕ) (x : E) :
    composeFamily B n (0, x) = x := by
  induction n with
  | zero => rfl
  | succ n ih => exact (hB n _).trans ih

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem composeFamily_fixed {B : ℕ → ℝ × E → E} {C : Set E}
    (hB : ∀ i t x, x ∉ C → B i (t, x) = x) (n : ℕ) (t : ℝ)
    {x : E} (hx : x ∉ C) : composeFamily B n (t, x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change B n (t, composeFamily B n (t, x)) = x
    rw [ih]
    exact hB n t x hx

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem composeFamily_preserves {F : Type*} {B : ℕ → ℝ × E → E} {f : E → F}
    (hB : ∀ i t x, f (B i (t, x)) = f x) (n : ℕ) (t : ℝ) (x : E) :
    f (composeFamily B n (t, x)) = f x := by
  induction n with
  | zero => rfl
  | succ n ih => exact (hB n t _).trans ih

/-- Actual inverse maps are retained by finite composition, at every real control time. -/
theorem exists_diffeomorph_composeFamily {B : ℕ → ℝ × E → E}
    (hB : ∀ i t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ∀ x, d x = B i (t, x)) (n : ℕ) (t : ℝ) :
    ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ∀ x, d x = composeFamily B n (t, x) := by
  induction n with
  | zero => exact ⟨Diffeomorph.refl 𝓘(ℝ, E) E ∞, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    obtain ⟨e, he⟩ := hB n t
    refine ⟨d.trans e, ?_⟩
    intro x
    change e (d x) = B n (t, composeFamily B n (t, x))
    rw [he, hd]

end Wikipedia.SmoothSixDPoincare.SmallPerturbation
