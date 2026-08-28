import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A quadratic upper bound from a second derivative bound

Two applications of the mean value inequality turn an upper bound on the
actual second derivative into a quantitative upper bound on the function.
-/

open Set

namespace NoExoticSixSphere.SecondDerivativeUpperBound

theorem derivative_le {g g' : ℝ → ℝ} {A T : ℝ} (hT : 0 ≤ T)
    (hg : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt g (g' t) t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, g' t ≤ -A)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : g t ≤ g 0 - A * t := by
  have hc : ContinuousOn g (Icc (0 : ℝ) T) :=
    fun s hs ↦ (hg s hs).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ g (interior (Icc (0 : ℝ) T)) :=
    fun s hs ↦ (hg s (interior_subset hs)).differentiableAt.differentiableWithinAt
  have hb : ∀ s ∈ interior (Icc (0 : ℝ) T), deriv g s ≤ -A := by
    intro s hs
    rw [(hg s (interior_subset hs)).deriv]
    exact hbound s (interior_subset hs)
  have hh := (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 ⟨le_rfl, hT⟩ t ht ht.1
  simp only [sub_zero] at hh
  linarith

theorem quadratic_secant_upper {f f' f'' : ℝ → ℝ} {A T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt f' (f'' t) t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, f'' t ≤ -A)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T) (hst : s ≤ t) :
    f t ≤ f s + f' 0 * (t - s) - (A / 2) * (t ^ 2 - s ^ 2) := by
  have hfirst (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : f' t ≤ f' 0 - A * t :=
    derivative_le hT hf' hbound ht
  let g : ℝ → ℝ := fun t ↦ f t - f' 0 * t + (A / 2) * t ^ 2
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt g (f' t - f' 0 + A * t) t := by
    convert! ((hf t ht).sub ((hasDerivAt_id t).const_mul (f' 0))).add
      (((hasDerivAt_id t).pow 2).const_mul (A / 2)) using 1
    simp only [id_eq]
    ring
  have hc : ContinuousOn g (Icc (0 : ℝ) T) :=
    fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ g (interior (Icc (0 : ℝ) T)) :=
    fun t ht ↦ (hg t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hnonpos : ∀ t ∈ interior (Icc (0 : ℝ) T), deriv g t ≤ 0 := by
    intro t ht
    rw [(hg t (interior_subset ht)).deriv]
    linarith [hfirst t (interior_subset ht)]
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) T) hc hd hnonpos
  have hh := hanti hs ht hst
  dsimp only [g] at hh
  nlinarith

theorem quadratic_upper {f f' f'' : ℝ → ℝ} {A T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt f' (f'' t) t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, f'' t ≤ -A) :
    f T ≤ f 0 + f' 0 * T - (A / 2) * T ^ 2 := by
  simpa only [sub_zero, zero_pow (by decide : 2 ≠ 0)] using
    quadratic_secant_upper hT hf hf' hbound ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT

theorem strictAntiOn_of_negative_second {f f' f'' : ℝ → ℝ} {A T : ℝ}
    (hT : 0 ≤ T) (hA : 0 < A)
    (hf : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt f' (f'' t) t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, f'' t ≤ -A) (hzero : f' 0 = 0) :
    StrictAntiOn f (Icc (0 : ℝ) T) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) T)
    (fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt)
  intro t ht
  have hti : t ∈ Ioo (0 : ℝ) T := by simpa only [interior_Icc] using ht
  have htc : t ∈ Icc (0 : ℝ) T := ⟨hti.1.le, hti.2.le⟩
  rw [(hf t htc).deriv]
  have hh := derivative_le hT hf' hbound htc
  rw [hzero] at hh
  have hn : -A * t < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hA) hti.1
  linarith

end NoExoticSixSphere.SecondDerivativeUpperBound
