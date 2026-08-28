import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCauchyHolomorphic

/-!
# Coordinate operations for the two-variable antiholomorphic solver

This file records the actual product and subtraction rules and the integral
in the first coordinate.  The latter is the same proved Cauchy–Green operator
after exchanging the two coordinates.
-/

noncomputable section

open Complex Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open HolomorphicCousin

theorem dbarFirst_add {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    dbarFirst (fun x => f x + g x) q = dbarFirst f q + dbarFirst g q := by
  have hfg : DifferentiableAt ℝ (fun x => f x + g x) q := hf.add hg
  rw [dbarFirst_eq_linear hfg, fderiv_fun_add hf hg, map_add,
    ← dbarFirst_eq_linear hf, ← dbarFirst_eq_linear hg]

theorem dbarSecond_add {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    dbarSecond (fun x => f x + g x) q = dbarSecond f q + dbarSecond g q := by
  have hfg : DifferentiableAt ℝ (fun x => f x + g x) q := hf.add hg
  rw [dbarSecond_eq_linear hfg, fderiv_fun_add hf hg, map_add,
    ← dbarSecond_eq_linear hf, ← dbarSecond_eq_linear hg]

theorem dbarFirst_sub {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    dbarFirst (fun x => f x - g x) q = dbarFirst f q - dbarFirst g q := by
  have hfg : DifferentiableAt ℝ (fun x => f x - g x) q := hf.sub hg
  rw [dbarFirst_eq_linear hfg, fderiv_fun_sub hf hg, map_sub,
    ← dbarFirst_eq_linear hf, ← dbarFirst_eq_linear hg]

theorem dbarSecond_sub {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    dbarSecond (fun x => f x - g x) q = dbarSecond f q - dbarSecond g q := by
  have hfg : DifferentiableAt ℝ (fun x => f x - g x) q := hf.sub hg
  rw [dbarSecond_eq_linear hfg, fderiv_fun_sub hf hg, map_sub,
    ← dbarSecond_eq_linear hf, ← dbarSecond_eq_linear hg]

theorem dbarFirst_mul {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    dbarFirst (fun x => f x * g x) q =
      f q * dbarFirst g q + g q * dbarFirst f q := by
  have hfg : DifferentiableAt ℝ (fun x => f x * g x) q := hf.mul hg
  rw [dbarFirst_eq_linear hfg, fderiv_fun_mul hf hg, map_add,
    dbarFirstLinear_complex_smul, dbarFirstLinear_complex_smul,
    ← dbarFirst_eq_linear hf, ← dbarFirst_eq_linear hg]

theorem dbarSecond_mul {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    dbarSecond (fun x => f x * g x) q =
      f q * dbarSecond g q + g q * dbarSecond f q := by
  have hfg : DifferentiableAt ℝ (fun x => f x * g x) q := hf.mul hg
  rw [dbarSecond_eq_linear hfg, fderiv_fun_mul hf hg, map_add,
    dbarSecondLinear_complex_smul, dbarSecondLinear_complex_smul,
    ← dbarSecond_eq_linear hf, ← dbarSecond_eq_linear hg]

@[simp] theorem dbarFirst_snd (f : ℂ → ℂ) (q : ℂ × ℂ) :
    dbarFirst (fun x => f x.2) q = 0 := by
  change dbar (fun _ => f q.2) q.1 = 0
  exact dbar_const _ _

@[simp] theorem dbarSecond_fst (f : ℂ → ℂ) (q : ℂ × ℂ) :
    dbarSecond (fun x => f x.1) q = 0 := by
  change dbar (fun _ => f q.1) q.2 = 0
  exact dbar_const _ _

@[simp] theorem dbarFirst_swap (f : ℂ × ℂ → ℂ) (q : ℂ × ℂ) :
    dbarFirst (fun x => f x.swap) q = dbarSecond f q.swap := rfl

@[simp] theorem dbarSecond_swap (f : ℂ × ℂ → ℂ) (q : ℂ × ℂ) :
    dbarSecond (fun x => f x.swap) q = dbarFirst f q.swap := rfl

/-- Cauchy–Green in the first coordinate. -/
def cauchyFirst (f : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  cauchyGreen (fun z => f (z, q.2)) q.1

theorem cauchyFirst_eq_swap (f : ℂ × ℂ → ℂ) (q : ℂ × ℂ) :
    cauchyFirst f q = cauchySecond (fun x => f x.swap) q.swap := rfl

theorem contDiff_cauchyFirst {n : ℕ∞} {f : ℂ × ℂ → ℂ} {k : Set ℂ}
    (hf : ContDiff ℝ n f) (hk : IsCompact k)
    (hfk : ∀ z w, z ∉ k → f (z, w) = 0) :
    ContDiff ℝ n (cauchyFirst f) := by
  have hswap : ContDiff ℝ n (Prod.swap : ℂ × ℂ → ℂ × ℂ) :=
    contDiff_snd.prodMk contDiff_fst
  exact (contDiff_cauchySecond (hf.comp hswap) hk
    (fun z w hw => hfk w z hw)).comp hswap

theorem dbarFirst_cauchyFirst {f : ℂ × ℂ → ℂ} {k : Set ℂ}
    (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ z w, z ∉ k → f (z, w) = 0) (q : ℂ × ℂ) :
    dbarFirst (cauchyFirst f) q = f q := by
  exact dbar_cauchyGreen (hf.comp (contDiff_prodMk_left q.2))
    (HasCompactSupport.intro hk (fun z hz => hfk z q.2 hz)) q.1

theorem dbarSecond_cauchyFirst {f : ℂ × ℂ → ℂ} {k : Set ℂ}
    (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ z w, z ∉ k → f (z, w) = 0) (q : ℂ × ℂ) :
    dbarSecond (cauchyFirst f) q = cauchyFirst (dbarSecond f) q := by
  have hswap : ContDiff ℝ 1 (Prod.swap : ℂ × ℂ → ℂ × ℂ) :=
    contDiff_snd.prodMk contDiff_fst
  exact dbarFirst_cauchySecond (hf.comp hswap) hk (fun z w hw => hfk w z hw) q.swap

/-- Vanishing of the second coordinate derivative on a strip survives the
integral in the first coordinate. -/
theorem dbarSecond_cauchyFirst_eq_zero {f : ℂ × ℂ → ℂ} {k U : Set ℂ}
    (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ z w, z ∉ k → f (z, w) = 0)
    (hd : ∀ z w, w ∈ U → dbarSecond f (z, w) = 0)
    (z : ℂ) {w : ℂ} (hw : w ∈ U) :
    dbarSecond (cauchyFirst f) (z, w) = 0 := by
  rw [dbarSecond_cauchyFirst hf hk hfk]
  simp only [cauchyFirst, cauchyGreen, hd _ _ hw, mul_zero,
    MeasureTheory.integral_zero]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
