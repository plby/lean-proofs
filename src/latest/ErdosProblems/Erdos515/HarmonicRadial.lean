import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Harmonic deficit estimates for Erdős Problem 515

The Lewis--Rossi--Weitsman argument uses Hall's radial lemma for an arbitrary bounded
subharmonic function.  On a zero-free or analytically normalized piece, the relevant deficit is
the positive harmonic function `1 - re g`.  This file records the Mathlib-facing estimates for
that harmonic part.  These estimates do not by themselves replace Hall's lemma: normalizing `f`
rather than `log |f|` only gives geometric growth of `|f|`, which is too slow for all exponents.

The circle identities below are also the input to the standard Hardy--Littlewood radial maximal
estimate.  In particular, the pointwise quadratic estimate says that the `H²` mass of `1 - g` on
every concentric circle is controlled by its (small) central harmonic deficit.
-/

open Complex InnerProductSpace Metric Real Set

namespace Erdos515

/-- The positive harmonic deficit of a holomorphic map into the unit disk. -/
def harmonicDeficit (g : ℂ → ℂ) (z : ℂ) : ℝ :=
  1 - (g z).re

lemma harmonicOnNhd_harmonicDeficit {g : ℂ → ℂ} {s : Set ℂ}
    (hg : AnalyticOnNhd ℂ g s) : HarmonicOnNhd (harmonicDeficit g) s := by
  refine (harmonicOnNhd_const (c := (1 : ℝ))).sub ?_
  intro z hz
  exact (hg z hz).harmonicAt_re

lemma harmonicDeficit_pos_of_norm_lt_one {g : ℂ → ℂ} {z : ℂ}
    (hg : ‖g z‖ < 1) : 0 < harmonicDeficit g z := by
  dsimp [harmonicDeficit]
  have hre : (g z).re < 1 := (Complex.re_le_norm _).trans_lt hg
  linarith

lemma harmonicDeficit_nonneg_of_norm_le_one {g : ℂ → ℂ} {z : ℂ}
    (hg : ‖g z‖ ≤ 1) : 0 ≤ harmonicDeficit g z := by
  dsimp [harmonicDeficit]
  have hre : (g z).re ≤ 1 := (Complex.re_le_norm _).trans hg
  linarith

/-- The harmonic deficit has constant circle average, equal to its value at the center. -/
lemma circleAverage_harmonicDeficit {g : ℂ → ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hR1 : R < 1) (hg : AnalyticOnNhd ℂ g (ball 0 1)) :
    circleAverage (harmonicDeficit g) 0 R = harmonicDeficit g 0 := by
  apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
  simpa [abs_of_nonneg hR] using
    (harmonicOnNhd_harmonicDeficit hg).mono (closedBall_subset_ball hR1)

/-- For a point in the closed unit disk, the square of its deficit from `1` is bounded by twice
its harmonic real-part deficit. -/
lemma norm_one_sub_sq_le_two_mul_deficit {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖1 - w‖ ^ 2 ≤ 2 * (1 - w.re) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  simp only [map_one, one_mul, conj_re]
  have hsq : Complex.normSq w ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  linarith

lemma norm_one_sub_sq_le_two_mul_harmonicDeficit {g : ℂ → ℂ} {z : ℂ}
    (hg : ‖g z‖ ≤ 1) : ‖1 - g z‖ ^ 2 ≤ 2 * harmonicDeficit g z := by
  simpa [harmonicDeficit] using norm_one_sub_sq_le_two_mul_deficit hg

/-- Uniform `H²` circle control for `1 - g`.  This is the quantitative input for the harmonic
piece of a Hall-type decomposition. -/
lemma circleAverage_norm_one_sub_sq_le {g : ℂ → ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hR1 : R < 1) (hg : AnalyticOnNhd ℂ g (ball 0 1))
    (hunit : ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ 1) :
    circleAverage (fun z ↦ ‖1 - g z‖ ^ 2) 0 R ≤ 2 * harmonicDeficit g 0 := by
  have hclosed : closedBall (0 : ℂ) R ⊆ ball 0 1 := closedBall_subset_ball hR1
  have hcontg : ContinuousOn g (closedBall (0 : ℂ) R) :=
    hg.continuousOn.mono hclosed
  have hint_sq : CircleIntegrable (fun z ↦ ‖1 - g z‖ ^ 2) 0 R := by
    apply ContinuousOn.circleIntegrable'
    exact ((continuousOn_const.sub hcontg).norm.pow 2).mono
      (sphere_subset_closedBall.trans (by simpa [abs_of_nonneg hR]))
  have hint_deficit : CircleIntegrable (harmonicDeficit g) 0 R := by
    apply ContinuousOn.circleIntegrable'
    exact (continuousOn_const.sub (Complex.continuous_re.comp_continuousOn hcontg)).mono
      (sphere_subset_closedBall.trans (by simpa [abs_of_nonneg hR]))
  have hint_two_deficit : CircleIntegrable (fun z ↦ 2 * harmonicDeficit g z) 0 R := by
    apply ContinuousOn.circleIntegrable'
    exact (continuousOn_const.mul
      (continuousOn_const.sub (Complex.continuous_re.comp_continuousOn hcontg))).mono
      (sphere_subset_closedBall.trans (by simpa [abs_of_nonneg hR]))
  calc
    circleAverage (fun z ↦ ‖1 - g z‖ ^ 2) 0 R
        ≤ circleAverage (fun z ↦ 2 * harmonicDeficit g z) 0 R := by
          apply circleAverage_mono hint_sq
            hint_two_deficit
          intro z hz
          apply norm_one_sub_sq_le_two_mul_harmonicDeficit
          apply hunit z
          apply hclosed
          simpa [abs_of_nonneg hR] using sphere_subset_closedBall hz
    _ = 2 * circleAverage (harmonicDeficit g) 0 R := by
      simpa [smul_eq_mul] using
        (circleAverage_fun_smul (a := (2 : ℝ)) (f := harmonicDeficit g) (c := 0) (R := R))
    _ = 2 * harmonicDeficit g 0 := by rw [circleAverage_harmonicDeficit hR hR1 hg]

end Erdos515
