/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.BrownianSmallBall

/-!
# A checked Gaussian-skeleton strip lower bound

The Brownian comparison in HLOZ Lemma A.8 uses the fact that a process killed
at the boundary of an interval loses only exponentially much mass in elapsed
Brownian time divided by the square of the interval width.  Mathlib does not
currently contain the reflection principle or the Dirichlet heat kernel, so
the continuous-time exit formula is not available as a library lemma.

This file proves the corresponding finite Gaussian-skeleton statement from
first principles.  It is the elementary block estimate used in a
discretization proof: at the end of every block we ask the process to return
to the middle half of the strip.  A transition between two points in that
middle interval has a uniform positive density, and Tonelli iteration gives
the exponential lower bound without any independence or asymptotic
placeholder.

For a fixed HLOZ level `l`, one step has variance `4*l^2`.  If the middle
interval has length `r`, the checked retention factor is

`q(l,r) = r / (sqrt (2*pi) * 2*l) * exp (-r^2/(8*l^2))`.

The theorem `hlozDiscreteStripMass_lower` says that the killed `N`-step mass
is at least `q(l,r)^N`.  The final theorem rewrites this as an exponential,
which is the exact discrete-block analogue of `c * exp (-C*u/r^2)` when the
block duration is chosen comparable to `r^2`.
-/

open scoped ENNReal NNReal

namespace Erdos1165.BrownianStrip

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BrownianSmallBall

/-- The middle half of a strip of half-width `r`: its length is exactly `r`. -/
def centralInterval (r : ℝ) : Set ℝ := Icc (-(r / 2)) (r / 2)

lemma measurableSet_centralInterval (r : ℝ) :
    MeasurableSet (centralInterval r) :=
  measurableSet_Icc

/-- The pointwise floor for an HLOZ Gaussian transition between two points
of `centralInterval r`. -/
def hlozCentralKernelFloor (l : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((√(2 * Real.pi) * (2 * l : ℝ))⁻¹ *
      Real.exp (-(r ^ 2) / (8 * (l : ℝ) ^ 2)))

/-- The resulting one-block retention factor. -/
def hlozCentralRetention (l : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal r * hlozCentralKernelFloor l r

lemma abs_sub_le_of_mem_centralInterval {r x y : ℝ}
    (hx : x ∈ centralInterval r) (hy : y ∈ centralInterval r) :
    |x - y| ≤ r := by
  rw [centralInterval, mem_Icc] at hx hy
  rw [abs_le]
  constructor <;> linarith

/-- Every transition inside the central interval dominates the same explicit
positive floor. -/
lemma hlozCentralKernelFloor_le {l : ℕ} (hl : 0 < l) {r x y : ℝ}
    (hr : 0 ≤ r) (hx : x ∈ centralInterval r) (hy : y ∈ centralInterval r) :
    hlozCentralKernelFloor l r ≤ ENNReal.ofReal (hlozKernel l x y) := by
  unfold hlozCentralKernelFloor
  exact ENNReal.ofReal_le_ofReal
    (hlozKernel_lower_of_abs_sub_le hl hr
      (abs_sub_le_of_mem_centralInterval hx hy))

/-- The killed Gaussian skeleton mass after `N` equal HLOZ Brownian blocks,
started at `x`.  At every observation time it is confined to the middle half
of the ambient strip. -/
def hlozDiscreteStripMass (l : ℕ) (r : ℝ) : ℕ → ℝ → ℝ≥0∞
  | 0, _ => 1
  | N + 1, x =>
      ∫⁻ y in centralInterval r,
        ENNReal.ofReal (hlozKernel l x y) * hlozDiscreteStripMass l r N y

@[simp] lemma hlozDiscreteStripMass_zero (l : ℕ) (r x : ℝ) :
    hlozDiscreteStripMass l r 0 x = 1 := rfl

@[simp] lemma hlozDiscreteStripMass_succ (l N : ℕ) (r x : ℝ) :
    hlozDiscreteStripMass l r (N + 1) x =
      ∫⁻ y in centralInterval r,
        ENNReal.ofReal (hlozKernel l x y) * hlozDiscreteStripMass l r N y := rfl

/-- The recursive density integral is exactly integration against the
Gaussian transition probability.  Thus `hlozDiscreteStripMass` is the
killed Markov-chain mass, not merely a formal analytic recursion. -/
lemma hlozDiscreteStripMass_succ_eq_gaussianReal {l : ℕ} (hl : 0 < l)
    (N : ℕ) (r x : ℝ) :
    hlozDiscreteStripMass l r (N + 1) x =
      ∫⁻ y in centralInterval r, hlozDiscreteStripMass l r N y
        ∂gaussianReal x (hlozVariance l) := by
  rw [hlozDiscreteStripMass_succ,
    gaussianReal_of_var_ne_zero x (hlozVariance_ne_zero hl)]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable
    volume (measurable_gaussianPDF x (hlozVariance l))
    (hlozDiscreteStripMass l r N) (measurableSet_centralInterval r)
    (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)]
  rfl

/-- The central interval has the expected Lebesgue mass. -/
lemma volume_centralInterval (r : ℝ) :
    volume (centralInterval r) = ENNReal.ofReal r := by
  rw [centralInterval, Real.volume_Icc]
  congr 1
  ring

/-- **Finite Gaussian-skeleton strip survival.**

Starting in the central interval, each killed Gaussian block retains at
least `q(l,r)` times the preceding mass.  Iterating gives the exact power
lower bound. -/
theorem hlozDiscreteStripMass_lower {l : ℕ} (hl : 0 < l) {r : ℝ}
    (hr : 0 ≤ r) (N : ℕ) {x : ℝ} (hx : x ∈ centralInterval r) :
    (hlozCentralRetention l r) ^ N ≤ hlozDiscreteStripMass l r N x := by
  induction N generalizing x with
  | zero => simp
  | succ N ih =>
      rw [hlozDiscreteStripMass_succ, pow_succ]
      calc
        hlozCentralRetention l r ^ N * hlozCentralRetention l r =
            ∫⁻ _y in centralInterval r,
              hlozCentralKernelFloor l r * hlozCentralRetention l r ^ N := by
          rw [setLIntegral_const, volume_centralInterval]
          simp only [hlozCentralRetention]
          ac_rfl
        _ ≤ ∫⁻ y in centralInterval r,
              ENNReal.ofReal (hlozKernel l x y) *
                hlozDiscreteStripMass l r N y := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem (measurableSet_centralInterval r)] with y hy
          exact mul_le_mul
            (hlozCentralKernelFloor_le hl hr hx hy)
            (ih hy) bot_le bot_le

lemma hlozCentralRetention_pos {l : ℕ} (hl : 0 < l) {r : ℝ} (hr : 0 < r) :
    0 < hlozCentralRetention l r := by
  unfold hlozCentralRetention hlozCentralKernelFloor
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hr).ne'
    (ENNReal.ofReal_pos.mpr (mul_pos (by positivity) (Real.exp_pos _))).ne'

lemma hlozCentralRetention_ne_top (l : ℕ) (r : ℝ) :
    hlozCentralRetention l r ≠ ∞ := by
  unfold hlozCentralRetention hlozCentralKernelFloor
  exact ENNReal.mul_ne_top (ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top

/-- Exponential form of the skeleton estimate.  Since the retention factor
is positive and finite, its `ENNReal` logarithm exponentiates back exactly. -/
theorem hlozDiscreteStripMass_exp_lower {l : ℕ} (hl : 0 < l) {r : ℝ}
    (hr : 0 < r) (N : ℕ) {x : ℝ} (hx : x ∈ centralInterval r) :
    ENNReal.ofReal
        (Real.exp ((N : ℝ) * Real.log (hlozCentralRetention l r).toReal)) ≤
      hlozDiscreteStripMass l r N x := by
  have hpos := hlozCentralRetention_pos hl hr
  have htop := hlozCentralRetention_ne_top l r
  have hreal : 0 < (hlozCentralRetention l r).toReal :=
    ENNReal.toReal_pos hpos.ne' htop
  rw [Real.exp_nat_mul, Real.exp_log hreal]
  rw [ENNReal.ofReal_pow hreal.le, ENNReal.ofReal_toReal htop]
  exact hlozDiscreteStripMass_lower hl hr.le N hx

/-! ## Diffusive blocks: an explicit `exp (-C u / r^2)` corollary -/

/-- The retention factor when the central interval length is `2*l`, hence
its square equals the Brownian duration `4*l^2` of one HLOZ block. -/
def standardBlockRetentionReal : ℝ :=
  (√(2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ))

/-- The positive cost of one diffusive block. -/
def standardBlockCost : ℝ := -Real.log standardBlockRetentionReal

lemma standardBlockRetentionReal_pos : 0 < standardBlockRetentionReal := by
  unfold standardBlockRetentionReal
  exact mul_pos (by positivity) (Real.exp_pos _)

lemma standardBlockRetentionReal_lt_one : standardBlockRetentionReal < 1 := by
  have hsqrt : (1 : ℝ) < √(2 * Real.pi) := by
    rw [Real.lt_sqrt zero_le_one]
    nlinarith [Real.two_le_pi]
  have hinv : (√(2 * Real.pi))⁻¹ < (1 : ℝ) :=
    inv_lt_one_of_one_lt₀ hsqrt
  have hmul : standardBlockRetentionReal < Real.exp (-(1 / 2 : ℝ)) := by
    unfold standardBlockRetentionReal
    nlinarith [mul_lt_mul_of_pos_right hinv (Real.exp_pos (-(1 / 2 : ℝ)))]
  exact hmul.trans (Real.exp_lt_one_iff.mpr (by norm_num))

lemma standardBlockCost_pos : 0 < standardBlockCost := by
  unfold standardBlockCost
  exact neg_pos.mpr
    (Real.log_neg standardBlockRetentionReal_pos standardBlockRetentionReal_lt_one)

lemma hlozCentralRetention_two_mul (l : ℕ) (hl : 0 < l) :
    hlozCentralRetention l (2 * (l : ℝ)) =
      ENNReal.ofReal standardBlockRetentionReal := by
  unfold hlozCentralRetention hlozCentralKernelFloor standardBlockRetentionReal
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * l)]
  congr 1
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hexponent :
      -((2 * (l : ℝ)) ^ 2) / (8 * (l : ℝ) ^ 2) = -(1 / 2 : ℝ) := by
    field_simp
    ring
  rw [hexponent]
  field_simp

/-- For diffusive blocks (duration `4*l^2`, strip scale `2*l`), the checked
Gaussian-skeleton survival bound is `exp (-C*N)` with one universal explicit
positive constant `C`. -/
theorem hlozDiscreteStripMass_diffusive_lower {l : ℕ} (hl : 0 < l) (N : ℕ) :
    ENNReal.ofReal (Real.exp (-standardBlockCost * (N : ℝ))) ≤
      hlozDiscreteStripMass l (2 * (l : ℝ)) N 0 := by
  have hr : (0 : ℝ) < 2 * l := by positivity
  have hx : (0 : ℝ) ∈ centralInterval (2 * (l : ℝ)) := by
    rw [centralInterval, mem_Icc]
    constructor <;> linarith
  have h := hlozDiscreteStripMass_exp_lower hl hr N hx
  rw [hlozCentralRetention_two_mul l hl,
    ENNReal.toReal_ofReal standardBlockRetentionReal_pos.le] at h
  convert h using 1
  congr 2
  unfold standardBlockCost
  ring

/-- The same estimate displayed with elapsed Brownian time divided by the
square of the strip scale.  Here `u = N * 4*l^2` and `r = 2*l`, so the ratio
is exactly `N`. -/
theorem hlozDiscreteStripMass_time_div_sq_lower {l : ℕ} (hl : 0 < l) (N : ℕ) :
    ENNReal.ofReal
        (Real.exp
          (-standardBlockCost *
            (((N : ℝ) * (4 * (l : ℝ) ^ 2)) / (2 * (l : ℝ)) ^ 2))) ≤
      hlozDiscreteStripMass l (2 * (l : ℝ)) N 0 := by
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  convert hlozDiscreteStripMass_diffusive_lower hl N using 1
  congr 3
  field_simp
  ring

end

end Erdos1165.BrownianStrip
