module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Measure.Real
import ErdosProblems.Erdos515.External.Ray.Analytic.Analytic
import ErdosProblems.Erdos515.External.Ray.Analytic.Log
import ErdosProblems.Erdos515.External.Ray.Koebe.Gronwall

/-!
## Bieberbach's coefficient inequality for univalent functions.

If `f : ball 0 1 → ℂ` is analytic and injective with `f 0 = 0, f' 0 = 1`, then `‖f'' 0‖ ≤ 4`.

The proof follows Wikipedia: https://en.wikipedia.org/wiki/Koebe_quarter_theorem. We construct

  `g w = sqrt (f (w⁻¹ ^ 2))⁻¹`

which is analytic and injective for `1 < ‖w‖`, then applying the Grönwall area theorem.  Our version
of the Grönwall area theorem is expressed in terms of `h` satisfying

  `g w = w * h w⁻¹`
  `h z = z * g z⁻¹ = z / sqrt (f (z ^ 2))`

We construct `sqrt (f (z ^ 2))` via analytic continuation, starting from a small radius seed. This
works because `f z / z ≠ 0` and is analytic throughout the ball.
-/

open Classical
open Complex (arg)
open Metric (ball closedBall isOpen_ball sphere)
open Set
open Filter (atTop Tendsto)
open MeasureTheory (volume)
open scoped ContDiff Topology NNReal Real
noncomputable section

variable {f : ℂ → ℂ} {z : ℂ}

structure Bier (f : ℂ → ℂ) : Prop where
  fa : AnalyticOnNhd ℂ f (ball 0 1)
  inj : InjOn f (ball 0 1)
  f0 : f 0 = 0
  d0 : deriv f 0 = 1

namespace Bier

private def m0 : 0 ∈ ball (0 : ℂ) 1 := by simp

def f_eq_zero_iff (b : Bier f) (m : z ∈ ball 0 1) : f z = 0 ↔ z = 0 := by
  simpa only [b.f0] using b.inj.eq_iff m (y := 0) (by simp)

/-- Pull a factor of `z` out of `f` -/
def f' (_ : Bier f) : ℂ → ℂ := dslope f 0
lemma analytic_f' (b : Bier f) : AnalyticOnNhd ℂ b.f' (ball 0 1) := fun z m ↦ (b.fa z m).dslope
lemma f'_ne_zero (b : Bier f) (m : z ∈ ball 0 1) : b.f' z ≠ 0 := by
  by_cases z0 : z = 0
  · simp [f', z0, b.d0]
  · simp [f', dslope_of_ne _ z0, slope, z0, b.f0, b.f_eq_zero_iff m]
lemma f_eq_z_mul_f' (b : Bier f) : f z = z * b.f' z := by
  by_cases z0 : z = 0
  · simp only [z0, b.f0, zero_mul]
  · simp [f', b.f0, dslope_of_ne _ z0, slope, z0]
lemma f'0 (b : Bier f) : b.f' 0 = 1 := by simp [f', b.d0]
lemma df'0 (b : Bier f) : deriv b.f' 0 = deriv (deriv f) 0 / 2 := by
  obtain ⟨p,fp⟩ := b.fa _ m0
  simp [f', fp.has_fpower_series_dslope_fslope.deriv, FormalMultilinearSeries.fslope,
    fp.coeff_eq_iteratedDeriv_div, iteratedDeriv_eq_iterate]

/-- The square root of `f'`: `sf z = sqrt (f' z)` -/
def exists_sf (b : Bier f) :=
  b.analytic_f'.exists_root (fun z m ↦ b.f'_ne_zero m) (n := 2) (by norm_num)
def sf (b : Bier f) : ℂ → ℂ := choose b.exists_sf
lemma analytic_sf (b : Bier f) : AnalyticOnNhd ℂ b.sf (ball 0 1) := (choose_spec b.exists_sf).1
lemma sq_sf (b : Bier f) (m : z ∈ ball 0 1) : b.f' z = b.sf z ^ 2 :=
  (choose_spec b.exists_sf).2.2 _ m
@[simp] lemma sf_ne_zero (b : Bier f) (m : z ∈ ball 0 1) : b.sf z ≠ 0 := by
  simpa [b.sq_sf m] using b.f'_ne_zero m
lemma sf0 (b : Bier f) : b.sf 0 = 1 := by simp [sf, (choose_spec b.exists_sf).2.1, b.f'0]
lemma dsf0 (b : Bier f) : deriv b.sf 0 = deriv (deriv f) 0 / 4 := by
  have e : EqOn (fun z ↦ b.sf z ^ 2) (fun z ↦ b.f' z) (ball 0 1) := fun z m ↦ by simp [b.sq_sf m]
  have d1 : deriv (fun z ↦ b.sf z ^ 2) 0 = 2 * b.sf 0 * deriv b.sf 0 := by
    simp only [deriv_fun_pow (b.analytic_sf _ m0).differentiableAt, Nat.cast_ofNat,
      Nat.add_one_sub_one, pow_one]
  have d2 : deriv (fun z ↦ b.sf z ^ 2) 0 = deriv b.f' 0 := by
    rw [(e.eventuallyEq_of_mem (isOpen_ball.mem_nhds m0)).deriv_eq]
  have e := d1.symm.trans d2
  simp only [b.sf0, mul_one, b.df'0] at e
  grind

/-- The inverse of `sf` -/
def fi (b : Bier f) : ℂ → ℂ := fun z ↦ (b.sf z)⁻¹
lemma analytic_fi (b : Bier f) : AnalyticOnNhd ℂ b.fi (ball 0 1) :=
  b.analytic_sf.inv (fun _ m ↦ b.sf_ne_zero m)
lemma fi0 (b : Bier f) : b.fi 0 = 1 := by simp [fi, b.sf0]
lemma dfi0 (b : Bier f) : deriv b.fi 0 = -deriv (deriv f) 0 / 4 := by
  unfold fi
  have m0 : 0 ∈ ball (0 : ℂ) 1 := by simp
  rw [deriv_fun_inv'' (b.analytic_sf _ m0).differentiableAt (b.sf_ne_zero m0), b.dsf0, b.sf0]
  ring
lemma fi_ne_zero (b : Bier f) (m : z ∈ ball 0 1) : b.fi z ≠ 0 := by simpa [fi] using b.sf_ne_zero m

/-- Generic derivative of `f (z ^ 2)` -/
lemma deriv_f_z2 (fa : AnalyticAt ℂ f (z ^ 2)) :
    deriv (fun z ↦ f (z ^ 2)) z = 2 * z * deriv f (z ^ 2) := by
  have d := deriv_comp (h₂ := f) (h := fun z ↦ z ^ 2) z ?_ ?_
  · simp only [Function.comp_def, differentiableAt_fun_id, deriv_fun_pow, Nat.cast_ofNat,
      Nat.add_one_sub_one, pow_one, deriv_id'', mul_one] at d
    simp only [d, mul_comm]
  · exact fa.differentiableAt
  · fun_prop

/-- The function we will feed into Grönwall, such that `g z = z * h z⁻¹` -/
def h (b : Bier f) : ℂ → ℂ := fun z ↦ b.fi (z ^ 2)
lemma h0 (b : Bier f) : b.h 0 = 1 := by simp [h, b.fi0]
lemma h_ne_zero (b : Bier f) (m : z ∈ ball 0 1) : b.h z ≠ 0 := by
  have m2 : z ^ 2 ∈ ball 0 1 := by simpa using m
  simp only [h, ne_eq, b.fi_ne_zero m2, not_false_eq_true]
lemma analytic_h (b : Bier f) : AnalyticOnNhd ℂ b.h (ball 0 1) :=
  b.analytic_fi.comp (analyticOnNhd_id.pow 2) (fun z m ↦ by simpa using m)
lemma dh (b : Bier f) (m : z ∈ ball 0 1) : deriv b.h z = 2 * z * deriv b.fi (z ^ 2) :=
  deriv_f_z2 (b.analytic_fi _ (by simpa using m))
lemma dh0 (b : Bier f) : deriv b.h 0 = 0 := by simp [dh _ m0]
lemma ddh0 (b : Bier f) : deriv (deriv b.h) 0 = -deriv (deriv f) 0 / 2 := by
  have e : EqOn (fun z ↦ deriv b.h z) (fun z ↦ 2 * z * deriv b.fi (z ^ 2)) (ball 0 1) :=
    fun z m ↦ b.dh m
  rw [(e.eventuallyEq_of_mem (isOpen_ball.mem_nhds m0)).deriv_eq]
  rw [deriv_fun_mul (c := fun z ↦ 2 * z) (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop)]
  · simp only [deriv_const', mul_zero, deriv_id'', mul_one, zero_add, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, b.dfi0, zero_mul, add_zero]
    ring
  · apply AnalyticAt.differentiableAt
    exact (b.analytic_fi 0 (by simp)).deriv.comp_of_eq (analyticAt_id.pow 2) (by simp)
lemma h_inj (b : Bier f) : InjOn (fun z ↦ z * b.h z⁻¹) (norm_Ioi 1) := by
  intro z zm w wm e
  have n : ∀ {x}, x ∈ norm_Ioi 1 → (x ^ 2)⁻¹ ∈ ball 0 1 := by
    intro x m
    simp only [norm_Ioi, mem_ofPred_eq, Metric.mem_ball, dist_zero_right, norm_inv, norm_pow] at m ⊢
    exact inv_lt_one_of_one_lt₀ (by exact one_lt_pow₀ (by bound) (by norm_num))
  have e2 : (z * b.h z⁻¹) ^ 2 = (w * b.h w⁻¹) ^ 2 := by simp only at e; simp [e]
  rw [← inv_inj] at e2
  simp only [h, fi, inv_pow, mul_pow, ← b.sq_sf (n zm), mul_inv, inv_inv,
    ← b.sq_sf (n wm), ← f_eq_z_mul_f', b.inj.eq_iff (n zm) (n wm), inv_inj,
    sq_eq_sq_iff_eq_or_eq_neg] at e2
  rcases e2 with e2 | e2
  · exact e2
  · simp only [e2, h, inv_neg, even_two, Even.neg_pow, inv_pow, mul_eq_mul_right_iff,
      b.fi_ne_zero (n wm), or_false] at e
    exact e2.trans e

end Bier

public theorem bieberbach (fa : AnalyticOnNhd ℂ f (ball 0 1)) (inj : InjOn f (ball 0 1))
    (f0 : f 0 = 0) (d0 : deriv f 0 = 1) : ‖deriv (deriv f) 0‖ ≤ 4 := by
  have b : Bier f := ⟨fa, inj, f0, d0⟩
  have le := le_trans MeasureTheory.measureReal_nonneg
    (gronwall_volume_le_two b.analytic_h b.h0 b.h_inj)
  simp only [Complex.norm_div, Complex.norm_ofNat, div_pow, sub_nonneg] at le
  nth_rw 2 [← mul_one π] at le
  rw [mul_le_mul_iff_right₀ Real.pi_pos] at le
  simp only [iteratedDeriv_eq_iterate, Function.iterate_succ_apply, Function.iterate_zero_apply,
    b.ddh0, Complex.norm_div, Complex.norm_ofNat, norm_neg] at le
  rw [div_le_one (by norm_num), sq_le_sq₀ (by bound) (by norm_num), div_le_iff₀ (by norm_num)] at le
  linarith
