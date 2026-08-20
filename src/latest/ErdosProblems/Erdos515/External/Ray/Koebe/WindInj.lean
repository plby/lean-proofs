module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import ErdosProblems.Erdos515.External.Ray.Koebe.Snap
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.CircleIntegral
import ErdosProblems.Erdos515.External.Ray.Misc.Bound
import ErdosProblems.Erdos515.External.Ray.Misc.Bounds
import ErdosProblems.Erdos515.External.Ray.Misc.Circle
import ErdosProblems.Erdos515.External.Ray.Misc.Complex

/-!
## Curves around the origin are star-shaped, from derivatives

If a function is analytic on a circle, is close to the identity, and winds monotonically around the
origin, it sweeps out a star-shaped curve.
-/

open Complex (arg I)
open Metric (sphere)
open Set
open scoped Real Topology
noncomputable section

/-!
### Star-shaped regions
-/

variable {f : ℂ → ℂ} {r a b t : ℝ} {z : ℂ}

/-- `f z ≈ z` on `sphere 0 r`, and `f` winds monotonically around the origin -/
public structure WindInj (f : ℂ → ℂ) (r : ℝ) : Prop where
  r0 : 0 < r
  fa : ∀ z, ‖z‖ = r → AnalyticAt ℂ f z
  close : ∀ z, ‖z‖ = r → ‖f z - z‖ ≤ r / 20
  mono : ∀ z, ‖z‖ = r → 0 < (z * (f z)⁻¹ * deriv f z).re

attribute [bound_forward] WindInj.r0

lemma WindInj.f_ne_zero (i : WindInj f r) (m : ‖z‖ = r) : f z ≠ 0 := by
  rw [← norm_pos_iff]
  calc ‖f z‖
    _ = ‖z + (f z - z)‖ := by ring_nf
    _ ≥ ‖z‖ - ‖f z - z‖ := by bound
    _ ≥ r - r / 20 := by bound [i.close z m]
    _ > 0 := by linarith [i.r0]

lemma WindInj.close_cm (i : WindInj f r) (t : ℝ) :
    ‖f (circleMap 0 r t) - circleMap 0 r t‖ ≤ r / 20 :=
  i.close (circleMap 0 r t) (by simp [i.r0.le])

lemma WindInj.mono_cm (i : WindInj f r) (t : ℝ) :
    0 < (circleMap 0 r t * (f (circleMap 0 r t))⁻¹ * deriv f (circleMap 0 r t)).re :=
  i.mono (circleMap 0 r t) (by simp [i.r0.le])

/-- `t ↦ snap (f (cis t))` is injective for close values, via monotonicity of `arg`.
    We use closeness to avoid `arg` wraparound issues. -/
lemma WindInj.inj_near (i : WindInj f r) {a b : ℝ} (ab : a < b) (ba : b ≤ a + 1/2) :
    snap (f (circleMap 0 r a)) ≠ snap (f (circleMap 0 r b)) := by
  generalize hc : f (circleMap 0 r a) = c
  rw [← hc]
  have c0 : c ≠ 0 := hc ▸ i.f_ne_zero (z := circleMap 0 r a) (by simp [i.r0.le])
  have cf0 : ∀ {t}, c⁻¹ * f (circleMap 0 r t) ≠ 0 := by
    intro t
    simpa only [ne_eq, mul_eq_zero, inv_eq_zero, c0, false_or] using
      i.f_ne_zero (z := circleMap 0 r t) (by simp [i.r0.le])
  generalize hg : (fun t : ℝ ↦ arg (c⁻¹ * f (circleMap 0 r (a + t)))) = g
  suffices h : g 0 ≠ g (b-a) by
    simp only [ne_eq, ← hg, add_zero, add_sub_cancel, ← snap_eq_snap_iff cf0 cf0] at h
    rwa [snap_mul (inv_ne_zero c0) (i.f_ne_zero (by simp [i.r0.le])),
      snap_mul (inv_ne_zero c0) (i.f_ne_zero (by simp [i.r0.le])), mul_right_inj] at h
  apply ne_of_lt
  suffices h : StrictMonoOn g (Icc 0 (b - a)) by
    apply h
    · simp only [mem_Icc, le_refl, sub_nonneg, true_and]; bound
    · simp only [mem_Icc, sub_nonneg, le_refl, and_true]; bound
    · bound
  have dg : ∀ t, t ∈ Icc 0 (b-a) → HasDerivAt g
      ((c⁻¹ * f (circleMap 0 r (a + t)))⁻¹ * (c⁻¹ * (deriv f (circleMap 0 r (a + t)) *
        ((1 : ℝ) • (circleMap 0 r (a + t) * I))))).im t := by
    intro t m; rw [← hg]
    apply HasDerivAt.arg
    · apply HasDerivAt.const_mul
      apply HasDerivAt.comp
      · exact (i.fa _ (by simp [i.r0.le])).differentiableAt.hasDerivAt
      · exact (hasDerivAt_circleMap 0 r (a + t)).scomp t ((hasDerivAt_id _).const_add _)
    · simp only [Complex.mem_slitPlane_iff]
      left
      apply re_mul_inv_pos_of_close
      simp only [← hc]
      have cc : ‖circleMap 0 r (a + t) - circleMap 0 r a‖ ≤ r / 2 := by
        have h := (lipschitzWith_circleMap 0 r).dist_le_mul (a + t) a
        simp only [Complex.dist_eq, Real.coe_nnabs, abs_of_pos i.r0, dist_self_add_left,
          Real.norm_eq_abs, abs_of_nonneg m.1] at h
        nlinarith [m.2, i.r0]
      calc ‖f (circleMap 0 r (a + t)) - f (circleMap 0 r a)‖
        _ = ‖f (circleMap 0 r (a + t)) - circleMap 0 r (a + t) +
              (circleMap 0 r (a + t) - circleMap 0 r a) -
              (f (circleMap 0 r a) - circleMap 0 r a)‖ := by abel_nf
        _ ≤ ‖f (circleMap 0 r (a + t)) - circleMap 0 r (a + t) +
              (circleMap 0 r (a + t) - circleMap 0 r a)‖ +
            ‖f (circleMap 0 r a) - circleMap 0 r a‖ := by bound
        _ ≤ ‖f (circleMap 0 r (a + t)) - circleMap 0 r (a + t)‖ +
            ‖circleMap 0 r (a + t) - circleMap 0 r a‖ +
            ‖f (circleMap 0 r a) - circleMap 0 r a‖ := by bound
        _ ≤ r/20 + r/2 + r/20 := by bound [i.close_cm (a + t), i.close_cm a]
        _ < r - r/20 := by linarith [i.r0]
        _ = ‖circleMap 0 r a‖ - r/20 := by simp [i.r0.le, abs_of_nonneg]
        _ ≤ ‖circleMap 0 r a‖ - ‖f (circleMap 0 r a) - circleMap 0 r a‖ := by bound [i.close_cm a]
        _ ≤ ‖circleMap 0 r a + (f (circleMap 0 r a) - circleMap 0 r a)‖ := by bound
        _ = ‖f (circleMap 0 r a)‖ := by ring_nf
  simp only [one_smul, mul_inv, inv_inv, ← mul_assoc, mul_comm _ c⁻¹, inv_mul_cancel₀ c0,
    one_mul, Complex.mul_I_im] at dg
  simp only [← mul_assoc, mul_comm _ (circleMap 0 r _)] at dg
  apply strictMonoOn_of_deriv_pos
  · apply convex_Icc
  · intro t m; exact (dg t m).continuousAt.continuousWithinAt
  · intro t m; simp only [(dg t (interior_subset m)).deriv, i.mono_cm]

/-- `t ↦ snap (f (cis t))` is injective for close values (symmetric version)` -/
lemma WindInj.inj_near' (i : WindInj f r) {a b : ℝ} (ne : a ≠ b) (ab : |b - a| ≤ 1/2) :
    snap (f (circleMap 0 r a)) ≠ snap (f (circleMap 0 r b)) := by
  by_cases h : a < b
  · rw [abs_of_nonneg (by bound)] at ab
    exact i.inj_near h (by linarith)
  · symm
    simp only [not_lt] at h
    rw [abs_of_nonpos (by bound)] at ab
    exact i.inj_near (ne.symm.lt_of_le h) (by linarith)

/-- `snap (f z)` is close to `z` -/
lemma WindInj.snap_close (i : WindInj f r) (m : ‖z‖ = r) : ‖snap (f z) - z / r‖ ≤ 1 / 9 := by
  have a0 : 0 < ‖f z‖ := by simp [i.f_ne_zero m]
  have aa0 : 0 < ‖(‖f z‖ : ℂ)‖ := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm, a0]
  rw [← mul_le_mul_iff_of_pos_right aa0, ← norm_mul, sub_mul, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg _), coe_snap (i.f_ne_zero m),
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr a0.ne'), div_mul_comm z]
  calc ‖f z - ‖f z‖ / r * z‖
    _ = ‖f z - z - (‖f z‖ / r - 1) * z‖ := by ring_nf
    _ ≤ ‖f z - z‖ + ‖(‖f z‖ / r - 1) * z‖ := by bound
    _ ≤ r/20 + ‖(‖f z‖ / r - 1) * z‖ := by bound [i.close z m]
    _ = r/20 + |‖f z‖ - ‖z‖| := by
        simp only [Complex.norm_mul, add_right_inj]
        rw [← m, ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
        nth_rw 2 [← abs_of_nonneg (norm_nonneg z)]
        rw [← abs_mul, sub_mul, one_mul, div_mul_cancel₀ _ (m ▸ i.r0.ne')]
    _ ≤ r/20 + ‖f z - z‖ := by bound [abs_norm_sub_norm_le (f z) z]
    _ ≤ r/20 + r/20 := by bound [i.close z m]
    _ ≤ 1/9 * (r - r/20) := by linarith [i.r0]
    _ ≤ 1/9 * (‖z‖ - r/20) := by simp only [m, le_refl]
    _ ≤ 1/9 * (‖z‖ - ‖f z - z‖) := by bound [i.close z m]
    _ ≤ 1/9 * ‖z + (f z - z)‖ := by bound
    _ = 1/9 * ‖f z‖ := by ring_nf

/-- `z ↦ snap (f z)` is injective -/
public lemma WindInj.inj (i : WindInj f r) : InjOn (fun z ↦ snap (f z)) (sphere 0 r) := by
  -- We're either close enough to apply `i.inj_near` or far enough that `i.close` works.
  intro x xm y ym e
  contrapose e
  simp only [mem_sphere_iff_norm, sub_zero] at xm ym ⊢
  by_cases xy : ‖y - x‖ ≤ r / 4
  · have im := image_circleMap_Ioc 0 r
    obtain ⟨a,_,xa⟩ := exists_circleMap_le xm
    have rm : ‖y / x‖ = 1 := by
      simp only [norm_div, ym, xm, ne_eq, not_false_eq_true, div_self, i.r0.ne']
    obtain ⟨t,tm,rt⟩ := exists_circleMap_le rm
    have x0 : x ≠ 0 := by simp only [← norm_pos_iff, xm, i.r0]
    have yb : y = circleMap 0 r (a + t) := by
      simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.ofReal_add, add_mul,
        Complex.exp_add, ← mul_assoc] at xa rt ⊢
      simp only [xa, rt, mul_div_cancel₀ _ x0]
    rw [← xa, yb]
    apply i.inj_near'
    · contrapose e
      simp only [left_eq_add] at e
      simp only [circleMap, Complex.ofReal_one, e, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
        mul_one, zero_add, eq_div_iff x0, one_mul] at rt
      simp only [rt]
    · simp only [add_sub_cancel_left]
      refine le_trans (abs_le_mul_norm_circleMap tm) ?_
      rw [← div_le_div_iff_of_pos_right (c := ‖x‖) (by positivity), ← norm_div, sub_div,
        div_self (norm_ne_zero_iff.mp (by positivity)), ← rt, xm,
        div_div_cancel_left' i.r0.ne'] at xy
      refine le_trans (mul_le_mul_of_nonneg_left xy (by bound)) ?_
      linarith [Real.pi_le_four]
  · simp only [not_le] at xy
    rw [← Circle.coe_inj, ← dist_eq_zero, dist_eq_norm]
    apply ne_of_gt
    calc ‖(snap (f x)).val - snap (f y)‖
      _ = ‖-(y - x) / r + (snap (f x) - x / r - (snap (f y) - y / r))‖ := by ring_nf
      _ ≥ ‖-(y - x) / r‖ - ‖snap (f x) - x / r - (snap (f y) - y / r)‖ := by bound
      _ ≥ ‖-(y - x) / r‖ - (‖snap (f x) - x / r‖ + ‖snap (f y) - y / r‖) := by bound
      _ ≥ ‖-(y - x) / r‖ - (1/9 + 1/9) := by bound [i.snap_close xm, i.snap_close ym]
      _ = ‖y - x‖ / r - 2/9 := by norm_num [abs_of_pos i.r0]; rw [norm_sub_rev]
      _ ≥ r / 4 / r - 2/9 := by bound
      _ ≥ 4⁻¹ - 2/9 := by rw [div_div_cancel_left' i.r0.ne']
      _ > 0 := by norm_num
