import ErdosProblems.Erdos69.FourierPhase
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A polynomial remainder bound on the imaginary axis

The bound has no exponential factor in the argument. This is needed when
only finitely many moments of the arithmetic model have been estimated.
-/

open scoped BigOperators
open Set

namespace Erdos69.Elementary

theorem iteratedDeriv_cexp_real_parameter (z : ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ ↦ Complex.exp (z * t)) =
      fun t : ℝ ↦ z ^ n * Complex.exp (z * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd : HasDerivAt (fun t : ℝ ↦ Complex.exp (z * t))
        (Complex.exp (z * t) * z) t := by
      simpa using (((hasDerivAt_id t).ofReal_comp).const_mul z).cexp
    rw [(hd.const_mul (z ^ n)).deriv]
    ring

theorem norm_exp_sub_taylor_imaginary (z : ℂ) (hz : z.re = 0) (n : ℕ) :
    ‖Complex.exp z - ∑ k ∈ Finset.range (n + 1), z ^ k / k.factorial‖ ≤
      ‖z‖ ^ (n + 1) / n.factorial := by
  let f : ℝ → ℂ := fun t ↦ Complex.exp (z * t)
  have hcont (j : ℕ) : ContDiff ℝ j f := by
    exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  have hderiv (j : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      iteratedDerivWithin j f (Icc 0 1) t = z ^ j * Complex.exp (z * t) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      (hcont j).contDiffAt ht]
    exact congrFun (iteratedDeriv_cexp_real_parameter z j) t
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin (n + 1) f (Icc 0 1) t‖ ≤ ‖z‖ ^ (n + 1) := by
    rw [hderiv _ _ ht, norm_mul, norm_pow, Complex.norm_exp]
    simp [Complex.mul_re, hz]
  have htaylor : taylorWithinEval f n (Icc 0 1) 0 1 =
      ∑ k ∈ Finset.range (n + 1), z ^ k / k.factorial := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hderiv k 0 (by simp)]
    simp [Complex.real_smul, div_eq_mul_inv, mul_comm]
  have h := taylor_mean_remainder_bound (a := (0 : ℝ)) (b := 1) (x := 1)
    (n := n) (by norm_num) (hcont (n + 1)).contDiffOn (by simp) hbound
  rw [htaylor] at h
  simpa [f] using h

noncomputable def phaseTaylor (n : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range n, ((2 * Real.pi : ℝ) * Complex.I) ^ k /
    k.factorial * (x : ℂ) ^ k

theorem fourierPhase_taylor_remainder (n : ℕ) (x : ℝ) :
    ‖fourierPhase x - phaseTaylor (n + 1) x‖ ≤
      (2 * Real.pi * |x|) ^ (n + 1) / n.factorial := by
  let z : ℂ := (2 * Real.pi * x : ℝ) * Complex.I
  have hz : z.re = 0 := by simp [z]
  have hnorm : ‖z‖ = 2 * Real.pi * |x| := by
    simp [z, norm_mul, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos]
  have hpoly : (∑ k ∈ Finset.range (n + 1), z ^ k / k.factorial) =
      phaseTaylor (n + 1) x := by
    apply Finset.sum_congr rfl
    intro k hk
    have hz' : z = ((2 * Real.pi : ℝ) * Complex.I) * (x : ℂ) := by
      dsimp [z]
      push_cast
      ring
    rw [hz', mul_pow]
    ring
  have h := norm_exp_sub_taylor_imaginary z hz n
  rw [hpoly, hnorm] at h
  exact h

end Erdos69.Elementary
