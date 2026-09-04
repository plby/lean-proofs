/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 225.
https://www.erdosproblems.com/forum/thread/225

Informal authors:
- E. B. Saff
- T. Sheil-Small

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos225.md
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic
import ErdosProblems.Erdos228.Bernstein
import ErdosProblems.Erdos1215.Reciprocal

/-!
# Erdős Problem 225

This file formalizes the trigonometric-polynomial statement through its
equivalent algebraic form: the roots of the associated algebraic polynomial
lie on the complex unit circle.
-/

namespace Erdos225

open scoped BigOperators Interval Topology
open Set MeasureTheory Filter

/-- The algebraic polynomial associated to the coefficient list. -/
noncomputable def coeffPolynomial (n : ℕ) (c : ℕ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (c k) * Polynomial.X ^ k

/-- The trigonometric polynomial on the real line. -/
noncomputable def trigPolynomial (n : ℕ) (c : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    c k * Complex.exp (Complex.I * ((k : ℂ) * (θ : ℂ)))

/-- The entire extension whose zeros are required to be real. -/
noncomputable def entireTrigPolynomial (n : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    c k * Complex.exp (Complex.I * ((k : ℂ) * z))

/-- Exact algebraic root condition corresponding to real angular roots. -/
def RootsOnUnitCircle (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, p.IsRoot z → ‖z‖ = 1

/-- All zeros of the entire angular extension are real. -/
def OnlyRealAngularRoots (n : ℕ) (c : ℕ → ℂ) : Prop :=
  ∀ z : ℂ, entireTrigPolynomial n c z = 0 → z.im = 0

@[simp]
theorem coeffPolynomial_eval (n : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    (coeffPolynomial n c).eval z =
      ∑ k ∈ Finset.range (n + 1), c k * z ^ k := by
  classical
  simp [coeffPolynomial, Polynomial.eval_finsetSum]

theorem natDegree_coeffPolynomial_le (n : ℕ) (c : ℕ → ℂ) :
    (coeffPolynomial n c).natDegree ≤ n := by
  classical
  unfold coeffPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  apply (Polynomial.natDegree_mul_le).trans
  simp only [Polynomial.natDegree_C, Polynomial.natDegree_pow,
    Polynomial.natDegree_X, mul_one, zero_add]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)

theorem natDegree_coeffPolynomial_eq (n : ℕ) (c : ℕ → ℂ) (hcn : c n ≠ 0) :
    (coeffPolynomial n c).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_coeffPolynomial_le n c
  · classical
    simp [coeffPolynomial, hcn]

/-- Ordinary Bernstein control for the associated algebraic polynomial.  The
sharp half-degree estimate later strengthens this under the root condition. -/
theorem norm_derivative_coeffPolynomial_le (n : ℕ) (c : ℕ → ℂ) {M : ℝ}
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → ‖(coeffPolynomial n c).eval z‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(coeffPolynomial n c).derivative.eval z‖ ≤ (n : ℝ) * M := by
  exact Erdos228.Bernstein.norm_derivative_eval_le_degree_mul_circleSup
    (natDegree_coeffPolynomial_le n c) hcircle hz

/-- Every point of the complex unit circle has an angular representative in
the closed fundamental interval. -/
theorem exists_angle_Icc_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      z = Complex.exp (Complex.I * (θ : ℂ)) := by
  rw [Complex.norm_eq_one_iff] at hz
  obtain ⟨θ, rfl⟩ := hz
  let t : ℝ := θ - 2 * Real.pi * ⌊θ / (2 * Real.pi)⌋
  refine ⟨t, ?_, ?_⟩
  · constructor
    · dsimp [t]
      nlinarith [Int.floor_le (θ / (2 * Real.pi)), Real.pi_pos,
        mul_div_cancel₀ θ (by positivity : (2 * Real.pi) ≠ 0)]
    · dsimp [t]
      nlinarith [Int.lt_floor_add_one (θ / (2 * Real.pi)), Real.pi_pos,
        mul_div_cancel₀ θ (by positivity : (2 * Real.pi) ≠ 0)]
  · dsimp [t]
    rw [Complex.exp_eq_exp_iff_exists_int]
    use ⌊θ / (2 * Real.pi)⌋
    push_cast
    ring

theorem trigPolynomial_eq_eval_exp (n : ℕ) (c : ℕ → ℂ) (θ : ℝ) :
    trigPolynomial n c θ =
      (coeffPolynomial n c).eval (Complex.exp (Complex.I * (θ : ℂ))) := by
  classical
  rw [coeffPolynomial_eval]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Complex.exp_nat_mul]
  congr 2
  ring

theorem norm_derivative_coeffPolynomial_le_of_trig_bound
    (n : ℕ) (c : ℕ → ℂ) {M : ℝ}
    (hbound : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖trigPolynomial n c θ‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(coeffPolynomial n c).derivative.eval z‖ ≤ (n : ℝ) * M := by
  apply norm_derivative_coeffPolynomial_le n c
  · intro w hw
    obtain ⟨θ, hθ, rfl⟩ := exists_angle_Icc_of_norm_eq_one hw
    rw [← trigPolynomial_eq_eval_exp]
    exact hbound θ hθ
  · exact hz

theorem entireTrigPolynomial_eq_eval_exp (n : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    entireTrigPolynomial n c z =
      (coeffPolynomial n c).eval (Complex.exp (Complex.I * z)) := by
  classical
  rw [coeffPolynomial_eval]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Complex.exp_nat_mul]
  congr 2
  ring

theorem continuous_trigPolynomial (n : ℕ) (c : ℕ → ℂ) :
    Continuous (trigPolynomial n c) := by
  classical
  unfold trigPolynomial
  fun_prop

theorem intervalIntegrable_norm_trigPolynomial (n : ℕ) (c : ℕ → ℂ) :
    IntervalIntegrable (fun θ : ℝ ↦ ‖trigPolynomial n c θ‖) volume
      0 (2 * Real.pi) := by
  exact (continuous_trigPolynomial n c).norm.intervalIntegrable _ _

/-- Algebraic unit-circle roots imply that every angular zero is real. -/
theorem rootsOnUnitCircle_onlyRealAngularRoots (n : ℕ) (c : ℕ → ℂ)
    (hroots : RootsOnUnitCircle (coeffPolynomial n c)) :
    OnlyRealAngularRoots n c := by
  intro z hz
  have hz' :
      (coeffPolynomial n c).eval (Complex.exp (Complex.I * z)) = 0 := by
    rw [← entireTrigPolynomial_eq_eval_exp]
    exact hz
  have hnorm :
      ‖Complex.exp (Complex.I * z)‖ = 1 := by
    apply hroots
    exact hz'
  rw [Complex.norm_exp] at hnorm
  have hre : (Complex.I * z).re = 0 := by
    apply Real.exp_injective
    simpa using hnorm
  simpa using hre

/-- If the constant coefficient is nonzero, real angular roots imply the
equivalent algebraic unit-circle root condition. -/
theorem onlyRealAngularRoots_rootsOnUnitCircle (n : ℕ) (c : ℕ → ℂ)
    (hc0 : c 0 ≠ 0) (hreal : OnlyRealAngularRoots n c) :
    RootsOnUnitCircle (coeffPolynomial n c) := by
  intro α hα
  have hα0 : α ≠ 0 := by
    intro hzero
    subst α
    have heval : (coeffPolynomial n c).eval 0 = 0 := hα
    rw [← Polynomial.coeff_zero_eq_eval_zero] at heval
    apply hc0
    simpa [coeffPolynomial] using heval
  let w : ℂ := -Complex.I * Complex.log α
  have hexp : Complex.exp (Complex.I * w) = α := by
    dsimp [w]
    rw [show Complex.I * (-Complex.I * Complex.log α) = Complex.log α by
      calc
        Complex.I * (-Complex.I * Complex.log α) =
            -(Complex.I * Complex.I) * Complex.log α := by ring
        _ = Complex.log α := by rw [Complex.I_mul_I]; simp]
    exact Complex.exp_log hα0
  have hz : entireTrigPolynomial n c w = 0 := by
    rw [entireTrigPolynomial_eq_eval_exp, hexp]
    exact hα
  have hwim : w.im = 0 := hreal w hz
  rw [← hexp, Complex.norm_exp]
  have hre : (Complex.I * w).re = 0 := by
    simpa using hwim
  rw [hre, Real.exp_zero]

/-- The elementary absolute-cosine integral used by the sharp constant. -/
theorem integral_abs_cos_half :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      |Real.cos (θ / 2)|) = 4 := by
  have hsplit :
      (∫ x : ℝ in (0 : ℝ)..Real.pi, |Real.cos x|) =
        (∫ x : ℝ in (0 : ℝ)..(Real.pi / 2), |Real.cos x|) +
        ∫ x : ℝ in (Real.pi / 2)..Real.pi, |Real.cos x| := by
    symm
    apply intervalIntegral.integral_add_adjacent_intervals
    · exact Real.continuous_cos.abs.intervalIntegrable _ _
    · exact Real.continuous_cos.abs.intervalIntegrable _ _
  have hleft :
      (∫ x : ℝ in (0 : ℝ)..(Real.pi / 2), |Real.cos x|) = 1 := by
    calc
      (∫ x : ℝ in (0 : ℝ)..(Real.pi / 2), |Real.cos x|) =
          ∫ x : ℝ in (0 : ℝ)..(Real.pi / 2), Real.cos x := by
            apply intervalIntegral.integral_congr
            intro x hx
            change |Real.cos x| = Real.cos x
            rw [abs_of_nonneg]
            have hzero : (0 : ℝ) ≤ Real.pi / 2 := by positivity
            have hx' : x ∈ Icc (0 : ℝ) (Real.pi / 2) := by
              simpa [uIcc_of_le hzero] using hx
            exact Real.cos_nonneg_of_mem_Icc
              ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
      _ = 1 := by rw [integral_cos]; simp
  have hright :
      (∫ x : ℝ in (Real.pi / 2)..Real.pi, |Real.cos x|) = 1 := by
    calc
      (∫ x : ℝ in (Real.pi / 2)..Real.pi, |Real.cos x|) =
          ∫ x : ℝ in (Real.pi / 2)..Real.pi, - Real.cos x := by
            apply intervalIntegral.integral_congr
            intro x hx
            change |Real.cos x| = - Real.cos x
            rw [abs_of_nonpos]
            have hhalf : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
            have hx' : x ∈ Icc (Real.pi / 2) Real.pi := by
              simpa [uIcc_of_le hhalf] using hx
            exact Real.cos_nonpos_of_pi_div_two_le_of_le hx'.1
              (by linarith [hx'.2, Real.pi_pos])
      _ = -(∫ x : ℝ in (Real.pi / 2)..Real.pi, Real.cos x) := by
            rw [intervalIntegral.integral_neg]
      _ = 1 := by rw [integral_cos]; simp
  have hbase : (∫ x : ℝ in (0 : ℝ)..Real.pi, |Real.cos x|) = 2 := by
    rw [hsplit, hleft, hright]
    norm_num
  have hscale := intervalIntegral.integral_comp_mul_left
    (f := fun x : ℝ => |Real.cos x|) (a := (0 : ℝ)) (b := 2 * Real.pi)
    (c := (1 / 2 : ℝ)) (by norm_num)
  norm_num [div_eq_mul_inv] at hscale
  have hendpoint : (1 / 2 : ℝ) * (2 * Real.pi) = Real.pi := by ring
  rw [hendpoint, hbase] at hscale
  norm_num at hscale ⊢
  simpa [div_eq_mul_inv, mul_comm] using hscale

/-- The pointwise chord-length identity behind the constant eight. -/
theorem norm_one_add_exp_I (θ : ℝ) :
    ‖(1 : ℂ) + Complex.exp (Complex.I * (θ : ℂ))‖ =
      2 * |Real.cos (θ / 2)| := by
  have harg :
      Complex.I * ((θ - Real.pi : ℝ) : ℂ) =
        Complex.I * (θ : ℂ) + ((-Real.pi : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hminus :
      Complex.exp (Complex.I * ((θ - Real.pi : ℝ) : ℂ)) - 1 =
        - ((1 : ℂ) + Complex.exp (Complex.I * (θ : ℂ))) := by
    rw [harg, Complex.exp_add]
    simp
    ring
  have hnorm := Complex.norm_exp_I_mul_ofReal_sub_one (θ - Real.pi)
  rw [hminus, norm_neg] at hnorm
  rw [hnorm]
  have hhalf : (θ - Real.pi) / 2 = θ / 2 - Real.pi / 2 := by ring
  rw [hhalf, Real.sin_sub]
  simp

/-- Chord length between two angular points on the unit circle. -/
theorem norm_exp_diff (θ φ : ℝ) :
    ‖Complex.exp (Complex.I * (θ : ℂ)) -
        Complex.exp (Complex.I * (φ : ℂ))‖ =
      2 * |Real.sin ((θ - φ) / 2)| := by
  rw [show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I from mul_comm _ _,
      show Complex.I * (φ : ℂ) = (φ : ℂ) * Complex.I from mul_comm _ _]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  have hdiff :
      ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) -
        ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I) =
      ((Real.cos θ - Real.cos φ : ℝ) : ℂ) +
        ((Real.sin θ - Real.sin φ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hdiff, Complex.norm_add_mul_I]
  have hsq :
      (Real.cos θ - Real.cos φ) ^ 2 + (Real.sin θ - Real.sin φ) ^ 2 =
        (2 * |Real.sin ((θ - φ) / 2)|) ^ 2 := by
    rw [mul_pow, sq_abs]
    have h1 := Real.sin_sq_add_cos_sq θ
    have h2 := Real.sin_sq_add_cos_sq φ
    have h3 := Real.cos_sub θ φ
    have h4 := Real.cos_two_mul ((θ - φ) / 2)
    have h5 : 2 * ((θ - φ) / 2) = θ - φ := by ring
    rw [h5] at h4
    have h6 := Real.sin_sq_add_cos_sq ((θ - φ) / 2)
    linear_combination h1 + h2 + 2 * h3 - 2 * h4 - 4 * h6
  rw [hsq, Real.sqrt_sq (by positivity)]

theorem periodic_abs_sin_half :
    Function.Periodic (fun θ : ℝ ↦ |Real.sin (θ / 2)|) (2 * Real.pi) := by
  intro θ
  have harg : (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi := by ring
  change |Real.sin ((θ + 2 * Real.pi) / 2)| = |Real.sin (θ / 2)|
  rw [harg, Real.sin_add_pi, abs_neg]

theorem integral_abs_sin_half_shift (φ : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      |Real.sin ((θ - φ) / 2)|) = 4 := by
  let F : ℝ → ℝ := fun x ↦ |Real.sin (x / 2)|
  have hper : Function.Periodic F (2 * Real.pi) := by
    simpa [F] using periodic_abs_sin_half
  have hshift := intervalIntegral.integral_comp_add_right
    (f := F) (a := (0 : ℝ)) (b := 2 * Real.pi) (-φ)
  have hperiod := hper.intervalIntegral_add_eq (-φ) 0
  have hsin :
      (∫ x : ℝ in (0 : ℝ)..Real.pi, |Real.sin x|) = 2 := by
    calc
      (∫ x : ℝ in (0 : ℝ)..Real.pi, |Real.sin x|) =
          ∫ x : ℝ in (0 : ℝ)..Real.pi, Real.sin x := by
            apply intervalIntegral.integral_congr
            intro x hx
            change |Real.sin x| = Real.sin x
            rw [abs_of_nonneg]
            have hx' : x ∈ Icc (0 : ℝ) Real.pi := by
              simpa [uIcc_of_le Real.pi_pos.le] using hx
            exact Real.sin_nonneg_of_mem_Icc hx'
      _ = 2 := by rw [integral_sin]; simp; norm_num
  have hbase : (∫ x : ℝ in (0 : ℝ)..(2 * Real.pi), F x) = 4 := by
    have hscale := intervalIntegral.integral_comp_mul_left
      (f := fun x : ℝ => |Real.sin x|) (a := (0 : ℝ)) (b := 2 * Real.pi)
      (c := (1 / 2 : ℝ)) (by norm_num)
    norm_num [div_eq_mul_inv] at hscale
    have hendpoint : (1 / 2 : ℝ) * (2 * Real.pi) = Real.pi := by ring
    rw [hendpoint, hsin] at hscale
    norm_num at hscale
    simpa [F, div_eq_mul_inv, mul_comm] using hscale
  rw [show (0 : ℝ) + -φ = -φ by ring,
    show 2 * Real.pi + -φ = -φ + 2 * Real.pi by ring] at hshift
  rw [hperiod, zero_add, hbase] at hshift
  simpa [F, sub_eq_add_neg] using hshift

/-- Every unit-circle chord has the same unnormalized mean length, namely
eight. -/
theorem integral_norm_exp_sub_of_norm_eq_one (α : ℂ) (hα : ‖α‖ = 1) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ‖Complex.exp (Complex.I * (θ : ℂ)) - α‖) = 8 := by
  rw [Complex.norm_eq_one_iff] at hα
  obtain ⟨φ, rfl⟩ := hα
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ‖Complex.exp (Complex.I * (θ : ℂ)) -
        Complex.exp ((φ : ℂ) * Complex.I)‖) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          2 * |Real.sin ((θ - φ) / 2)| := by
            apply intervalIntegral.integral_congr
            intro θ hθ
            rw [show (φ : ℂ) * Complex.I = Complex.I * (φ : ℂ) by ring]
            exact norm_exp_diff θ φ
    _ = 2 * ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          |Real.sin ((θ - φ) / 2)| := by
            rw [intervalIntegral.integral_const_mul]
    _ = 8 := by rw [integral_abs_sin_half_shift]; norm_num

/-- The full inequality in degree one.  This also checks every normalization
used by the general proof: a normalized unit-circle chord has mean four. -/
theorem erdos_225_degree_one (c : ℕ → ℂ) (hc1 : c 1 ≠ 0)
    (hroots : RootsOnUnitCircle (coeffPolynomial 1 c))
    (hbound : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖trigPolynomial 1 c θ‖ ≤ 1) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ‖trigPolynomial 1 c θ‖) ≤ 4 := by
  let α : ℂ := -c 0 / c 1
  have hroot : (coeffPolynomial 1 c).IsRoot α := by
    rw [Polynomial.IsRoot.def, coeffPolynomial_eval]
    simp [α, Finset.sum_range_succ]
    field_simp
    ring
  have hα : ‖α‖ = 1 := hroots α hroot
  have hc0norm : ‖c 0‖ = ‖c 1‖ := by
    dsimp [α] at hα
    rw [norm_div, norm_neg, div_eq_one_iff_eq] at hα
    · exact hα
    · rwa [norm_ne_zero_iff]
  have hnegα : ‖-α‖ = 1 := by simpa using hα
  obtain ⟨θ0, hθ0, hθ0exp⟩ := exists_angle_Icc_of_norm_eq_one hnegα
  have hmax := hbound θ0 hθ0
  have hvalue : trigPolynomial 1 c θ0 = 2 * c 0 := by
    rw [trigPolynomial]
    norm_num [Finset.sum_range_succ]
    rw [← hθ0exp]
    simp [α]
    field_simp
    ring
  rw [hvalue, norm_mul] at hmax
  norm_num at hmax
  have hc1half : ‖c 1‖ ≤ (1 / 2 : ℝ) := by
    rw [← hc0norm]
    nlinarith
  have hfactor : ∀ θ : ℝ,
      trigPolynomial 1 c θ =
        c 1 * (Complex.exp (Complex.I * (θ : ℂ)) - α) := by
    intro θ
    simp [trigPolynomial, Finset.sum_range_succ, α]
    field_simp
    ring
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ‖trigPolynomial 1 c θ‖) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          ‖c 1‖ * ‖Complex.exp (Complex.I * (θ : ℂ)) - α‖ := by
            apply intervalIntegral.integral_congr
            intro θ hθ
            change ‖trigPolynomial 1 c θ‖ =
              ‖c 1‖ * ‖Complex.exp (Complex.I * (θ : ℂ)) - α‖
            rw [hfactor θ, norm_mul]
    _ = ‖c 1‖ * (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          ‖Complex.exp (Complex.I * (θ : ℂ)) - α‖) := by
            rw [intervalIntegral.integral_const_mul]
    _ = ‖c 1‖ * 8 := by rw [integral_norm_exp_sub_of_norm_eq_one α hα]
    _ ≤ 4 := by nlinarith

/-- The unnormalized circle integral of the extremal chord function is eight. -/
theorem integral_norm_one_add_exp_I :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ‖(1 : ℂ) + Complex.exp (Complex.I * (θ : ℂ))‖) = 8 := by
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ‖(1 : ℂ) + Complex.exp (Complex.I * (θ : ℂ))‖) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          2 * |Real.cos (θ / 2)| := by
            apply intervalIntegral.integral_congr
            intro θ hθ
            exact norm_one_add_exp_I θ
    _ = 2 * ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          |Real.cos (θ / 2)| := by
            rw [intervalIntegral.integral_const_mul]
    _ = 8 := by rw [integral_abs_cos_half]; norm_num

/-- The measure-theoretic assembly of the reciprocal-quotient argument.  This
isolates the only genuinely complex-analytic input: construction of an
auxiliary disk map whose chord mean is at most eight. -/
theorem turanMalik_of_auxiliary {n : ℕ} (g : ℝ → ℂ) (W : ℝ → ℂ) (L : ℝ)
    (hL : 0 ≤ L)
    (hg : IntervalIntegrable (fun θ : ℝ ↦ ‖g θ‖) volume 0 (2 * Real.pi))
    (hW : IntervalIntegrable
      (fun θ : ℝ ↦ ‖(1 : ℂ) + W θ‖ * L) volume 0 (2 * Real.pi))
    (hpoint : ∀ θ : ℝ,
      (n : ℝ) * ‖g θ‖ ≤ ‖(1 : ℂ) + W θ‖ * L)
    (hmean :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ‖(1 : ℂ) + W θ‖) ≤ 8) :
    (n : ℝ) * (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ‖g θ‖) ≤ 8 * L := by
  calc
    (n : ℝ) * (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ‖g θ‖) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), (n : ℝ) * ‖g θ‖ := by
          rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ‖(1 : ℂ) + W θ‖ * L := by
          apply intervalIntegral.integral_mono
          · exact Real.two_pi_pos.le
          · exact hg.const_mul _
          · exact hW
          · intro θ
            exact hpoint θ
    _ = (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ‖(1 : ℂ) + W θ‖) * L := by
          rw [intervalIntegral.integral_mul_const]
    _ ≤ 8 * L := mul_le_mul_of_nonneg_right hmean hL

/-- Numerical assembly of the two sharp analytic ingredients.  The two
hypotheses are exactly the unnormalized Turán--Malik estimate and the
Erdős--Lax half-degree estimate, respectively. -/
theorem integral_le_four_of_sharp_bounds {n : ℕ} (hn : 0 < n)
    (g : ℝ → ℂ) (L : ℝ)
    (hmalik :
      (n : ℝ) * (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ‖g θ‖) ≤ 8 * L)
    (hlax : 2 * L ≤ (n : ℝ)) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ‖g θ‖) ≤ 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ‖g θ‖)
        = ((n : ℝ) * (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ‖g θ‖)) / n := by
            field_simp
    _ ≤ (8 * L) / n := (div_le_div_of_nonneg_right hmalik hnR.le)
    _ ≤ 4 := by
      apply (div_le_iff₀ hnR).2
      nlinarith

/-! ### Conjugate-reciprocal algebra

The next lemmas are the algebraic half of the Erdős--Lax input.  They are
kept here rather than hidden behind an assumption: when all roots are on the
circle, the conjugate reciprocal is a unimodular scalar multiple of the
original polynomial.
-/

theorem coeff_conjReflect_of_le (N : ℕ) (p : Polynomial ℂ) (i : ℕ)
    (hi : i ≤ N) :
    (Erdos1215.conjReflect N p).coeff i =
      starRingEnd ℂ (p.coeff (N - i)) := by
  simp [Erdos1215.conjReflect, Polynomial.coeff_reflect,
    Polynomial.revAt_le hi]

theorem conjReflect_derivative_relation {N : ℕ} (hN : 0 < N)
    (p : Polynomial ℂ) (hdeg : p.natDegree ≤ N) :
    Polynomial.C (N : ℂ) * Erdos1215.conjReflect N p -
        Polynomial.X * (Erdos1215.conjReflect N p).derivative =
      Erdos1215.conjReflect (N - 1) p.derivative := by
  ext (_ | i)
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_mul_zero, sub_zero]
    rw [coeff_conjReflect_of_le N p 0 (Nat.zero_le N)]
    rw [coeff_conjReflect_of_le (N - 1) p.derivative 0 (Nat.zero_le _)]
    simp only [Polynomial.coeff_derivative]
    have hsub : N - 1 - 0 + 1 = N := by omega
    rw [hsub]
    simp only [tsub_zero, map_mul, map_add, map_natCast, map_one]
    have hcast : (N : ℂ) = ((N - 1 : ℕ) : ℂ) + 1 := by
      exact_mod_cast (by omega : N = (N - 1 : ℕ) + 1)
    rw [hcast]
    ring
  · by_cases hi : i + 1 ≤ N - 1
    · have hiN : i + 1 ≤ N := by omega
      have hi' : i + 1 ≤ N - 1 := hi
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
      rw [coeff_conjReflect_of_le N p (i + 1) hiN]
      rw [coeff_conjReflect_of_le (N - 1) p.derivative (i + 1) hi']
      simp only [Polynomial.coeff_derivative]
      simp only [map_mul, map_add, map_natCast, map_one]
      have hcast : (N : ℂ) =
          ((N - 1 - (i + 1) + 1 : ℕ) : ℂ) + (i + 1 : ℂ) := by
        exact_mod_cast
          (by omega : N = (N - 1 - (i + 1) + 1 : ℕ) + (i + 1))
      rw [hcast]
      have hidx : N - 1 - (i + 1) + 1 = N - (i + 1) := by omega
      rw [hidx]
      have hcast2 : ((N - (i + 1) : ℕ) : ℂ) =
          ((N - 1 - (i + 1) : ℕ) : ℂ) + 1 := by
        exact_mod_cast hidx.symm
      rw [hcast2]
      ring
    · by_cases hieq : i + 1 = N
      · subst N
        have hcoeffsucc : p.coeff (i + 2) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt hdeg (by omega))
        have hrev : Polynomial.revAt i (i + 1) = i + 1 :=
          Polynomial.revAt_eq_self_of_lt (by omega)
        simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
        rw [coeff_conjReflect_of_le (i + 1) p (i + 1) (by omega)]
        simp only [Nat.sub_self]
        simp [Erdos1215.conjReflect, Polynomial.coeff_reflect, hrev,
          Polynomial.coeff_derivative, hcoeffsucc]
        ring
      · have hlt : N < i + 1 := by omega
        have hcoeff : p.coeff (i + 1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hlt)
        have hcoeffsucc : p.coeff (i + 2) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt hdeg (by omega))
        simp [Erdos1215.conjReflect, Polynomial.coeff_reflect,
          Polynomial.revAt_eq_self_of_lt hlt,
          Polynomial.revAt_eq_self_of_lt (by omega : N - 1 < i + 1),
          Polynomial.coeff_X_mul,
          Polynomial.coeff_derivative, hcoeff, hcoeffsucc]

theorem conjReflect_linear_factor {a : ℂ} (ha : ‖a‖ = 1) :
    Erdos1215.conjReflect 1 (Polynomial.X - Polynomial.C a) =
      Polynomial.C (-starRingEnd ℂ a) *
        (Polynomial.X - Polynomial.C a) := by
  have haunit : starRingEnd ℂ a * a = 1 := by
    rw [starRingEnd_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, ha]
    norm_num
  ext i
  rcases i with _ | _ | i
  · simp [Erdos1215.conjReflect, Polynomial.coeff_one, haunit]
  · simp [Erdos1215.conjReflect, Polynomial.coeff_one]
  · have hne : i + 1 + 1 ≠ 1 := by omega
    dsimp [Erdos1215.conjReflect]
    rw [Polynomial.coeff_reflect,
      Polynomial.revAt_eq_self_of_lt (by omega : 1 < i + 2)]
    simp [Polynomial.coeff_X]

theorem conjReflect_prod_linear (m : Multiset ℂ)
    (hm : ∀ a ∈ m, ‖a‖ = 1) :
    Erdos1215.conjReflect m.card
        ((m.map fun a => Polynomial.X - Polynomial.C a).prod) =
      Polynomial.C ((m.map fun a => -starRingEnd ℂ a).prod) *
        (m.map fun a => Polynomial.X - Polynomial.C a).prod := by
  induction m using Multiset.induction_on with
  | empty => simp [Erdos1215.conjReflect]
  | @cons a m ih =>
      have ha : ‖a‖ = 1 := hm a (by simp)
      have hm' : ∀ b ∈ m, ‖b‖ = 1 := by
        intro b hb
        exact hm b (by simp [hb])
      rw [Multiset.card_cons]
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [show m.card + 1 = 1 + m.card by omega]
      rw [Erdos1215.conjReflect_mul 1 m.card
        (Polynomial.X - Polynomial.C a)
        ((m.map fun b => Polynomial.X - Polynomial.C b).prod)
        (by simp) (by
          calc
            ((m.map fun b => Polynomial.X - Polynomial.C b).prod).natDegree ≤
                ((m.map fun b => Polynomial.X - Polynomial.C b).map
                  Polynomial.natDegree).sum :=
              Polynomial.natDegree_multiset_prod_le _
            _ ≤ (m.map fun b => Polynomial.X - Polynomial.C b).card := by simp
            _ = m.card := by simp)]
      rw [conjReflect_linear_factor ha, ih hm']
      simp
      ring

theorem norm_multiset_prod_eq_one (m : Multiset ℂ)
    (hm : ∀ a ∈ m, ‖a‖ = 1) : ‖m.prod‖ = 1 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
      rw [Multiset.prod_cons, norm_mul, hm a (by simp)]
      simp [ih (by
        intro b hb
        exact hm b (by simp [hb]))]

theorem conjReflect_eq_scalar_mul_of_roots_on_circle {p : Polynomial ℂ}
    {N : ℕ} (hdeg : p.natDegree = N) (hp0 : p ≠ 0)
    (hroots : ∀ z : ℂ, p.IsRoot z → ‖z‖ = 1) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧
      Erdos1215.conjReflect N p = Polynomial.C lam * p := by
  let m := p.roots
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hcard : m.card = N := by
    dsimp [m]
    rw [← hdeg]
    exact hsplits.natDegree_eq_card_roots.symm
  have hm : ∀ a ∈ m, ‖a‖ = 1 := by
    intro a ha
    apply hroots a
    exact (Polynomial.mem_roots hp0).mp ha
  let σ : ℂ := (m.map fun a => -starRingEnd ℂ a).prod
  let lam : ℂ := starRingEnd ℂ p.leadingCoeff * σ / p.leadingCoeff
  refine ⟨lam, ?_, ?_⟩
  · have hlc : p.leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hp0
    have hσ : ‖σ‖ = 1 := by
      dsimp [σ]
      apply norm_multiset_prod_eq_one
      intro a ha
      rcases Multiset.mem_map.mp ha with ⟨b, hb, rfl⟩
      simp [hm b hb]
    dsimp [lam]
    rw [norm_div, norm_mul, starRingEnd_apply, norm_star, hσ, mul_one,
      div_self (norm_ne_zero_iff.mpr hlc)]
  · have hfactor : p = Polynomial.C p.leadingCoeff *
        (m.map fun a => Polynomial.X - Polynomial.C a).prod :=
      hsplits.eq_prod_roots
    rw [hfactor]
    rw [← hcard]
    rw [show m.card = 0 + m.card by omega]
    rw [Erdos1215.conjReflect_mul 0 m.card
      (Polynomial.C p.leadingCoeff)
      ((m.map fun a => Polynomial.X - Polynomial.C a).prod)
      (by simp) (by
        calc
          ((m.map fun a => Polynomial.X - Polynomial.C a).prod).natDegree ≤
              ((m.map fun a => Polynomial.X - Polynomial.C a).map
                Polynomial.natDegree).sum :=
            Polynomial.natDegree_multiset_prod_le _
          _ ≤ (m.map fun a => Polynomial.X - Polynomial.C a).card := by simp
          _ = m.card := by simp)]
    rw [conjReflect_prod_linear m hm]
    have hlc : p.leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hp0
    have hlam :
        lam * p.leadingCoeff = starRingEnd ℂ p.leadingCoeff * σ := by
      dsimp [lam]
      field_simp
    dsimp [σ] at hlam
    simp only [Erdos1215.conjReflect, Polynomial.map_C,
      Polynomial.reflect_C, pow_zero, mul_one]
    rw [← mul_assoc, ← Polynomial.C_mul]
    rw [← hlam]
    rw [Polynomial.C_mul]
    ring

/-! ### Logarithmic derivative comparison

For a zero in the closed disk, its contribution to the logarithmic
derivative has real part at least one half on the unit circle.  Summing this
elementary estimate is the finite-dimensional core of Malik's derivative
comparison.
-/

theorem half_le_re_z_div_sub {a z : ℂ} (ha : ‖a‖ ≤ 1)
    (hz : ‖z‖ = 1) (hza : z ≠ a) :
    (1 / 2 : ℝ) ≤ (z / (z - a)).re := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by simp [hz])
  have hden : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hnormsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]
    norm_num
  have ha2 : Complex.normSq a ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [(sq_le_sq₀ (norm_nonneg a) zero_le_one).2 ha]
  have hpos : 0 < (z.re - a.re) ^ 2 + (z.im - a.im) ^ 2 := by
    have hh := Complex.normSq_pos.mpr hden
    norm_num [Complex.normSq] at hh ⊢
    nlinarith
  norm_num [Complex.div_re, Complex.normSq] at hnormsq ha2 ⊢
  simp only [sq] at hpos ⊢
  rw [← add_div]
  rw [le_div_iff₀ hpos]
  nlinarith

theorem norm_nat_sub_le_of_re {n : ℕ} {w : ℂ}
    (h : (n : ℝ) ≤ 2 * w.re) :
    ‖(n : ℂ) - w‖ ≤ ‖w‖ := by
  rw [← (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _))]
  rw [Complex.sq_norm, Complex.sq_norm]
  norm_num [Complex.normSq] at h ⊢
  nlinarith

theorem multiset_sum_le_sum_of_forall {m : Multiset ℂ}
    {f g : ℂ → ℝ} (h : ∀ a ∈ m, f a ≤ g a) :
    (m.map f).sum ≤ (m.map g).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact add_le_add (h a (by simp))
        (ih (by
          intro b hb
          exact h b (by simp [hb])))

theorem root_log_sum_re_ge_half_degree {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree = n) (hp0 : p ≠ 0)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ = 1) (hzp : p.eval z ≠ 0) :
    (n : ℝ) ≤ 2 *
      ((p.roots.map fun a => z / (z - a)).sum).re := by
  have hcard : p.roots.card = n := by
    rw [← hdeg]
    exact (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hsum : (p.roots.map fun _a => (1 / 2 : ℝ)).sum ≤
      (p.roots.map fun a => (z / (z - a)).re).sum := by
    apply multiset_sum_le_sum_of_forall
    intro a ha
    apply half_le_re_z_div_sub
    · apply hroots a
      exact (Polynomial.mem_roots hp0).mp ha
    · exact hz
    · intro hza
      subst a
      exact hzp ((Polynomial.mem_roots hp0).mp ha).eq_zero
  have hconst : (p.roots.map fun _a => (1 / 2 : ℝ)).sum =
      p.roots.card * (1 / 2 : ℝ) := by simp
  rw [hconst, hcard] at hsum
  have hre : ((p.roots.map fun a => z / (z - a)).sum).re =
      (p.roots.map fun a => (z / (z - a)).re).sum := by
    induction p.roots using Multiset.induction_on with
    | empty => simp
    | cons a m ih => simp [ih]
  rw [← hre] at hsum
  norm_num at hsum ⊢
  linarith

theorem root_log_sum_identity {p : Polynomial ℂ} (_hp0 : p ≠ 0)
    {z : ℂ} (hzp : p.eval z ≠ 0) :
    z * (p.derivative.eval z / p.eval z) =
      (p.roots.map fun a => z / (z - a)).sum := by
  rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hzp]
  rw [← Multiset.sum_map_mul_left]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro a ha
  simp [div_eq_mul_inv]

theorem norm_log_derivative_complement_le {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree = n) (hp0 : p ≠ 0)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ = 1) (hzp : p.eval z ≠ 0) :
    ‖(n : ℂ) - z * (p.derivative.eval z / p.eval z)‖ ≤
      ‖z * (p.derivative.eval z / p.eval z)‖ := by
  rw [root_log_sum_identity hp0 hzp]
  apply norm_nat_sub_le_of_re
  exact root_log_sum_re_ge_half_degree hdeg hp0 hroots hz hzp

theorem norm_polar_eval_le_derivative_of_roots_in_disk
    {p : Polynomial ℂ} {n : ℕ} (hdeg : p.natDegree = n) (hp0 : p ≠ 0)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖((Polynomial.C (n : ℂ) * p - Polynomial.X * p.derivative).eval z)‖ ≤
      ‖p.derivative.eval z‖ := by
  have hzp : p.eval z ≠ 0 := by
    intro hz0
    have hzroot : p.IsRoot z := hz0
    have := hroots z hzroot
    linarith
  have hq := norm_log_derivative_complement_le hdeg hp0
    (fun a ha => (hroots a ha).le) hz hzp
  have hmul := mul_le_mul_of_nonneg_right hq (norm_nonneg (p.eval z))
  have hleft : ‖(n : ℂ) - z * (p.derivative.eval z / p.eval z)‖ *
      ‖p.eval z‖ =
      ‖(n : ℂ) * p.eval z - z * p.derivative.eval z‖ := by
    rw [← norm_mul]
    congr 1
    field_simp
  have hright : ‖z * (p.derivative.eval z / p.eval z)‖ *
      ‖p.eval z‖ = ‖p.derivative.eval z‖ := by
    rw [norm_mul, norm_div, hz, one_mul]
    field_simp
  rw [hleft, hright] at hmul
  simpa using hmul

theorem norm_conjReflect_derivative_le_of_roots_in_disk
    {p : Polynomial ℂ} {n : ℕ} (hn : 0 < n) (hdeg : p.natDegree = n)
    (hp0 : p ≠ 0) (hcoeff0 : p.coeff 0 ≠ 0)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(Erdos1215.conjReflect n p).derivative.eval z‖ ≤
      ‖p.derivative.eval z‖ := by
  let q := Erdos1215.conjReflect n p
  have hqdeg_le : q.natDegree ≤ n := by
    dsimp [q, Erdos1215.conjReflect]
    exact (Polynomial.natDegree_reflect_le.trans
      (by simp [hdeg]))
  have hqcoeff : q.coeff n ≠ 0 := by
    rw [coeff_conjReflect_of_le n p n le_rfl]
    simpa using (map_ne_zero (starRingEnd ℂ)).mpr hcoeff0
  have hqdeg : q.natDegree = n :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hqdeg_le hqcoeff
  have hqderivdeg : q.derivative.natDegree = n - 1 := by
    rw [Polynomial.natDegree_derivative, hqdeg]
  have hrel := conjReflect_derivative_relation hn q hqdeg_le
  have hqq : Erdos1215.conjReflect n q = p := by simp [q]
  rw [hqq] at hrel
  have heval := congrArg (fun r : Polynomial ℂ => r.eval z) hrel
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at heval
  have hnorm :=
    Erdos1215.norm_conjReflect_eval_of_norm_eq_one q.derivative hz
  rw [hqderivdeg] at hnorm
  calc
    ‖q.derivative.eval z‖ =
        ‖(Erdos1215.conjReflect (n - 1) q.derivative).eval z‖ :=
      hnorm.symm
    _ = ‖(n : ℂ) * p.eval z - z * p.derivative.eval z‖ := by
      rw [← heval]
    _ = ‖((Polynomial.C (n : ℂ) * p -
          Polynomial.X * p.derivative).eval z)‖ := by simp
    _ ≤ ‖p.derivative.eval z‖ :=
      norm_polar_eval_le_derivative_of_roots_in_disk hdeg hp0 hroots hz

theorem exists_aligned_outer_scalar {n : ℕ} (hn : 0 < n)
    {d z : ℂ} (hz : ‖z‖ = 1) (hd : ‖d‖ ≤ (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ℂ, ‖w‖ = 1 + ε / n ∧
      ‖d - w * (n : ℂ) * z ^ (n - 1)‖ =
        (n : ℝ) + ε - ‖d‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hzpow : ‖z ^ (n - 1)‖ = 1 := by simp [norm_pow, hz]
  have hzpow0 : z ^ (n - 1) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    simp [hzpow]
  let R : ℝ := (n : ℝ) + ε
  have hR : 0 < R := by dsimp [R]; linarith
  let u : ℂ := Complex.exp ((d.arg : ℂ) * Complex.I)
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    exact Complex.norm_exp_ofReal_mul_I d.arg
  have hdu : (‖d‖ : ℂ) * u = d := by
    dsimp [u]
    simp
  let w : ℂ := (R : ℂ) * u / ((n : ℂ) * z ^ (n - 1))
  refine ⟨w, ?_, ?_⟩
  · dsimp [w]
    have hRnorm : ‖(R : ℂ)‖ = R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    rw [norm_div, norm_mul, norm_mul, hRnorm, hu,
      Complex.norm_natCast, hzpow]
    dsimp [R]
    field_simp
  · dsimp [w]
    have hcancel : ((R : ℂ) * u / ((n : ℂ) * z ^ (n - 1))) *
        (n : ℂ) * z ^ (n - 1) = (R : ℂ) * u := by
      field_simp
    rw [hcancel]
    calc
      ‖d - (R : ℂ) * u‖ =
          ‖((‖d‖ : ℂ) - (R : ℂ)) * u‖ := by
        nth_rw 1 [← hdu]
        ring_nf
      _ = ‖(‖d‖ : ℂ) - (R : ℂ)‖ := by rw [norm_mul, hu, mul_one]
      _ = |‖d‖ - R| := by
        have hcast :
            (‖d‖ : ℂ) - (R : ℂ) = ((‖d‖ - R : ℝ) : ℂ) := by
          push_cast
          rfl
        rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      _ = (n : ℝ) + ε - ‖d‖ := by
        have hle : ‖d‖ ≤ R := by dsimp [R]; linarith
        rw [abs_of_nonpos (by linarith)]
        dsimp [R]
        ring

theorem roots_sub_outer_monomial_in_disk {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree = n)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ 1)
    {w : ℂ} (hw : 1 < ‖w‖) {a : ℂ}
    (ha : (p - Polynomial.C w * Polynomial.X ^ n).IsRoot a) :
    ‖a‖ < 1 := by
  by_contra hnot
  have ha1 : 1 ≤ ‖a‖ := le_of_not_gt hnot
  have hout := Erdos228.Bernstein.norm_eval_le_circle_bound_mul_pow
    hdeg.le hcircle ha1
  have heq : p.eval a = w * a ^ n := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      sub_eq_zero] at ha
    exact ha
  rw [heq, norm_mul, norm_pow] at hout
  have hpow : 0 < ‖a‖ ^ n :=
    pow_pos (lt_of_lt_of_le zero_lt_one ha1) n
  have hwle : ‖w‖ ≤ 1 := by
    apply le_of_mul_le_mul_right (a := ‖a‖ ^ n)
    · simpa using hout
    · exact hpow
  exact (not_le_of_gt hw) hwle

/-- Malik's derivative-sum inequality on the unit circle, specialized to the
normalization used by Erdős 225. -/
theorem norm_derivative_add_conjReflect_derivative_le
    {p : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hdeg : p.natDegree = n) (hcoeff0 : p.coeff 0 ≠ 0)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖p.derivative.eval z‖ +
        ‖(Erdos1215.conjReflect n p).derivative.eval z‖ ≤ (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpderiv :
      ‖p.derivative.eval z‖ ≤ (n : ℝ) :=
    by simpa using
      (Erdos228.Bernstein.norm_derivative_eval_le_degree_mul_circleSup
        hdeg.le hcircle hz)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨w, hw, halign⟩ :=
    exists_aligned_outer_scalar hn hz hpderiv hε
  have hwgt : 1 < ‖w‖ := by
    rw [hw]
    have : 0 < ε / (n : ℝ) := div_pos hε hnR
    linarith
  let F : Polynomial ℂ := p - Polynomial.C w * Polynomial.X ^ n
  have hFroots : ∀ a : ℂ, F.IsRoot a → ‖a‖ < 1 := by
    intro a ha
    exact roots_sub_outer_monomial_in_disk hdeg hcircle hwgt ha
  have hpcoeff : ‖p.coeff n‖ ≤ 1 :=
    Erdos228.Bernstein.norm_coeff_le_of_circle_bound hdeg.le hcircle
  have hpw : p.coeff n ≠ w := by
    intro hpw
    rw [hpw] at hpcoeff
    exact (not_le_of_gt hwgt) hpcoeff
  have hFcoeffn : F.coeff n ≠ 0 := by
    simpa [F, Polynomial.coeff_C_mul_X_pow] using sub_ne_zero.mpr hpw
  have hFdeg_le : F.natDegree ≤ n := by
    calc
      F.natDegree ≤ max n n := by
        apply Polynomial.natDegree_sub_le_of_le
        · exact hdeg.le
        · exact (Polynomial.natDegree_mul_le).trans (by simp)
      _ = n := by simp
  have hFdeg : F.natDegree = n :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hFdeg_le hFcoeffn
  have hFne : F ≠ 0 := by
    intro hzero
    rw [hzero] at hFcoeffn
    simp at hFcoeffn
  have hFcoeff0 : F.coeff 0 ≠ 0 := by
    have h0n : 0 ≠ n := Nat.ne_of_lt hn
    simpa [F, h0n] using hcoeff0
  have hstarF :
      Erdos1215.conjReflect n F =
        Erdos1215.conjReflect n p - Polynomial.C (starRingEnd ℂ w) := by
    rw [show F = p - Polynomial.C w * Polynomial.X ^ n by rfl,
      Erdos1215.conjReflect_sub]
    congr 1
    have hterm := Erdos1215.conjReflect_mul 0 n
      (Polynomial.C w) (Polynomial.X ^ n) (by simp) (by simp)
    simp [Erdos1215.conjReflect]
  have hstarFderiv :
      (Erdos1215.conjReflect n F).derivative =
        (Erdos1215.conjReflect n p).derivative := by
    rw [hstarF]
    simp
  have hFderiv :
      F.derivative.eval z =
        p.derivative.eval z - w * (n : ℂ) * z ^ (n - 1) := by
    simp [F, Polynomial.derivative_X_pow]
    ring
  have hcompare :=
    norm_conjReflect_derivative_le_of_roots_in_disk hn hFdeg hFne
      hFcoeff0 hFroots hz
  rw [hstarFderiv, hFderiv] at hcompare
  calc
    ‖p.derivative.eval z‖ +
        ‖(Erdos1215.conjReflect n p).derivative.eval z‖
        ≤ ‖p.derivative.eval z‖ +
          ‖p.derivative.eval z - w * (n : ℂ) * z ^ (n - 1)‖ := by
            gcongr
    _ = ‖p.derivative.eval z‖ +
        ((n : ℝ) + ε - ‖p.derivative.eval z‖) := by rw [halign]
    _ = (n : ℝ) + ε := by ring

/-- Erdős--Lax half-degree estimate in the exact form needed below. -/
theorem norm_derivative_le_half_degree_of_roots_on_circle
    {p : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hdeg : p.natDegree = n) (hp0 : p ≠ 0) (hcoeff0 : p.coeff 0 ≠ 0)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ = 1)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    2 * ‖p.derivative.eval z‖ ≤ (n : ℝ) := by
  obtain ⟨lam, hlam, hself⟩ :=
    conjReflect_eq_scalar_mul_of_roots_on_circle hdeg hp0 hroots
  have hderiv :
      (Erdos1215.conjReflect n p).derivative.eval z =
        lam * p.derivative.eval z := by
    rw [hself]
    simp
  have hnorm :
      ‖(Erdos1215.conjReflect n p).derivative.eval z‖ =
        ‖p.derivative.eval z‖ := by
    rw [hderiv, norm_mul, hlam, one_mul]
  have hsum :=
    norm_derivative_add_conjReflect_derivative_le hn hdeg hcoeff0 hcircle hz
  rw [hnorm] at hsum
  nlinarith

/-! ### Littlewood subordination on the disk -/

theorem norm_circleAverage_le_circleAverage_norm (f : ℂ → ℂ)
    (c : ℂ) (R : ℝ) :
    ‖Real.circleAverage f c R‖ ≤
      Real.circleAverage (fun z : ℂ ↦ ‖f z‖) c R := by
  unfold Real.circleAverage
  rw [norm_smul]
  simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr Real.two_pi_pos)]
  simp only [smul_eq_mul]
  change (2 * Real.pi)⁻¹ *
      ‖∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (circleMap c R θ)‖ ≤
    (2 * Real.pi)⁻¹ *
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap c R θ)‖)
  gcongr
  exact intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le

theorem circleAverage_poissonKernel_nonneg {w : ℂ} (hw : ‖w‖ < 1) :
    ∀ z ∈ Metric.sphere (0 : ℂ) (1 : ℝ), 0 ≤ poissonKernel 0 w z := by
  intro z hz
  rw [poissonKernel_def]
  have hz' : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
  have hnum : 0 ≤ ‖z - 0‖ ^ 2 - ‖w - 0‖ ^ 2 := by
    simp only [sub_zero]
    nlinarith [sq_lt_sq₀ (norm_nonneg w) zero_le_one |>.2 hw]
  exact div_nonneg hnum (sq_nonneg _)

theorem circleAverage_poisson_comp_eq_one
    {W : ℂ → ℂ}
    (hW : DiffContOnCl ℂ W (Metric.ball 0 1))
    (hW0 : W 0 = 0)
    (hWdisk : ∀ x ∈ Metric.closedBall (0 : ℂ) 1, ‖W x‖ < 1)
    {η : ℂ} (hη : η ∈ Metric.sphere (0 : ℂ) 1) :
    Real.circleAverage (fun x : ℂ ↦ poissonKernel 0 (W x) η) 0 1 = 1 := by
  have hηnorm : ‖η‖ = 1 := by simpa [Metric.mem_sphere] using hη
  let H : ℂ → ℂ := fun x ↦ (η + W x) / (η - W x)
  have hden : ∀ x ∈ closure (Metric.ball (0 : ℂ) 1), η - W x ≠ 0 := by
    intro x hx hzero
    have heq : η = W x := sub_eq_zero.mp hzero
    have hx' : x ∈ Metric.closedBall (0 : ℂ) 1 :=
      Metric.closure_ball_subset_closedBall hx
    have hlt := hWdisk x hx'
    rw [← heq, hηnorm] at hlt
    linarith
  have hH : DiffContOnCl ℂ H (Metric.ball 0 1) := by
    dsimp [H]
    have hnum : DiffContOnCl ℂ (fun x ↦ η + W x) (Metric.ball 0 1) :=
      hW.const_add η
    have hdenF : DiffContOnCl ℂ (fun x ↦ η - W x) (Metric.ball 0 1) :=
      hW.const_sub η
    simpa [div_eq_mul_inv] using hnum.smul (hdenF.inv hden)
  have hH' : DiffContOnCl ℂ H (Metric.ball 0 |(1 : ℝ)|) := by
    simpa using hH
  have hmean : Real.circleAverage H 0 1 = H 0 := by
    exact hH'.circleAverage
  have hHint : CircleIntegrable H 0 1 := by
    apply (hH'.continuousOn_ball.mono Metric.sphere_subset_closedBall).circleIntegrable'
  have hre :
      Real.circleAverage (Complex.reCLM ∘ H) 0 1 =
        (Real.circleAverage H 0 1).re := by
    exact Complex.reCLM.circleAverage_comp_comm hHint
  calc
    Real.circleAverage (fun x : ℂ ↦ poissonKernel 0 (W x) η) 0 1 =
        Real.circleAverage (Complex.reCLM ∘ H) 0 1 := by
          apply Real.circleAverage_congr_sphere
          intro x hx
          simp [poissonKernel_eq_re_herglotzRieszKernel, H,
            herglotzRieszKernel_def]
    _ = (Real.circleAverage H 0 1).re := hre
    _ = (H 0).re := by rw [hmean]
    _ = 1 := by
      have hη0 : η ≠ 0 := norm_ne_zero_iff.mp (by simp [hηnorm])
      simp [H, hW0, hη0]

theorem circleAverage_circleAverage_swap_of_continuous_circle
    {K : ℂ → ℂ → ℝ}
    (hFcont : Continuous (fun z : ℝ × ℝ ↦
      K (circleMap 0 1 z.1) (circleMap 0 1 z.2))) :
    Real.circleAverage
        (fun x : ℂ ↦ Real.circleAverage (fun η : ℂ ↦ K x η) 0 1) 0 1 =
      Real.circleAverage
        (fun η : ℂ ↦ Real.circleAverage (fun x : ℂ ↦ K x η) 0 1) 0 1 := by
  let F : ℝ → ℝ → ℝ := fun θ φ ↦
    K (circleMap 0 1 θ) (circleMap 0 1 φ)
  have hFcont' : Continuous (fun z : ℝ × ℝ ↦ F z.1 z.2) := by
    simpa [F] using hFcont
  have hFint :
      IntegrableOn F.uncurry
        (uIoc (0 : ℝ) (2 * Real.pi) ×ˢ uIoc (0 : ℝ) (2 * Real.pi)) := by
    have hIcc : IntegrableOn F.uncurry
        (Icc ((0 : ℝ), (0 : ℝ)) (2 * Real.pi, 2 * Real.pi)) volume :=
      hFcont'.continuousOn.integrableOn_Icc
    apply hIcc.mono_set
    rintro ⟨θ, φ⟩ ⟨hθ, hφ⟩
    rw [uIoc_of_le Real.two_pi_pos.le] at hθ hφ
    have hθ' := Ioc_subset_Icc_self hθ
    have hφ' := Ioc_subset_Icc_self hφ
    exact ⟨⟨hθ'.1, hφ'.1⟩, ⟨hθ'.2, hφ'.2⟩⟩
  have hswap :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi), F θ φ) =
      ∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), F θ φ :=
    intervalIntegral_intervalIntegral_swap hFint
  unfold Real.circleAverage
  simp only [smul_eq_mul]
  change (2 * Real.pi)⁻¹ *
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        (2 * Real.pi)⁻¹ *
          (∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi), F θ φ)) =
    (2 * Real.pi)⁻¹ *
      (∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi),
        (2 * Real.pi)⁻¹ *
          (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), F θ φ))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hswap]

theorem circleAverage_poisson_one_add {w : ℂ} (hw : ‖w‖ < 1) :
    Real.circleAverage
      (poissonKernel 0 w • (fun z : ℂ ↦ (1 : ℂ) + z)) 0 1 =
    (1 : ℂ) + w := by
  have hf : DiffContOnCl ℂ (fun z : ℂ ↦ (1 : ℂ) + z)
      (Metric.ball 0 (1 : ℝ)) := by
    exact differentiable_id.const_add (1 : ℂ) |>.diffContOnCl
  have hwball : w ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball] using hw
  exact DiffContOnCl.circleAverage_poissonKernel_smul
    (f := fun z : ℂ ↦ (1 : ℂ) + z) (R := (1 : ℝ)) (w := w) (c := 0)
    hf hwball

theorem littlewood_chord_circleAverage_le_strict
    {W : ℂ → ℂ}
    (hW : DiffContOnCl ℂ W (Metric.ball 0 1))
    (hW0 : W 0 = 0)
    (hWdisk : ∀ x ∈ Metric.closedBall (0 : ℂ) 1, ‖W x‖ < 1) :
    Real.circleAverage (fun x : ℂ ↦ ‖(1 : ℂ) + W x‖) 0 1 ≤
      Real.circleAverage (fun η : ℂ ↦ ‖(1 : ℂ) + η‖) 0 1 := by
  let K : ℂ → ℂ → ℝ := fun x η ↦
    poissonKernel 0 (W x) η * ‖(1 : ℂ) + η‖
  have hWcircle : Continuous (fun θ : ℝ ↦ W (circleMap 0 1 θ)) := by
    apply hW.continuousOn_ball.comp_continuous (by fun_prop)
    intro θ
    exact Metric.sphere_subset_closedBall (by
      simpa only [abs_one] using (circleMap_mem_sphere' 0 1 θ))
  have hWcircle_lt : ∀ θ : ℝ, ‖W (circleMap 0 1 θ)‖ < 1 := by
    intro θ
    apply hWdisk
    exact Metric.sphere_subset_closedBall (by
      simpa only [abs_one] using (circleMap_mem_sphere' 0 1 θ))
  have hneq : ∀ θ φ : ℝ,
      circleMap 0 1 φ - W (circleMap 0 1 θ) ≠ 0 := by
    intro θ φ hzero
    have heq : circleMap 0 1 φ = W (circleMap 0 1 θ) := sub_eq_zero.mp hzero
    have hnorm : ‖circleMap 0 1 φ‖ = 1 := by
      simp
    rw [heq] at hnorm
    linarith [hWcircle_lt θ]
  have hFcont : Continuous (fun z : ℝ × ℝ ↦
      K (circleMap 0 1 z.1) (circleMap 0 1 z.2)) := by
    have hc2 : Continuous (fun z : ℝ × ℝ ↦ circleMap 0 1 z.2) := by
      fun_prop
    have hw1 : Continuous (fun z : ℝ × ℝ ↦ W (circleMap 0 1 z.1)) :=
      hWcircle.comp continuous_fst
    have hnum : Continuous (fun z : ℝ × ℝ ↦
        ‖circleMap 0 1 z.2‖ ^ 2 - ‖W (circleMap 0 1 z.1)‖ ^ 2) :=
      hc2.norm.pow 2 |>.sub (hw1.norm.pow 2)
    have hden : Continuous (fun z : ℝ × ℝ ↦
        ‖circleMap 0 1 z.2 - W (circleMap 0 1 z.1)‖ ^ 2) :=
      (hc2.sub hw1).norm.pow 2
    have hden0 : ∀ z : ℝ × ℝ,
        ‖circleMap 0 1 z.2 - W (circleMap 0 1 z.1)‖ ^ 2 ≠ 0 := by
      intro z
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hneq z.1 z.2))
    dsimp only [K, poissonKernel]
    simp only [sub_zero]
    change Continuous (fun z : ℝ × ℝ ↦
      (‖circleMap 0 1 z.2‖ ^ 2 - ‖W (circleMap 0 1 z.1)‖ ^ 2) /
        ‖circleMap 0 1 z.2 - W (circleMap 0 1 z.1)‖ ^ 2 *
          ‖(1 : ℂ) + circleMap 0 1 z.2‖)
    exact (hnum.div hden hden0).mul ((continuous_const.add hc2).norm)
  have hpoint : ∀ x ∈ Metric.sphere (0 : ℂ) 1,
      ‖(1 : ℂ) + W x‖ ≤ Real.circleAverage (fun η : ℂ ↦ K x η) 0 1 := by
    intro x hx
    have hxclosed : x ∈ Metric.closedBall (0 : ℂ) 1 :=
      Metric.sphere_subset_closedBall hx
    have hwlt : ‖W x‖ < 1 := hWdisk x hxclosed
    have hpoisson :
        Real.circleAverage
          (poissonKernel 0 (W x) • (fun z : ℂ ↦ (1 : ℂ) + z)) 0 1 =
        (1 : ℂ) + W x := by
      exact circleAverage_poisson_one_add hwlt
    calc
      ‖(1 : ℂ) + W x‖ =
          ‖Real.circleAverage
            (poissonKernel 0 (W x) • (fun z : ℂ ↦ (1 : ℂ) + z)) 0 1‖ := by
            rw [hpoisson]
      _ ≤ Real.circleAverage
          (fun η : ℂ ↦
            ‖(poissonKernel 0 (W x) • (fun z : ℂ ↦ (1 : ℂ) + z)) η‖) 0 1 :=
            norm_circleAverage_le_circleAverage_norm _ _ _
      _ = Real.circleAverage (fun η : ℂ ↦ K x η) 0 1 := by
            apply Real.circleAverage_congr_sphere
            intro η hη
            have hη' : η ∈ Metric.sphere (0 : ℂ) 1 := by
              simpa only [abs_one] using hη
            change ‖poissonKernel 0 (W x) η • ((1 : ℂ) + η)‖ =
              poissonKernel 0 (W x) η * ‖(1 : ℂ) + η‖
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (circleAverage_poissonKernel_nonneg hwlt η hη')]
  have hleftInt : CircleIntegrable (fun x : ℂ ↦ ‖(1 : ℂ) + W x‖) 0 1 := by
    unfold CircleIntegrable
    exact ((continuous_const.add hWcircle).norm.intervalIntegrable _ _)
  have hrightInt :
      CircleIntegrable
        (fun x : ℂ ↦ Real.circleAverage (fun η : ℂ ↦ K x η) 0 1) 0 1 := by
    unfold CircleIntegrable
    unfold Real.circleAverage
    simp only [smul_eq_mul]
    have hA : Continuous (fun θ : ℝ ↦
        ∫ φ : ℝ in (0 : ℝ)..(2 * Real.pi),
          K (circleMap 0 1 θ) (circleMap 0 1 φ)) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun θ φ : ℝ ↦ K (circleMap 0 1 θ) (circleMap 0 1 φ))
        hFcont 0 (2 * Real.pi)
    exact (hA.const_mul _).intervalIntegrable _ _
  calc
    Real.circleAverage (fun x : ℂ ↦ ‖(1 : ℂ) + W x‖) 0 1 ≤
        Real.circleAverage
          (fun x : ℂ ↦ Real.circleAverage (fun η : ℂ ↦ K x η) 0 1) 0 1 := by
          apply Real.circleAverage_mono hleftInt hrightInt
          simpa only [abs_one] using hpoint
    _ = Real.circleAverage
          (fun η : ℂ ↦ Real.circleAverage (fun x : ℂ ↦ K x η) 0 1) 0 1 :=
            circleAverage_circleAverage_swap_of_continuous_circle hFcont
    _ = Real.circleAverage (fun η : ℂ ↦ ‖(1 : ℂ) + η‖) 0 1 := by
          apply Real.circleAverage_congr_sphere
          intro η hη
          have hη' : η ∈ Metric.sphere (0 : ℂ) 1 := by
            simpa only [abs_one] using hη
          have hkernel := circleAverage_poisson_comp_eq_one hW hW0 hWdisk hη'
          calc
            Real.circleAverage (fun x : ℂ ↦ K x η) 0 1 =
                Real.circleAverage
                  (fun x : ℂ ↦ poissonKernel 0 (W x) η * ‖(1 : ℂ) + η‖) 0 1 := rfl
            _ = ‖(1 : ℂ) + η‖ *
                Real.circleAverage (fun x : ℂ ↦ poissonKernel 0 (W x) η) 0 1 := by
                  calc
                    Real.circleAverage
                        (fun x : ℂ ↦ poissonKernel 0 (W x) η * ‖(1 : ℂ) + η‖) 0 1 =
                        Real.circleAverage
                          (fun x : ℂ ↦ ‖(1 : ℂ) + η‖ *
                            poissonKernel 0 (W x) η) 0 1 := by
                          apply Real.circleAverage_congr_sphere
                          intro x hx
                          change poissonKernel 0 (W x) η * ‖(1 : ℂ) + η‖ =
                            ‖(1 : ℂ) + η‖ * poissonKernel 0 (W x) η
                          rw [mul_comm]
                    _ = ‖(1 : ℂ) + η‖ *
                        Real.circleAverage
                          (fun x : ℂ ↦ poissonKernel 0 (W x) η) 0 1 := by
                          simpa only [smul_eq_mul] using
                            (Real.circleAverage_fun_smul
                              (a := ‖(1 : ℂ) + η‖)
                              (f := fun x : ℂ ↦ poissonKernel 0 (W x) η)
                              (c := (0 : ℂ)) (R := (1 : ℝ)))
            _ = ‖(1 : ℂ) + η‖ := by rw [hkernel, mul_one]

theorem littlewood_chord_interval_le_strict
    {W : ℂ → ℂ}
    (hW : DiffContOnCl ℂ W (Metric.ball 0 1))
    (hW0 : W 0 = 0)
    (hWdisk : ∀ x ∈ Metric.closedBall (0 : ℂ) 1, ‖W x‖ < 1) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ‖(1 : ℂ) + W (circleMap 0 1 θ)‖) ≤
    ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ‖(1 : ℂ) + circleMap 0 1 θ‖ := by
  have h := littlewood_chord_circleAverage_le_strict hW hW0 hWdisk
  unfold Real.circleAverage at h
  simp only [smul_eq_mul] at h
  exact (mul_le_mul_iff_of_pos_left (inv_pos.mpr Real.two_pi_pos)).mp h

/-! ### The reciprocal quotient for unit-circle roots -/

theorem isRoot_conjReflect_imp_isRoot_star_inv
    {r : Polynomial ℂ} {N : ℕ} (hdeg : r.natDegree ≤ N)
    {z : ℂ} (hz0 : z ≠ 0)
    (hz : (Erdos1215.conjReflect N r).IsRoot z) :
    r.IsRoot (star z)⁻¹ := by
  have hstarz0 : star z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz0
  let : Invertible (star z) := invertibleOfNonzero hstarz0
  have hmapzero :
      ((Erdos1215.conjReflect N r).map (starRingEnd ℂ)).eval (star z) = 0 := by
    simpa using congrArg (starRingEnd ℂ) hz.eq_zero
  have hreflect :
      (Erdos1215.conjReflect N (Erdos1215.conjReflect N r)).eval
          (star z)⁻¹ = 0 := by
    have hiff := Polynomial.eval₂_reflect_eq_zero_iff (RingHom.id ℂ)
      (star z) N
      ((Erdos1215.conjReflect N r).map (starRingEnd ℂ))
      (Polynomial.natDegree_map_le.trans
        (by
          dsimp [Erdos1215.conjReflect]
          calc
            (Polynomial.reflect N (r.map (starRingEnd ℂ))).natDegree ≤
                max N (r.map (starRingEnd ℂ)).natDegree :=
              Polynomial.natDegree_reflect_le
            _ = N := max_eq_left (Polynomial.natDegree_map_le.trans hdeg)))
    rw [invOf_eq_inv] at hiff
    exact hiff.mpr hmapzero
  rw [Erdos1215.conjReflect_conjReflect] at hreflect
  exact hreflect

theorem derivative_roots_in_closed_disk
    {p : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hdeg : p.natDegree = n)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ ≤ 1)
    {a : ℂ} (ha : p.derivative.IsRoot a) :
    ‖a‖ ≤ 1 := by
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp] at hdeg
    simp at hdeg
    omega
  have hdegree : 0 < p.degree := by
    rw [p.degree_eq_natDegree hp0, hdeg]
    exact_mod_cast hn
  have haSet : a ∈ p.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    constructor
    · exact Polynomial.derivative_ne_zero.mpr (by rw [hdeg]; omega)
    · simpa using ha.eq_zero
  have haHull :
      a ∈ convexHull ℝ (p.rootSet ℂ) :=
    Polynomial.rootSet_derivative_subset_convexHull_rootSet hdegree haSet
  have hsubset : p.rootSet ℂ ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro b hb
    have hbroot : p.IsRoot b := by
      rw [Polynomial.mem_rootSet] at hb
      simpa using hb.2
    simpa [Metric.mem_closedBall] using hroots b hbroot
  have haBall : a ∈ Metric.closedBall (0 : ℂ) 1 :=
    convexHull_min hsubset (convex_closedBall (0 : ℂ) 1) haHull
  simpa [Metric.mem_closedBall] using haBall

theorem conjReflect_derivative_eval_ne_zero_on_open_disk
    {p : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hdeg : p.natDegree = n)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (Erdos1215.conjReflect (n - 1) p.derivative).eval z ≠ 0 := by
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp] at hdeg
    simp at hdeg
    omega
  have hpcoeff : p.coeff n ≠ 0 := by
    rw [← hdeg]
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0
  by_cases hz0 : z = 0
  · subst z
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    rw [coeff_conjReflect_of_le (n - 1) p.derivative 0 (Nat.zero_le _)]
    simp only [Nat.sub_zero, Polynomial.coeff_derivative]
    have hidx : n - 1 + 1 = n := by omega
    rw [hidx]
    have hcast : ((n - 1 : ℕ) : ℂ) + 1 ≠ 0 := by
      exact_mod_cast (by omega : (n - 1 : ℕ) + 1 ≠ 0)
    simp [hpcoeff, hcast]
  · intro hzero
    have hrootstar : p.derivative.IsRoot (star z)⁻¹ :=
      isRoot_conjReflect_imp_isRoot_star_inv
        (by rw [Polynomial.natDegree_derivative, hdeg]) hz0 hzero
    have hle := derivative_roots_in_closed_disk hn hdeg hroots hrootstar
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hgt : 1 < ‖(star z)⁻¹‖ := by
      rw [norm_inv, norm_star]
      exact one_lt_inv₀ hzpos |>.2 hz
    linarith

noncomputable def malikAuxiliary (n : ℕ) (p : Polynomial ℂ) (z : ℂ) : ℂ :=
  z * (Erdos1215.conjReflect n p).derivative.eval z /
    (Erdos1215.conjReflect (n - 1) p.derivative).eval z

theorem re_z_div_sub_le_half {a z : ℂ} (ha : ‖a‖ = 1)
    (hz : ‖z‖ < 1) :
    (z / (z - a)).re ≤ (1 / 2 : ℝ) := by
  have hza : a ≠ z := by
    intro h
    rw [h] at ha
    linarith
  have hbase := half_le_re_z_div_sub hz.le ha hza
  have hid : z / (z - a) = 1 - a / (a - z) := by
    field_simp
    ring
  rw [hid]
  norm_num at hbase ⊢
  linarith

theorem norm_log_derivative_le_complement_of_roots_on_circle
    {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree = n) (hp0 : p ≠ 0)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖z * (p.derivative.eval z / p.eval z)‖ ≤
      ‖(n : ℂ) - z * (p.derivative.eval z / p.eval z)‖ := by
  have hzp : p.eval z ≠ 0 := by
    intro hz0
    have := hroots z hz0
    linarith
  rw [root_log_sum_identity hp0 hzp]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.sq_norm]
  have hcard : p.roots.card = n := by
    rw [← hdeg]
    exact (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hsum : ((p.roots.map fun a => z / (z - a)).sum).re ≤
      (n : ℝ) / 2 := by
    have hle : (p.roots.map fun a => (z / (z - a)).re).sum ≤
        (p.roots.map fun _a => (1 / 2 : ℝ)).sum := by
      apply multiset_sum_le_sum_of_forall
      intro a ha
      apply re_z_div_sub_le_half
      · apply hroots a
        exact (Polynomial.mem_roots hp0).mp ha
      · exact hz
    have hre : ((p.roots.map fun a => z / (z - a)).sum).re =
        (p.roots.map fun a => (z / (z - a)).re).sum := by
      induction p.roots using Multiset.induction_on with
      | empty => simp
      | cons a m ih => simp [ih]
    rw [hre]
    rw [show (p.roots.map fun _a => (1 / 2 : ℝ)).sum =
        p.roots.card * (1 / 2 : ℝ) by simp] at hle
    rw [hcard] at hle
    norm_num at hle ⊢
    linarith
  norm_num [Complex.normSq] at hsum ⊢
  nlinarith

theorem malikAuxiliary_norm_le_one_on_open_disk
    {p : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hdeg : p.natDegree = n) (hp0 : p ≠ 0)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖malikAuxiliary n p z‖ ≤ 1 := by
  obtain ⟨lam, hlam, hself⟩ :=
    conjReflect_eq_scalar_mul_of_roots_on_circle hdeg hp0 hroots
  have hderiv :
      (Erdos1215.conjReflect n p).derivative.eval z =
        lam * p.derivative.eval z := by
    rw [hself]
    simp
  have hrel := conjReflect_derivative_relation hn p hdeg.le
  have heval := congrArg (fun r : Polynomial ℂ => r.eval z) hrel
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at heval
  have hden :
      (Erdos1215.conjReflect (n - 1) p.derivative).eval z =
        lam * ((n : ℂ) * p.eval z - z * p.derivative.eval z) := by
    rw [← heval, hself]
    simp
    ring
  have hzp : p.eval z ≠ 0 := by
    intro hz0
    have := hroots z hz0
    linarith
  have hlog := norm_log_derivative_le_complement_of_roots_on_circle
    hdeg hp0 hroots hz
  have hmul := mul_le_mul_of_nonneg_right hlog (norm_nonneg (p.eval z))
  have hleft :
      ‖z * (p.derivative.eval z / p.eval z)‖ * ‖p.eval z‖ =
        ‖z * p.derivative.eval z‖ := by
    rw [← norm_mul]
    congr 1
    field_simp
  have hright :
      ‖(n : ℂ) - z * (p.derivative.eval z / p.eval z)‖ * ‖p.eval z‖ =
        ‖(n : ℂ) * p.eval z - z * p.derivative.eval z‖ := by
    rw [← norm_mul]
    congr 1
    field_simp
  rw [hleft, hright] at hmul
  have hden0 :
      (Erdos1215.conjReflect (n - 1) p.derivative).eval z ≠ 0 :=
    conjReflect_derivative_eval_ne_zero_on_open_disk hn hdeg
      (fun a ha => (hroots a ha).le) hz
  have hdenpos :
      0 < ‖(Erdos1215.conjReflect (n - 1) p.derivative).eval z‖ :=
    norm_pos_iff.mpr hden0
  rw [malikAuxiliary, norm_div, hderiv]
  simp only [norm_mul]
  rw [hlam]
  simp only [one_mul]
  apply (div_le_iff₀ hdenpos).2
  rw [one_mul, hden, norm_mul, hlam, one_mul]
  simpa [norm_mul] using hmul

theorem differentiableOn_malikAuxiliary
    {p : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hdeg : p.natDegree = n)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ = 1) :
    DifferentiableOn ℂ (malikAuxiliary n p) (Metric.ball 0 1) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
  have hden :
      (Erdos1215.conjReflect (n - 1) p.derivative).eval z ≠ 0 :=
    conjReflect_derivative_eval_ne_zero_on_open_disk hn hdeg
      (fun a ha => (hroots a ha).le) hz'
  unfold malikAuxiliary
  exact
    ((differentiableAt_id.mul
      (Erdos1215.conjReflect n p).derivative.differentiableAt).div
        (Erdos1215.conjReflect (n - 1) p.derivative).differentiableAt hden).differentiableWithinAt

theorem malikAuxiliary_zero
    {p : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hdeg : p.natDegree = n)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ = 1) :
    malikAuxiliary n p 0 = 0 := by
  have hden :
      (Erdos1215.conjReflect (n - 1) p.derivative).eval 0 ≠ 0 :=
    conjReflect_derivative_eval_ne_zero_on_open_disk hn hdeg
      (fun a ha => (hroots a ha).le) (by simp)
  simp [malikAuxiliary]

theorem malikAuxiliary_norm_le_norm_on_open_disk
    {p : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hdeg : p.natDegree = n) (hp0 : p ≠ 0)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖malikAuxiliary n p z‖ ≤ ‖z‖ := by
  apply Complex.norm_le_norm_of_mapsTo_ball
    (differentiableOn_malikAuxiliary hn hdeg hroots)
  · intro w hw
    have hw' : ‖w‖ < 1 := by simpa [Metric.mem_ball] using hw
    have hle := malikAuxiliary_norm_le_one_on_open_disk hn hdeg hp0 hroots hw'
    simpa [Metric.mem_closedBall] using hle
  · exact malikAuxiliary_zero hn hdeg hroots
  · exact hz

theorem diffContOnCl_radial_malikAuxiliary
    {p : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hdeg : p.natDegree = n)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ = 1)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    DiffContOnCl ℂ
      (fun z : ℂ ↦ malikAuxiliary n p ((ρ : ℂ) * z))
      (Metric.ball 0 1) := by
  have hden : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      (Erdos1215.conjReflect (n - 1) p.derivative).eval ((ρ : ℂ) * z) ≠ 0 := by
    intro z hz
    apply conjReflect_derivative_eval_ne_zero_on_open_disk hn hdeg
      (fun a ha => (hroots a ha).le)
    have hzle : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
    nlinarith [mul_le_mul_of_nonneg_left hzle hρ0]
  apply DiffContOnCl.mk_ball
  · intro z hz
    have hzcl : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      Metric.ball_subset_closedBall hz
    unfold malikAuxiliary
    exact
      (((differentiableAt_const (c := (ρ : ℂ))).mul differentiableAt_id).mul
        ((Erdos1215.conjReflect n p).derivative.differentiableAt.comp z
          ((differentiableAt_const (c := (ρ : ℂ))).mul differentiableAt_id))).div
        ((Erdos1215.conjReflect (n - 1) p.derivative).differentiableAt.comp z
          ((differentiableAt_const (c := (ρ : ℂ))).mul differentiableAt_id))
        (hden z hzcl) |>.differentiableWithinAt
  · unfold malikAuxiliary
    fun_prop (disch := aesop (config := { warnOnNonterminal := false }))

theorem radial_malikAuxiliary_norm_lt_one
    {p : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hdeg : p.natDegree = n) (hp0 : p ≠ 0)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ = 1)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    ‖malikAuxiliary n p ((ρ : ℂ) * z)‖ < 1 := by
  have hzle : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hz
  have hy : ‖(ρ : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
    nlinarith [mul_le_mul_of_nonneg_left hzle hρ0]
  calc
    ‖malikAuxiliary n p ((ρ : ℂ) * z)‖ ≤ ‖(ρ : ℂ) * z‖ :=
      malikAuxiliary_norm_le_norm_on_open_disk hn hdeg hp0 hroots hy
    _ = ρ * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
    _ ≤ ρ := by nlinarith [mul_le_mul_of_nonneg_left hzle hρ0]
    _ < 1 := hρ1

/-! ### Boundary passage and the final theorem -/

theorem ae_eval_ne_zero_circle
    {D : Polynomial ℂ} (hD : D ≠ 0) :
    ∀ᵐ θ : ℝ ∂volume, θ ∈ uIoc (0 : ℝ) (2 * Real.pi) →
      D.eval (circleMap 0 1 θ) ≠ 0 := by
  have hbad : {z : ℂ | D.eval z = 0}.Finite := by
    apply D.roots.finite_toSet.subset
    intro z hz
    exact (Polynomial.mem_roots hD).mpr hz
  have hgoodCircle :
      ∀ᶠ z : ℂ in Filter.codiscreteWithin (Metric.sphere (0 : ℂ) |(1 : ℝ)|),
        D.eval z ≠ 0 := by
    have hmem :
        {z : ℂ | D.eval z = 0}ᶜ ∈
          Filter.codiscreteWithin (Metric.sphere (0 : ℂ) |(1 : ℝ)|) :=
      compl_finite_mem_codiscreteWithin hbad
    change {z : ℂ | D.eval z ≠ 0} ∈
      Filter.codiscreteWithin (Metric.sphere (0 : ℂ) |(1 : ℝ)|)
    exact hmem
  have hgoodAngles :
      ∀ᶠ θ : ℝ in Filter.codiscreteWithin (uIoc (0 : ℝ) (2 * Real.pi)),
        D.eval (circleMap 0 1 θ) ≠ 0 := by
    have hpre := circleMap_preimage_codiscrete one_ne_zero hgoodCircle
    have hpre' : ∀ᶠ θ : ℝ in Filter.codiscrete ℝ,
        D.eval (circleMap 0 1 θ) ≠ 0 := by
      exact hpre
    exact Filter.Eventually.filter_mono
      (Filter.codiscreteWithin_mono (by tauto)) hpre'
  rw [← ae_restrict_iff' measurableSet_uIoc]
  exact ae_restrict_le_codiscreteWithin measurableSet_uIoc hgoodAngles

theorem rho_nonneg (k : ℕ) :
    0 ≤ (1 : ℝ) - 1 / ((k : ℝ) + 1) := by
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by norm_num
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hdiv : 1 / ((k : ℝ) + 1) ≤ 1 := (div_le_iff₀ hkpos).2 (by linarith)
  linarith

theorem rho_lt_one (k : ℕ) :
    (1 : ℝ) - 1 / ((k : ℝ) + 1) < 1 := by
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have : 0 < 1 / ((k : ℝ) + 1) := by positivity
  linarith

theorem tendsto_rho :
    Tendsto (fun k : ℕ ↦ (1 : ℝ) - 1 / ((k : ℝ) + 1))
      Filter.atTop (𝓝 1) := by
  simpa using
    (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

theorem circleAverage_malikAuxiliary_le_chord
    {p : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hdeg : p.natDegree = n) (hp0 : p ≠ 0)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ = 1) :
    IntervalIntegrable
        (fun θ : ℝ ↦ ‖(1 : ℂ) +
          malikAuxiliary n p (circleMap 0 1 θ)‖)
        volume 0 (2 * Real.pi) ∧
      Real.circleAverage
        (fun z : ℂ ↦ ‖(1 : ℂ) + malikAuxiliary n p z‖) 0 1 ≤
      Real.circleAverage (fun z : ℂ ↦ ‖(1 : ℂ) + z‖) 0 1 := by
  let ρ : ℕ → ℝ := fun k ↦ 1 - 1 / ((k : ℝ) + 1)
  let F : ℕ → ℝ → ℝ := fun k θ ↦
    ‖(1 : ℂ) + malikAuxiliary n p ((ρ k : ℂ) * circleMap 0 1 θ)‖
  let f : ℝ → ℝ := fun θ ↦
    ‖(1 : ℂ) + malikAuxiliary n p (circleMap 0 1 θ)‖
  let C : ℝ := ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
    ‖(1 : ℂ) + circleMap 0 1 θ‖
  have hρ0 : ∀ k, 0 ≤ ρ k := by
    intro k
    simpa [ρ] using rho_nonneg k
  have hρ1 : ∀ k, ρ k < 1 := by
    intro k
    simpa [ρ] using rho_lt_one k
  have hWr (k : ℕ) :
      DiffContOnCl ℂ
        (fun z : ℂ ↦ malikAuxiliary n p ((ρ k : ℂ) * z))
        (Metric.ball 0 1) :=
    diffContOnCl_radial_malikAuxiliary hn hdeg hroots (hρ0 k) (hρ1 k)
  have hWr0 (k : ℕ) :
      (fun z : ℂ ↦ malikAuxiliary n p ((ρ k : ℂ) * z)) 0 = 0 := by
    simp [malikAuxiliary_zero hn hdeg hroots]
  have hWrdisk (k : ℕ) :
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        ‖malikAuxiliary n p ((ρ k : ℂ) * z)‖ < 1 := by
    intro z hz
    exact radial_malikAuxiliary_norm_lt_one hn hdeg hp0 hroots
      (hρ0 k) (hρ1 k) hz
  have hmean (k : ℕ) :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), F k θ) ≤ C := by
    simpa [F, C] using
      (littlewood_chord_interval_le_strict (hWr k) (hWr0 k) (hWrdisk k))
  have hD0 :
      (Erdos1215.conjReflect (n - 1) p.derivative) ≠ 0 := by
    intro hzero
    have hval :
        (Erdos1215.conjReflect (n - 1) p.derivative).eval 0 ≠ 0 :=
      conjReflect_derivative_eval_ne_zero_on_open_disk hn hdeg
        (fun a ha => (hroots a ha).le) (by simp)
    rw [hzero] at hval
    simp at hval
  have hgood :
      ∀ᵐ θ : ℝ ∂volume, θ ∈ uIoc (0 : ℝ) (2 * Real.pi) →
        (Erdos1215.conjReflect (n - 1) p.derivative).eval
          (circleMap 0 1 θ) ≠ 0 :=
    ae_eval_ne_zero_circle hD0
  have hFmeasAll :
      ∀ k : ℕ, AEStronglyMeasurable (F k)
          (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))) := by
    intro k
    have hcircle :
        Continuous (fun θ : ℝ ↦
          malikAuxiliary n p ((ρ k : ℂ) * circleMap 0 1 θ)) := by
      apply (hWr k).continuousOn_ball.comp_continuous (by fun_prop)
      intro θ
      exact Metric.sphere_subset_closedBall (by
        simpa only [abs_one] using (circleMap_mem_sphere' 0 1 θ))
    have hcont : Continuous (F k) := by
      dsimp [F]
      exact (continuous_const.add hcircle).norm
    exact hcont.aestronglyMeasurable
  have hFmeas :
      ∀ᶠ k : ℕ in Filter.atTop,
        AEStronglyMeasurable (F k)
          (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))) :=
    Filter.Eventually.of_forall hFmeasAll
  have hboundAll :
      ∀ k : ℕ, ∀ θ : ℝ,
        θ ∈ uIoc (0 : ℝ) (2 * Real.pi) → ‖F k θ‖ ≤ (2 : ℝ) := by
    intro k θ hθ
    have hnorm :
        ‖malikAuxiliary n p ((ρ k : ℂ) * circleMap 0 1 θ)‖ < 1 := by
      apply hWrdisk k
      exact Metric.sphere_subset_closedBall (by
        simpa only [abs_one] using (circleMap_mem_sphere' 0 1 θ))
    dsimp [F]
    rw [abs_of_nonneg (norm_nonneg _)]
    calc
      ‖(1 : ℂ) + malikAuxiliary n p ((ρ k : ℂ) * circleMap 0 1 θ)‖
          ≤ ‖(1 : ℂ)‖ +
            ‖malikAuxiliary n p ((ρ k : ℂ) * circleMap 0 1 θ)‖ :=
            norm_add_le _ _
      _ ≤ 2 := by norm_num; linarith
  have hbound :
      ∀ᶠ k : ℕ in Filter.atTop, ∀ᵐ θ : ℝ ∂volume,
        θ ∈ uIoc (0 : ℝ) (2 * Real.pi) → ‖F k θ‖ ≤ (2 : ℝ) :=
    Filter.Eventually.of_forall fun k =>
      Filter.Eventually.of_forall fun θ hθ => hboundAll k θ hθ
  have hlim :
      ∀ᵐ θ : ℝ ∂volume, θ ∈ uIoc (0 : ℝ) (2 * Real.pi) →
        Tendsto (fun k : ℕ ↦ F k θ) Filter.atTop (𝓝 (f θ)) := by
    filter_upwards [hgood] with θ hθ hden
    have harg :
        Tendsto (fun k : ℕ ↦ (ρ k : ℂ) * circleMap 0 1 θ)
          Filter.atTop (𝓝 (circleMap 0 1 θ)) := by
      have hρ : Tendsto ρ Filter.atTop (𝓝 (1 : ℝ)) := by
        simpa [ρ] using tendsto_rho
      have hρC : Tendsto (fun k : ℕ ↦ (ρ k : ℂ))
          Filter.atTop (𝓝 (1 : ℂ)) :=
        (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hρ
      simpa using hρC.mul tendsto_const_nhds
    have hWcont : ContinuousAt (malikAuxiliary n p) (circleMap 0 1 θ) := by
      unfold malikAuxiliary
      fun_prop (disch := aesop)
    dsimp [F, f]
    exact ((hWcont.tendsto.comp harg).const_add (1 : ℂ)).norm
  have hDCT :
      Tendsto (fun k : ℕ ↦ ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), F k θ)
        Filter.atTop
        (𝓝 (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ)) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ : ℝ ↦ (2 : ℝ)) hFmeas hbound intervalIntegrable_const hlim
  have hlimRestrict :
      ∀ᵐ θ : ℝ ∂volume.restrict (uIoc (0 : ℝ) (2 * Real.pi)),
        Tendsto (fun k : ℕ ↦ F k θ) Filter.atTop (𝓝 (f θ)) := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    exact hlim
  have hfmeas :
      AEStronglyMeasurable f
        (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))) :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop hFmeasAll hlimRestrict
  have hfbound :
      ∀ᵐ θ : ℝ ∂volume.restrict (uIoc (0 : ℝ) (2 * Real.pi)),
        ‖f θ‖ ≤ (2 : ℝ) := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hlim] with θ hθlim
    intro hθ
    apply le_of_tendsto (hθlim hθ).norm
    exact Filter.Eventually.of_forall fun k => hboundAll k θ hθ
  have hfintOn :
      IntegrableOn f (uIoc (0 : ℝ) (2 * Real.pi)) volume := by
    apply Integrable.mono'
      (show Integrable (fun _ : ℝ ↦ (2 : ℝ))
          (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))) by
        exact intervalIntegrable_iff.mp intervalIntegrable_const)
      hfmeas hfbound
  have hfint : IntervalIntegrable f volume 0 (2 * Real.pi) :=
    intervalIntegrable_iff.mpr hfintOn
  have hintle :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) ≤ C :=
    le_of_tendsto hDCT (Filter.Eventually.of_forall hmean)
  refine ⟨?_, ?_⟩
  · simpa [f] using hfint
  · unfold Real.circleAverage
    simp only [smul_eq_mul]
    apply (mul_le_mul_iff_of_pos_left (inv_pos.mpr Real.two_pi_pos)).2
    simpa [f, C] using hintle

theorem malik_boundary_pointwise_le
    {p : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hdeg : p.natDegree = n) (hp0 : p ≠ 0)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ = 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (n : ℝ) * ‖p.eval z‖ ≤
      ‖(1 : ℂ) + malikAuxiliary n p z‖ * ‖p.derivative.eval z‖ := by
  obtain ⟨lam, hlam, hself⟩ :=
    conjReflect_eq_scalar_mul_of_roots_on_circle hdeg hp0 hroots
  have hlam0 : lam ≠ 0 := norm_ne_zero_iff.mp (by simp [hlam])
  have hrel := conjReflect_derivative_relation hn p hdeg.le
  have heval := congrArg (fun r : Polynomial ℂ => r.eval z) hrel
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at heval
  have hdeneq :
      (Erdos1215.conjReflect (n - 1) p.derivative).eval z =
        lam * ((n : ℂ) * p.eval z - z * p.derivative.eval z) := by
    rw [← heval, hself]
    simp
    ring
  have hderivdeg : p.derivative.natDegree = n - 1 := by
    rw [Polynomial.natDegree_derivative, hdeg]
  have hdennorm :
      ‖(Erdos1215.conjReflect (n - 1) p.derivative).eval z‖ =
        ‖p.derivative.eval z‖ := by
    simpa [hderivdeg] using
      (Erdos1215.norm_conjReflect_eval_of_norm_eq_one p.derivative hz)
  by_cases hden0 :
      (Erdos1215.conjReflect (n - 1) p.derivative).eval z = 0
  · have hpder0 : p.derivative.eval z = 0 := by
      apply norm_eq_zero.mp
      rw [← hdennorm, hden0]
      simp
    have hcomp0 : (n : ℂ) * p.eval z - z * p.derivative.eval z = 0 := by
      have hmul0 :
          lam * ((n : ℂ) * p.eval z - z * p.derivative.eval z) = 0 := by
        rw [← hdeneq, hden0]
      exact (mul_eq_zero.mp hmul0).resolve_left hlam0
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    have hpz0 : p.eval z = 0 := by
      rw [hpder0, mul_zero, sub_zero] at hcomp0
      exact (mul_eq_zero.mp hcomp0).resolve_left hnC
    simp [hpz0, hpder0]
  · have hone :
        (1 : ℂ) + malikAuxiliary n p z =
          (n : ℂ) * (Erdos1215.conjReflect n p).eval z /
            (Erdos1215.conjReflect (n - 1) p.derivative).eval z := by
      unfold malikAuxiliary
      field_simp
      rw [← heval]
      ring
    have hqnorm :
        ‖(Erdos1215.conjReflect n p).eval z‖ = ‖p.eval z‖ := by
      simpa [hdeg] using Erdos1215.norm_conjReflect_eval_of_norm_eq_one p hz
    have hnormeq :
        ‖(1 : ℂ) + malikAuxiliary n p z‖ *
            ‖(Erdos1215.conjReflect (n - 1) p.derivative).eval z‖ =
          (n : ℝ) * ‖p.eval z‖ := by
      rw [hone, norm_div, norm_mul, Complex.norm_natCast, hqnorm]
      field_simp
    rw [← hdennorm]
    exact hnormeq.symm.le

theorem integral_norm_one_add_malikAuxiliary_le_eight
    {p : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hdeg : p.natDegree = n) (hp0 : p ≠ 0)
    (hroots : ∀ a : ℂ, p.IsRoot a → ‖a‖ = 1) :
    IntervalIntegrable
        (fun θ : ℝ ↦ ‖(1 : ℂ) +
          malikAuxiliary n p
            (Complex.exp (Complex.I * (θ : ℂ)))‖)
        volume 0 (2 * Real.pi) ∧
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ‖(1 : ℂ) + malikAuxiliary n p
          (Complex.exp (Complex.I * (θ : ℂ)))‖) ≤ 8 := by
  obtain ⟨hint, hmean⟩ :=
    circleAverage_malikAuxiliary_le_chord hn hdeg hp0 hroots
  have hmeans :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ‖(1 : ℂ) + malikAuxiliary n p (circleMap 0 1 θ)‖) ≤
      ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ‖(1 : ℂ) + circleMap 0 1 θ‖ := by
    unfold Real.circleAverage at hmean
    simp only [smul_eq_mul] at hmean
    exact (mul_le_mul_iff_of_pos_left (inv_pos.mpr Real.two_pi_pos)).mp hmean
  have hchord :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ‖(1 : ℂ) + circleMap 0 1 θ‖) = 8 := by
    simpa [circleMap, mul_comm] using integral_norm_one_add_exp_I
  refine ⟨?_, ?_⟩
  · simpa [circleMap, mul_comm] using hint
  · rw [hchord] at hmeans
    simpa [circleMap, mul_comm] using hmeans

/-- Erdős Problem 225 in coefficient form.  The normalization hypothesis is
stated as an actual maximum-one condition: the pointwise upper bound and an
attaining angle. -/
theorem erdos_225
    (n : ℕ) (c : ℕ → ℂ) (hn : 0 < n) (hcn : c n ≠ 0) (hc0 : c 0 ≠ 0)
    (hroots : RootsOnUnitCircle (coeffPolynomial n c))
    (hmax :
      (∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
        ‖trigPolynomial n c θ‖ ≤ 1) ∧
      ∃ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
        ‖trigPolynomial n c θ‖ = 1) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ‖trigPolynomial n c θ‖) ≤ 4 := by
  let p : Polynomial ℂ := coeffPolynomial n c
  have hdeg : p.natDegree = n := by
    dsimp [p]
    exact natDegree_coeffPolynomial_eq n c hcn
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp] at hdeg
    simp at hdeg
    omega
  have hcoeff0 : p.coeff 0 ≠ 0 := by
    dsimp [p]
    simpa [coeffPolynomial] using hc0
  have hcircle : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ 1 := by
    intro z hz
    obtain ⟨θ, hθ, rfl⟩ := exists_angle_Icc_of_norm_eq_one hz
    rw [← trigPolynomial_eq_eval_exp]
    exact hmax.1 θ hθ
  have haux :=
    integral_norm_one_add_malikAuxiliary_le_eight hn hdeg hp0 hroots
  let W : ℝ → ℂ := fun θ ↦
    malikAuxiliary n p (Complex.exp (Complex.I * (θ : ℂ)))
  have hWint :
      IntervalIntegrable (fun θ : ℝ ↦ ‖(1 : ℂ) + W θ‖ * ((n : ℝ) / 2))
        volume 0 (2 * Real.pi) := by
    simpa [W] using haux.1.mul_const ((n : ℝ) / 2)
  have hWmean :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ‖(1 : ℂ) + W θ‖) ≤ 8 := by
    simpa [W] using haux.2
  have hpoint : ∀ θ : ℝ,
      (n : ℝ) * ‖trigPolynomial n c θ‖ ≤
        ‖(1 : ℂ) + W θ‖ * ((n : ℝ) / 2) := by
    intro θ
    let z : ℂ := Complex.exp (Complex.I * (θ : ℂ))
    have hz : ‖z‖ = 1 := by simp [z]
    have hboundary := malik_boundary_pointwise_le hn hdeg hp0 hroots hz
    have hlax :=
      norm_derivative_le_half_degree_of_roots_on_circle
        hn hdeg hp0 hcoeff0 hroots hcircle hz
    have hderiv : ‖p.derivative.eval z‖ ≤ (n : ℝ) / 2 := by
      linarith
    calc
      (n : ℝ) * ‖trigPolynomial n c θ‖ =
          (n : ℝ) * ‖p.eval z‖ := by
            rw [trigPolynomial_eq_eval_exp]
      _ ≤ ‖(1 : ℂ) + malikAuxiliary n p z‖ *
          ‖p.derivative.eval z‖ := hboundary
      _ ≤ ‖(1 : ℂ) + malikAuxiliary n p z‖ * ((n : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hderiv (norm_nonneg _)
      _ = ‖(1 : ℂ) + W θ‖ * ((n : ℝ) / 2) := by rfl
  have hmalik :
      (n : ℝ) * (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ‖trigPolynomial n c θ‖) ≤ 8 * ((n : ℝ) / 2) :=
    turanMalik_of_auxiliary (n := n) (trigPolynomial n c) W ((n : ℝ) / 2)
      (by positivity) (intervalIntegrable_norm_trigPolynomial n c) hWint hpoint hWmean
  apply integral_le_four_of_sharp_bounds hn (trigPolynomial n c) ((n : ℝ) / 2)
    hmalik
  ring_nf
  exact le_rfl

theorem erdos_225_of_onlyRealAngularRoots
    (n : ℕ) (c : ℕ → ℂ) (hn : 0 < n) (hcn : c n ≠ 0) (hc0 : c 0 ≠ 0)
    (hreal : OnlyRealAngularRoots n c)
    (hmax :
      (∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
        ‖trigPolynomial n c θ‖ ≤ 1) ∧
      ∃ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
        ‖trigPolynomial n c θ‖ = 1) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ‖trigPolynomial n c θ‖) ≤ 4 := by
  apply erdos_225 n c hn hcn hc0
  · exact onlyRealAngularRoots_rootsOnUnitCircle n c hc0 hreal
  · exact hmax

end Erdos225
