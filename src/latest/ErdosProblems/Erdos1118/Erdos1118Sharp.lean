/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos1118.Erdos1118Construction

/-!
# Quantitative chaplet approximation for Erdős Problem 1118

This file supplies the effective form of the pole-moving argument needed for the sharp
converse.  The central device is Newton improvement of a polynomial approximate reciprocal.
It squares the relative residual before every pole move, so a fixed-size relative move only
doubles the degree.  Consequently a chain of `L` moves costs degree exponential in `L`, which
is the correct scale after taking two logarithms of the maximum modulus.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace Erdos1118Sharp

/-- Relative error when `p` is used as a polynomial approximate inverse of `z - a`. -/
noncomputable def poleResidual (a z : ℂ) (p : Polynomial ℂ) : ℂ :=
  1 - (z - a) * p.eval z

/-- One Newton step for the reciprocal of the linear polynomial `X - a`. -/
noncomputable def poleNewton (a : ℂ) (p : Polynomial ℂ) : Polynomial ℂ :=
  p * (2 - (Polynomial.X - Polynomial.C a) * p)

@[simp] lemma poleNewton_eval (a z : ℂ) (p : Polynomial ℂ) :
    (poleNewton a p).eval z = p.eval z * (2 - (z - a) * p.eval z) := by
  simp [poleNewton]

/-- Newton improvement exactly squares the relative residual. -/
lemma poleResidual_newton (a z : ℂ) (p : Polynomial ℂ) :
    poleResidual a z (poleNewton a p) = (poleResidual a z p) ^ 2 := by
  simp only [poleResidual, poleNewton_eval]
  ring

/-- Reinterpreting the same polynomial at a moved pole changes its residual by a linear term. -/
lemma poleResidual_move (a b z : ℂ) (p : Polynomial ℂ) :
    poleResidual b z p = poleResidual a z p + (b - a) * p.eval z := by
  simp only [poleResidual]
  ring

lemma norm_poleNewton_eval_le {a z : ℂ} {p : Polynomial ℂ} {d e : ℝ}
    (hd : 0 < d) (hsep : d ≤ ‖z - a‖)
    (hres : ‖poleResidual a z (poleNewton a p)‖ ≤ e) :
    ‖(poleNewton a p).eval z‖ ≤ (1 + e) / d := by
  have hmul : ‖z - a‖ * ‖(poleNewton a p).eval z‖ ≤ 1 + e := by
    rw [← norm_mul]
    have hid : (z - a) * (poleNewton a p).eval z =
        1 - poleResidual a z (poleNewton a p) := by
      simp [poleResidual]
    rw [hid]
    calc
      ‖1 - poleResidual a z (poleNewton a p)‖ ≤
          ‖(1 : ℂ)‖ + ‖poleResidual a z (poleNewton a p)‖ :=
        norm_sub_le _ _
      _ ≤ 1 + e := by simpa using add_le_add_left hres 1
  have hmul' : d * ‖(poleNewton a p).eval z‖ ≤ 1 + e :=
    (mul_le_mul_of_nonneg_right hsep (norm_nonneg _)).trans hmul
  exact (le_div_iff₀ hd).2 (by simpa [mul_comm] using hmul')

/-- A Newton improvement followed by a move of at most `d/16` preserves residual `1/4`.
The constants are deliberately slack, making the induction insensitive to rounding in the
discrete pole chains. -/
lemma poleResidual_newton_move_le_quarter
    {a b z : ℂ} {p : Polynomial ℂ} {d : ℝ}
    (hd : 0 < d) (hsep : d ≤ ‖z - a‖)
    (hstep : ‖b - a‖ ≤ d / 16)
    (hres : ‖poleResidual a z p‖ ≤ 1 / 4) :
    ‖poleResidual b z (poleNewton a p)‖ ≤ 1 / 4 := by
  have hnew : ‖poleResidual a z (poleNewton a p)‖ ≤ 1 / 16 := by
    rw [poleResidual_newton, norm_pow]
    nlinarith [norm_nonneg (poleResidual a z p)]
  have hp : ‖(poleNewton a p).eval z‖ ≤ (1 + 1 / 16) / d :=
    norm_poleNewton_eval_le hd hsep hnew
  rw [poleResidual_move]
  calc
    ‖poleResidual a z (poleNewton a p) +
        (b - a) * (poleNewton a p).eval z‖ ≤
        ‖poleResidual a z (poleNewton a p)‖ +
          ‖(b - a) * (poleNewton a p).eval z‖ := norm_add_le _ _
    _ ≤ 1 / 16 + (d / 16) * ((1 + 1 / 16) / d) := by
      rw [norm_mul]
      exact add_le_add hnew (mul_le_mul hstep hp (norm_nonneg _) (by positivity))
    _ ≤ 1 / 4 := by field_simp [hd.ne']; norm_num

/-- The Newton step has at most twice the old degree plus one. -/
lemma poleNewton_natDegree_le (a : ℂ) (p : Polynomial ℂ) :
    (poleNewton a p).natDegree ≤ 2 * p.natDegree + 1 := by
  unfold poleNewton
  calc
    (p * (2 - (Polynomial.X - Polynomial.C a) * p)).natDegree ≤
        p.natDegree + (2 - (Polynomial.X - Polynomial.C a) * p).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ p.natDegree + max (Polynomial.C (2 : ℂ)).natDegree
          (((Polynomial.X - Polynomial.C a) * p).natDegree) := by
      gcongr
      exact Polynomial.natDegree_sub_le _ _
    _ ≤ 2 * p.natDegree + 1 := by
      have hlin : (Polynomial.X - Polynomial.C a).natDegree ≤ 1 := by
        exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
      have hprod : ((Polynomial.X - Polynomial.C a) * p).natDegree ≤
          1 + p.natDegree :=
        Polynomial.natDegree_mul_le.trans (by
          simpa only [add_comm] using add_le_add_right hlin p.natDegree)
      simp only [Polynomial.natDegree_C]
      omega

/-! ## Finite Newton pole chains -/

/-- Polynomial obtained after Newton improvement at each consecutive center of a pole chain. -/
noncomputable def poleChainPolynomial (a : ℕ → ℂ) (p : Polynomial ℂ) :
    ℕ → Polynomial ℂ
  | 0 => p
  | n + 1 => poleNewton (a n) (poleChainPolynomial a p n)

@[simp] lemma poleChainPolynomial_zero (a : ℕ → ℂ) (p : Polynomial ℂ) :
    poleChainPolynomial a p 0 = p := rfl

@[simp] lemma poleChainPolynomial_succ (a : ℕ → ℂ) (p : Polynomial ℂ) (n : ℕ) :
    poleChainPolynomial a p (n + 1) =
      poleNewton (a n) (poleChainPolynomial a p n) := rfl

lemma poleChainPolynomial_residual_le_quarter
    {K : Set ℂ} {a : ℕ → ℂ} {p : Polynomial ℂ} {d : ℝ}
    (hd : 0 < d)
    (hsep : ∀ n z, z ∈ K → d ≤ ‖z - a n‖)
    (hstep : ∀ n, ‖a (n + 1) - a n‖ ≤ d / 16)
    (hstart : ∀ z ∈ K, ‖poleResidual (a 0) z p‖ ≤ 1 / 4) :
    ∀ n z, z ∈ K →
      ‖poleResidual (a n) z (poleChainPolynomial a p n)‖ ≤ 1 / 4 := by
  intro n
  induction n with
  | zero =>
      intro z hz
      simpa using hstart z hz
  | succ n ih =>
      intro z hz
      exact poleResidual_newton_move_le_quarter hd (hsep n z hz) (hstep n) (ih z hz)

lemma poleChainPolynomial_residual_le_quarter_of_lt
    {K : Set ℂ} {a : ℕ → ℂ} {p : Polynomial ℂ} {d : ℝ} {N : ℕ}
    (hd : 0 < d)
    (hsep : ∀ n < N, ∀ z, z ∈ K → d ≤ ‖z - a n‖)
    (hstep : ∀ n < N, ‖a (n + 1) - a n‖ ≤ d / 16)
    (hstart : ∀ z ∈ K, ‖poleResidual (a 0) z p‖ ≤ 1 / 4) :
    ∀ z, z ∈ K →
      ‖poleResidual (a N) z (poleChainPolynomial a p N)‖ ≤ 1 / 4 := by
  have haux : ∀ n ≤ N, ∀ z, z ∈ K →
      ‖poleResidual (a n) z (poleChainPolynomial a p n)‖ ≤ 1 / 4 := by
    intro n hn
    induction n with
    | zero =>
        intro z hz
        simpa using hstart z hz
    | succ n ih =>
        intro z hz
        have hnlt : n < N := by omega
        exact poleResidual_newton_move_le_quarter hd (hsep n hnlt z hz)
          (hstep n hnlt) (ih (by omega) z hz)
  exact haux N le_rfl

lemma poleChainPolynomial_natDegree_add_one_le
    (a : ℕ → ℂ) (p : Polynomial ℂ) (n : ℕ) :
    (poleChainPolynomial a p n).natDegree + 1 ≤ 2 ^ n * (p.natDegree + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [poleChainPolynomial_succ]
      have hn := poleNewton_natDegree_le (a n) (poleChainPolynomial a p n)
      calc
        (poleNewton (a n) (poleChainPolynomial a p n)).natDegree + 1 ≤
            2 * (poleChainPolynomial a p n).natDegree + 1 + 1 :=
          Nat.add_le_add_right hn 1
        _ = 2 * ((poleChainPolynomial a p n).natDegree + 1) := by omega
        _ ≤ 2 * (2 ^ n * (p.natDegree + 1)) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) * (p.natDegree + 1) := by
          rw [pow_succ]
          ring

/-- The degree bound for a chain started with a constant approximate reciprocal. -/
lemma poleChainPolynomial_natDegree_lt_two_pow
    (a : ℕ → ℂ) (c : ℂ) (n : ℕ) :
    (poleChainPolynomial a (Polynomial.C c) n).natDegree < 2 ^ n := by
  have h := poleChainPolynomial_natDegree_add_one_le a (Polynomial.C c) n
  simpa using h

/-- Zeroth-order approximation to the reciprocal at a pole outside a disk. -/
noncomputable def farPolePolynomial (a : ℂ) : Polynomial ℂ :=
  Polynomial.C (-a⁻¹)

@[simp] lemma farPolePolynomial_eval (a z : ℂ) :
    (farPolePolynomial a).eval z = -a⁻¹ := by simp [farPolePolynomial]

lemma poleResidual_farPolePolynomial {a z : ℂ} (ha : a ≠ 0) :
    poleResidual a z (farPolePolynomial a) = z * a⁻¹ := by
  simp [poleResidual, farPolePolynomial]
  field_simp
  ring

lemma norm_poleResidual_farPolePolynomial_le {a z : ℂ} {T : ℝ}
    (ha : 4 * T ≤ ‖a‖) (hz : ‖z‖ ≤ T) (hT : 0 < T) :
    ‖poleResidual a z (farPolePolynomial a)‖ ≤ 1 / 4 := by
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    simp only [norm_zero] at ha
    linarith
  rw [poleResidual_farPolePolynomial ha0, norm_mul, norm_inv, ← div_eq_mul_inv]
  exact (div_le_iff₀ (norm_pos_iff.mpr ha0)).2 (by
    nlinarith [mul_le_mul_of_nonneg_left hz (show (0 : ℝ) ≤ 4 by norm_num)])

/-! ## Uniform clearance in the slit chaplet -/

/-- Minimum of the radial and corridor clearances available to a moving pole. -/
noncomputable def chapletClearance (R S ε ρ : ℝ) : ℝ :=
  min (ρ - R) (min (S - ρ) ε)

lemma chapletClearance_pos {R S ε ρ : ℝ}
    (hRρ : R < ρ) (hρS : ρ < S) (hε : 0 < ε) :
    0 < chapletClearance R S ε ρ := by
  exact lt_min (sub_pos.mpr hRρ) (lt_min (sub_pos.mpr hρS) hε)

lemma chapletClearance_le_left (R S ε ρ : ℝ) :
    chapletClearance R S ε ρ ≤ ρ - R := min_le_left _ _

lemma chapletClearance_le_gap (R S ε ρ : ℝ) :
    chapletClearance R S ε ρ ≤ S - ρ :=
  min_le_right _ _ |>.trans (min_le_left _ _)

lemma chapletClearance_le_corridor (R S ε ρ : ℝ) :
    chapletClearance R S ε ρ ≤ ε :=
  min_le_right _ _ |>.trans (min_le_right _ _)

lemma chapletClearance_le_norm_sub_of_norm_eq
    {R S T ε ρ : ℝ} (hRρ : R < ρ) (hρS : ρ < S)
    {a z : ℂ} (ha : ‖a‖ = ρ) (hz : z ∈ Erdos1118Construction.chapletSet R S T ε) :
    chapletClearance R S ε ρ ≤ ‖z - a‖ := by
  rcases Erdos1118Construction.norm_bounds_of_mem_chapletSet hz with hzR | hzS
  · have hrev : ‖a‖ - ‖z‖ ≤ ‖z - a‖ := by
      simpa [norm_sub_rev] using norm_sub_norm_le a z
    rw [ha] at hrev
    exact (chapletClearance_le_left R S ε ρ).trans (by linarith)
  · have hrev : ‖z‖ - ‖a‖ ≤ ‖z - a‖ := norm_sub_norm_le z a
    rw [ha] at hrev
    exact (chapletClearance_le_gap R S ε ρ).trans (by linarith [hzS.1])

lemma chapletClearance_le_norm_sub_of_positive_real
    {R S T ε ρ x : ℝ} (hR0 : 0 ≤ R) (hRρ : R < ρ) (hρx : ρ ≤ x)
    {z : ℂ} (hz : z ∈ Erdos1118Construction.chapletSet R S T ε) :
    chapletClearance R S ε ρ ≤ ‖z - (x : ℂ)‖ := by
  rcases hz with hzDisk | hzOuter
  · have hzR : ‖z‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hzDisk
    have hrev : ‖(x : ℂ)‖ - ‖z‖ ≤ ‖z - (x : ℂ)‖ := by
      simpa [norm_sub_rev] using norm_sub_norm_le (x : ℂ) z
    have hx0 : 0 < x := hR0.trans_lt hRρ |>.trans_le hρx
    have hrev' : x - ‖z‖ ≤ ‖z - (x : ℂ)‖ := by
      simpa [Complex.norm_real, abs_of_pos hx0] using hrev
    exact (chapletClearance_le_left R S ε ρ).trans (by linarith)
  · rcases hzOuter.2.2 with hre | him
    · have hx0 : 0 < x := hR0.trans_lt hRρ |>.trans_le hρx
      have hreal : x - z.re ≤ |(z - (x : ℂ)).re| := by
        change x - z.re ≤ |z.re - x|
        rw [abs_of_nonpos]
        · ring_nf
          exact le_rfl
        · linarith
      have hclearx : chapletClearance R S ε ρ ≤ x := by
        calc
          chapletClearance R S ε ρ ≤ ρ - R := chapletClearance_le_left _ _ _ _
          _ ≤ ρ := by linarith
          _ ≤ x := hρx
      exact hclearx.trans (by
        calc
          x ≤ x - z.re := by linarith
          _ ≤ |(z - (x : ℂ)).re| := hreal
          _ ≤ ‖z - (x : ℂ)‖ := Complex.abs_re_le_norm _)
    · exact (chapletClearance_le_corridor R S ε ρ).trans (by
        calc
          ε ≤ |z.im| := him
          _ = |(z - (x : ℂ)).im| := by simp
          _ ≤ ‖z - (x : ℂ)‖ := Complex.abs_im_le_norm _)

/-! ## Explicit linear and circular pole chains -/

/-- Number of moves used for each half of the route from `4T` to a pole on `‖z‖ = ρ`. -/
noncomputable def chapletPoleSteps (T d : ℝ) : ℕ :=
  ⌈64 * T / d⌉₊

lemma chapletPoleSteps_pos {T d : ℝ} (hT : 0 < T) (hd : 0 < d) :
    0 < chapletPoleSteps T d := by
  rw [chapletPoleSteps, Nat.ceil_pos]
  positivity

lemma chapletPoleSteps_lower {T d : ℝ} :
    64 * T / d ≤ (chapletPoleSteps T d : ℝ) := by
  exact Nat.le_ceil _

/-- Equally spaced centers along the positive real segment from `B` down to `ρ`. -/
noncomputable def linePoleCenter (B ρ : ℝ) (L n : ℕ) : ℂ :=
  ((B + (ρ - B) * (n : ℝ) / (L : ℝ) : ℝ) : ℂ)

@[simp] lemma linePoleCenter_zero (B ρ : ℝ) (L : ℕ) :
    linePoleCenter B ρ L 0 = (B : ℂ) := by
  simp [linePoleCenter]

lemma linePoleCenter_eq_rho {B ρ : ℝ} {L : ℕ} (hL : L ≠ 0) :
    linePoleCenter B ρ L L = (ρ : ℂ) := by
  simp [linePoleCenter, hL]

lemma linePoleCenter_real_ge_rho {B ρ : ℝ} {L n : ℕ}
    (hρB : ρ ≤ B) (hn : n ≤ L) (hL : L ≠ 0) :
    ρ ≤ (linePoleCenter B ρ L n).re := by
  change ρ ≤ B + (ρ - B) * (n : ℝ) / (L : ℝ)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnL : (n : ℝ) ≤ L := by exact_mod_cast hn
  have hfrac : 0 ≤ (n : ℝ) / L ∧ (n : ℝ) / L ≤ 1 :=
    ⟨div_nonneg hn0 hLpos.le, (div_le_one hLpos).2 hnL⟩
  have hid : B + (ρ - B) * (n : ℝ) / (L : ℝ) =
      ρ + (B - ρ) * (1 - (n : ℝ) / (L : ℝ)) := by ring
  rw [hid]
  exact le_add_of_nonneg_right
    (mul_nonneg (sub_nonneg.mpr hρB) (sub_nonneg.mpr hfrac.2))

lemma norm_linePoleCenter_succ_sub {B ρ : ℝ} {L n : ℕ} (hL : L ≠ 0) :
    ‖linePoleCenter B ρ L (n + 1) - linePoleCenter B ρ L n‖ =
      |B - ρ| / L := by
  simp only [linePoleCenter]
  push_cast
  have hcoe : ((B : ℂ) + ((ρ : ℂ) - (B : ℂ)) * ((n : ℂ) + 1) / (L : ℂ) -
      ((B : ℂ) + ((ρ : ℂ) - (B : ℂ)) * (n : ℂ) / (L : ℂ))) =
      ((B + (ρ - B) * ((n : ℝ) + 1) / (L : ℝ) -
        (B + (ρ - B) * (n : ℝ) / (L : ℝ)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcoe, Complex.norm_real, Real.norm_eq_abs]
  have hcast : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have heq : (B + (ρ - B) * ((n : ℝ) + 1) / (L : ℝ)) -
      (B + (ρ - B) * (n : ℝ) / (L : ℝ)) = (ρ - B) / (L : ℝ) := by
    push_cast
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos (show (0 : ℝ) < L by exact_mod_cast Nat.pos_of_ne_zero hL),
    abs_sub_comm]

/-- Equally spaced centers along the circle from the positive point `ρ` to `a`. -/
noncomputable def circlePoleCenter (ρ : ℝ) (a : ℂ) (L n : ℕ) : ℂ :=
  circleMap 0 ρ (a.arg * (n : ℝ) / (L : ℝ))

@[simp] lemma circlePoleCenter_zero (ρ : ℝ) (a : ℂ) (L : ℕ) :
    circlePoleCenter ρ a L 0 = (ρ : ℂ) := by
  simp [circlePoleCenter, circleMap]

lemma circlePoleCenter_eq_pole {ρ : ℝ} {a : ℂ} {L : ℕ}
    (ha : ‖a‖ = ρ) (hL : L ≠ 0) :
    circlePoleCenter ρ a L L = a := by
  rw [circlePoleCenter]
  have hcast : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  rw [show a.arg * (L : ℝ) / (L : ℝ) = a.arg by field_simp]
  rw [circleMap_zero]
  simpa [ha] using Complex.norm_mul_exp_arg_mul_I a

lemma norm_circlePoleCenter {ρ : ℝ} (hρ : 0 ≤ ρ) (a : ℂ) (L n : ℕ) :
    ‖circlePoleCenter ρ a L n‖ = ρ := by
  simp [circlePoleCenter, abs_of_nonneg hρ]

lemma norm_circlePoleCenter_succ_sub_le {T d ρ : ℝ} {a : ℂ} {L n : ℕ}
    (hρ0 : 0 ≤ ρ) (hρT : ρ ≤ T) (hd : 0 < d) (hL : L ≠ 0)
    (hsize : 64 * T / d ≤ (L : ℝ)) :
    ‖circlePoleCenter ρ a L (n + 1) - circlePoleCenter ρ a L n‖ ≤ d / 16 := by
  have hlip := (lipschitzWith_circleMap (0 : ℂ) ρ).norm_sub_le
      (a.arg * ((n + 1 : ℕ) : ℝ) / (L : ℝ))
      (a.arg * (n : ℝ) / (L : ℝ))
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
  have harg : |a.arg| ≤ Real.pi := Complex.abs_arg_le_pi a
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hT0 : 0 ≤ T := hρ0.trans hρT
  have hratio : 4 * T / (L : ℝ) ≤ d / 16 := by
    rw [div_le_iff₀ hLpos, div_eq_mul_inv]
    have hLd : 64 * T ≤ (L : ℝ) * d := (div_le_iff₀ hd).1 hsize
    nlinarith
  calc
    ‖circlePoleCenter ρ a L (n + 1) - circlePoleCenter ρ a L n‖ ≤
        |ρ| * |a.arg * ((n + 1 : ℕ) : ℝ) / (L : ℝ) -
          a.arg * (n : ℝ) / (L : ℝ)| := by
      simpa [circlePoleCenter, Real.norm_eq_abs, NNReal.smul_def] using hlip
    _ = ρ * (|a.arg| / (L : ℝ)) := by
      rw [abs_of_nonneg hρ0]
      congr 1
      have heq : a.arg * ((n + 1 : ℕ) : ℝ) / (L : ℝ) -
          a.arg * (n : ℝ) / (L : ℝ) = a.arg / (L : ℝ) := by
        push_cast
        field_simp
        ring
      rw [heq, abs_div, abs_of_pos hLpos]
    _ ≤ T * (Real.pi / (L : ℝ)) := by
      exact mul_le_mul hρT (div_le_div_of_nonneg_right harg hLpos.le)
        (div_nonneg (abs_nonneg _) hLpos.le) hT0
    _ ≤ 4 * T / (L : ℝ) := by
      simpa [mul_comm, mul_div_assoc] using
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpi.le hT0) hLpos.le)
    _ ≤ d / 16 := hratio

/-! ## A quantitative polynomial approximate inverse for one pole -/

noncomputable def linePoleApproximation (R S T ε ρ : ℝ) : Polynomial ℂ :=
  let d := chapletClearance R S ε ρ
  let L := chapletPoleSteps T d
  poleChainPolynomial (linePoleCenter (4 * T) ρ L) (farPolePolynomial ((4 * T : ℝ) : ℂ)) L

noncomputable def chapletPoleApproximation
    (R S T ε ρ : ℝ) (a : ℂ) : Polynomial ℂ :=
  let d := chapletClearance R S ε ρ
  let L := chapletPoleSteps T d
  poleChainPolynomial (circlePoleCenter ρ a L) (linePoleApproximation R S T ε ρ) L

lemma linePoleApproximation_residual_le_quarter
    {R S T ε ρ : ℝ}
    (hR0 : 0 ≤ R) (hRρ : R < ρ) (hρS : ρ < S) (hST : S ≤ T) (hε : 0 < ε)
    {z : ℂ} (hz : z ∈ Erdos1118Construction.chapletSet R S T ε) :
    ‖poleResidual (ρ : ℂ) z (linePoleApproximation R S T ε ρ)‖ ≤ 1 / 4 := by
  let d := chapletClearance R S ε ρ
  let L := chapletPoleSteps T d
  have hd : 0 < d := chapletClearance_pos hRρ hρS hε
  have hT : 0 < T := (hR0.trans_lt hRρ).trans hρS |>.trans_le hST
  have hL : L ≠ 0 := (chapletPoleSteps_pos hT hd).ne'
  have hρT : ρ ≤ T := hρS.le.trans hST
  have hρfourT : ρ ≤ 4 * T := by nlinarith
  have hsize : 64 * T / d ≤ (L : ℝ) := chapletPoleSteps_lower
  have hchain := poleChainPolynomial_residual_le_quarter_of_lt
    (K := Erdos1118Construction.chapletSet R S T ε)
    (a := linePoleCenter (4 * T) ρ L)
    (p := farPolePolynomial ((4 * T : ℝ) : ℂ)) (d := d) (N := L)
    hd
    (by
      intro n hn z hz
      have hx : ρ ≤ (linePoleCenter (4 * T) ρ L n).re :=
        linePoleCenter_real_ge_rho hρfourT hn.le hL
      have hreal : linePoleCenter (4 * T) ρ L n =
          (((linePoleCenter (4 * T) ρ L n).re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp [linePoleCenter]
      rw [hreal]
      exact chapletClearance_le_norm_sub_of_positive_real hR0 hRρ hx hz)
    (by
      intro n hn
      rw [norm_linePoleCenter_succ_sub hL, abs_of_nonneg (sub_nonneg.mpr hρfourT)]
      have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
      have hratio : 4 * T / (L : ℝ) ≤ d / 16 := by
        rw [div_le_iff₀ hLpos]
        have hLd : 64 * T ≤ (L : ℝ) * d := (div_le_iff₀ hd).1 hsize
        nlinarith
      have hρ0 : 0 ≤ ρ := hR0.trans hRρ.le
      exact (div_le_div_of_nonneg_right (sub_le_self _ hρ0) hLpos.le).trans hratio)
    (by
      intro z hz
      have hzT : ‖z‖ ≤ T := by
        rcases Erdos1118Construction.norm_bounds_of_mem_chapletSet hz with hzR | hzT
        · exact hzR.trans (hRρ.le.trans (hρS.le.trans hST))
        · exact hzT.2
      have hnorm : ‖(((4 * T : ℝ) : ℂ))‖ = 4 * T := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 4 * T)]
      rw [linePoleCenter_zero]
      apply norm_poleResidual_farPolePolynomial_le (a := ((4 * T : ℝ) : ℂ))
        (T := T) (z := z)
      · rw [hnorm]
      · exact hzT
      · exact hT)
    z hz
  have hend := linePoleCenter_eq_rho (B := 4 * T) (ρ := ρ) hL
  simpa [linePoleApproximation, d, L, hend] using hchain

lemma chapletPoleApproximation_residual_le_quarter
    {R S T ε ρ : ℝ}
    (hR0 : 0 ≤ R) (hRρ : R < ρ) (hρS : ρ < S) (hST : S ≤ T) (hε : 0 < ε)
    {a : ℂ} (ha : ‖a‖ = ρ)
    {z : ℂ} (hz : z ∈ Erdos1118Construction.chapletSet R S T ε) :
    ‖poleResidual a z (chapletPoleApproximation R S T ε ρ a)‖ ≤ 1 / 4 := by
  let d := chapletClearance R S ε ρ
  let L := chapletPoleSteps T d
  have hd : 0 < d := chapletClearance_pos hRρ hρS hε
  have hT : 0 < T := (hR0.trans_lt hRρ).trans hρS |>.trans_le hST
  have hL : L ≠ 0 := (chapletPoleSteps_pos hT hd).ne'
  have hρ0 : 0 ≤ ρ := hR0.trans hRρ.le
  have hρT : ρ ≤ T := hρS.le.trans hST
  have hsize : 64 * T / d ≤ (L : ℝ) := chapletPoleSteps_lower
  have hchain := poleChainPolynomial_residual_le_quarter_of_lt
    (K := Erdos1118Construction.chapletSet R S T ε)
    (a := circlePoleCenter ρ a L)
    (p := linePoleApproximation R S T ε ρ) (d := d) (N := L)
    hd
    (by
      intro n hn z hz
      exact chapletClearance_le_norm_sub_of_norm_eq hRρ hρS
        (norm_circlePoleCenter hρ0 a L n) hz)
    (by
      intro n hn
      exact norm_circlePoleCenter_succ_sub_le hρ0 hρT hd hL hsize)
    (by
      intro z hz
      simpa using linePoleApproximation_residual_le_quarter hR0 hRρ hρS hST hε hz)
    z hz
  have hend := circlePoleCenter_eq_pole (a := a) ha hL
  simpa [chapletPoleApproximation, d, L, hend] using hchain

lemma linePoleApproximation_natDegree_add_one_le
    (R S T ε ρ : ℝ) :
    (linePoleApproximation R S T ε ρ).natDegree + 1 ≤
      2 ^ (chapletPoleSteps T (chapletClearance R S ε ρ)) := by
  let d := chapletClearance R S ε ρ
  let L := chapletPoleSteps T d
  have h := poleChainPolynomial_natDegree_add_one_le
    (linePoleCenter (4 * T) ρ L) (farPolePolynomial ((4 * T : ℝ) : ℂ)) L
  have hp : (farPolePolynomial ((4 * T : ℝ) : ℂ)).natDegree = 0 := by
    unfold farPolePolynomial
    exact Polynomial.natDegree_C _
  change (poleChainPolynomial (linePoleCenter (4 * T) ρ L)
      (farPolePolynomial ((4 * T : ℝ) : ℂ)) L).natDegree + 1 ≤ 2 ^ L
  calc
    _ ≤ 2 ^ L * ((farPolePolynomial ((4 * T : ℝ) : ℂ)).natDegree + 1) := h
    _ = 2 ^ L := by rw [hp]; simp

lemma chapletPoleApproximation_natDegree_add_one_le
    (R S T ε ρ : ℝ) (a : ℂ) :
    (chapletPoleApproximation R S T ε ρ a).natDegree + 1 ≤
      2 ^ (2 * chapletPoleSteps T (chapletClearance R S ε ρ)) := by
  let d := chapletClearance R S ε ρ
  let L := chapletPoleSteps T d
  have hcirc := poleChainPolynomial_natDegree_add_one_le
    (circlePoleCenter ρ a L) (linePoleApproximation R S T ε ρ) L
  have hline := linePoleApproximation_natDegree_add_one_le R S T ε ρ
  calc
    (chapletPoleApproximation R S T ε ρ a).natDegree + 1 ≤
        2 ^ L * ((linePoleApproximation R S T ε ρ).natDegree + 1) := by
      simpa [chapletPoleApproximation, d, L] using hcirc
    _ ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul_left _ (by simpa [d, L] using hline)
    _ = 2 ^ (2 * L) := by rw [← pow_add]; congr 1; omega

/-! ## Simultaneous inversion of all denominator factors -/

/-- Relative residual for a polynomial approximate inverse of an arbitrary polynomial. -/
noncomputable def inverseResidual (D q : Polynomial ℂ) (z : ℂ) : ℂ :=
  1 - D.eval z * q.eval z

/-- Newton improvement for an approximate polynomial inverse of `D`. -/
noncomputable def inverseNewton (D q : Polynomial ℂ) : Polynomial ℂ :=
  q * (2 - D * q)

@[simp] lemma inverseNewton_eval (D q : Polynomial ℂ) (z : ℂ) :
    (inverseNewton D q).eval z = q.eval z * (2 - D.eval z * q.eval z) := by
  simp [inverseNewton]

lemma inverseResidual_newton (D q : Polynomial ℂ) (z : ℂ) :
    inverseResidual D (inverseNewton D q) z = (inverseResidual D q z) ^ 2 := by
  simp only [inverseResidual, inverseNewton_eval]
  ring

lemma inverseResidual_mul (D E q p : Polynomial ℂ) (z : ℂ) :
    inverseResidual (D * E) (q * p) z =
      inverseResidual D q z +
        (D.eval z * q.eval z) * inverseResidual E p z := by
  simp only [inverseResidual, Polynomial.eval_mul]
  ring

/-- Product of the linear factors indexed by a concrete root list. -/
noncomputable def linearFactorProduct (s : List ℂ) : Polynomial ℂ :=
  (s.map fun a ↦ Polynomial.X - Polynomial.C a).prod

@[simp] lemma linearFactorProduct_nil : linearFactorProduct ([] : List ℂ) = 1 := by
  simp [linearFactorProduct]

@[simp] lemma linearFactorProduct_cons (a : ℂ) (s : List ℂ) :
    linearFactorProduct (a :: s) =
      (Polynomial.X - Polynomial.C a) * linearFactorProduct s := by
  simp [linearFactorProduct]

@[simp] lemma linearFactorProduct_eval_cons (a z : ℂ) (s : List ℂ) :
    (linearFactorProduct (a :: s)).eval z =
      (z - a) * (linearFactorProduct s).eval z := by
  simp

/-- Recursively multiply one-pole approximate inverses and restore relative error by Newton. -/
noncomputable def listInverseApproximation (P : ℂ → Polynomial ℂ) :
    List ℂ → Polynomial ℂ
  | [] => 1
  | a :: s =>
      inverseNewton (linearFactorProduct (a :: s))
        (P a * listInverseApproximation P s)

@[simp] lemma listInverseApproximation_nil (P : ℂ → Polynomial ℂ) :
    listInverseApproximation P [] = 1 := rfl

@[simp] lemma listInverseApproximation_cons (P : ℂ → Polynomial ℂ) (a : ℂ) (s : List ℂ) :
    listInverseApproximation P (a :: s) =
      inverseNewton (linearFactorProduct (a :: s))
        (P a * listInverseApproximation P s) := rfl

lemma listInverseApproximation_residual_le_quarter
    {K : Set ℂ} {P : ℂ → Polynomial ℂ} {s : List ℂ}
    (hP : ∀ a ∈ s, ∀ z ∈ K,
      ‖poleResidual a z (P a)‖ ≤ 1 / 16) :
    ∀ z ∈ K,
      ‖inverseResidual (linearFactorProduct s) (listInverseApproximation P s) z‖ ≤ 1 / 4 := by
  induction s with
  | nil =>
      intro z hz
      simp [inverseResidual]
  | cons a s ih =>
      intro z hz
      have ha : ‖poleResidual a z (P a)‖ ≤ 1 / 16 := hP a (by simp) z hz
      have hsP : ∀ b ∈ s, ∀ w ∈ K, ‖poleResidual b w (P b)‖ ≤ 1 / 16 := by
        intro b hb
        exact hP b (by simp [hb])
      have hs := ih hsP z hz
      let D := linearFactorProduct s
      let Q := listInverseApproximation P s
      let E := Polynomial.X - Polynomial.C a
      have hE : inverseResidual E (P a) z = poleResidual a z (P a) := by
        simp [inverseResidual, poleResidual, E]
      have hDQ : ‖D.eval z * Q.eval z‖ ≤ 5 / 4 := by
        have hid : D.eval z * Q.eval z = 1 - inverseResidual D Q z := by
          simp [inverseResidual]
        rw [hid]
        calc
          ‖1 - inverseResidual D Q z‖ ≤ ‖(1 : ℂ)‖ + ‖inverseResidual D Q z‖ :=
            norm_sub_le _ _
          _ ≤ 1 + 1 / 4 := by simpa [D, Q] using add_le_add_left hs 1
          _ = 5 / 4 := by norm_num
      have hraw : ‖inverseResidual (E * D) ((P a) * Q) z‖ ≤ 21 / 64 := by
        rw [inverseResidual_mul]
        calc
          ‖inverseResidual E (P a) z +
              (E.eval z * (P a).eval z) * inverseResidual D Q z‖ ≤
              ‖inverseResidual E (P a) z‖ +
                ‖(E.eval z * (P a).eval z) * inverseResidual D Q z‖ := norm_add_le _ _
          _ ≤ 1 / 16 + (1 + 1 / 16) * (1 / 4) := by
            have hEP : ‖E.eval z * (P a).eval z‖ ≤ 1 + 1 / 16 := by
              have hid : E.eval z * (P a).eval z = 1 - inverseResidual E (P a) z := by
                simp [inverseResidual]
              rw [hid]
              calc
                ‖1 - inverseResidual E (P a) z‖ ≤
                    ‖(1 : ℂ)‖ + ‖inverseResidual E (P a) z‖ := norm_sub_le _ _
                _ ≤ 1 + 1 / 16 := by simpa [hE] using add_le_add_left ha 1

            rw [norm_mul]
            exact add_le_add (by simpa [hE] using ha)
              (mul_le_mul hEP (by simpa [D, Q] using hs) (norm_nonneg _) (by positivity))
          _ = 21 / 64 := by norm_num
      rw [listInverseApproximation_cons, inverseResidual_newton, norm_pow]
      have hfactorEq : linearFactorProduct (a :: s) = E * D := by
        simp [E, D, mul_comm]
      rw [hfactorEq]
      nlinarith [norm_nonneg (inverseResidual (E * D) (P a * Q) z)]

/-- One final Newton step improves the one-pole residual from `1/4` to `1/16`. -/
noncomputable def refinedChapletPoleApproximation
    (R S T ε ρ : ℝ) (a : ℂ) : Polynomial ℂ :=
  poleNewton a (chapletPoleApproximation R S T ε ρ a)

lemma refinedChapletPoleApproximation_residual_le_sixteenth
    {R S T ε ρ : ℝ}
    (hR0 : 0 ≤ R) (hRρ : R < ρ) (hρS : ρ < S) (hST : S ≤ T) (hε : 0 < ε)
    {a : ℂ} (ha : ‖a‖ = ρ)
    {z : ℂ} (hz : z ∈ Erdos1118Construction.chapletSet R S T ε) :
    ‖poleResidual a z (refinedChapletPoleApproximation R S T ε ρ a)‖ ≤ 1 / 16 := by
  rw [refinedChapletPoleApproximation, poleResidual_newton, norm_pow]
  have h := chapletPoleApproximation_residual_le_quarter hR0 hRρ hρS hST hε ha hz
  nlinarith [norm_nonneg (poleResidual a z (chapletPoleApproximation R S T ε ρ a))]

lemma chapletDenominator_monic {ρ : ℝ} {N : ℕ} (hN : N ≠ 0) :
    (Erdos1118Construction.chapletDenominator ρ N).Monic := by
  unfold Erdos1118Construction.chapletDenominator
  exact Polynomial.monic_X_pow_add_C (((ρ : ℝ) : ℂ) ^ N) hN

lemma linearFactorProduct_chapletDenominator_roots
    {ρ : ℝ} {N : ℕ} (hN : N ≠ 0) :
    linearFactorProduct
        (Erdos1118Construction.chapletDenominator ρ N).roots.toList =
      Erdos1118Construction.chapletDenominator ρ N := by
  let D := Erdos1118Construction.chapletDenominator ρ N
  have hsplits : D.Splits := IsAlgClosed.splits D
  have hfactor := hsplits.eq_prod_roots_of_monic (chapletDenominator_monic hN)
  rw [linearFactorProduct, Multiset.prod_map_toList]
  exact hfactor.symm

/-- Quantitative polynomial reciprocal of the radial-separator denominator. -/
noncomputable def chapletDenominatorInverse
    (R S T ε ρ : ℝ) (N : ℕ) : Polynomial ℂ :=
  listInverseApproximation (refinedChapletPoleApproximation R S T ε ρ)
    (Erdos1118Construction.chapletDenominator ρ N).roots.toList

lemma chapletDenominatorInverse_residual_le_quarter
    {R S T ε ρ : ℝ} {N : ℕ}
    (hR0 : 0 ≤ R) (hRρ : R < ρ) (hρS : ρ < S) (hST : S ≤ T) (hε : 0 < ε)
    (hρ : 0 < ρ) (hN : N ≠ 0)
    {z : ℂ} (hz : z ∈ Erdos1118Construction.chapletSet R S T ε) :
    ‖inverseResidual (Erdos1118Construction.chapletDenominator ρ N)
      (chapletDenominatorInverse R S T ε ρ N) z‖ ≤ 1 / 4 := by
  let D := Erdos1118Construction.chapletDenominator ρ N
  have hlist := listInverseApproximation_residual_le_quarter
    (K := Erdos1118Construction.chapletSet R S T ε)
    (P := refinedChapletPoleApproximation R S T ε ρ)
    (s := D.roots.toList)
    (by
      intro a ha z hz
      have haroot : a ∈ D.roots := Multiset.mem_toList.mp ha
      have hanorm : ‖a‖ = ρ :=
        Erdos1118Construction.norm_eq_of_mem_chapletDenominator_roots hρ hN haroot
      exact refinedChapletPoleApproximation_residual_le_sixteenth
        hR0 hRρ hρS hST hε hanorm hz)
    z hz
  rw [linearFactorProduct_chapletDenominator_roots hN] at hlist
  exact hlist

/-- Repeated Newton refinement of a polynomial approximate reciprocal. -/
noncomputable def iteratedInverseNewton (D q : Polynomial ℂ) : ℕ → Polynomial ℂ
  | 0 => q
  | n + 1 => inverseNewton D (iteratedInverseNewton D q n)

@[simp] lemma iteratedInverseNewton_zero (D q : Polynomial ℂ) :
    iteratedInverseNewton D q 0 = q := rfl

@[simp] lemma iteratedInverseNewton_succ (D q : Polynomial ℂ) (n : ℕ) :
    iteratedInverseNewton D q (n + 1) =
      inverseNewton D (iteratedInverseNewton D q n) := rfl

lemma inverseResidual_iteratedInverseNewton (D q : Polynomial ℂ) (n : ℕ) (z : ℂ) :
    inverseResidual D (iteratedInverseNewton D q n) z =
      (inverseResidual D q z) ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedInverseNewton_succ, inverseResidual_newton, ih, pow_succ]
      ring

lemma norm_inverseResidual_iteratedInverseNewton_le
    {D q : Polynomial ℂ} {z : ℂ} {e : ℝ}
    (he0 : 0 ≤ e) (he : ‖inverseResidual D q z‖ ≤ e) (n : ℕ) :
    ‖inverseResidual D (iteratedInverseNewton D q n) z‖ ≤ e ^ (2 ^ n) := by
  rw [inverseResidual_iteratedInverseNewton, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) he _

noncomputable def refinedChapletDenominatorInverse
    (R S T ε ρ : ℝ) (N k : ℕ) : Polynomial ℂ :=
  let D := Erdos1118Construction.chapletDenominator ρ N
  iteratedInverseNewton D (chapletDenominatorInverse R S T ε ρ N) k

lemma refinedChapletDenominatorInverse_residual_le
    {R S T ε ρ : ℝ} {N k : ℕ}
    (hR0 : 0 ≤ R) (hRρ : R < ρ) (hρS : ρ < S) (hST : S ≤ T) (hε : 0 < ε)
    (hρ : 0 < ρ) (hN : N ≠ 0)
    {z : ℂ} (hz : z ∈ Erdos1118Construction.chapletSet R S T ε) :
    ‖inverseResidual (Erdos1118Construction.chapletDenominator ρ N)
      (refinedChapletDenominatorInverse R S T ε ρ N k) z‖ ≤
        (1 / 4 : ℝ) ^ (2 ^ k) := by
  apply norm_inverseResidual_iteratedInverseNewton_le (e := (1 / 4 : ℝ)) (by norm_num)
  exact chapletDenominatorInverse_residual_le_quarter
    hR0 hRρ hρS hST hε hρ hN hz

/-! ## Degree accounting -/

lemma inverseNewton_natDegree_add_one_le (D q : Polynomial ℂ) :
    (inverseNewton D q).natDegree + 1 ≤
      2 * (q.natDegree + 1) + (D.natDegree + 1) := by
  unfold inverseNewton
  calc
    (q * (2 - D * q)).natDegree + 1 ≤
        q.natDegree + (2 - D * q).natDegree + 1 :=
      Nat.add_le_add_right Polynomial.natDegree_mul_le 1
    _ ≤ q.natDegree + max (Polynomial.C (2 : ℂ)).natDegree (D * q).natDegree + 1 := by
      gcongr
      exact Polynomial.natDegree_sub_le _ _
    _ ≤ q.natDegree + (D.natDegree + q.natDegree) + 1 := by
      apply Nat.add_le_add_right
      apply Nat.add_le_add_left
      exact max_le (by simp) Polynomial.natDegree_mul_le
    _ ≤ 2 * (q.natDegree + 1) + (D.natDegree + 1) := by omega

lemma linearFactorProduct_natDegree_le_length (s : List ℂ) :
    (linearFactorProduct s).natDegree ≤ s.length := by
  induction s with
  | nil => simp
  | cons a s ih =>
      rw [linearFactorProduct_cons]
      calc
        ((Polynomial.X - Polynomial.C a) * linearFactorProduct s).natDegree ≤
            (Polynomial.X - Polynomial.C a).natDegree +
              (linearFactorProduct s).natDegree := Polynomial.natDegree_mul_le
        _ ≤ 1 + s.length := by
          gcongr
          exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
        _ = (a :: s).length := by simp [Nat.add_comm]

lemma listInverseApproximation_natDegree_add_one_le
    {P : ℂ → Polynomial ℂ} {s : List ℂ} {E : ℕ}
    (hE : 1 ≤ E) (hP : ∀ a ∈ s, (P a).natDegree + 1 ≤ E) :
    (listInverseApproximation P s).natDegree + 1 ≤
      8 ^ s.length * (E + s.length + 1) := by
  induction s with
  | nil => simp [hE]
  | cons a s ih =>
      have ha : (P a).natDegree + 1 ≤ E := hP a (by simp)
      have hs : ∀ b ∈ s, (P b).natDegree + 1 ≤ E := by
        intro b hb
        exact hP b (by simp [hb])
      have htail := ih hs
      let Q := listInverseApproximation P s
      let D := linearFactorProduct (a :: s)
      let q := P a * Q
      have hq : q.natDegree + 1 ≤
          E + 8 ^ s.length * (E + s.length + 1) := by
        calc
          q.natDegree + 1 ≤ (P a).natDegree + Q.natDegree + 1 :=
            Nat.add_le_add_right Polynomial.natDegree_mul_le 1
          _ ≤ ((P a).natDegree + 1) + (Q.natDegree + 1) := by omega
          _ ≤ E + 8 ^ s.length * (E + s.length + 1) := Nat.add_le_add ha htail
      have hD : D.natDegree + 1 ≤ s.length + 2 := by
        dsimp only [D]
        have h := linearFactorProduct_natDegree_le_length (a :: s)
        simp only [List.length_cons] at h ⊢
        omega
      rw [listInverseApproximation_cons]
      have hnew := inverseNewton_natDegree_add_one_le D q
      change (inverseNewton D q).natDegree + 1 ≤
        8 ^ (s.length + 1) * (E + (s.length + 1) + 1)
      calc
        _ ≤ 2 * (q.natDegree + 1) + (D.natDegree + 1) := hnew
        _ ≤ 2 * (E + 8 ^ s.length * (E + s.length + 1)) +
            (s.length + 2) := Nat.add_le_add (Nat.mul_le_mul_left 2 hq) hD
        _ ≤ 8 ^ (s.length + 1) * (E + (s.length + 1) + 1) := by
          have hpow : 1 ≤ 8 ^ s.length := one_le_pow₀ (by norm_num)
          have hnonneg : 0 ≤ E + s.length + 1 := Nat.zero_le _
          rw [pow_succ]
          nlinarith

lemma poleNewton_natDegree_add_one_le (a : ℂ) (p : Polynomial ℂ) :
    (poleNewton a p).natDegree + 1 ≤ 2 * (p.natDegree + 1) := by
  have h := poleNewton_natDegree_le a p
  omega

lemma refinedChapletPoleApproximation_natDegree_add_one_le
    (R S T ε ρ : ℝ) (a : ℂ) :
    (refinedChapletPoleApproximation R S T ε ρ a).natDegree + 1 ≤
      2 ^ (2 * chapletPoleSteps T (chapletClearance R S ε ρ) + 1) := by
  unfold refinedChapletPoleApproximation
  calc
    _ ≤ 2 * ((chapletPoleApproximation R S T ε ρ a).natDegree + 1) :=
      poleNewton_natDegree_add_one_le _ _
    _ ≤ 2 * 2 ^ (2 * chapletPoleSteps T (chapletClearance R S ε ρ)) :=
      Nat.mul_le_mul_left 2 (chapletPoleApproximation_natDegree_add_one_le R S T ε ρ a)
    _ = 2 ^ (2 * chapletPoleSteps T (chapletClearance R S ε ρ) + 1) := by
      rw [pow_succ]
      ring

lemma chapletDenominator_natDegree {ρ : ℝ} {N : ℕ} (hN : N ≠ 0) :
    (Erdos1118Construction.chapletDenominator ρ N).natDegree = N := by
  change (Polynomial.X ^ N + Polynomial.C (((ρ : ℝ) : ℂ) ^ N)).natDegree = N
  exact Polynomial.natDegree_X_pow_add_C

lemma chapletDenominator_roots_toList_length {ρ : ℝ} {N : ℕ} (hN : N ≠ 0) :
    (Erdos1118Construction.chapletDenominator ρ N).roots.toList.length = N := by
  rw [Multiset.length_toList,
    Polynomial.splits_iff_card_roots.mp
      (IsAlgClosed.splits (Erdos1118Construction.chapletDenominator ρ N)),
    chapletDenominator_natDegree hN]

lemma chapletDenominatorInverse_natDegree_add_one_le
    {ρ : ℝ} {N : ℕ} (hN : N ≠ 0) (R S T ε : ℝ) :
    (chapletDenominatorInverse R S T ε ρ N).natDegree + 1 ≤
      8 ^ N *
        (2 ^ (2 * chapletPoleSteps T (chapletClearance R S ε ρ) + 1) + N + 1) := by
  let E := 2 ^ (2 * chapletPoleSteps T (chapletClearance R S ε ρ) + 1)
  let s := (Erdos1118Construction.chapletDenominator ρ N).roots.toList
  have hE : 1 ≤ E := one_le_pow₀ (by norm_num)
  have hP : ∀ a ∈ s,
      (refinedChapletPoleApproximation R S T ε ρ a).natDegree + 1 ≤ E := by
    intro a ha
    exact refinedChapletPoleApproximation_natDegree_add_one_le R S T ε ρ a
  have h := listInverseApproximation_natDegree_add_one_le hE hP
  have hlen : s.length = N := chapletDenominator_roots_toList_length hN
  simpa [chapletDenominatorInverse, s, E, hlen] using h

lemma iteratedInverseNewton_natDegree_add_one_le
    (D q : Polynomial ℂ) (k : ℕ) :
    (iteratedInverseNewton D q k).natDegree + 1 ≤
      3 ^ k * (q.natDegree + D.natDegree + 2) := by
  induction k with
  | zero => simp; omega
  | succ k ih =>
      rw [iteratedInverseNewton_succ]
      have h := inverseNewton_natDegree_add_one_le D (iteratedInverseNewton D q k)
      calc
        _ ≤ 2 * ((iteratedInverseNewton D q k).natDegree + 1) +
            (D.natDegree + 1) := h
        _ ≤ 2 * (3 ^ k * (q.natDegree + D.natDegree + 2)) +
            (D.natDegree + 1) := Nat.add_le_add_right (Nat.mul_le_mul_left 2 ih) _
        _ ≤ 3 ^ (k + 1) * (q.natDegree + D.natDegree + 2) := by
          have hpow : 1 ≤ 3 ^ k := one_le_pow₀ (by norm_num)
          rw [pow_succ]
          nlinarith

lemma refinedChapletDenominatorInverse_natDegree_add_one_le
    {ρ : ℝ} {N : ℕ} (hN : N ≠ 0) (R S T ε : ℝ) (k : ℕ) :
    (refinedChapletDenominatorInverse R S T ε ρ N k).natDegree + 1 ≤
      3 ^ k *
        (8 ^ N *
          (2 ^ (2 * chapletPoleSteps T (chapletClearance R S ε ρ) + 1) + N + 1) +
            N + 1) := by
  let D := Erdos1118Construction.chapletDenominator ρ N
  let q := chapletDenominatorInverse R S T ε ρ N
  have h := iteratedInverseNewton_natDegree_add_one_le D q k
  have hq := chapletDenominatorInverse_natDegree_add_one_le (ρ := ρ) hN R S T ε
  have hD : D.natDegree = N := chapletDenominator_natDegree hN
  change (iteratedInverseNewton D q k).natDegree + 1 ≤ _
  calc
    _ ≤ 3 ^ k * (q.natDegree + D.natDegree + 2) := h
    _ ≤ 3 ^ k *
        (8 ^ N *
          (2 ^ (2 * chapletPoleSteps T (chapletClearance R S ε ρ) + 1) + N + 1) +
            N + 1) := by
      apply Nat.mul_le_mul_left
      rw [hD]
      change q.natDegree + 1 ≤
        8 ^ N *
          (2 ^ (2 * chapletPoleSteps T (chapletClearance R S ε ρ) + 1) + N + 1) at hq
      omega

/-! ## A quantitative polynomial radial separator -/

/-- The polynomial obtained by multiplying the refined approximate reciprocal by the
numerator of the rational radial separator.  Two final Newton steps give ample numerical
slack for the subsequent sharpening iteration. -/
noncomputable def baseChapletSeparator
    (R S T ε ρ : ℝ) (N : ℕ) : Polynomial ℂ :=
  Polynomial.C (((ρ : ℝ) : ℂ) ^ N) *
    refinedChapletDenominatorInverse R S T ε ρ N 2

lemma baseChapletSeparator_eval_eq
    {R S T ε ρ : ℝ} {N : ℕ} (hρ : 0 < ρ) (hN : N ≠ 0)
    (hRρ : R < ρ) (hρS : ρ < S)
    {z : ℂ} (hz : z ∈ Erdos1118Construction.chapletSet R S T ε) :
    (baseChapletSeparator R S T ε ρ N).eval z =
      ((((ρ : ℝ) : ℂ) ^ N) *
          ((Erdos1118Construction.chapletDenominator ρ N).eval z)⁻¹) *
        (1 - inverseResidual (Erdos1118Construction.chapletDenominator ρ N)
          (refinedChapletDenominatorInverse R S T ε ρ N 2) z) := by
  have hD : (Erdos1118Construction.chapletDenominator ρ N).eval z ≠ 0 := by
    let z' : Erdos1118Construction.chapletSet R S T ε := ⟨z, hz⟩
    exact Erdos1118Construction.chapletDenominator_eval_ne_zero hρ hN hRρ hρS z'
  simp only [baseChapletSeparator, Polynomial.eval_mul, Polynomial.eval_C,
    inverseResidual]
  field_simp [hD]
  ring

/-- One cubic sharpening step.  It has superattracting fixed points at both `0` and `1`. -/
noncomputable def sharpenStep (p : Polynomial ℂ) : Polynomial ℂ :=
  p ^ 2 * (Polynomial.C 3 - Polynomial.C 2 * p)

@[simp] lemma sharpenStep_eval (p : Polynomial ℂ) (z : ℂ) :
    (sharpenStep p).eval z = (p.eval z) ^ 2 * (3 - 2 * p.eval z) := by
  simp [sharpenStep]

lemma one_sub_sharpenStep_eval (p : Polynomial ℂ) (z : ℂ) :
    1 - (sharpenStep p).eval z =
      (1 - p.eval z) ^ 2 * (3 - 2 * (1 - p.eval z)) := by
  rw [sharpenStep_eval]
  ring

/-- Iterated cubic sharpening. -/
noncomputable def sharpenPolynomial (p : Polynomial ℂ) : ℕ → Polynomial ℂ
  | 0 => p
  | k + 1 => sharpenStep (sharpenPolynomial p k)

@[simp] lemma sharpenPolynomial_zero (p : Polynomial ℂ) :
    sharpenPolynomial p 0 = p := rfl

@[simp] lemma sharpenPolynomial_succ (p : Polynomial ℂ) (k : ℕ) :
    sharpenPolynomial p (k + 1) = sharpenStep (sharpenPolynomial p k) := rfl

/-- The explicit error after `k` sharpening steps. -/
noncomputable def sharpenError (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (2 ^ k + 2)

lemma sharpenError_zero : sharpenError 0 = 1 / 8 := by
  norm_num [sharpenError]

lemma sharpenError_succ (k : ℕ) :
    sharpenError (k + 1) = 4 * (sharpenError k) ^ 2 := by
  unfold sharpenError
  rw [pow_succ]
  ring_nf

lemma sharpenStep_norm_le {p : Polynomial ℂ} {z : ℂ} {e : ℝ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 8) (hp : ‖p.eval z‖ ≤ e) :
    ‖(sharpenStep p).eval z‖ ≤ 4 * e ^ 2 := by
  rw [sharpenStep_eval, norm_mul, norm_pow]
  have hfactor : ‖(3 : ℂ) - 2 * p.eval z‖ ≤ 3 + 2 * e := by
    calc
      ‖(3 : ℂ) - 2 * p.eval z‖ ≤ ‖(3 : ℂ)‖ + ‖(2 : ℂ) * p.eval z‖ :=
        norm_sub_le _ _
      _ ≤ 3 + 2 * e := by
        rw [norm_mul]
        norm_num
        linarith
  calc
    ‖p.eval z‖ ^ 2 * ‖(3 : ℂ) - 2 * p.eval z‖ ≤
        e ^ 2 * (3 + 2 * e) := by
      gcongr
    _ ≤ 4 * e ^ 2 := by nlinarith [sq_nonneg e]

lemma sharpenStep_sub_one_norm_le {p : Polynomial ℂ} {z : ℂ} {e : ℝ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 8) (hp : ‖p.eval z - 1‖ ≤ e) :
    ‖(sharpenStep p).eval z - 1‖ ≤ 4 * e ^ 2 := by
  have hu : ‖1 - p.eval z‖ ≤ e := by simpa [norm_sub_rev] using hp
  rw [← norm_neg, neg_sub, one_sub_sharpenStep_eval, norm_mul, norm_pow]
  have hfactor : ‖(3 : ℂ) - 2 * (1 - p.eval z)‖ ≤ 3 + 2 * e := by
    calc
      ‖(3 : ℂ) - 2 * (1 - p.eval z)‖ ≤
          ‖(3 : ℂ)‖ + ‖(2 : ℂ) * (1 - p.eval z)‖ := norm_sub_le _ _
      _ ≤ 3 + 2 * e := by
        rw [norm_mul]
        norm_num
        linarith
  calc
    ‖1 - p.eval z‖ ^ 2 * ‖(3 : ℂ) - 2 * (1 - p.eval z)‖ ≤
        e ^ 2 * (3 + 2 * e) := by gcongr
    _ ≤ 4 * e ^ 2 := by nlinarith [sq_nonneg e]

lemma sharpenError_nonneg (k : ℕ) : 0 ≤ sharpenError k := by
  unfold sharpenError
  positivity

lemma sharpenError_le_eighth (k : ℕ) : sharpenError k ≤ 1 / 8 := by
  induction k with
  | zero => rw [sharpenError_zero]
  | succ k ih =>
      rw [sharpenError_succ]
      nlinarith [sharpenError_nonneg k, sq_nonneg (sharpenError k)]

lemma sharpenPolynomial_norm_le
    {p : Polynomial ℂ} {z : ℂ} (hp : ‖p.eval z‖ ≤ 1 / 8) (k : ℕ) :
    ‖(sharpenPolynomial p k).eval z‖ ≤ sharpenError k := by
  induction k with
  | zero =>
      rw [sharpenPolynomial_zero, sharpenError_zero]
      exact hp
  | succ k ih =>
      rw [sharpenPolynomial_succ, sharpenError_succ]
      exact sharpenStep_norm_le (sharpenError_nonneg k) (sharpenError_le_eighth k) ih

lemma sharpenPolynomial_sub_one_norm_le
    {p : Polynomial ℂ} {z : ℂ} (hp : ‖p.eval z - 1‖ ≤ 1 / 8) (k : ℕ) :
    ‖(sharpenPolynomial p k).eval z - 1‖ ≤ sharpenError k := by
  induction k with
  | zero =>
      rw [sharpenPolynomial_zero, sharpenError_zero]
      exact hp
  | succ k ih =>
      rw [sharpenPolynomial_succ, sharpenError_succ]
      exact sharpenStep_sub_one_norm_le (sharpenError_nonneg k)
        (sharpenError_le_eighth k) ih

lemma sharpenStep_natDegree_add_one_le (p : Polynomial ℂ) :
    (sharpenStep p).natDegree + 1 ≤ 3 * (p.natDegree + 1) := by
  unfold sharpenStep
  calc
    (p ^ 2 * (Polynomial.C 3 - Polynomial.C 2 * p)).natDegree + 1 ≤
        (p ^ 2).natDegree +
          (Polynomial.C 3 - Polynomial.C 2 * p).natDegree + 1 :=
      Nat.add_le_add_right Polynomial.natDegree_mul_le 1
    _ ≤ 2 * p.natDegree + p.natDegree + 1 := by
      have hp2 : (p ^ 2).natDegree ≤ 2 * p.natDegree := by
        simpa using Polynomial.natDegree_pow_le p 2
      have hsub : (Polynomial.C 3 - Polynomial.C 2 * p).natDegree ≤ p.natDegree := by
        refine (Polynomial.natDegree_sub_le _ _).trans ?_
        exact max_le (by simp) (Polynomial.natDegree_mul_le.trans (by simp))
      omega
    _ ≤ 3 * (p.natDegree + 1) := by omega

lemma sharpenPolynomial_natDegree_add_one_le (p : Polynomial ℂ) (k : ℕ) :
    (sharpenPolynomial p k).natDegree + 1 ≤ 3 ^ k * (p.natDegree + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [sharpenPolynomial_succ]
      calc
        _ ≤ 3 * ((sharpenPolynomial p k).natDegree + 1) :=
          sharpenStep_natDegree_add_one_le _
        _ ≤ 3 * (3 ^ k * (p.natDegree + 1)) := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ (k + 1) * (p.natDegree + 1) := by rw [pow_succ]; ring

lemma ratio_div_one_sub_le_fifteenth {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 16) : q / (1 - q) ≤ 1 / 15 := by
  have hden : 0 < 1 - q := by linarith
  rw [div_le_iff₀ hden]
  linarith

lemma baseChapletSeparator_sub_one_norm_le_eighth
    {R S T ε ρ : ℝ} {N : ℕ}
    (hR0 : 0 ≤ R) (hRρ : R < ρ) (hρS : ρ < S) (hST : S ≤ T)
    (hε : 0 < ε) (hN : N ≠ 0)
    (hinner : (R / ρ) ^ N ≤ 1 / 16)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖(baseChapletSeparator R S T ε ρ N).eval z - 1‖ ≤ 1 / 8 := by
  have hρ : 0 < ρ := hR0.trans_lt hRρ
  have hzK : z ∈ Erdos1118Construction.chapletSet R S T ε :=
    Or.inl (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)
  let z' : Erdos1118Construction.chapletSet R S T ε := ⟨z, hzK⟩
  let r : ℂ := (((ρ : ℝ) : ℂ) ^ N) *
    ((Erdos1118Construction.chapletDenominator ρ N).eval z)⁻¹
  let e : ℂ := inverseResidual (Erdos1118Construction.chapletDenominator ρ N)
    (refinedChapletDenominatorInverse R S T ε ρ N 2) z
  have hratio0 : 0 ≤ (R / ρ) ^ N :=
    pow_nonneg (div_nonneg hR0 hρ.le) N
  have hrsub : ‖r - 1‖ ≤ 1 / 15 := by
    have hsep := Erdos1118Construction.chapletSeparator_sub_one_norm_le
      (R := R) (S := S) (T := T) (ε := ε) (ρ := ρ) (N := N)
      hR0 hρ hN hRρ hρS z' hz
    have hbound := ratio_div_one_sub_le_fifteenth hratio0 hinner
    have heval :
        Erdos1118Construction.chapletSeparatorOn R S T ε ρ N hρ hN hRρ hρS z' = r := by
      rw [Erdos1118Construction.chapletSeparatorOn_apply]
      change (((ρ : ℝ) : ℂ) ^ N) *
          (z ^ N + (((ρ : ℝ) : ℂ) ^ N))⁻¹ =
        (((ρ : ℝ) : ℂ) ^ N) *
          ((Erdos1118Construction.chapletDenominator ρ N).eval z)⁻¹
      simp [Erdos1118Construction.chapletDenominator]
    rw [heval] at hsep
    exact hsep.trans hbound
  have hr : ‖r‖ ≤ 16 / 15 := by
    calc
      ‖r‖ = ‖(r - 1) + 1‖ := by ring_nf
      _ ≤ ‖r - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 16 / 15 := by norm_num at *; linarith
  have he : ‖e‖ ≤ 1 / 256 := by
    have he' := refinedChapletDenominatorInverse_residual_le
      hR0 hRρ hρS hST hε hρ hN (k := 2) hzK
    norm_num [e] at he' ⊢
    exact he'
  have hformula : (baseChapletSeparator R S T ε ρ N).eval z = r * (1 - e) := by
    simpa only [r, e] using baseChapletSeparator_eval_eq hρ hN hRρ hρS hzK
  rw [hformula]
  have hid : r * (1 - e) - 1 = (r - 1) - r * e := by ring
  rw [hid]
  calc
    ‖(r - 1) - r * e‖ ≤ ‖r - 1‖ + ‖r * e‖ := norm_sub_le _ _
    _ ≤ 1 / 15 + (16 / 15) * (1 / 256) := by
      rw [norm_mul]
      gcongr
    _ ≤ 1 / 8 := by norm_num

lemma baseChapletSeparator_norm_le_eighth
    {R S T ε ρ : ℝ} {N : ℕ}
    (hR0 : 0 ≤ R) (hRρ : R < ρ) (hρS : ρ < S) (hST : S ≤ T)
    (hε : 0 < ε) (hN : N ≠ 0)
    (houter : (ρ / S) ^ N ≤ 1 / 16)
    {z : ℂ} (hzS : S ≤ ‖z‖) (hzT : ‖z‖ ≤ T)
    (hzcorr : z.re ≤ 0 ∨ ε ≤ |z.im|) :
    ‖(baseChapletSeparator R S T ε ρ N).eval z‖ ≤ 1 / 8 := by
  have hρ : 0 < ρ := hR0.trans_lt hRρ
  have hS : 0 < S := hρ.trans hρS
  have hzK : z ∈ Erdos1118Construction.chapletSet R S T ε :=
    Or.inr ⟨hzS, hzT, hzcorr⟩
  let z' : Erdos1118Construction.chapletSet R S T ε := ⟨z, hzK⟩
  let r : ℂ := (((ρ : ℝ) : ℂ) ^ N) *
    ((Erdos1118Construction.chapletDenominator ρ N).eval z)⁻¹
  let e : ℂ := inverseResidual (Erdos1118Construction.chapletDenominator ρ N)
    (refinedChapletDenominatorInverse R S T ε ρ N 2) z
  have hratio0 : 0 ≤ (ρ / S) ^ N :=
    pow_nonneg (div_nonneg hρ.le hS.le) N
  have hr : ‖r‖ ≤ 1 / 15 := by
    have hsep := Erdos1118Construction.chapletSeparator_norm_le
      (R := R) (S := S) (T := T) (ε := ε) (ρ := ρ) (N := N)
      hS hρ hN hRρ hρS z' hzS
    have hbound := ratio_div_one_sub_le_fifteenth hratio0 houter
    have heval :
        Erdos1118Construction.chapletSeparatorOn R S T ε ρ N hρ hN hRρ hρS z' = r := by
      rw [Erdos1118Construction.chapletSeparatorOn_apply]
      change (((ρ : ℝ) : ℂ) ^ N) *
          (z ^ N + (((ρ : ℝ) : ℂ) ^ N))⁻¹ =
        (((ρ : ℝ) : ℂ) ^ N) *
          ((Erdos1118Construction.chapletDenominator ρ N).eval z)⁻¹
      simp [Erdos1118Construction.chapletDenominator]
    rw [heval] at hsep
    exact hsep.trans hbound
  have he : ‖e‖ ≤ 1 / 256 := by
    have he' := refinedChapletDenominatorInverse_residual_le
      hR0 hRρ hρS hST hε hρ hN (k := 2) hzK
    norm_num [e] at he' ⊢
    exact he'
  have hformula : (baseChapletSeparator R S T ε ρ N).eval z = r * (1 - e) := by
    simpa only [r, e] using baseChapletSeparator_eval_eq hρ hN hRρ hρS hzK
  rw [hformula, norm_mul]
  have hone : ‖(1 : ℂ) - e‖ ≤ 1 + 1 / 256 := by
    exact (norm_sub_le _ _).trans (by norm_num at *; linarith)
  calc
    ‖r‖ * ‖(1 : ℂ) - e‖ ≤ (1 / 15) * (1 + 1 / 256) := by gcongr
    _ ≤ 1 / 8 := by norm_num

/-- The fully sharpened quantitative cutoff. -/
noncomputable def quantitativeChapletSeparator
    (R S T ε ρ : ℝ) (N k : ℕ) : Polynomial ℂ :=
  sharpenPolynomial (baseChapletSeparator R S T ε ρ N) k

lemma quantitativeChapletSeparator_sub_one_norm_le
    {R S T ε ρ : ℝ} {N k : ℕ}
    (hR0 : 0 ≤ R) (hRρ : R < ρ) (hρS : ρ < S) (hST : S ≤ T)
    (hε : 0 < ε) (hN : N ≠ 0)
    (hinner : (R / ρ) ^ N ≤ 1 / 16)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖(quantitativeChapletSeparator R S T ε ρ N k).eval z - 1‖ ≤
      sharpenError k := by
  apply sharpenPolynomial_sub_one_norm_le
  exact baseChapletSeparator_sub_one_norm_le_eighth hR0 hRρ hρS hST hε hN hinner hz

lemma quantitativeChapletSeparator_norm_le
    {R S T ε ρ : ℝ} {N k : ℕ}
    (hR0 : 0 ≤ R) (hRρ : R < ρ) (hρS : ρ < S) (hST : S ≤ T)
    (hε : 0 < ε) (hN : N ≠ 0)
    (houter : (ρ / S) ^ N ≤ 1 / 16)
    {z : ℂ} (hzS : S ≤ ‖z‖) (hzT : ‖z‖ ≤ T)
    (hzcorr : z.re ≤ 0 ∨ ε ≤ |z.im|) :
    ‖(quantitativeChapletSeparator R S T ε ρ N k).eval z‖ ≤ sharpenError k := by
  apply sharpenPolynomial_norm_le
  exact baseChapletSeparator_norm_le_eighth hR0 hRρ hρS hST hε hN houter
    hzS hzT hzcorr

/-! ## A normalized stage geometry -/

lemma nat_ratio_pow_four_mul_le {A : ℕ} (hA : 0 < A) :
    (((A : ℝ) / (A + 1 : ℕ)) ^ (4 * A)) ≤ 1 / 16 := by
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hbern : (2 : ℝ) ≤ (1 + 1 / (A : ℝ)) ^ A := by
    have h := one_add_mul_le_pow (a := 1 / (A : ℝ))
      (by
        have hnonneg : (0 : ℝ) ≤ 1 / A := by positivity
        linarith) A
    calc
      (2 : ℝ) = 1 + (A : ℝ) * (1 / (A : ℝ)) := by field_simp; norm_num
      _ ≤ (1 + 1 / (A : ℝ)) ^ A := h
  have hratio : ((A : ℝ) / (A + 1 : ℕ)) ^ A ≤ 1 / 2 := by
    rw [div_pow]
    have hden : (0 : ℝ) < ((A + 1 : ℕ) : ℝ) ^ A := by positivity
    rw [div_le_iff₀ hden]
    have hA_pow : (0 : ℝ) < ((A : ℝ) ^ A) := by positivity
    have hone : 1 + 1 / (A : ℝ) = ((A + 1 : ℕ) : ℝ) / (A : ℝ) := by
      push_cast
      field_simp
    rw [hone, div_pow] at hbern
    have hbern' : 2 * ((A : ℝ) ^ A) ≤ (((A + 1 : ℕ) : ℝ) ^ A) :=
      (le_div_iff₀ hA_pow).mp hbern
    nlinarith
  calc
    ((A : ℝ) / (A + 1 : ℕ)) ^ (4 * A) =
        (((A : ℝ) / (A + 1 : ℕ)) ^ A) ^ 4 := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ (1 / 2 : ℝ) ^ 4 := by gcongr
    _ = 1 / 16 := by norm_num

noncomputable def stageGap (R : ℝ) (A : ℕ) : ℝ := R / A
noncomputable def stagePoleRadius (R : ℝ) (A : ℕ) : ℝ := R + stageGap R A
noncomputable def stagePatchRadius (R : ℝ) (A : ℕ) : ℝ := R + 2 * stageGap R A
noncomputable def stageOuterRadius (R : ℝ) : ℝ := 4 * R
noncomputable def stageExponent (A : ℕ) : ℕ := 8 * (A + 1)

lemma stageGap_pos {R : ℝ} {A : ℕ} (hR : 0 < R) (hA : 0 < A) :
    0 < stageGap R A := by
  unfold stageGap
  positivity

lemma stage_inner_lt_pole {R : ℝ} {A : ℕ} (hR : 0 < R) (hA : 0 < A) :
    R < stagePoleRadius R A := by
  unfold stagePoleRadius
  linarith [stageGap_pos hR hA]

lemma stage_pole_lt_patch {R : ℝ} {A : ℕ} (hR : 0 < R) (hA : 0 < A) :
    stagePoleRadius R A < stagePatchRadius R A := by
  unfold stagePoleRadius stagePatchRadius
  linarith [stageGap_pos hR hA]

lemma stage_patch_le_outer {R : ℝ} {A : ℕ} (hR : 0 < R) (hA : 0 < A) :
    stagePatchRadius R A ≤ stageOuterRadius R := by
  have hAreal : (1 : ℝ) ≤ A := by exact_mod_cast hA
  unfold stagePatchRadius stageOuterRadius stageGap
  have hdiv : R / (A : ℝ) ≤ R := (div_le_self hR.le hAreal)
  linarith

lemma stageExponent_ne_zero (A : ℕ) : stageExponent A ≠ 0 := by
  unfold stageExponent
  omega

lemma stage_inner_ratio_pow_le {R : ℝ} {A : ℕ} (hR : 0 < R) (hA : 0 < A) :
    (R / stagePoleRadius R A) ^ stageExponent A ≤ 1 / 16 := by
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hratio : R / stagePoleRadius R A = (A : ℝ) / (A + 1 : ℕ) := by
    unfold stagePoleRadius stageGap
    push_cast
    field_simp
  rw [hratio]
  have hbase0 : 0 ≤ (A : ℝ) / (A + 1 : ℕ) := by positivity
  have hbase1 : (A : ℝ) / (A + 1 : ℕ) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < (A + 1 : ℕ))]
    norm_num
  exact (pow_le_pow_of_le_one hbase0 hbase1
    (show 4 * A ≤ stageExponent A by unfold stageExponent; omega)).trans
      (nat_ratio_pow_four_mul_le hA)

lemma stage_outer_ratio_pow_le {R : ℝ} {A : ℕ} (hR : 0 < R) (hA : 0 < A) :
    (stagePoleRadius R A / stagePatchRadius R A) ^ stageExponent A ≤ 1 / 16 := by
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hratio : stagePoleRadius R A / stagePatchRadius R A =
      ((A + 1 : ℕ) : ℝ) / (A + 2 : ℕ) := by
    unfold stagePoleRadius stagePatchRadius stageGap
    push_cast
    field_simp
  rw [hratio]
  let B := A + 1
  have hB : 0 < B := by omega
  have hbase1 : (B : ℝ) / (B + 1 : ℕ) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < (B + 1 : ℕ))]
    norm_num
  have hbase0 : 0 ≤ (B : ℝ) / (B + 1 : ℕ) := by positivity
  have hexp : 4 * B ≤ stageExponent A := by
    unfold B stageExponent
    omega
  exact (pow_le_pow_of_le_one hbase0 hbase1 hexp).trans (nat_ratio_pow_four_mul_le hB)

/-- The cutoff factor associated to one radial stage. -/
noncomputable def stageFactor (R : ℝ) (A k : ℕ) : Polynomial ℂ :=
  quantitativeChapletSeparator R (stagePatchRadius R A) (stageOuterRadius R)
    (stageGap R A) (stagePoleRadius R A) (stageExponent A) k

lemma stageFactor_sub_one_norm_le
    {R : ℝ} {A k : ℕ} (hR : 0 < R) (hA : 0 < A)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖(stageFactor R A k).eval z - 1‖ ≤ sharpenError k := by
  exact quantitativeChapletSeparator_sub_one_norm_le hR.le
    (stage_inner_lt_pole hR hA) (stage_pole_lt_patch hR hA)
    (stage_patch_le_outer hR hA) (stageGap_pos hR hA)
    (stageExponent_ne_zero A) (stage_inner_ratio_pow_le hR hA) hz

lemma stageFactor_norm_le
    {R : ℝ} {A k : ℕ} (hR : 0 < R) (hA : 0 < A)
    {z : ℂ} (hzS : stagePatchRadius R A ≤ ‖z‖)
    (hzT : ‖z‖ ≤ stageOuterRadius R)
    (hzcorr : z.re ≤ 0 ∨ stageGap R A ≤ |z.im|) :
    ‖(stageFactor R A k).eval z‖ ≤ sharpenError k := by
  exact quantitativeChapletSeparator_norm_le hR.le
    (stage_inner_lt_pole hR hA) (stage_pole_lt_patch hR hA)
    (stage_patch_le_outer hR hA) (stageGap_pos hR hA)
    (stageExponent_ne_zero A) (stage_outer_ratio_pow_le hR hA) hzS hzT hzcorr

/-! ## Extrapolating a polynomial from an inner disk -/

lemma norm_coeff_mul_radius_pow_le_of_norm_eval_le
    {p : Polynomial ℂ} {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ R → ‖p.eval z‖ ≤ B) (i : ℕ) :
    ‖p.coeff i‖ * R ^ i ≤ B := by
  let q : Polynomial ℂ := p.comp (Polynomial.C (R : ℂ) * Polynomial.X)
  have hcircle : CircleIntegrable (fun z : ℂ ↦ ‖q.eval z‖ ^ 2) 0 1 := by
    exact (show Continuous (fun z : ℂ ↦ ‖q.eval z‖ ^ 2) by fun_prop).continuousOn.circleIntegrable'
  have havg : Real.circleAverage (fun z : ℂ ↦ ‖q.eval z‖ ^ 2) 0 1 ≤ B ^ 2 := by
    apply Real.circleAverage_mono_on_of_le_circle hcircle
    intro z hz
    have hznorm : ‖z‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_left] using hz
    have hscaled : ‖(R : ℂ) * z‖ = R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, hznorm, mul_one]
    have hp := hbound ((R : ℂ) * z) (by rw [hscaled])
    have hp0 := norm_nonneg (q.eval z)
    have heval : q.eval z = p.eval ((R : ℂ) * z) := by
      simp [q, Polynomial.eval_comp]
    rw [heval]
    nlinarith [norm_nonneg (p.eval ((R : ℂ) * z))]
  have hsum : ∑ j ∈ q.support, ‖q.coeff j‖ ^ 2 ≤ B ^ 2 := by
    rw [q.sum_sq_norm_coeff_eq_circleAverage]
    exact havg
  have hterm : ‖q.coeff i‖ ^ 2 ≤ ∑ j ∈ q.support, ‖q.coeff j‖ ^ 2 := by
    by_cases hi : i ∈ q.support
    · exact Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖q.coeff j‖) hi
    · have hcoeff : q.coeff i = 0 := by
        by_contra hne
        exact hi (Polynomial.mem_support_iff.mpr hne)
      rw [hcoeff, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
      exact Finset.sum_nonneg fun j _ ↦ sq_nonneg ‖q.coeff j‖
  have hqi : ‖q.coeff i‖ ≤ B := by
    nlinarith [norm_nonneg (q.coeff i), hterm.trans hsum]
  simpa [q, Polynomial.comp_C_mul_X_coeff, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR, norm_pow] using hqi

lemma norm_eval_le_of_norm_le_disk
    {p : Polynomial ℂ} {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ R → ‖p.eval z‖ ≤ B) (z : ℂ) :
    ‖p.eval z‖ ≤
      (p.natDegree + 1 : ℕ) * B *
        (max 1 (‖z‖ / R)) ^ p.natDegree := by
  by_cases hz : ‖z‖ ≤ R
  · have hfac : (1 : ℝ) ≤ (p.natDegree + 1 : ℕ) := by exact_mod_cast Nat.succ_pos _
    have hmax : (1 : ℝ) ≤ max 1 (‖z‖ / R) := le_max_left _ _
    have hpow : (1 : ℝ) ≤ (max 1 (‖z‖ / R)) ^ p.natDegree := one_le_pow₀ hmax
    calc
      ‖p.eval z‖ ≤ B := hbound z hz
      _ ≤ (p.natDegree + 1 : ℕ) * B := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac hB
      _ = (p.natDegree + 1 : ℕ) * B * 1 := by ring
      _ ≤ (p.natDegree + 1 : ℕ) * B *
          (max 1 (‖z‖ / R)) ^ p.natDegree :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (by positivity) hB)
  · have hratio : 1 ≤ ‖z‖ / R := (le_div_iff₀ hR).2 (by
      simpa using (le_of_not_ge hz))
    have hratio0 : 0 ≤ ‖z‖ / R := hratio.trans' (by norm_num)
    rw [Polynomial.eval_eq_sum_range]
    calc
      ‖∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * z ^ i‖ ≤
          ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i * z ^ i‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range (p.natDegree + 1),
          B * (‖z‖ / R) ^ p.natDegree := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ p.natDegree := by simpa using hi
        have hc := norm_coeff_mul_radius_pow_le_of_norm_eval_le hR hB hbound i
        have hpowmono : (‖z‖ / R) ^ i ≤ (‖z‖ / R) ^ p.natDegree :=
          pow_right_mono₀ hratio hi'
        have hrewrite : ‖p.coeff i * z ^ i‖ =
            (‖p.coeff i‖ * R ^ i) * (‖z‖ / R) ^ i := by
          rw [norm_mul, norm_pow, div_pow]
          field_simp
        rw [hrewrite]
        exact mul_le_mul hc hpowmono (pow_nonneg hratio0 i) hB
      _ = (p.natDegree + 1 : ℕ) * B *
          (max 1 (‖z‖ / R)) ^ p.natDegree := by
        rw [max_eq_right hratio]
        simp [nsmul_eq_mul, mul_assoc]

/-! ## Degree of a normalized stage -/

lemma stage_chapletClearance {R : ℝ} {A : ℕ} (hR : 0 < R) (hA : 0 < A) :
    chapletClearance R (stagePatchRadius R A) (stageGap R A)
      (stagePoleRadius R A) = stageGap R A := by
  unfold chapletClearance stagePoleRadius stagePatchRadius
  have hg : 0 ≤ stageGap R A := (stageGap_pos hR hA).le
  simp only [add_sub_cancel_left, add_sub_add_left_eq_sub, two_mul]
  rw [min_eq_left le_rfl, min_eq_left le_rfl]

lemma stage_chapletPoleSteps {R : ℝ} {A : ℕ} (hR : 0 < R) (hA : 0 < A) :
    chapletPoleSteps (stageOuterRadius R)
      (chapletClearance R (stagePatchRadius R A) (stageGap R A)
        (stagePoleRadius R A)) = 256 * A := by
  rw [stage_chapletClearance hR hA]
  unfold chapletPoleSteps stageOuterRadius stageGap
  have hR0 : R ≠ 0 := hR.ne'
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have heq : 64 * (4 * R) / (R / (A : ℝ)) = (256 * A : ℕ) := by
    push_cast
    field_simp
    ring
  rw [heq, Nat.ceil_natCast]

lemma baseChapletSeparator_natDegree_add_one_le
    {R S T ε ρ : ℝ} {N : ℕ} (hρ : 0 < ρ) :
    (baseChapletSeparator R S T ε ρ N).natDegree + 1 ≤
      (refinedChapletDenominatorInverse R S T ε ρ N 2).natDegree + 1 := by
  unfold baseChapletSeparator
  have hC : (Polynomial.C (((ρ : ℝ) : ℂ) ^ N)).natDegree = 0 :=
    Polynomial.natDegree_C _
  calc
    _ ≤ (Polynomial.C (((ρ : ℝ) : ℂ) ^ N)).natDegree +
        (refinedChapletDenominatorInverse R S T ε ρ N 2).natDegree + 1 :=
      Nat.add_le_add_right Polynomial.natDegree_mul_le 1
    _ = _ := by rw [hC]; omega

lemma stageFactor_natDegree_add_one_le
    {R : ℝ} {A k : ℕ} (hR : 0 < R) (hA : 0 < A) :
    (stageFactor R A k).natDegree + 1 ≤
      3 ^ k *
        (3 ^ 2 *
          (8 ^ (stageExponent A) *
              (2 ^ (2 * (256 * A) + 1) + stageExponent A + 1) +
            stageExponent A + 1)) := by
  let R' := R
  let S := stagePatchRadius R A
  let T := stageOuterRadius R
  let ε := stageGap R A
  let ρ := stagePoleRadius R A
  let N := stageExponent A
  have hρ : 0 < ρ := hR.trans (stage_inner_lt_pole hR hA)
  have hN : N ≠ 0 := stageExponent_ne_zero A
  have hsharp := sharpenPolynomial_natDegree_add_one_le
    (baseChapletSeparator R' S T ε ρ N) k
  have hbase := baseChapletSeparator_natDegree_add_one_le
    (R := R') (S := S) (T := T) (ε := ε) (ρ := ρ) (N := N) hρ
  have hinv := refinedChapletDenominatorInverse_natDegree_add_one_le
    (ρ := ρ) hN R' S T ε 2
  have hL : chapletPoleSteps T (chapletClearance R' S ε ρ) = 256 * A := by
    simpa [R', S, T, ε, ρ] using stage_chapletPoleSteps hR hA
  change (sharpenPolynomial (baseChapletSeparator R' S T ε ρ N) k).natDegree + 1 ≤ _
  calc
    _ ≤ 3 ^ k * ((baseChapletSeparator R' S T ε ρ N).natDegree + 1) := hsharp
    _ ≤ 3 ^ k *
        ((refinedChapletDenominatorInverse R' S T ε ρ N 2).natDegree + 1) :=
      Nat.mul_le_mul_left _ hbase
    _ ≤ 3 ^ k *
        (3 ^ 2 *
          (8 ^ N *
              (2 ^ (2 * chapletPoleSteps T (chapletClearance R' S ε ρ) + 1) + N + 1) +
            N + 1)) := Nat.mul_le_mul_left _ hinv
    _ = _ := by rw [hL]

/-! ## Arbitrarily high-order polynomial sharpening -/

/-- Degree used by the symmetric binomial cutoff of order `m`. -/
def cutoffDegree (m : ℕ) : ℕ := 2 * m - 1

/-- One term of the binomial cutoff. -/
noncomputable def cutoffTerm (p : Polynomial ℂ) (d j : ℕ) : Polynomial ℂ :=
  p ^ j * (1 - p) ^ (d - j) * Polynomial.C (d.choose j : ℂ)

/-- The upper half of the binomial expansion of `(p + (1-p))^(2m-1)`. -/
noncomputable def highOrderCutoff (p : Polynomial ℂ) (m : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.Ico m (cutoffDegree m + 1), cutoffTerm p (cutoffDegree m) j

/-- The complementary lower half. -/
noncomputable def lowOrderCutoff (p : Polynomial ℂ) (m : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range m, cutoffTerm p (cutoffDegree m) j

lemma cutoffDegree_add_one {m : ℕ} (hm : 0 < m) : cutoffDegree m + 1 = 2 * m := by
  unfold cutoffDegree
  omega

lemma low_add_highOrderCutoff {p : Polynomial ℂ} {m : ℕ} (hm : 0 < m) :
    lowOrderCutoff p m + highOrderCutoff p m = 1 := by
  let d := cutoffDegree m
  have hmd : m ≤ d + 1 := by rw [cutoffDegree_add_one hm]; omega
  have hsplit := Finset.sum_range_add_sum_Ico (fun j ↦ cutoffTerm p d j) hmd
  rw [lowOrderCutoff, highOrderCutoff]
  change (∑ j ∈ Finset.range m, cutoffTerm p d j) +
      (∑ j ∈ Finset.Ico m (d + 1), cutoffTerm p d j) = 1
  rw [hsplit]
  simp only [cutoffTerm]
  change (∑ j ∈ Finset.range (d + 1),
      p ^ j * (1 - p) ^ (d - j) * (d.choose j : Polynomial ℂ)) = 1
  rw [← add_pow]
  ring

@[simp] lemma cutoffTerm_eval (p : Polynomial ℂ) (d j : ℕ) (z : ℂ) :
    (cutoffTerm p d j).eval z =
      (p.eval z) ^ j * (1 - p.eval z) ^ (d - j) * (d.choose j : ℂ) := by
  simp [cutoffTerm]

lemma highOrderCutoff_eval (p : Polynomial ℂ) (m : ℕ) (z : ℂ) :
    (highOrderCutoff p m).eval z =
      ∑ j ∈ Finset.Ico m (cutoffDegree m + 1),
        (p.eval z) ^ j * (1 - p.eval z) ^ (cutoffDegree m - j) *
          (cutoffDegree m).choose j := by
  rw [highOrderCutoff, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [cutoffTerm]

lemma lowOrderCutoff_eval (p : Polynomial ℂ) (m : ℕ) (z : ℂ) :
    (lowOrderCutoff p m).eval z =
      ∑ j ∈ Finset.range m,
        (p.eval z) ^ j * (1 - p.eval z) ^ (cutoffDegree m - j) *
          (cutoffDegree m).choose j := by
  rw [lowOrderCutoff, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [cutoffTerm]

lemma two_mul_nat_le_thirtytwo_pow {m : ℕ} (hm : 0 < m) : 2 * m ≤ 32 ^ m := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        norm_num
      · have ihm := ih (Nat.pos_of_ne_zero hm0)
        have hp : 1 ≤ 32 ^ m := one_le_pow₀ (by norm_num)
        rw [pow_succ]
        nlinarith

lemma cutoff_numeric_bound {m : ℕ} (hm : 0 < m) :
    (2 * m : ℝ) * (1 / 1024 : ℝ) ^ m * 4 ^ (cutoffDegree m) ≤
      (1 / 2 : ℝ) ^ m := by
  have hnat := two_mul_nat_le_thirtytwo_pow hm
  have hreal : (2 * m : ℝ) ≤ 32 ^ m := by exact_mod_cast hnat
  have hd : cutoffDegree m ≤ 2 * m := by unfold cutoffDegree; omega
  have hpow : (4 : ℝ) ^ cutoffDegree m ≤ 4 ^ (2 * m) :=
    pow_right_mono₀ (by norm_num : (1 : ℝ) ≤ 4) hd
  calc
    (2 * m : ℝ) * (1 / 1024 : ℝ) ^ m * 4 ^ cutoffDegree m ≤
        32 ^ m * (1 / 1024 : ℝ) ^ m * 4 ^ (2 * m) := by
      gcongr
    _ = (1 / 2 : ℝ) ^ m := by
      rw [show (4 : ℝ) ^ (2 * m) = (16 : ℝ) ^ m by
        rw [show 2 * m = m * 2 by omega, pow_mul, pow_two, ← mul_pow]
        norm_num]
      rw [← mul_pow, ← mul_pow]
      norm_num

lemma norm_cutoffTerm_le
    {p : Polynomial ℂ} {z : ℂ} {m j : ℕ}
    (hm : 0 < m) (hj : j ∈ Finset.Ico m (cutoffDegree m + 1))
    (hp : ‖p.eval z‖ ≤ 1 / 1024) :
    ‖(cutoffTerm p (cutoffDegree m) j).eval z‖ ≤
      (1 / 1024 : ℝ) ^ m * 4 ^ cutoffDegree m := by
  have hjm : m ≤ j := Finset.mem_Ico.mp hj |>.1
  have hjd : j ≤ cutoffDegree m := by
    have := Finset.mem_Ico.mp hj |>.2
    omega
  have hp0 : 0 ≤ ‖p.eval z‖ := norm_nonneg _
  have hp1 : ‖p.eval z‖ ≤ 1 := hp.trans (by norm_num)
  have hppow : ‖p.eval z‖ ^ j ≤ (1 / 1024 : ℝ) ^ m := by
    calc
      ‖p.eval z‖ ^ j ≤ ‖p.eval z‖ ^ m := pow_le_pow_of_le_one hp0 hp1 hjm
      _ ≤ (1 / 1024 : ℝ) ^ m := pow_le_pow_left₀ hp0 hp m
  have hone : ‖(1 : ℂ) - p.eval z‖ ≤ 2 := by
    calc
      ‖(1 : ℂ) - p.eval z‖ ≤ 1 + ‖p.eval z‖ := by simpa using norm_sub_le (1 : ℂ) (p.eval z)
      _ ≤ 2 := by linarith
  have honepow : ‖(1 : ℂ) - p.eval z‖ ^ (cutoffDegree m - j) ≤
      2 ^ cutoffDegree m := by
    calc
      _ ≤ 2 ^ (cutoffDegree m - j) := pow_le_pow_left₀ (norm_nonneg _) hone _
      _ ≤ 2 ^ cutoffDegree m := pow_right_mono₀ (by norm_num) (Nat.sub_le _ _)
  have hchoose : ((cutoffDegree m).choose j : ℝ) ≤ 2 ^ cutoffDegree m := by
    exact_mod_cast Nat.choose_le_two_pow (cutoffDegree m) j
  rw [cutoffTerm_eval, norm_mul, norm_mul, norm_pow, norm_pow, norm_natCast]
  calc
    ‖p.eval z‖ ^ j * ‖(1 : ℂ) - p.eval z‖ ^ (cutoffDegree m - j) *
        (cutoffDegree m).choose j ≤
        (1 / 1024 : ℝ) ^ m * 2 ^ cutoffDegree m * 2 ^ cutoffDegree m := by
      gcongr
    _ = (1 / 1024 : ℝ) ^ m * 4 ^ cutoffDegree m := by
      rw [show (4 : ℝ) ^ cutoffDegree m =
          2 ^ cutoffDegree m * 2 ^ cutoffDegree m by rw [← mul_pow]; norm_num]
      ring

lemma highOrderCutoff_norm_le {p : Polynomial ℂ} {z : ℂ} {m : ℕ}
    (hm : 0 < m) (hp : ‖p.eval z‖ ≤ 1 / 1024) :
    ‖(highOrderCutoff p m).eval z‖ ≤ (1 / 2 : ℝ) ^ m := by
  rw [highOrderCutoff_eval]
  calc
    ‖∑ j ∈ Finset.Ico m (cutoffDegree m + 1),
        p.eval z ^ j * (1 - p.eval z) ^ (cutoffDegree m - j) *
          (cutoffDegree m).choose j‖ ≤
        ∑ j ∈ Finset.Ico m (cutoffDegree m + 1),
          ‖(cutoffTerm p (cutoffDegree m) j).eval z‖ := by
      simpa only [cutoffTerm_eval] using
        norm_sum_le (Finset.Ico m (cutoffDegree m + 1))
          (fun j ↦ (cutoffTerm p (cutoffDegree m) j).eval z)
    _ ≤ ∑ _j ∈ Finset.Ico m (cutoffDegree m + 1),
          ((1 / 1024 : ℝ) ^ m * 4 ^ cutoffDegree m) := by
      exact Finset.sum_le_sum fun j hj ↦ norm_cutoffTerm_le hm hj hp
    _ ≤ (2 * m : ℝ) * (1 / 1024 : ℝ) ^ m * 4 ^ cutoffDegree m := by
      have hcard : (Finset.Ico m (cutoffDegree m + 1)).card ≤ 2 * m := by
        simp [cutoffDegree_add_one hm]
      rw [Finset.sum_const, nsmul_eq_mul]
      calc
        ((Finset.Ico m (cutoffDegree m + 1)).card : ℝ) *
            ((1 / 1024 : ℝ) ^ m * 4 ^ cutoffDegree m) ≤
            (2 * m : ℝ) * ((1 / 1024 : ℝ) ^ m * 4 ^ cutoffDegree m) := by
          gcongr
          exact_mod_cast hcard
        _ = _ := by ring
    _ ≤ (1 / 2 : ℝ) ^ m := cutoff_numeric_bound hm

lemma highOrderCutoff_sub_one_norm_le {p : Polynomial ℂ} {z : ℂ} {m : ℕ}
    (hm : 0 < m) (hp : ‖p.eval z - 1‖ ≤ 1 / 1024) :
    ‖(highOrderCutoff p m).eval z - 1‖ ≤ (1 / 2 : ℝ) ^ m := by
  have hcomp := congrArg (fun q : Polynomial ℂ ↦ q.eval z) (low_add_highOrderCutoff (p := p) hm)
  have hid : (highOrderCutoff p m).eval z - 1 = -(lowOrderCutoff p m).eval z := by
    simp only [Polynomial.eval_add, Polynomial.eval_one] at hcomp
    rw [← hcomp]
    ring
  rw [hid, norm_neg, lowOrderCutoff_eval]
  let u : ℂ := 1 - p.eval z
  have hu : ‖u‖ ≤ 1 / 1024 := by simpa [u, norm_sub_rev] using hp
  have hsum : ‖∑ j ∈ Finset.range m,
      p.eval z ^ j * u ^ (cutoffDegree m - j) * (cutoffDegree m).choose j‖ ≤
      (2 * m : ℝ) * (1 / 1024 : ℝ) ^ m * 4 ^ cutoffDegree m := by
    calc
      _ ≤ ∑ j ∈ Finset.range m,
          ‖p.eval z ^ j * u ^ (cutoffDegree m - j) *
            ((cutoffDegree m).choose j : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range m,
          ((1 / 1024 : ℝ) ^ m * 4 ^ cutoffDegree m) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjlt : j < m := Finset.mem_range.mp hj
        have hdm : m ≤ cutoffDegree m - j := by
          unfold cutoffDegree
          omega
        have hupow : ‖u‖ ^ (cutoffDegree m - j) ≤ (1 / 1024 : ℝ) ^ m := by
          calc
            _ ≤ ‖u‖ ^ m := pow_le_pow_of_le_one (norm_nonneg _)
              (hu.trans (by norm_num)) hdm
            _ ≤ (1 / 1024 : ℝ) ^ m := pow_le_pow_left₀ (norm_nonneg _) hu m
        have hpbig : ‖p.eval z‖ ≤ 2 := by
          calc
            ‖p.eval z‖ = ‖(p.eval z - 1) + 1‖ := by ring_nf
            _ ≤ ‖p.eval z - 1‖ + 1 := by simpa using norm_add_le (p.eval z - 1) (1 : ℂ)
            _ ≤ 2 := by linarith
        have hppow : ‖p.eval z‖ ^ j ≤ 2 ^ cutoffDegree m := by
          calc
            _ ≤ 2 ^ j := pow_le_pow_left₀ (norm_nonneg _) hpbig j
            _ ≤ 2 ^ cutoffDegree m := pow_right_mono₀ (by norm_num) (by
              unfold cutoffDegree
              omega)
        have hchoose : ((cutoffDegree m).choose j : ℝ) ≤ 2 ^ cutoffDegree m := by
          exact_mod_cast Nat.choose_le_two_pow (cutoffDegree m) j
        rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_natCast]
        calc
          ‖p.eval z‖ ^ j * ‖u‖ ^ (cutoffDegree m - j) *
              (cutoffDegree m).choose j ≤
              2 ^ cutoffDegree m * (1 / 1024 : ℝ) ^ m *
                2 ^ cutoffDegree m := by gcongr
          _ = (1 / 1024 : ℝ) ^ m * 4 ^ cutoffDegree m := by
            rw [show (4 : ℝ) ^ cutoffDegree m =
                2 ^ cutoffDegree m * 2 ^ cutoffDegree m by rw [← mul_pow]; norm_num]
            ring
      _ ≤ (2 * m : ℝ) * (1 / 1024 : ℝ) ^ m * 4 ^ cutoffDegree m := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        calc
          (m : ℝ) * ((1 / 1024 : ℝ) ^ m * 4 ^ cutoffDegree m) ≤
              (2 * m : ℝ) * ((1 / 1024 : ℝ) ^ m * 4 ^ cutoffDegree m) := by
            gcongr
            exact_mod_cast (show m ≤ 2 * m by omega)
          _ = _ := by ring
  exact hsum.trans (cutoff_numeric_bound hm)

lemma highOrderCutoff_natDegree_add_one_le
    (p : Polynomial ℂ) {m : ℕ} (hm : 0 < m) :
    (highOrderCutoff p m).natDegree + 1 ≤ 2 * m * (p.natDegree + 1) := by
  have hsum : (highOrderCutoff p m).natDegree ≤ cutoffDegree m * p.natDegree := by
    unfold highOrderCutoff
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    unfold cutoffTerm
    have hjd : j ≤ cutoffDegree m := by
      have := Finset.mem_Ico.mp hj |>.2
      omega
    calc
      (p ^ j * (1 - p) ^ (cutoffDegree m - j) *
          Polynomial.C ((cutoffDegree m).choose j : ℂ)).natDegree ≤
          (p ^ j * (1 - p) ^ (cutoffDegree m - j)).natDegree := by
        exact Polynomial.natDegree_mul_le.trans (by simp)
      _ ≤ (p ^ j).natDegree + ((1 - p) ^ (cutoffDegree m - j)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ j * p.natDegree + (cutoffDegree m - j) * p.natDegree := by
        apply Nat.add_le_add
        · exact Polynomial.natDegree_pow_le
        · exact Polynomial.natDegree_pow_le.trans (by
            apply Nat.mul_le_mul_left
            exact (Polynomial.natDegree_sub_le _ _).trans (by simp))
      _ = cutoffDegree m * p.natDegree := by
        rw [← Nat.add_mul, Nat.add_sub_of_le hjd]
  calc
    (highOrderCutoff p m).natDegree + 1 ≤ cutoffDegree m * p.natDegree + 1 :=
      Nat.add_le_add_right hsum 1
    _ ≤ cutoffDegree m * p.natDegree + (cutoffDegree m + p.natDegree + 1) := by omega
    _ = (cutoffDegree m + 1) * (p.natDegree + 1) := by ring
    _ = 2 * m * (p.natDegree + 1) := by rw [cutoffDegree_add_one hm]

/-- The high-order stage factor used in the final inverse construction. -/
noncomputable def highOrderStageFactor (R : ℝ) (A m : ℕ) : Polynomial ℂ :=
  highOrderCutoff (stageFactor R A 3) m

lemma highOrderStageFactor_sub_one_norm_le
    {R : ℝ} {A m : ℕ} (hR : 0 < R) (hA : 0 < A) (hm : 0 < m)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖(highOrderStageFactor R A m).eval z - 1‖ ≤ (1 / 2 : ℝ) ^ m := by
  apply highOrderCutoff_sub_one_norm_le hm
  have h := stageFactor_sub_one_norm_le (k := 3) hR hA hz
  norm_num [sharpenError] at h ⊢
  exact h

lemma highOrderStageFactor_norm_le
    {R : ℝ} {A m : ℕ} (hR : 0 < R) (hA : 0 < A) (hm : 0 < m)
    {z : ℂ} (hzS : stagePatchRadius R A ≤ ‖z‖)
    (hzT : ‖z‖ ≤ stageOuterRadius R)
    (hzcorr : z.re ≤ 0 ∨ stageGap R A ≤ |z.im|) :
    ‖(highOrderStageFactor R A m).eval z‖ ≤ (1 / 2 : ℝ) ^ m := by
  apply highOrderCutoff_norm_le hm
  have h := stageFactor_norm_le (k := 3) hR hA hzS hzT hzcorr
  norm_num [sharpenError] at h ⊢
  exact h

/-! ## Coarse degree bounds -/

lemma eight_mul_add_one_le_two_pow_eight_mul (B : ℕ) (hB : 0 < B) :
    8 * B + 1 ≤ 2 ^ (8 * B) := by
  induction B with
  | zero => omega
  | succ B ih =>
      by_cases hB0 : B = 0
      · subst B
        norm_num
      · have ih' := ih (Nat.pos_of_ne_zero hB0)
        rw [show 8 * (B + 1) = 8 * B + 8 by ring, pow_add]
        norm_num
        have hp : 1 ≤ 2 ^ (8 * B) := one_le_pow₀ (by norm_num)
        omega

lemma twenty_mul_le_two_pow_ten_mul (B : ℕ) (hB : 0 < B) :
    20 * B ≤ 2 ^ (10 * B) := by
  induction B with
  | zero => omega
  | succ B ih =>
      by_cases hB0 : B = 0
      · subst B
        norm_num
      · have ih' := ih (Nat.pos_of_ne_zero hB0)
        rw [show 10 * (B + 1) = 10 * B + 10 by ring, pow_add]
        norm_num
        have hp : 1 ≤ 2 ^ (10 * B) := one_le_pow₀ (by norm_num)
        omega

/-- The detailed pole-moving formula has degree at most `2^(600(A+1))`.
Only this deliberately coarse exponential form is needed below. -/
lemma stageFactor_natDegree_add_one_le_two_pow
    {R : ℝ} {A : ℕ} (hR : 0 < R) (hA : 0 < A) :
    (stageFactor R A 3).natDegree + 1 ≤ 2 ^ (600 * (A + 1)) := by
  let B := A + 1
  have hB : 0 < B := by unfold B; omega
  have hraw := stageFactor_natDegree_add_one_le (R := R) (A := A) (k := 3) hR hA
  have hlin : 8 * B + 1 ≤ 2 ^ (8 * B) := eight_mul_add_one_le_two_pow_eight_mul B hB
  have hAexp : 512 * A + 1 ≤ 512 * B := by unfold B; omega
  have he : 2 ^ (512 * A + 1) ≤ 2 ^ (512 * B) :=
    Nat.pow_le_pow_right (by norm_num) hAexp
  have hlin' : 8 * B + 1 ≤ 2 ^ (512 * B) :=
    hlin.trans (Nat.pow_le_pow_right (by norm_num) (by omega : 8 * B ≤ 512 * B))
  have hsum : 2 ^ (512 * A + 1) + (8 * B + 1) ≤ 2 ^ (513 * B) := by
    calc
      2 ^ (512 * A + 1) + (8 * B + 1) ≤
          2 ^ (512 * B) + 2 ^ (512 * B) := Nat.add_le_add he hlin'
      _ = 2 ^ (512 * B + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (513 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hinner :
      8 ^ (8 * B) * (2 ^ (512 * A + 1) + 8 * B + 1) + 8 * B + 1 ≤
        2 ^ (538 * B) := by
    have h8 : 8 ^ (8 * B) = 2 ^ (24 * B) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
      congr 1
      ring
    calc
      8 ^ (8 * B) * (2 ^ (512 * A + 1) + 8 * B + 1) + 8 * B + 1 ≤
          2 ^ (24 * B) * 2 ^ (513 * B) + 2 ^ (8 * B) := by
        rw [h8]
        have hsum' : 2 ^ (512 * A + 1) + 8 * B + 1 ≤ 2 ^ (513 * B) := by
          simpa only [add_assoc] using hsum
        have hp := Nat.mul_le_mul_left (2 ^ (24 * B)) hsum'
        simpa only [add_assoc] using Nat.add_le_add hp hlin
      _ = 2 ^ (537 * B) + 2 ^ (8 * B) := by
        have hexp : 24 * B + 513 * B = 537 * B := by omega
        rw [← hexp, pow_add]
      _ ≤ 2 ^ (537 * B) + 2 ^ (537 * B) := by
        exact Nat.add_le_add_left
          (Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega)) _
      _ = 2 ^ (537 * B + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (538 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpref : 3 ^ 3 * 3 ^ 2 ≤ 2 ^ (8 * B) := by
    calc
      3 ^ 3 * 3 ^ 2 = 243 := by norm_num
      _ ≤ 2 ^ 8 := by norm_num
      _ ≤ 2 ^ (8 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc
    (stageFactor R A 3).natDegree + 1 ≤
        3 ^ 3 * (3 ^ 2 *
          (8 ^ (stageExponent A) *
              (2 ^ (2 * (256 * A) + 1) + stageExponent A + 1) +
            stageExponent A + 1)) := hraw
    _ = (3 ^ 3 * 3 ^ 2) *
          (8 ^ (8 * B) * (2 ^ (512 * A + 1) + 8 * B + 1) + 8 * B + 1) := by
      unfold stageExponent B
      ring
    _ ≤ 2 ^ (8 * B) * 2 ^ (538 * B) := Nat.mul_le_mul hpref hinner
    _ = 2 ^ (546 * B) := by
      have hexp : 8 * B + 538 * B = 546 * B := by omega
      rw [← hexp, pow_add]
    _ ≤ 2 ^ (600 * (A + 1)) :=
      Nat.pow_le_pow_right (by norm_num) (by unfold B; omega)

lemma highOrderStageFactor_natDegree_add_one_le_two_pow
    {R : ℝ} {A m : ℕ} (hR : 0 < R) (hA : 0 < A) (hm : 0 < m) :
    (highOrderStageFactor R A m).natDegree + 1 ≤
      2 * m * 2 ^ (600 * (A + 1)) := by
  exact (highOrderCutoff_natDegree_add_one_le (stageFactor R A 3) hm).trans
    (Nat.mul_le_mul_left (2 * m) (stageFactor_natDegree_add_one_le_two_pow hR hA))

/-! ## Recursive polynomial product -/

noncomputable def sharpRadius (n : ℕ) : ℝ := (4 : ℝ) ^ n

lemma sharpRadius_pos (n : ℕ) : 0 < sharpRadius n := by
  unfold sharpRadius
  positivity

lemma sharpRadius_succ (n : ℕ) : sharpRadius (n + 1) = stageOuterRadius (sharpRadius n) := by
  unfold sharpRadius stageOuterRadius
  rw [pow_succ]
  ring

lemma three_mul_le_two_pow_six_mul {d : ℕ} :
    3 * (d + 1) ≤ 2 ^ (6 * (d + 1)) := by
  let x := d + 1
  have h := two_mul_nat_le_thirtytwo_pow (m := x) (by unfold x; omega)
  have htwo : 2 ≤ 2 ^ x := by
    simpa using pow_right_mono₀ (a := (2 : ℕ)) (by norm_num) (show 1 ≤ x by unfold x; omega)
  have h32 : 3 * x ≤ 64 ^ x := by
    calc
      3 * x ≤ 2 * (2 * x) := by omega
      _ ≤ 2 * 32 ^ x := Nat.mul_le_mul_left 2 h
      _ ≤ 2 ^ x * 32 ^ x := Nat.mul_le_mul_right (32 ^ x) htwo
      _ = 64 ^ x := by rw [← mul_pow]; norm_num
  dsimp only [x] at h32
  simpa [show (64 : ℕ) = 2 ^ 6 by norm_num, pow_mul] using h32

/-- Sharpening order sufficient both for locally uniform convergence and for suppressing the old
polynomial throughout the following radius-four annulus. -/
def sharpMultiplicity (p : Polynomial ℂ) (n : ℕ) : ℕ :=
  6 * (p.natDegree + 1) + 2 * (n + 1) * p.natDegree + n + 4

lemma sharpMultiplicity_pos (p : Polynomial ℂ) (n : ℕ) :
    0 < sharpMultiplicity p n := by
  unfold sharpMultiplicity
  omega

lemma sharpOuterRadius_eq_two_pow (n : ℕ) :
    stageOuterRadius (sharpRadius n) = (2 : ℝ) ^ (2 * (n + 1)) := by
  unfold stageOuterRadius sharpRadius
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
  congr 1
  omega

lemma sharp_suppression_bound (p : Polynomial ℂ) (n : ℕ) :
    (3 * (p.natDegree + 1) : ℝ) *
        (stageOuterRadius (sharpRadius n)) ^ p.natDegree *
          (1 / 2 : ℝ) ^ sharpMultiplicity p n ≤
      (1 / 2 : ℝ) ^ (n + 4) := by
  let d := p.natDegree
  let a := 6 * (d + 1) + 2 * (n + 1) * d
  have hcoeffNat := three_mul_le_two_pow_six_mul (d := d)
  have hcoeff : (3 * (d + 1) : ℝ) ≤ (2 : ℝ) ^ (6 * (d + 1)) := by
    exact_mod_cast hcoeffNat
  have hr : (stageOuterRadius (sharpRadius n)) ^ d =
      (2 : ℝ) ^ (2 * (n + 1) * d) := by
    rw [sharpOuterRadius_eq_two_pow, ← pow_mul]
  have ha : (2 : ℝ) ^ (6 * (d + 1)) * (2 : ℝ) ^ (2 * (n + 1) * d) =
      (2 : ℝ) ^ a := by
    rw [← pow_add]
  have hm : sharpMultiplicity p n = a + (n + 4) := by
    unfold sharpMultiplicity a d
    omega
  change (3 * (d + 1) : ℝ) * (stageOuterRadius (sharpRadius n)) ^ d *
      (1 / 2 : ℝ) ^ sharpMultiplicity p n ≤ _
  rw [hr, hm, pow_add]
  calc
    (3 * (d + 1) : ℝ) * 2 ^ (2 * (n + 1) * d) *
        ((1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ (n + 4)) ≤
        (2 ^ (6 * (d + 1)) * 2 ^ (2 * (n + 1) * d)) *
          ((1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ (n + 4)) := by
      gcongr
    _ = (1 / 2 : ℝ) ^ (n + 4) := by
      rw [ha]
      have htwo : (2 : ℝ) ^ a * (1 / 2 : ℝ) ^ a = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        (2 : ℝ) ^ a * ((1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ (n + 4)) =
            ((2 : ℝ) ^ a * (1 / 2 : ℝ) ^ a) * (1 / 2 : ℝ) ^ (n + 4) := by ring
        _ = _ := by rw [htwo, one_mul]

/-- Recursive approximating polynomials for an arbitrary positive integer complexity sequence. -/
noncomputable def sharpPolynomials (A : ℕ → ℕ) : ℕ → Polynomial ℂ
  | 0 => Polynomial.X
  | n + 1 =>
      let p := sharpPolynomials A n
      p * highOrderStageFactor (sharpRadius n) (A n) (sharpMultiplicity p n)

@[simp] lemma sharpPolynomials_zero (A : ℕ → ℕ) :
    sharpPolynomials A 0 = Polynomial.X := rfl

lemma sharpPolynomials_succ (A : ℕ → ℕ) (n : ℕ) :
    sharpPolynomials A (n + 1) =
      sharpPolynomials A n *
        highOrderStageFactor (sharpRadius n) (A n)
          (sharpMultiplicity (sharpPolynomials A n) n) := rfl

noncomputable def sharpIncrement (A : ℕ → ℕ) (n : ℕ) (z : ℂ) : ℂ :=
  (sharpPolynomials A (n + 1)).eval z - (sharpPolynomials A n).eval z

lemma sharpIncrement_eq (A : ℕ → ℕ) (n : ℕ) (z : ℂ) :
    sharpIncrement A n z = (sharpPolynomials A n).eval z *
      ((highOrderStageFactor (sharpRadius n) (A n)
          (sharpMultiplicity (sharpPolynomials A n) n)).eval z - 1) := by
  rw [sharpIncrement, sharpPolynomials_succ, Polynomial.eval_mul]
  ring

noncomputable def sharpBudget (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 4)

lemma sharpBudget_succ (n : ℕ) :
    sharpBudget (n + 1) = sharpBudget n + (1 / 2 : ℝ) ^ (n + 4) := by
  simp [sharpBudget, Finset.sum_range_succ]

lemma sharpBudget_nonneg (n : ℕ) : 0 ≤ sharpBudget n := by
  unfold sharpBudget
  positivity

lemma sharpBudget_le_one (n : ℕ) : sharpBudget n ≤ 1 := by
  have hgeom := sum_geometric_two_le n
  have heq : sharpBudget n = (1 / 16 : ℝ) *
      (∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j) := by
    unfold sharpBudget
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_add]
    norm_num
    ring
  rw [heq]
  nlinarith

lemma one_le_sharpRadius (n : ℕ) : 1 ≤ sharpRadius n := by
  unfold sharpRadius
  exact one_le_pow₀ (by norm_num)

lemma sharpMultiplicity_ge (p : Polynomial ℂ) (n : ℕ) :
    n + 4 ≤ sharpMultiplicity p n := by
  unfold sharpMultiplicity
  omega

lemma sharpPolynomials_norm_le_exp_budget
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) :
    ∀ n z, ‖z‖ ≤ 1 →
      ‖(sharpPolynomials A n).eval z‖ ≤ Real.exp (sharpBudget n) := by
  intro n
  induction n with
  | zero =>
      intro z hz
      simp only [sharpPolynomials_zero, Polynomial.eval_X]
      have hbudget : Real.exp (sharpBudget 0) = 1 := by
        simp [sharpBudget]
      rw [hbudget]
      exact hz
  | succ n ih =>
      intro z hz
      rw [sharpPolynomials_succ, Polynomial.eval_mul, norm_mul, sharpBudget_succ,
        Real.exp_add]
      have hp := ih z hz
      have hzR : ‖z‖ ≤ sharpRadius n := hz.trans (one_le_sharpRadius n)
      let m := sharpMultiplicity (sharpPolynomials A n) n
      have hm : 0 < m := sharpMultiplicity_pos _ _
      have hgsub := highOrderStageFactor_sub_one_norm_le
        (sharpRadius_pos n) (hA n) hm hzR
      have hmge : n + 4 ≤ m := sharpMultiplicity_ge _ _
      have herr : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ (n + 4) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hmge
      have hg : ‖(highOrderStageFactor (sharpRadius n) (A n) m).eval z‖ ≤
          1 + (1 / 2 : ℝ) ^ (n + 4) := by
        calc
          ‖(highOrderStageFactor (sharpRadius n) (A n) m).eval z‖ =
              ‖((highOrderStageFactor (sharpRadius n) (A n) m).eval z - 1) + 1‖ := by
                ring_nf
          _ ≤ ‖(highOrderStageFactor (sharpRadius n) (A n) m).eval z - 1‖ + 1 := by
            simpa using norm_add_le
              ((highOrderStageFactor (sharpRadius n) (A n) m).eval z - 1) (1 : ℂ)
          _ ≤ 1 + (1 / 2 : ℝ) ^ (n + 4) := by linarith
      have hexp : 1 + (1 / 2 : ℝ) ^ (n + 4) ≤
          Real.exp ((1 / 2 : ℝ) ^ (n + 4)) := by
        simpa [add_comm] using Real.add_one_le_exp ((1 / 2 : ℝ) ^ (n + 4))
      exact mul_le_mul hp (hg.trans hexp) (norm_nonneg _)
        (Real.exp_nonneg (sharpBudget n))

lemma sharpPolynomials_norm_le_three_on_unit
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(sharpPolynomials A n).eval z‖ ≤ 3 := by
  exact (sharpPolynomials_norm_le_exp_budget hA n z hz).trans (by
    calc
      Real.exp (sharpBudget n) ≤ Real.exp 1 := Real.exp_le_exp.mpr (sharpBudget_le_one n)
      _ ≤ 3 := Real.exp_one_lt_three.le)

lemma sharpPolynomials_global_bound
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (n : ℕ) (z : ℂ) :
    ‖(sharpPolynomials A n).eval z‖ ≤
      ((sharpPolynomials A n).natDegree + 1 : ℕ) * 3 *
        (max 1 ‖z‖) ^ (sharpPolynomials A n).natDegree := by
  simpa using norm_eval_le_of_norm_le_disk (p := sharpPolynomials A n)
    (R := 1) (B := 3) (by norm_num) (by norm_num)
    (fun w hw ↦ sharpPolynomials_norm_le_three_on_unit hA n hw) z

lemma sharpIncrement_norm_le
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (n : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ sharpRadius n) :
    ‖sharpIncrement A n z‖ ≤ (1 / 2 : ℝ) ^ (n + 4) := by
  let p := sharpPolynomials A n
  let m := sharpMultiplicity p n
  have hm : 0 < m := sharpMultiplicity_pos _ _
  have hp0 := sharpPolynomials_global_bound hA n z
  have hmax : max 1 ‖z‖ ≤ stageOuterRadius (sharpRadius n) := by
    rw [max_le_iff]
    exact ⟨(one_le_sharpRadius n).trans (by
      unfold stageOuterRadius
      nlinarith [sharpRadius_pos n]),
      hz.trans (by unfold stageOuterRadius; nlinarith [sharpRadius_pos n])⟩
  have hp : ‖p.eval z‖ ≤
      (3 * (p.natDegree + 1) : ℝ) *
        (stageOuterRadius (sharpRadius n)) ^ p.natDegree := by
    calc
      ‖p.eval z‖ ≤ (p.natDegree + 1 : ℕ) * 3 * (max 1 ‖z‖) ^ p.natDegree := hp0
      _ ≤ (p.natDegree + 1 : ℕ) * 3 *
          (stageOuterRadius (sharpRadius n)) ^ p.natDegree := by gcongr
      _ = (3 * (p.natDegree + 1) : ℝ) *
          (stageOuterRadius (sharpRadius n)) ^ p.natDegree := by
        push_cast
        ring
  have hg : ‖(highOrderStageFactor (sharpRadius n) (A n) m).eval z - 1‖ ≤
      (1 / 2 : ℝ) ^ m := by
    exact highOrderStageFactor_sub_one_norm_le (sharpRadius_pos n) (hA n) hm
      hz
  rw [sharpIncrement_eq, norm_mul]
  have hupper : 0 ≤ (3 * (p.natDegree + 1) : ℝ) *
      (stageOuterRadius (sharpRadius n)) ^ p.natDegree := by
    have houter : 0 ≤ stageOuterRadius (sharpRadius n) := by
      unfold stageOuterRadius
      exact mul_nonneg (by norm_num) (sharpRadius_pos n).le
    exact mul_nonneg (by positivity) (pow_nonneg houter _)
  exact (mul_le_mul hp hg (norm_nonneg _) hupper).trans
    (sharp_suppression_bound p n)

/-- On the bulk of the `n`th annulus the newly formed polynomial is exponentially small. -/
lemma sharpPolynomials_succ_norm_le_on_bulk
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (n : ℕ) {z : ℂ}
    (hzS : stagePatchRadius (sharpRadius n) (A n) ≤ ‖z‖)
    (hzT : ‖z‖ ≤ sharpRadius (n + 1))
    (hzcorr : z.re ≤ 0 ∨ stageGap (sharpRadius n) (A n) ≤ |z.im|) :
    ‖(sharpPolynomials A (n + 1)).eval z‖ ≤ (1 / 2 : ℝ) ^ (n + 4) := by
  let p := sharpPolynomials A n
  let m := sharpMultiplicity p n
  have hm : 0 < m := sharpMultiplicity_pos _ _
  have hp0 := sharpPolynomials_global_bound hA n z
  have hmax : max 1 ‖z‖ ≤ stageOuterRadius (sharpRadius n) := by
    rw [max_le_iff]
    exact ⟨(one_le_sharpRadius n).trans (by
      unfold stageOuterRadius
      nlinarith [sharpRadius_pos n]), by simpa [sharpRadius_succ] using hzT⟩
  have hp : ‖p.eval z‖ ≤
      (3 * (p.natDegree + 1) : ℝ) *
        (stageOuterRadius (sharpRadius n)) ^ p.natDegree := by
    calc
      ‖p.eval z‖ ≤ (p.natDegree + 1 : ℕ) * 3 * (max 1 ‖z‖) ^ p.natDegree := hp0
      _ ≤ (p.natDegree + 1 : ℕ) * 3 *
          (stageOuterRadius (sharpRadius n)) ^ p.natDegree := by gcongr
      _ = (3 * (p.natDegree + 1) : ℝ) *
          (stageOuterRadius (sharpRadius n)) ^ p.natDegree := by
        push_cast
        ring
  have hg : ‖(highOrderStageFactor (sharpRadius n) (A n) m).eval z‖ ≤
      (1 / 2 : ℝ) ^ m := by
    exact highOrderStageFactor_norm_le (sharpRadius_pos n) (hA n) hm hzS
      (by simpa [sharpRadius_succ] using hzT) hzcorr
  rw [sharpPolynomials_succ, Polynomial.eval_mul, norm_mul]
  have hupper : 0 ≤ (3 * (p.natDegree + 1) : ℝ) *
      (stageOuterRadius (sharpRadius n)) ^ p.natDegree := by
    have houter : 0 ≤ stageOuterRadius (sharpRadius n) := by
      unfold stageOuterRadius
      exact mul_nonneg (by norm_num) (sharpRadius_pos n).le
    exact mul_nonneg (by positivity) (pow_nonneg houter _)
  exact (mul_le_mul hp hg (norm_nonneg _) hupper).trans
    (sharp_suppression_bound p n)

/-! ## The locally uniform limit -/

noncomputable def sharpError (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 4)

lemma sharpError_nonneg (n : ℕ) : 0 ≤ sharpError n := by
  unfold sharpError
  positivity

lemma summable_sharpError : Summable sharpError := by
  have h : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have heq : sharpError = fun n : ℕ ↦ (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ n := by
    funext n
    rw [sharpError, pow_add]
    norm_num
    ring
  rw [heq]
  exact h.mul_left _

lemma sharpRadius_mono : Monotone sharpRadius := by
  intro n m hnm
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hnm

lemma sharpRadius_tendsto : Tendsto sharpRadius atTop atTop := by
  exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)

lemma sharpIncrement_summableLocallyUniformly
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) :
    SummableLocallyUniformlyOn (sharpIncrement A) (Set.univ : Set ℂ) := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually isOpen_univ
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  refine ⟨sharpError, summable_sharpError, ?_⟩
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [sharpRadius_tendsto.eventually (eventually_ge_atTop R)] with n hn z hz
  exact sharpIncrement_norm_le hA n ((hR z hz).trans hn)

/-- The locally uniform limit of the recursively suppressed polynomials. -/
noncomputable def sharpFunction (A : ℕ → ℕ) : ℂ → ℂ :=
  fun z ↦ z + ∑' n : ℕ, sharpIncrement A n z

lemma sharpFunction_differentiable
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) :
    Differentiable ℂ (sharpFunction A) := by
  have hsum : DifferentiableOn ℂ (fun z ↦ ∑' n : ℕ, sharpIncrement A n z) Set.univ := by
    apply (sharpIncrement_summableLocallyUniformly hA).differentiableOn isOpen_univ
    intro n z _
    exact ((sharpPolynomials A (n + 1)).differentiableAt.sub
      (sharpPolynomials A n).differentiableAt)
  rw [← differentiableOn_univ]
  exact differentiableOn_id.add hsum

lemma summable_sharpError_nat_add (N : ℕ) :
    Summable (fun i : ℕ ↦ sharpError (i + N)) :=
  summable_sharpError.comp_injective (add_left_injective N)

lemma tsum_sharpError_nat_add (N : ℕ) :
    ∑' i : ℕ, sharpError (i + N) = 2 * sharpError N := by
  have heq : (fun i : ℕ ↦ sharpError (i + N)) =
      fun i : ℕ ↦ sharpError N * (1 / 2 : ℝ) ^ i := by
    funext i
    simp only [sharpError, pow_add]
    ring
  rw [heq, tsum_mul_left, tsum_geometric_two]
  ring

lemma sharpError_succ_twice (n : ℕ) :
    2 * sharpError (n + 1) = sharpError n := by
  simp [sharpError, pow_succ]
  ring

lemma sum_sharpIncrement (A : ℕ → ℕ) (N : ℕ) (z : ℂ) :
    ∑ i ∈ Finset.range N, sharpIncrement A i z =
      (sharpPolynomials A N).eval z - z := by
  induction N with
  | zero => simp [sharpPolynomials]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [sharpIncrement]
      ring

lemma summable_sharpIncrement {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (z : ℂ) :
    Summable (fun n ↦ sharpIncrement A n z) :=
  (sharpIncrement_summableLocallyUniformly hA).summable (Set.mem_univ z)

lemma sharpFunction_sub_polynomial_eq_tail
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (N : ℕ) (z : ℂ) :
    sharpFunction A z - (sharpPolynomials A N).eval z =
      ∑' i : ℕ, sharpIncrement A (i + N) z := by
  have hsplit := (summable_sharpIncrement hA z).sum_add_tsum_nat_add N
  rw [sum_sharpIncrement] at hsplit
  unfold sharpFunction
  rw [← hsplit]
  ring

lemma sharpFunction_sub_polynomial_succ_norm_le
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (n : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ sharpRadius (n + 1)) :
    ‖sharpFunction A z - (sharpPolynomials A (n + 1)).eval z‖ ≤
      sharpError n := by
  rw [sharpFunction_sub_polynomial_eq_tail hA]
  have hbound : ∀ i : ℕ,
      ‖sharpIncrement A (i + (n + 1)) z‖ ≤ sharpError (i + (n + 1)) := by
    intro i
    apply sharpIncrement_norm_le hA
    exact hz.trans (sharpRadius_mono (Nat.le_add_left (n + 1) i))
  calc
    ‖∑' i : ℕ, sharpIncrement A (i + (n + 1)) z‖ ≤
        ∑' i : ℕ, sharpError (i + (n + 1)) :=
      tsum_of_norm_bounded (summable_sharpError_nat_add (n + 1)).hasSum hbound
    _ = 2 * sharpError (n + 1) := tsum_sharpError_nat_add (n + 1)
    _ = sharpError n := sharpError_succ_twice n

lemma sharpFunction_norm_le_on_bulk
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (n : ℕ) {z : ℂ}
    (hzS : stagePatchRadius (sharpRadius n) (A n) ≤ ‖z‖)
    (hzT : ‖z‖ ≤ sharpRadius (n + 1))
    (hzcorr : z.re ≤ 0 ∨ stageGap (sharpRadius n) (A n) ≤ |z.im|) :
    ‖sharpFunction A z‖ ≤ 2 * sharpError n := by
  have hstage := sharpPolynomials_succ_norm_le_on_bulk hA n hzS hzT hzcorr
  have htail := sharpFunction_sub_polynomial_succ_norm_le hA n hzT
  calc
    ‖sharpFunction A z‖ =
        ‖(sharpFunction A z - (sharpPolynomials A (n + 1)).eval z) +
          (sharpPolynomials A (n + 1)).eval z‖ := by ring_nf
    _ ≤ ‖sharpFunction A z - (sharpPolynomials A (n + 1)).eval z‖ +
        ‖(sharpPolynomials A (n + 1)).eval z‖ := norm_add_le _ _
    _ ≤ sharpError n + sharpError n := add_le_add htail hstage
    _ = 2 * sharpError n := by ring

/-! ## The exceptional set and its area -/

noncomputable def sharpAreaTerm (A : ℕ → ℕ) (n : ℕ) : ℝ :=
  sharpRadius n ^ 2 / A n

noncomputable def sharpRadialBad (A : ℕ → ℕ) (n : ℕ) : Set ℂ :=
  Metric.closedBall 0 (stagePatchRadius (sharpRadius n) (A n)) \
    Metric.closedBall 0 (sharpRadius n)

noncomputable def sharpCorridorBox (A : ℕ → ℕ) (n : ℕ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹'
    (Set.Icc (-sharpRadius (n + 1)) (sharpRadius (n + 1)) ×ˢ
      Set.Icc (-stageGap (sharpRadius n) (A n))
        (stageGap (sharpRadius n) (A n)))

noncomputable def sharpBadSet (A : ℕ → ℕ) : Set ℂ :=
  ⋃ n : ℕ, sharpRadialBad A n ∪ sharpCorridorBox A n

lemma mem_sharpCorridorBox_of_norm_le_of_abs_im_le
    (A : ℕ → ℕ) (n : ℕ) {z : ℂ}
    (hzT : ‖z‖ ≤ sharpRadius (n + 1))
    (hzim : |z.im| ≤ stageGap (sharpRadius n) (A n)) :
    z ∈ sharpCorridorBox A n := by
  change (z.re, z.im) ∈
    Set.Icc (-sharpRadius (n + 1)) (sharpRadius (n + 1)) ×ˢ
      Set.Icc (-stageGap (sharpRadius n) (A n))
        (stageGap (sharpRadius n) (A n))
  constructor
  · rw [Set.mem_Icc]
    have hre := Complex.abs_re_le_norm z |>.trans hzT
    simpa only [abs_le] using hre
  · rw [Set.mem_Icc]
    simpa only [abs_le] using hzim

lemma volume_sharpCorridorBox (A : ℕ → ℕ) (n : ℕ) :
    volume (sharpCorridorBox A n) =
      ENNReal.ofReal (2 * sharpRadius (n + 1)) *
        ENNReal.ofReal (2 * stageGap (sharpRadius n) (A n)) := by
  unfold sharpCorridorBox
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet)]
  change (volume.prod volume)
      (Set.Icc (-sharpRadius (n + 1)) (sharpRadius (n + 1)) ×ˢ
        Set.Icc (-stageGap (sharpRadius n) (A n))
          (stageGap (sharpRadius n) (A n))) = _
  rw [Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  congr 2 <;> ring_nf

lemma volume_sharpCorridorBox_eq_areaTerm
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (n : ℕ) :
    volume (sharpCorridorBox A n) =
      ENNReal.ofReal (16 * sharpAreaTerm A n) := by
  rw [volume_sharpCorridorBox, ← ENNReal.ofReal_mul]
  · apply congrArg ENNReal.ofReal
    rw [sharpRadius_succ]
    unfold stageOuterRadius stageGap sharpAreaTerm
    have hA0 : (A n : ℝ) ≠ 0 := by exact_mod_cast (hA n).ne'
    field_simp
    ring
  · exact mul_nonneg (by positivity) (sharpRadius_pos (n + 1)).le

lemma volume_sharpRadialBad
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (n : ℕ) :
    volume (sharpRadialBad A n) =
      ENNReal.ofReal
          (stagePatchRadius (sharpRadius n) (A n) ^ 2 - sharpRadius n ^ 2) *
        NNReal.pi := by
  have hR : 0 ≤ sharpRadius n := (sharpRadius_pos n).le
  have hS : 0 ≤ stagePatchRadius (sharpRadius n) (A n) := by
    unfold stagePatchRadius
    linarith [stageGap_pos (sharpRadius_pos n) (hA n)]
  have hRS : sharpRadius n ≤ stagePatchRadius (sharpRadius n) (A n) := by
    unfold stagePatchRadius
    linarith [stageGap_pos (sharpRadius_pos n) (hA n)]
  have hfinite : volume (Metric.closedBall (0 : ℂ) (sharpRadius n)) ≠ ∞ := by
    rw [Complex.volume_closedBall]
    exact ENNReal.mul_ne_top (by simp) (by simp)
  unfold sharpRadialBad
  rw [measure_sdiff (Metric.closedBall_subset_closedBall hRS)
    measurableSet_closedBall.nullMeasurableSet hfinite]
  rw [Complex.volume_closedBall, Complex.volume_closedBall,
      ← ENNReal.sub_mul (fun _ _ ↦ by simp),
      ← ENNReal.ofReal_pow hS, ← ENNReal.ofReal_pow hR,
      ← ENNReal.ofReal_sub _ (sq_nonneg (sharpRadius n))]

lemma sharpRadialDifference_le
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (n : ℕ) :
    stagePatchRadius (sharpRadius n) (A n) ^ 2 - sharpRadius n ^ 2 ≤
      8 * sharpAreaTerm A n := by
  let R := sharpRadius n
  let g := stageGap R (A n)
  have hR : 0 ≤ R := (sharpRadius_pos n).le
  have hg : 0 ≤ g := (stageGap_pos (sharpRadius_pos n) (hA n)).le
  have hAreal : (1 : ℝ) ≤ A n := by exact_mod_cast hA n
  have hgR : g ≤ R := by
    unfold g stageGap
    exact div_le_self hR hAreal
  have hrewrite : R * g = sharpAreaTerm A n := by
    unfold g stageGap sharpAreaTerm R
    ring
  unfold stagePatchRadius
  change (R + 2 * g) ^ 2 - R ^ 2 ≤ 8 * sharpAreaTerm A n
  calc
    (R + 2 * g) ^ 2 - R ^ 2 = 4 * R * g + 4 * g ^ 2 := by ring
    _ ≤ 8 * (R * g) := by nlinarith
    _ = 8 * sharpAreaTerm A n := by rw [hrewrite]

lemma volume_sharpRadialBad_le
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (n : ℕ) :
    volume (sharpRadialBad A n) ≤
      ENNReal.ofReal (8 * sharpAreaTerm A n) * NNReal.pi := by
  rw [volume_sharpRadialBad hA]
  gcongr
  exact sharpRadialDifference_le hA n

lemma sharpAreaTerm_nonneg
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (n : ℕ) :
    0 ≤ sharpAreaTerm A n := by
  unfold sharpAreaTerm
  positivity

lemma volume_sharpBadSet_ne_top
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n)
    (hsum : Summable (sharpAreaTerm A)) :
    volume (sharpBadSet A) ≠ ∞ := by
  have hcoe : (∑' n : ℕ, ENNReal.ofReal (sharpAreaTerm A n)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (sharpAreaTerm_nonneg hA) hsum]
    exact ENNReal.ofReal_ne_top
  have hrad :
      (∑' n : ℕ, ENNReal.ofReal (8 * sharpAreaTerm A n) * NNReal.pi) ≠ ∞ := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (by simp) hcoe
    · simp
  have hcorr :
      (∑' n : ℕ, ENNReal.ofReal (16 * sharpAreaTerm A n)) ≠ ∞ := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top (by simp) hcoe
  have hmajor :
      (∑' n : ℕ, (ENNReal.ofReal (8 * sharpAreaTerm A n) * NNReal.pi +
        ENNReal.ofReal (16 * sharpAreaTerm A n))) ≠ ∞ := by
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr ⟨hrad, hcorr⟩
  apply ne_top_of_le_ne_top hmajor
  exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum (fun n ↦ by
    calc
      volume (sharpRadialBad A n ∪ sharpCorridorBox A n) ≤
          volume (sharpRadialBad A n) + volume (sharpCorridorBox A n) :=
        measure_union_le _ _
      _ ≤ ENNReal.ofReal (8 * sharpAreaTerm A n) * NNReal.pi +
          ENNReal.ofReal (16 * sharpAreaTerm A n) := by
        gcongr
        · exact volume_sharpRadialBad_le hA n
        · exact (volume_sharpCorridorBox_eq_areaTerm hA n).le))

lemma volume_sharpBadSet_union_closedBall_ne_top
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n)
    (hsum : Summable (sharpAreaTerm A)) (R : ℝ) :
    volume (sharpBadSet A ∪ Metric.closedBall (0 : ℂ) R) ≠ ∞ := by
  have hball : volume (Metric.closedBall (0 : ℂ) R) ≠ ∞ := by
    rw [Complex.volume_closedBall]
    exact ENNReal.mul_ne_top (by simp) (by simp)
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨volume_sharpBadSet_ne_top hA hsum, hball⟩)
    (measure_union_le _ _)

/-- Every radius larger than one belongs to one of the radius-four stage annuli. -/
lemma exists_sharpAnnulusIndex {x : ℝ} (hx : 1 < x) :
    ∃ n : ℕ, sharpRadius n < x ∧ x ≤ sharpRadius (n + 1) := by
  have hex : ∃ n : ℕ, x ≤ sharpRadius (n + 1) := by
    have hev := sharpRadius_tendsto.eventually (eventually_ge_atTop x)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    exact ⟨N, hN N (le_refl N) |>.trans (sharpRadius_mono (Nat.le_succ N))⟩
  let N := Nat.find hex
  have hright : x ≤ sharpRadius (N + 1) := Nat.find_spec hex
  have hleft : sharpRadius N < x := by
    by_cases hN : N = 0
    · simpa [hN, sharpRadius] using hx
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hN
      have hklt : k < Nat.find hex := by
        change k < N
        omega
      have hsmall : ¬x ≤ sharpRadius (k + 1) := Nat.find_min hex hklt
      rw [hk]
      exact lt_of_not_ge hsmall
  exact ⟨N, hleft, hright⟩

/-- Off the exceptional set, a point outside the unit disk is in an annular bulk. -/
lemma exists_sharpBulkIndex
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) {z : ℂ} (hz : 1 < ‖z‖)
    (hbad : z ∉ sharpBadSet A) :
    ∃ n : ℕ,
      stagePatchRadius (sharpRadius n) (A n) ≤ ‖z‖ ∧
      ‖z‖ ≤ sharpRadius (n + 1) ∧
      (z.re ≤ 0 ∨ stageGap (sharpRadius n) (A n) ≤ |z.im|) := by
  obtain ⟨n, hnR, hnT⟩ := exists_sharpAnnulusIndex hz
  have hnS : stagePatchRadius (sharpRadius n) (A n) ≤ ‖z‖ := by
    by_contra hnot
    have hzS : ‖z‖ ≤ stagePatchRadius (sharpRadius n) (A n) := le_of_not_ge hnot
    have hzbad : z ∈ sharpRadialBad A n := by
      constructor
      · simpa [Metric.mem_closedBall, dist_zero_right] using hzS
      · intro hzclosed
        have : ‖z‖ ≤ sharpRadius n := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hzclosed
        exact (not_lt_of_ge this) hnR
    apply hbad
    exact Set.mem_iUnion.2 ⟨n, Or.inl hzbad⟩
  have hcorr : z.re ≤ 0 ∨ stageGap (sharpRadius n) (A n) ≤ |z.im| := by
    by_contra hnot
    have him : |z.im| ≤ stageGap (sharpRadius n) (A n) :=
      le_of_not_ge (not_or.mp hnot).2
    have hzbox : z ∈ sharpCorridorBox A n :=
      mem_sharpCorridorBox_of_norm_le_of_abs_im_le A n hnT him
    apply hbad
    exact Set.mem_iUnion.2 ⟨n, Or.inr hzbox⟩
  exact ⟨n, hnS, hnT, hcorr⟩

lemma two_mul_sharpError_lt_one (n : ℕ) : 2 * sharpError n < 1 := by
  have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [sharpError, pow_add]
  norm_num
  nlinarith

lemma tsum_sharpError : ∑' n : ℕ, sharpError n = 1 / 8 := by
  have heq : sharpError = fun n : ℕ ↦ (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ n := by
    funext n
    rw [sharpError, pow_add]
    norm_num
    ring
  rw [heq, tsum_mul_left, tsum_geometric_two]
  norm_num

lemma sharpFunction_sub_id_norm_le
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖sharpFunction A z - z‖ ≤ 1 / 8 := by
  have hbound : ∀ n : ℕ, ‖sharpIncrement A n z‖ ≤ sharpError n := by
    intro n
    exact sharpIncrement_norm_le hA n (hz.trans (one_le_sharpRadius n))
  have hsum : Summable (fun n ↦ sharpIncrement A n z) :=
    summable_sharpIncrement hA z
  unfold sharpFunction
  rw [add_sub_cancel_left]
  calc
    ‖∑' n : ℕ, sharpIncrement A n z‖ ≤ ∑' n : ℕ, sharpError n :=
      tsum_of_norm_bounded summable_sharpError.hasSum hbound
    _ = 1 / 8 := tsum_sharpError

lemma sharpFunction_nonconstant
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) :
    ∃ z w : ℂ, sharpFunction A z ≠ sharpFunction A w := by
  have h0 := sharpFunction_sub_id_norm_le hA (z := 0) (by norm_num)
  have h1 := sharpFunction_sub_id_norm_le hA (z := 1) (by norm_num)
  refine ⟨0, 1, ?_⟩
  intro heq
  have hone : (1 : ℝ) ≤ 1 / 8 + 1 / 8 := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖(1 - sharpFunction A 1) + (sharpFunction A 0 - 0)‖ := by
        rw [heq]
        ring_nf
      _ ≤ ‖1 - sharpFunction A 1‖ + ‖sharpFunction A 0 - 0‖ := norm_add_le _ _
      _ = ‖sharpFunction A 1 - 1‖ + ‖sharpFunction A 0 - 0‖ := by
        rw [norm_sub_rev]
      _ ≤ 1 / 8 + 1 / 8 := add_le_add h1 h0
  norm_num at hone

lemma sharpFunction_superlevel_subset
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) :
    {z : ℂ | 1 < ‖sharpFunction A z‖} ⊆
      sharpBadSet A ∪ Metric.closedBall (0 : ℂ) 1 := by
  intro z hz
  by_contra hmem
  have hnotbad : z ∉ sharpBadSet A := fun h ↦ hmem (Or.inl h)
  have hnotball : z ∉ Metric.closedBall (0 : ℂ) 1 := fun h ↦ hmem (Or.inr h)
  have hz1 : 1 < ‖z‖ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hnotball
  obtain ⟨n, hzS, hzT, hzcorr⟩ := exists_sharpBulkIndex hA hz1 hnotbad
  have hf := sharpFunction_norm_le_on_bulk hA n hzS hzT hzcorr
  exact (not_lt_of_ge (hf.trans (two_mul_sharpError_lt_one n).le)) hz

lemma sharpFunction_hasFiniteArea
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n)
    (hsum : Summable (sharpAreaTerm A)) :
    volume {z : ℂ | 1 < ‖sharpFunction A z‖} ≠ ∞ := by
  apply ne_top_of_le_ne_top (volume_sharpBadSet_union_closedBall_ne_top hA hsum 1)
  exact measure_mono (sharpFunction_superlevel_subset hA)

/-! ## Degree of the recursive product -/

lemma thirtytwo_mul_le_two_pow_ten_mul (B : ℕ) (hB : 0 < B) :
    32 * B ≤ 2 ^ (10 * B) := by
  induction B with
  | zero => omega
  | succ B ih =>
      by_cases hB0 : B = 0
      · subst B
        norm_num
      · have ih' := ih (Nat.pos_of_ne_zero hB0)
        rw [show 10 * (B + 1) = 10 * B + 10 by ring, pow_add]
        norm_num
        have hp : 1 ≤ 2 ^ (10 * B) := one_le_pow₀ (by norm_num)
        omega

lemma sharpMultiplicity_le (p : Polynomial ℂ) (n : ℕ) :
    sharpMultiplicity p n ≤ 12 * (n + 1) * (p.natDegree + 1) := by
  let d := p.natDegree
  have h1 : 6 * (d + 1) ≤ 6 * (n + 1) * (d + 1) := by
    exact Nat.mul_le_mul_right (d + 1) (by omega)
  have h2 : 2 * (n + 1) * d ≤ 2 * (n + 1) * (d + 1) := by
    exact Nat.mul_le_mul_left (2 * (n + 1)) (by omega)
  have h3 : n + 4 ≤ 4 * (n + 1) * (d + 1) := by
    have hd : 1 ≤ d + 1 := by omega
    have hn : n + 4 ≤ 4 * (n + 1) := by omega
    exact hn.trans (Nat.le_mul_of_pos_right _ (by omega))
  calc
    sharpMultiplicity p n =
        (6 * (d + 1) + 2 * (n + 1) * d) + (n + 4) := by
      unfold sharpMultiplicity d
      omega
    _ ≤ (6 * (n + 1) * (d + 1) + 2 * (n + 1) * (d + 1)) +
        4 * (n + 1) * (d + 1) := Nat.add_le_add (Nat.add_le_add h1 h2) h3
    _ = 12 * (n + 1) * (d + 1) := by ring

lemma sharpPolynomials_natDegree_succ_le
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (n : ℕ) :
    (sharpPolynomials A (n + 1)).natDegree + 1 ≤
      ((sharpPolynomials A n).natDegree + 1) *
        (2 * sharpMultiplicity (sharpPolynomials A n) n *
          2 ^ (600 * (A n + 1))) := by
  let p := sharpPolynomials A n
  let g := highOrderStageFactor (sharpRadius n) (A n) (sharpMultiplicity p n)
  have hm : 0 < sharpMultiplicity p n := sharpMultiplicity_pos _ _
  have hprod : (sharpPolynomials A (n + 1)).natDegree + 1 ≤
      (p.natDegree + 1) * (g.natDegree + 1) := by
    rw [sharpPolynomials_succ]
    change (p * g).natDegree + 1 ≤ _
    have hd := Polynomial.natDegree_mul_le (p := p) (q := g)
    calc
      (p * g).natDegree + 1 ≤ p.natDegree + g.natDegree + 1 :=
        Nat.add_le_add_right hd 1
      _ ≤ (p.natDegree + 1) * (g.natDegree + 1) := by
        nlinarith [Nat.zero_le (p.natDegree * g.natDegree)]
  have hg : g.natDegree + 1 ≤
      2 * sharpMultiplicity p n * 2 ^ (600 * (A n + 1)) := by
    exact highOrderStageFactor_natDegree_add_one_le_two_pow
      (sharpRadius_pos n) (hA n) hm
  exact hprod.trans (Nat.mul_le_mul_left (p.natDegree + 1) hg)

lemma index_le_of_four_mul_le
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (hfour : ∀ n, 4 * A n ≤ A (n + 1)) :
    ∀ n, n + 1 ≤ A n := by
  intro n
  induction n with
  | zero =>
      have := hA 0
      omega
  | succ n ih =>
      have h := hfour n
      omega

/-- Fourfold growth of the complexity absorbs the quadratic degree recurrence. -/
lemma sharpPolynomials_natDegree_add_one_le
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (hfour : ∀ n, 4 * A n ≤ A (n + 1)) :
    ∀ n, (sharpPolynomials A n).natDegree + 1 ≤ 2 ^ (1000 * A n) := by
  intro n
  induction n with
  | zero =>
      simp only [sharpPolynomials_zero, Polynomial.natDegree_X]
      exact (show 2 ≤ 2 ^ (1000 * A 0) by
        exact (show 2 ^ 1 ≤ 2 ^ (1000 * A 0) by
          exact Nat.pow_le_pow_right (by norm_num) (by have := hA 0; omega)))
  | succ n ih =>
      let p := sharpPolynomials A n
      let d := p.natDegree
      let m := sharpMultiplicity p n
      have hdeg := sharpPolynomials_natDegree_succ_le hA n
      have hm : m ≤ 12 * (n + 1) * (d + 1) := sharpMultiplicity_le p n
      have hnA : n + 1 ≤ A n := index_le_of_four_mul_le hA hfour n
      have hlin0 : 32 * (n + 1) ≤ 32 * A n := Nat.mul_le_mul_left 32 hnA
      have hlin : 32 * (n + 1) ≤ 2 ^ (10 * A n) :=
        hlin0.trans (thirtytwo_mul_le_two_pow_ten_mul (A n) (hA n))
      have hquad : (d + 1) ^ 2 ≤ (2 ^ (1000 * A n)) ^ 2 := by
        exact Nat.pow_le_pow_left ih 2
      have hcoarse :
          (sharpPolynomials A (n + 1)).natDegree + 1 ≤
            32 * (n + 1) * (d + 1) ^ 2 * 2 ^ (600 * (A n + 1)) := by
        change _ ≤ 32 * (n + 1) * (d + 1) ^ 2 * _
        calc
          (sharpPolynomials A (n + 1)).natDegree + 1 ≤
              (d + 1) * (2 * m * 2 ^ (600 * (A n + 1))) := hdeg
          _ ≤ (d + 1) *
              (2 * (12 * (n + 1) * (d + 1)) * 2 ^ (600 * (A n + 1))) := by
            gcongr
          _ = 24 * (n + 1) * (d + 1) ^ 2 * 2 ^ (600 * (A n + 1)) := by
            ring
          _ ≤ 32 * (n + 1) * (d + 1) ^ 2 * 2 ^ (600 * (A n + 1)) := by
            gcongr <;> norm_num
      have hpow :
          32 * (n + 1) * (d + 1) ^ 2 * 2 ^ (600 * (A n + 1)) ≤
            2 ^ (3210 * A n) := by
        calc
          32 * (n + 1) * (d + 1) ^ 2 * 2 ^ (600 * (A n + 1)) ≤
              2 ^ (10 * A n) * (2 ^ (1000 * A n)) ^ 2 *
                2 ^ (600 * (A n + 1)) := by gcongr
          _ = 2 ^ (2010 * A n + 600 * (A n + 1)) := by
            have hsquare : (2 ^ (1000 * A n)) ^ 2 = 2 ^ (2000 * A n) := by
              rw [← pow_mul]
              congr 1
              ring
            rw [hsquare]
            have he : 10 * A n + 2000 * A n = 2010 * A n := by omega
            rw [← he, pow_add, pow_add]
          _ ≤ 2 ^ (3210 * A n) := by
            apply Nat.pow_le_pow_right (by norm_num)
            have := hA n
            omega
      exact (hcoarse.trans hpow).trans
        (Nat.pow_le_pow_right (by norm_num) (by
          have h := hfour n
          omega : 3210 * A n ≤ 1000 * A (n + 1)))

/-- The polynomial visible on the `n`th annulus is controlled by the current, rather than the
next, complexity.  This one-step form is what permits comparison with `φ(r)` for `r ≥ 4^n`. -/
lemma sharpPolynomials_succ_natDegree_add_one_le
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (hfour : ∀ n, 4 * A n ≤ A (n + 1))
    (n : ℕ) :
    (sharpPolynomials A (n + 1)).natDegree + 1 ≤ 2 ^ (3210 * A n) := by
  let p := sharpPolynomials A n
  let d := p.natDegree
  let m := sharpMultiplicity p n
  have hdeg := sharpPolynomials_natDegree_succ_le hA n
  have hp : d + 1 ≤ 2 ^ (1000 * A n) :=
    sharpPolynomials_natDegree_add_one_le hA hfour n
  have hm : m ≤ 12 * (n + 1) * (d + 1) := sharpMultiplicity_le p n
  have hnA : n + 1 ≤ A n := index_le_of_four_mul_le hA hfour n
  have hlin : 32 * (n + 1) ≤ 2 ^ (10 * A n) :=
    (Nat.mul_le_mul_left 32 hnA).trans
      (thirtytwo_mul_le_two_pow_ten_mul (A n) (hA n))
  have hquad : (d + 1) ^ 2 ≤ (2 ^ (1000 * A n)) ^ 2 :=
    Nat.pow_le_pow_left hp 2
  calc
    (sharpPolynomials A (n + 1)).natDegree + 1 ≤
        (d + 1) * (2 * m * 2 ^ (600 * (A n + 1))) := hdeg
    _ ≤ (d + 1) *
        (2 * (12 * (n + 1) * (d + 1)) * 2 ^ (600 * (A n + 1))) := by
      gcongr
    _ = 24 * (n + 1) * (d + 1) ^ 2 * 2 ^ (600 * (A n + 1)) := by ring
    _ ≤ 32 * (n + 1) * (d + 1) ^ 2 * 2 ^ (600 * (A n + 1)) := by
      gcongr <;> norm_num
    _ ≤ 2 ^ (10 * A n) * (2 ^ (1000 * A n)) ^ 2 *
        2 ^ (600 * (A n + 1)) := by gcongr
    _ = 2 ^ (2010 * A n + 600 * (A n + 1)) := by
      have hsquare : (2 ^ (1000 * A n)) ^ 2 = 2 ^ (2000 * A n) := by
        rw [← pow_mul]
        congr 1
        ring
      rw [hsquare]
      have he : 10 * A n + 2000 * A n = 2010 * A n := by omega
      rw [← he, pow_add, pow_add]
    _ ≤ 2 ^ (3210 * A n) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have := hA n
      omega

lemma six_mul_le_two_pow_four_mul (B : ℕ) (hB : 0 < B) :
    6 * B ≤ 2 ^ (4 * B) := by
  induction B with
  | zero => omega
  | succ B ih =>
      by_cases hB0 : B = 0
      · subst B
        norm_num
      · have ih' := ih (Nat.pos_of_ne_zero hB0)
        rw [show 4 * (B + 1) = 4 * B + 4 by ring, pow_add]
        norm_num
        have hp : 1 ≤ 2 ^ (4 * B) := one_le_pow₀ (by norm_num)
        omega

/-- A purely numerical pointwise bound on the entire limit in the `n`th annulus. -/
lemma sharpFunction_norm_le_on_annulus
    {A : ℕ → ℕ} (hA : ∀ n, 0 < A n) (hfour : ∀ n, 4 * A n ≤ A (n + 1))
    (n : ℕ) {z : ℂ} (hz1 : 1 ≤ ‖z‖) (hzT : ‖z‖ ≤ sharpRadius (n + 1)) :
    ‖sharpFunction A z‖ ≤
      ((2 ^ (9 * A n * 2 ^ (3210 * A n)) : ℕ) : ℝ) := by
  let p := sharpPolynomials A (n + 1)
  let Q := 2 ^ (3210 * A n)
  have hQ : 0 < Q := pow_pos (by norm_num) _
  have hdeg : p.natDegree + 1 ≤ Q :=
    sharpPolynomials_succ_natDegree_add_one_le hA hfour n
  have hd : p.natDegree ≤ Q := (Nat.le_succ p.natDegree).trans hdeg
  have hnA : n + 1 ≤ A n := index_le_of_four_mul_le hA hfour n
  have hr : ‖z‖ ≤ ((4 ^ (A n) : ℕ) : ℝ) := by
    calc
      ‖z‖ ≤ sharpRadius (n + 1) := hzT
      _ ≤ sharpRadius (A n) := sharpRadius_mono hnA
      _ = ((4 ^ (A n) : ℕ) : ℝ) := by simp [sharpRadius]
  have hp0 := sharpPolynomials_global_bound hA (n + 1) z
  have hmax : max 1 ‖z‖ = ‖z‖ := max_eq_right hz1
  have hpow : ‖z‖ ^ p.natDegree ≤
      (2 : ℝ) ^ (2 * A n * Q) := by
    calc
      ‖z‖ ^ p.natDegree ≤ (((4 ^ A n : ℕ) : ℝ)) ^ p.natDegree := by gcongr
      _ ≤ (((4 ^ A n : ℕ) : ℝ)) ^ Q := by
        exact pow_le_pow_right₀ (by
          exact_mod_cast (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 4) : 1 ≤ 4 ^ A n)) hd
      _ = (2 : ℝ) ^ (2 * A n * Q) := by
        have hnat : (4 ^ A n) ^ Q = 2 ^ (2 * A n * Q) := by
          calc
            (4 ^ A n) ^ Q = 4 ^ (A n * Q) := (pow_mul 4 (A n) Q).symm
            _ = (2 ^ 2) ^ (A n * Q) := by norm_num
            _ = 2 ^ (2 * (A n * Q)) := (pow_mul 2 2 (A n * Q)).symm
            _ = 2 ^ (2 * A n * Q) := by ring
        exact_mod_cast hnat
  have hcoeffNat : 3 * (p.natDegree + 1) ≤ 2 ^ (6 * Q) := by
    calc
      3 * (p.natDegree + 1) ≤ 2 ^ (6 * (p.natDegree + 1)) :=
        three_mul_le_two_pow_six_mul
      _ ≤ 2 ^ (6 * Q) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left 6 hdeg)
  have hcoeff : (3 * (p.natDegree + 1) : ℝ) ≤ (2 : ℝ) ^ (6 * Q) := by
    exact_mod_cast hcoeffNat
  have hp : ‖p.eval z‖ ≤ (2 : ℝ) ^ (8 * A n * Q) := by
    calc
      ‖p.eval z‖ ≤ (p.natDegree + 1 : ℕ) * 3 *
          (max 1 ‖z‖) ^ p.natDegree := hp0
      _ = (3 * (p.natDegree + 1) : ℝ) * ‖z‖ ^ p.natDegree := by
        rw [hmax]
        push_cast
        ring
      _ ≤ (2 : ℝ) ^ (6 * Q) * (2 : ℝ) ^ (2 * A n * Q) := by
        exact mul_le_mul hcoeff hpow (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (6 * Q + 2 * A n * Q) := by rw [← pow_add]
      _ ≤ (2 : ℝ) ^ (8 * A n * Q) := by
        apply pow_le_pow_right₀ (by norm_num)
        have hA1 : 1 ≤ A n := by omega
        have hQAQ : Q ≤ A n * Q := by
          simpa only [one_mul] using Nat.mul_le_mul_right Q hA1
        calc
          6 * Q + 2 * A n * Q ≤ 6 * (A n * Q) + 2 * A n * Q := by
            exact Nat.add_le_add_right (Nat.mul_le_mul_left 6 hQAQ) _
          _ = 8 * A n * Q := by ring
  have htail := sharpFunction_sub_polynomial_succ_norm_le hA n hzT
  have herr : sharpError n ≤ 1 := by
    unfold sharpError
    exact pow_le_one₀ (by norm_num) (by norm_num)
  calc
    ‖sharpFunction A z‖ ≤ ‖p.eval z‖ +
        ‖sharpFunction A z - p.eval z‖ := by
      have := norm_add_le (p.eval z) (sharpFunction A z - p.eval z)
      simpa [add_comm] using this
    _ ≤ (2 : ℝ) ^ (8 * A n * Q) + 1 := add_le_add hp (htail.trans herr)
    _ ≤ (2 : ℝ) ^ (8 * A n * Q + 1) := by
      calc
        (2 : ℝ) ^ (8 * A n * Q) + 1 ≤
            (2 : ℝ) ^ (8 * A n * Q) + (2 : ℝ) ^ (8 * A n * Q) := by
          gcongr
          exact one_le_pow₀ (by norm_num)
        _ = (2 : ℝ) ^ (8 * A n * Q + 1) := by rw [pow_succ]; ring
    _ ≤ (2 : ℝ) ^ (9 * A n * Q) := by
      apply pow_le_pow_right₀ (by norm_num)
      have hA1 : 1 ≤ A n := by omega
      have hQ1 : 1 ≤ Q := by omega
      have hAQ1 : 1 ≤ A n * Q := by
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      calc
        8 * A n * Q + 1 ≤ 8 * A n * Q + A n * Q := Nat.add_le_add_left hAQ1 _
        _ = 9 * A n * Q := by ring
    _ = ((2 ^ (9 * A n * 2 ^ (3210 * A n)) : ℕ) : ℝ) := by
      change (2 : ℝ) ^ (9 * A n * Q) = _
      norm_cast

/-! ## Extracting a summable scale from the integral hypothesis -/

noncomputable def phiSample (φ : ℝ → ℝ) (n : ℕ) : ℝ :=
  (16 : ℝ) ^ n / φ (sharpRadius n)

noncomputable def sharpSamplingInterval (n : ℕ) : Set ℝ :=
  Set.Ioc (sharpRadius n) (2 * sharpRadius n)

lemma sharpRadius_sq (n : ℕ) : sharpRadius n ^ 2 = (16 : ℝ) ^ n := by
  unfold sharpRadius
  calc
    ((4 : ℝ) ^ n) ^ 2 = 4 ^ (n * 2) := (pow_mul 4 n 2).symm
    _ = 4 ^ (2 * n) := by rw [mul_comm]
    _ = (4 ^ 2) ^ n := pow_mul 4 2 n
    _ = (16 : ℝ) ^ n := by norm_num

lemma pairwise_disjoint_sharpSamplingInterval :
    Pairwise (fun n m ↦ Disjoint (sharpSamplingInterval n) (sharpSamplingInterval m)) := by
  intro n m hnm
  have hforward {a b : ℕ} (hab : a < b) :
      Disjoint (sharpSamplingInterval a) (sharpSamplingInterval b) := by
    apply Set.Ioc_disjoint_Ioc_of_le
    calc
      2 * sharpRadius a ≤ sharpRadius (a + 1) := by
        rw [sharpRadius_succ]
        unfold stageOuterRadius
        nlinarith [sharpRadius_pos a]
      _ ≤ sharpRadius b := sharpRadius_mono (by omega)
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact hforward hlt
  · exact (hforward hgt).symm

lemma iUnion_sharpSamplingInterval_subset_Ioi :
    (⋃ n : ℕ, sharpSamplingInterval n) ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact (sharpRadius_pos n).trans hn.1

lemma phiSample_nonneg
    {φ : ℝ → ℝ} (hφpos : ∀ r, 0 ≤ r → 0 < φ r) (n : ℕ) :
    0 ≤ phiSample φ n := by
  unfold phiSample
  exact div_nonneg (pow_nonneg (by norm_num) _)
    (hφpos (sharpRadius n) (sharpRadius_pos n).le).le

lemma phiSample_succ_le_integral
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) (n : ℕ) :
    phiSample φ (n + 1) ≤
      16 * ∫ r in sharpSamplingInterval n, r / φ r := by
  let R := sharpRadius n
  let S := sharpRadius (n + 1)
  have hR : 0 < R := sharpRadius_pos n
  have hS : 0 < S := sharpRadius_pos (n + 1)
  have hRS : S = 4 * R := sharpRadius_succ n
  have hsub : sharpSamplingInterval n ⊆ Set.Ioi (0 : ℝ) := by
    intro r hr
    exact hR.trans hr.1
  have hgint : IntegrableOn (fun r : ℝ ↦ r / φ r) (sharpSamplingInterval n) :=
    hInt.mono_set hsub
  have hcint : IntegrableOn (fun _ : ℝ ↦ R / φ S) (sharpSamplingInterval n) := by
    unfold sharpSamplingInterval
    exact continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hpoint : ∀ r ∈ sharpSamplingInterval n, R / φ S ≤ r / φ r := by
    intro r hr
    have hr0 : 0 ≤ r := (hR.trans hr.1).le
    have hrS : r ≤ S := by
      rw [hRS]
      nlinarith [hr.2, hR]
    have hφr : 0 < φ r := hφpos r hr0
    have hφS : 0 < φ S := hφpos S hS.le
    exact div_le_div₀ hr0 hr.1.le hφr (hφmono hrS)
  have hmono : (∫ _ in sharpSamplingInterval n, R / φ S) ≤
      ∫ r in sharpSamplingInterval n, r / φ r :=
    setIntegral_mono_on hcint hgint measurableSet_Ioc hpoint
  have hconst : (∫ _ in sharpSamplingInterval n, R / φ S) = R ^ 2 / φ S := by
    unfold sharpSamplingInterval
    rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioc]
    have heq : 2 * sharpRadius n - sharpRadius n = R := by
      dsimp only [R]
      ring
    rw [heq, ENNReal.toReal_ofReal hR.le]
    change R * (R / φ S) = R ^ 2 / φ S
    field_simp
  calc
    phiSample φ (n + 1) = 16 * (R ^ 2 / φ S) := by
      unfold phiSample S R
      rw [sharpRadius_sq, pow_succ]
      ring
    _ ≤ 16 * ∫ r in sharpSamplingInterval n, r / φ r :=
      mul_le_mul_of_nonneg_left (hconst ▸ hmono) (by norm_num)

lemma summable_phiSample
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) :
    Summable (phiSample φ) := by
  let g : ℝ → ℝ := fun r ↦ r / φ r
  have hgint : IntegrableOn g (⋃ n : ℕ, sharpSamplingInterval n) :=
    hInt.mono_set iUnion_sharpSamplingInterval_subset_Ioi
  have hsumInt : Summable (fun n : ℕ ↦ ∫ r in sharpSamplingInterval n, g r) :=
    (hasSum_integral_iUnion (fun _ ↦ measurableSet_Ioc)
      pairwise_disjoint_sharpSamplingInterval hgint).summable
  have hsumMajor : Summable (fun n : ℕ ↦
      16 * ∫ r in sharpSamplingInterval n, g r) := hsumInt.mul_left 16
  have htail : Summable (fun n : ℕ ↦ phiSample φ (n + 1)) := by
    apply Summable.of_nonneg_of_le
    · intro n
      exact phiSample_nonneg hφpos (n + 1)
    · intro n
      exact phiSample_succ_le_integral hφmono hφpos hInt n
    · exact hsumMajor
  exact (summable_nat_add_iff (f := phiSample φ) 1).mp
    (by simpa only [Nat.add_comm] using htail)

noncomputable def smoothDenominator (φ : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, (1 / 4 : ℝ) ^ k * phiSample φ (n + k)

noncomputable def smoothScale (φ : ℝ → ℝ) (n : ℕ) : ℝ :=
  (16 : ℝ) ^ n / smoothDenominator φ n

lemma summable_smoothKernel : Summable (fun k : ℕ ↦ (1 / 4 : ℝ) ^ k) :=
  summable_geometric_of_norm_lt_one (by norm_num)

lemma summable_smoothPair
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) :
    Summable (fun p : ℕ × ℕ ↦
      (1 / 4 : ℝ) ^ p.2 * phiSample φ (p.1 + p.2)) := by
  have ht := summable_phiSample hφmono hφpos hInt
  have hprod : Summable (fun p : ℕ × ℕ ↦
      phiSample φ p.1 * (1 / 4 : ℝ) ^ p.2) := by
    apply summable_mul_of_summable_norm
    · simpa only [Real.norm_eq_abs, abs_of_nonneg (phiSample_nonneg hφpos _)] using ht
    · simpa only [Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) _)] using
          summable_smoothKernel
  have hinj : Function.Injective (fun p : ℕ × ℕ ↦ (p.1 + p.2, p.2)) := by
    rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ hpq
    simp only [Prod.mk.injEq] at hpq ⊢
    omega
  have hc := hprod.comp_injective hinj
  change Summable (fun p : ℕ × ℕ ↦
    phiSample φ (p.1 + p.2) * (1 / 4 : ℝ) ^ p.2) at hc
  simpa only [mul_comm] using hc

lemma summable_smoothDenominator
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) :
    Summable (smoothDenominator φ) := by
  change Summable (fun n : ℕ ↦
    ∑' k : ℕ, (1 / 4 : ℝ) ^ k * phiSample φ (n + k))
  exact (summable_smoothPair hφmono hφpos hInt).prod

lemma summable_smoothDenominator_term
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) (n : ℕ) :
    Summable (fun k : ℕ ↦ (1 / 4 : ℝ) ^ k * phiSample φ (n + k)) := by
  exact (summable_smoothPair hφmono hφpos hInt).prod_factor n

lemma phiSample_le_smoothDenominator
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) (n : ℕ) :
    phiSample φ n ≤ smoothDenominator φ n := by
  have hs := summable_smoothDenominator_term hφmono hφpos hInt n
  have hle := hs.sum_le_tsum (Finset.range 1) (fun k hk ↦ by
    exact mul_nonneg (pow_nonneg (by norm_num) _) (phiSample_nonneg hφpos _))
  simpa [smoothDenominator] using hle

lemma smoothDenominator_pos
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) (n : ℕ) :
    0 < smoothDenominator φ n := by
  have ht : 0 < phiSample φ n := by
    unfold phiSample
    exact div_pos (pow_pos (by norm_num) _) (hφpos _ (sharpRadius_pos n).le)
  exact ht.trans_le (phiSample_le_smoothDenominator hφmono hφpos hInt n)

lemma smoothDenominator_succ_le_four_mul
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) (n : ℕ) :
    smoothDenominator φ (n + 1) ≤ 4 * smoothDenominator φ n := by
  let F : ℕ → ℝ := fun k ↦ (1 / 4 : ℝ) ^ k * phiSample φ (n + k)
  have hF := summable_smoothDenominator_term hφmono hφpos hInt n
  have hsplit := hF.sum_add_tsum_nat_add 1
  have htail : (∑' k : ℕ, F (k + 1)) =
      (1 / 4 : ℝ) * smoothDenominator φ (n + 1) := by
    unfold F smoothDenominator
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [pow_succ']
    have heq : n + (k + 1) = n + 1 + k := by omega
    rw [heq]
    ring
  have hnonneg : 0 ≤ phiSample φ n := phiSample_nonneg hφpos n
  have hquarter : (1 / 4 : ℝ) * smoothDenominator φ (n + 1) ≤
      smoothDenominator φ n := by
    rw [← htail]
    unfold smoothDenominator
    rw [← hsplit]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, F, pow_zero,
      one_mul, Nat.zero_add]
    exact le_add_of_nonneg_left hnonneg
  nlinarith

lemma smoothScale_pos
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) (n : ℕ) :
    0 < smoothScale φ n := by
  unfold smoothScale
  exact div_pos (pow_pos (by norm_num) _)
    (smoothDenominator_pos hφmono hφpos hInt n)

lemma smoothScale_le_phi
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) (n : ℕ) :
    smoothScale φ n ≤ φ (sharpRadius n) := by
  have hb := phiSample_le_smoothDenominator hφmono hφpos hInt n
  have hbp := smoothDenominator_pos hφmono hφpos hInt n
  have hφp := hφpos (sharpRadius n) (sharpRadius_pos n).le
  unfold smoothScale phiSample at *
  rw [div_le_iff₀ hbp]
  rw [div_le_iff₀ hφp] at hb
  nlinarith

lemma four_mul_smoothScale_le_succ
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) (n : ℕ) :
    4 * smoothScale φ n ≤ smoothScale φ (n + 1) := by
  have hb := smoothDenominator_succ_le_four_mul hφmono hφpos hInt n
  have hbn := smoothDenominator_pos hφmono hφpos hInt n
  have hbs := smoothDenominator_pos hφmono hφpos hInt (n + 1)
  unfold smoothScale
  rw [pow_succ]
  field_simp [hbn.ne', hbs.ne']
  nlinarith

/-- Integer complexities: the ceiling supplies the analytic scale and `16^n` absorbs the
rounding loss while preserving the finite-area inequality. -/
noncomputable def regularizedComplexity (φ : ℝ → ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (smoothScale φ n) + 16 ^ n

lemma regularizedComplexity_pos (φ : ℝ → ℝ) (n : ℕ) :
    0 < regularizedComplexity φ n := by
  unfold regularizedComplexity
  have : 0 < 16 ^ n := pow_pos (by norm_num) _
  omega

lemma regularizedComplexity_four_mul_le
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) (n : ℕ) :
    4 * regularizedComplexity φ n ≤ regularizedComplexity φ (n + 1) := by
  let a := smoothScale φ n
  let b := smoothScale φ (n + 1)
  have ha0 : 0 ≤ a := (smoothScale_pos hφmono hφpos hInt n).le
  have hb0 : 0 ≤ b := (smoothScale_pos hφmono hφpos hInt (n + 1)).le
  have hab : 4 * a ≤ b := four_mul_smoothScale_le_succ hφmono hφpos hInt n
  have hceilA : (Nat.ceil a : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
  have hceilB : b ≤ (Nat.ceil b : ℝ) := Nat.le_ceil b
  have hpow : (1 : ℝ) ≤ (16 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  apply_mod_cast (show
    (4 : ℝ) * ((Nat.ceil a : ℝ) + (16 : ℝ) ^ n) ≤
      (Nat.ceil b : ℝ) + (16 : ℝ) ^ (n + 1) by
    rw [pow_succ]
    calc
      (4 : ℝ) * ((Nat.ceil a : ℝ) + 16 ^ n) ≤
          4 * (a + 1 + 16 ^ n) := by nlinarith
      _ ≤ b + 4 + 4 * 16 ^ n := by nlinarith
      _ ≤ (Nat.ceil b : ℝ) + 16 ^ n * 16 := by nlinarith)

lemma regularizedComplexity_cast_ge_scale
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) (n : ℕ) :
    smoothScale φ n ≤ (regularizedComplexity φ n : ℝ) := by
  unfold regularizedComplexity
  push_cast
  exact (Nat.le_ceil (smoothScale φ n)).trans (le_add_of_nonneg_right (by positivity))

lemma sharpAreaTerm_regularized_le
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) (n : ℕ) :
    sharpAreaTerm (regularizedComplexity φ) n ≤ smoothDenominator φ n := by
  have ha := regularizedComplexity_cast_ge_scale hφmono hφpos hInt n
  have hscale := smoothScale_pos hφmono hφpos hInt n
  have hA : (0 : ℝ) < regularizedComplexity φ n := by
    exact_mod_cast regularizedComplexity_pos φ n
  have hdiv : (16 : ℝ) ^ n / (regularizedComplexity φ n : ℝ) ≤
      (16 : ℝ) ^ n / smoothScale φ n := by
    exact div_le_div_of_nonneg_left (pow_nonneg (by norm_num) _) hscale ha
  calc
    sharpAreaTerm (regularizedComplexity φ) n =
        (16 : ℝ) ^ n / (regularizedComplexity φ n : ℝ) := by
      unfold sharpAreaTerm
      rw [sharpRadius_sq]
    _ ≤ (16 : ℝ) ^ n / smoothScale φ n := hdiv
    _ = smoothDenominator φ n := by
      unfold smoothScale
      have hp : (16 : ℝ) ^ n ≠ 0 := (pow_pos (by norm_num) _).ne'
      have hb := (smoothDenominator_pos hφmono hφpos hInt n).ne'
      field_simp

lemma summable_regularizedAreaTerm
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) :
    Summable (sharpAreaTerm (regularizedComplexity φ)) := by
  apply Summable.of_nonneg_of_le
  · exact sharpAreaTerm_nonneg (regularizedComplexity_pos φ)
  · exact sharpAreaTerm_regularized_le hφmono hφpos hInt
  · exact summable_smoothDenominator hφmono hφpos hInt

lemma regularizedComplexity_cast_le
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) (n : ℕ) :
    (regularizedComplexity φ n : ℝ) ≤
      φ (sharpRadius n) + 1 + (16 : ℝ) ^ n := by
  unfold regularizedComplexity
  push_cast
  calc
    (Nat.ceil (smoothScale φ n) : ℝ) + (16 : ℝ) ^ n ≤
        smoothScale φ n + 1 + 16 ^ n := by
      nlinarith [Nat.ceil_lt_add_one (smoothScale_pos hφmono hφpos hInt n).le]
    _ ≤ φ (sharpRadius n) + 1 + 16 ^ n := by
      linarith [smoothScale_le_phi hφmono hφpos hInt n]

/-- The regularized integer complexity is bounded by a constant multiple of the original
growth gauge at every sampled radius. -/
lemma exists_regularizedComplexity_le_phi
    {φ : ℝ → ℝ} (hφmono : Monotone φ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hInt : IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      (regularizedComplexity φ n : ℝ) ≤ K * φ (sharpRadius n) := by
  have hsum := summable_phiSample hφmono hφpos hInt
  have htend : Tendsto (phiSample φ) atTop (𝓝 0) := hsum.tendsto_atTop_zero
  have hev : ∀ᶠ n in atTop, phiSample φ n < 1 := by
    have := htend.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
    filter_upwards [this] with n hn
    have habs : |phiSample φ n| < 1 := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hn
    exact (abs_lt.mp habs).2
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  let q : ℕ → ℝ := fun n ↦ (regularizedComplexity φ n : ℝ) / φ (sharpRadius n)
  let K : ℝ := 3 + 1 / φ 1 + ∑ n ∈ Finset.range N, q n
  have hφ1 : 0 < φ 1 := hφpos 1 (by norm_num)
  have hq0 (n : ℕ) : 0 ≤ q n := by
    unfold q
    exact div_nonneg (by positivity) (hφpos _ (sharpRadius_pos n).le).le
  have hK : 0 < K := by
    unfold K
    have hsum0 : 0 ≤ ∑ n ∈ Finset.range N, q n := Finset.sum_nonneg fun n _ ↦ hq0 n
    have hinv : 0 < 1 / φ 1 := by positivity
    linarith
  refine ⟨K, hK, fun n ↦ ?_⟩
  have hφn : 0 < φ (sharpRadius n) := hφpos _ (sharpRadius_pos n).le
  rw [← div_le_iff₀ hφn]
  change q n ≤ K
  by_cases hn : n < N
  · have hterm : q n ≤ ∑ j ∈ Finset.range N, q j := by
      exact Finset.single_le_sum (fun j _ ↦ hq0 j) (Finset.mem_range.mpr hn)
    unfold K
    linarith [show 0 < 1 / φ 1 by positivity]
  · have hnN : N ≤ n := Nat.le_of_not_gt hn
    have ht : (16 : ℝ) ^ n < φ (sharpRadius n) := by
      have hs := hN n hnN
      unfold phiSample at hs
      exact (div_lt_one hφn).mp hs
    have hbase := regularizedComplexity_cast_le hφmono hφpos hInt n
    have hφmono1 : φ 1 ≤ φ (sharpRadius n) :=
      hφmono (one_le_sharpRadius n)
    have hone : 1 ≤ (1 / φ 1) * φ (sharpRadius n) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hφ1]
      simpa [mul_comm] using hφmono1
    have hAn : (regularizedComplexity φ n : ℝ) ≤
        (2 + 1 / φ 1) * φ (sharpRadius n) := by
      nlinarith
    have hqn : q n ≤ 2 + 1 / φ 1 := by
      unfold q
      exact (div_le_iff₀ hφn).mpr hAn
    unfold K
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range N, q j := Finset.sum_nonneg fun j _ ↦ hq0 j
    linarith

/-! ## Converting the numerical stage bound into a double-logarithmic bound -/

lemma nine_mul_le_two_pow_four_mul (B : ℕ) (hB : 0 < B) :
    9 * B ≤ 2 ^ (4 * B) := by
  induction B with
  | zero => omega
  | succ B ih =>
      by_cases hB0 : B = 0
      · subst B
        norm_num
      · have ih' := ih (Nat.pos_of_ne_zero hB0)
        rw [show 4 * (B + 1) = 4 * B + 4 by ring, pow_add]
        norm_num
        have hp : 1 ≤ 2 ^ (4 * B) := one_le_pow₀ (by norm_num)
        omega

lemma stageExponentBound_le_two_pow {A : ℕ} (hA : 0 < A) :
    9 * A * 2 ^ (3210 * A) + 1 ≤ 2 ^ (3215 * A) := by
  have h9 := nine_mul_le_two_pow_four_mul A hA
  have hmul : 9 * A * 2 ^ (3210 * A) ≤ 2 ^ (3214 * A) := by
    calc
      9 * A * 2 ^ (3210 * A) ≤ 2 ^ (4 * A) * 2 ^ (3210 * A) :=
        Nat.mul_le_mul_right _ h9
      _ = 2 ^ (3214 * A) := by
        have he : 4 * A + 3210 * A = 3214 * A := by omega
        rw [← he, pow_add]
  have hp : 1 ≤ 2 ^ (3214 * A) := one_le_pow₀ (by norm_num)
  calc
    9 * A * 2 ^ (3210 * A) + 1 ≤
        2 ^ (3214 * A) + 2 ^ (3214 * A) := Nat.add_le_add hmul hp
    _ = 2 ^ (3214 * A + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ (3215 * A) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)

lemma real_two_pow_le_exp (N : ℕ) : (2 : ℝ) ^ N ≤ Real.exp N := by
  calc
    (2 : ℝ) ^ N ≤ (Real.exp 1) ^ N :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le N
    _ = Real.exp N := by
      rw [← Real.exp_nat_mul]
      norm_num

lemma log_log_le_of_stage_bound
    {A : ℕ} (hA : 0 < A) {x : ℝ} (hx1 : 1 < x)
    (hx : x ≤ (2 : ℝ) ^ (9 * A * 2 ^ (3210 * A) + 1)) :
    Real.log (Real.log x) ≤ 4000 * A := by
  let N : ℕ := 9 * A * 2 ^ (3210 * A) + 1
  have hN : 0 < N := by unfold N; omega
  have hNpow : N ≤ 2 ^ (3215 * A) := stageExponentBound_le_two_pow hA
  have hNexp : (N : ℝ) ≤ Real.exp (4000 * A) := by
    calc
      (N : ℝ) ≤ ((2 ^ (3215 * A) : ℕ) : ℝ) := by exact_mod_cast hNpow
      _ = (2 : ℝ) ^ (3215 * A) := by norm_cast
      _ ≤ Real.exp (3215 * A) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          real_two_pow_le_exp (3215 * A)
      _ ≤ Real.exp (4000 * A) := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith [show (0 : ℝ) < A by exact_mod_cast hA]
  have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
  have hlogx : Real.log x ≤ (N : ℝ) := by
    calc
      Real.log x ≤ Real.log ((2 : ℝ) ^ N) :=
        Real.log_le_log (by positivity) (by simpa only [N] using hx)
      _ = (N : ℝ) * Real.log 2 := by rw [Real.log_pow]
      _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hlogtwo (by positivity)
      _ = N := by ring
  calc
    Real.log (Real.log x) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (Real.log_pos hx1) hlogx
    _ ≤ Real.log (Real.exp (4000 * A)) :=
      Real.log_le_log (by exact_mod_cast hN) hNexp
    _ = 4000 * A := by rw [Real.log_exp]

end Erdos1118Sharp
